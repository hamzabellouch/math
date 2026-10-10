import Mathlib
import OAI.Analysis.MatrixSigning.Model
import OAI.Analysis.MatrixSigning.Matrices.Space
import OAI.Analysis.MatrixSigning.Potential.Normalizer

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
open scoped BigOperators ComplexOrder
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates

def coordinates (x : Input) (i : Fin x.N) : Fin x.d × Fin x.d → ℚ := fun p =>
  if p.1 ≤ p.2 then (x.entries i p.1 p.2).1.value else (x.entries i p.2 p.1).2.value

def trace (x : Input) (i : Fin x.N) : ℚ := ∑ j,(x.entries i j j).1.value

def orientation (x : Input) (i : Fin x.N) : ℚ := if 0 ≤ trace x i then 1 else -1

def scale (x : Input) : ℚ := ∑ i,|trace x i|

def indices (x : Input) : List (Fin x.N) :=
  (List.finRange x.N).filter (fun i => decide (trace x i ≠ 0))

def index (x : Input) : Fin (indices x).length → Fin x.N := (indices x).get

def normalizedCoordinates (x : Input) (j : Fin (indices x).length) : Fin x.d × Fin x.d → ℚ :=
  (scale x)⁻¹ • (orientation x (index x j) • coordinates x (index x j))

lemma index_injective (x : Input) : Function.Injective (index x) :=
  ((List.nodup_finRange x.N).filter _).injective_get

lemma index_range (x : Input) (i : Fin x.N) : (∃ j,index x j=i) ↔ trace x i ≠ 0 := by
  change (∃ j,(indices x).get j=i) ↔ _
  rw [← List.mem_iff_get]
  simp [indices]

lemma index_trace_ne (x : Input) (j : Fin (indices x).length) : trace x (index x j) ≠ 0 :=
  (index_range x _).mp ⟨j,rfl⟩

lemma indices_length_le (x : Input) : (indices x).length ≤ x.N := by
  have hh := List.length_filter_le (fun i => decide (trace x i ≠ 0)) (List.finRange x.N)
  simp only [List.length_finRange] at hh
  exact hh

noncomputable section

lemma trace_cast (x : Input) (i : Fin x.N) : (trace x i : ℝ)=CurrentKS.realTrace (x.matrix i) := by
  simp [trace,CurrentKS.realTrace,Matrix.trace,Matrix.diag,Input.matrix,toComplex]

lemma orientation_cast (x : Input) (i : Fin x.N) : (orientation x i : ℝ)=traceSign (x.matrix i) := by
  have hh : 0 ≤ trace x i ↔ (0:ℝ) ≤ CurrentKS.realTrace (x.matrix i) := by
    rw [←trace_cast];exact_mod_cast Iff.rfl
  simp only [orientation,traceSign,hh]
  split_ifs <;> norm_num

lemma scale_cast (x : Input) : (scale x : ℝ)=normalizer x.matrix := by
  simp [scale,normalizer,←trace_cast]

lemma coordinates_cast (x : Input) (hx : Admissible x) (i : Fin x.N) :
    (fun p => (coordinates x i p:ℝ))=HermitianCoordinates.encode ⟨x.matrix i,(hx i).1⟩ := by
  funext p
  simp only [coordinates,HermitianCoordinates.encode,Input.matrix,Matrix.map_apply,toComplex]
  split_ifs <;> rfl

lemma decode_coordinates (x : Input) (hx : Admissible x) (i : Fin x.N) :
    decode (fun p => (coordinates x i p:ℝ))=x.matrix i := by
  rw [coordinates_cast x hx i]
  exact congrArg Subtype.val (assemble_extract (⟨x.matrix i,(hx i).1⟩ : H x.d))

lemma trace_zero_iff (x : Input) (hx : Admissible x) (i : Fin x.N) :
    trace x i=0 ↔ x.matrix i=0 := by
  rw [← realTrace_eq_zero_iff (x.matrix i) (hx i).1 (hx i).2,←trace_cast]
  exact_mod_cast Iff.rfl

lemma scale_pos (x : Input) (hne : (indices x).length ≠ 0) : 0 < scale x := by
  have hl : 0 < (indices x).length := Nat.pos_of_ne_zero hne
  let j : Fin (indices x).length := ⟨0,hl⟩
  exact Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨index x j,Finset.mem_univ _,
    abs_pos.mpr (index_trace_ne x j)⟩

lemma dimension_ne (x : Input) (hx : Admissible x) (hne : (indices x).length ≠ 0) : x.d ≠ 0 := by
  intro hd
  let i := index x ⟨0,Nat.pos_of_ne_zero hne⟩
  have hz : x.matrix i=0 := by
    ext j k
    have hj := j.isLt
    omega
  exact index_trace_ne x _ ((trace_zero_iff x hx i).mpr hz)

lemma decode_normalizedCoordinates (x : Input) (hx : Admissible x) (j : Fin (indices x).length) :
    decode (fun p => (normalizedCoordinates x j p:ℝ))=normalizedMatrix x.matrix (index x j) := by
  have he : (fun p => (normalizedCoordinates x j p:ℝ))=
      (scale x:ℝ)⁻¹ • ((orientation x (index x j):ℝ) • (fun p => (coordinates x (index x j) p:ℝ))) := by
    funext p
    simp [normalizedCoordinates]
  rw [he,decode_smul,decode_smul,decode_coordinates x hx,scale_cast,orientation_cast]
  rfl

lemma normalized_input_properties (x : Input) (hx : Admissible x)
    (hne : (indices x).length ≠ 0) :
    let A := fun j => assemble (WithLp.toLp 2 fun p => (normalizedCoordinates x j p:ℝ))
    (∀ j,A j∈psdCone x.d) ∧ (∀ j,A j≠0) ∧
    (∀ j,(A j:Mat x.d).rank ≤ 1) ∧ (∑ j,Hermitian.realTrace (A j))=1 := by
  let A := fun j => assemble (WithLp.toLp 2 fun p => (normalizedCoordinates x j p:ℝ))
  have hA (j) : (A j:Mat x.d)=normalizedMatrix x.matrix (index x j) :=
    decode_normalizedCoordinates x hx j
  have hD : normalizer x.matrix ≠ 0 := by
    rw [←scale_cast]
    exact_mod_cast (scale_pos x hne).ne'
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    change (A j:Mat x.d).PosSemidef
    rw [hA]
    exact normalizedMatrix_posSemidef x.matrix (fun i => (hx i).1) (fun i => (hx i).2) _
  · intro j hj
    change A j=0 at hj
    have hz : normalizedMatrix x.matrix (index x j)=0 := by rw [←hA j,hj];rfl
    exact index_trace_ne x j ((trace_zero_iff x hx _).mpr
      ((normalizedMatrix_eq_zero_iff x.matrix hD _).mp hz))
  · intro j
    rw [hA]
    exact normalizedMatrix_rank x.matrix (fun i => (hx i).2) _
  · change (∑ j,Hermitian.realTrace (A j))=1
    have he : (∑ j,CurrentKS.realTrace (normalizedMatrix x.matrix (index x j)))=
        ∑ i,CurrentKS.realTrace (normalizedMatrix x.matrix i) := by
      apply Fintype.sum_of_injective (index x) (index_injective x)
      · intro i hi
        have hz : trace x i=0 := by
          by_contra hz
          exact hi ((index_range x i).mpr hz)
        have hm := (trace_zero_iff x hx i).mp hz
        rw [(normalizedMatrix_eq_zero_iff x.matrix hD i).mpr hm]
        simp [CurrentKS.realTrace]
      · intro j;rfl
    have ht := normalized_trace_sum x.matrix hD
    rw [←he] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro j _
    change CurrentKS.realTrace (A j:Mat x.d)=_
    rw [hA]

end
end CurrentKS.RationalInput

end OAI
