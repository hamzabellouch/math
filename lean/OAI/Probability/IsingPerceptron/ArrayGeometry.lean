import Mathlib
import OAI.Probability.IsingPerceptron.ArraySynchronization
import OAI.Probability.IsingPerceptron.EnrichedGGFinite

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma spinOverlap_symm {N : ℕ} (x y : Spin N) : spinOverlap x y = spinOverlap y x := by
  simp only [spinOverlap,mul_comm]

lemma spinOverlap_posSemidef {N m : ℕ} (x : Fin m → Spin N) :
    Matrix.PosSemidef (fun i j => spinOverlap (x i) (x j)) := by
  let A : Matrix (Fin m) (Fin N) ℝ := fun i k => spinValue (x i k)
  have hp := (Matrix.posSemidef_self_mul_conjTranspose A).smul (inv_nonneg.mpr (Nat.cast_nonneg N : (0:ℝ) ≤ N))
  have he : (show Matrix (Fin m) (Fin m) ℝ from fun i j => spinOverlap (x i) (x j)) = (N:ℝ)⁻¹ • (A*Aᴴ) := by
    ext i j
    change (∑ k, spinValue (x i k)*spinValue (x j k))/(N:ℝ) =
      (N:ℝ)⁻¹ * ∑ k, spinValue (x i k)*spinValue (x j k)
    ring
  rw [he]
  exact hp

lemma labeledCommonDepth_symm (n : ℕ) (x y : LabeledLeaf n) :
    labeledCommonDepth n x y = labeledCommonDepth n y x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [labeledCommonDepth,eq_comm,ih]

lemma labeledCommonDepth_ultra (n : ℕ) (x y z : LabeledLeaf n) :
    min (labeledCommonDepth n x z) (labeledCommonDepth n y z) ≤ labeledCommonDepth n x y := by
  let d := min (labeledCommonDepth n x z) (labeledCommonDepth n y z)
  have hd : d ≤ n := (min_le_left _ _).trans (labeledCommonDepth_le n x z)
  apply (labeled_prefix_eq_iff n x y hd).mp
  exact ((labeled_prefix_eq_iff n x z hd).mpr (min_le_left _ _)).trans
    ((labeled_prefix_eq_iff n y z hd).mpr (min_le_right _ _)).symm

lemma treeOverlap_symm (n : ℕ) (x y : LabeledLeaf n) : treeOverlap n x y = treeOverlap n y x := by
  simp only [treeOverlap,labeledCommonDepth_symm n x y]

lemma treeOverlap_self (n : ℕ) (x : LabeledLeaf n) : treeOverlap n x x = (n:ℝ)/(n+1:ℕ) := by
  simp only [treeOverlap,labeledCommonDepth_self]

lemma treeOverlap_ultra (n : ℕ) (x : ℕ → LabeledLeaf n) :
    IsUltrametricArray (fun i j => treeOverlap n (x i) (x j)) := by
  intro i j k
  have ht := labeledCommonDepth_ultra n (x i) (x j) (x k)
  have ht' : min (labeledCommonDepth n (x i) (x k) : ℝ) (labeledCommonDepth n (x j) (x k)) ≤
      labeledCommonDepth n (x i) (x j) := by exact_mod_cast ht
  simpa only [treeOverlap,min_div_div_right (by positivity : (0:ℝ) ≤ (n+1:ℕ))] using
    div_le_div_of_nonneg_right ht' (by positivity : (0:ℝ) ≤ (n+1:ℕ))

lemma labeledCommonDepth_sum (n : ℕ) (x y : LabeledLeaf n) :
    (∑ d ∈ Finset.range n, if (labeledAddress n x).take (d+1) =
      (labeledAddress n y).take (d+1) then (1:ℝ) else 0) = labeledCommonDepth n x y := by
  have hc := labeledCommonDepth_le n x y
  calc
    _ = ∑ d ∈ Finset.range n, if d < labeledCommonDepth n x y then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [labeled_prefix_eq_iff n x y (d := d+1) (by have := Finset.mem_range.mp hd; omega), Nat.add_one_le_iff]
    _ = labeledCommonDepth n x y := by
      simp only [Finset.sum_boole]
      congr 1
      have he : (Finset.range n).filter (fun d => d < labeledCommonDepth n x y) =
          Finset.range (labeledCommonDepth n x y) := by
        ext d
        simp only [Finset.mem_filter,Finset.mem_range]
        omega
      rw [he,Finset.card_range]

lemma treeOverlap_posSemidef (n : ℕ) {m : ℕ} (x : Fin m → LabeledLeaf n) :
    Matrix.PosSemidef (fun i j => treeOverlap n (x i) (x j)) := by
  classical
  let A : ℕ → Matrix (Fin m) (Fin m) ℝ := fun d =>
    Matrix.submatrix (1 : Matrix (List ChildLabel) (List ChildLabel) ℝ)
      (fun i => (labeledAddress n (x i)).take (d+1)) (fun i => (labeledAddress n (x i)).take (d+1))
  have hp (d : ℕ) : (A d).PosSemidef := Matrix.PosSemidef.one.submatrix _
  have hs := (Matrix.posSemidef_sum (Finset.range n) (fun d _ => hp d)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ)))
  have he : (fun i j => treeOverlap n (x i) (x j)) =
      ((n+1:ℕ):ℝ)⁻¹ • (∑ d ∈ Finset.range n, A d) := by
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,A,Matrix.submatrix_apply,Matrix.one_apply]
    rw [labeledCommonDepth_sum]
    simp only [treeOverlap,div_eq_mul_inv,mul_comm]
  rw [he]
  exact hs

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma replicaLaw_map_reindex {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : ℕ → ℕ) (he : Function.Injective e) :
    (replicaLaw P ν hν).map (fun σ i => σ (e i)) = replicaLaw P ν hν := by
  unfold replicaLaw
  rw [Measure.map_comp P _ (by fun_prop)]
  congr 1
  funext ω
  rw [Kernel.map_apply _ (by fun_prop)]
  exact Measure.map_infinitePi_infinitePi_of_inj he

def permuteJointArray (e : ℕ → ℕ) (x : JointArray) : JointArray :=
  fun ij => x (e ij.1,e ij.2)

lemma continuous_permuteJointArray (e : ℕ → ℕ) : Continuous (permuteJointArray e) := by
  unfold permuteJointArray
  fun_prop

lemma overlapArrayLaw_map_reindex {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (κ : X → X → JointEntry) (e : ℕ → ℕ) (he : Function.Injective e) :
    (overlapArrayLaw P ν hν κ : Measure JointArray).map (permuteJointArray e) =
      (overlapArrayLaw P ν hν κ : Measure JointArray) := by
  change ((replicaLaw P ν hν).map (sampledOverlapArray κ)).map _ = _
  rw [Measure.map_map (continuous_permuteJointArray e).measurable (measurable_sampledOverlapArray κ)]
  have hh : permuteJointArray e ∘ sampledOverlapArray κ =
      sampledOverlapArray κ ∘ (fun σ i => σ (e i)) := rfl
  rw [hh,← Measure.map_map (measurable_sampledOverlapArray κ) (by fun_prop),replicaLaw_map_reindex P ν hν e he]
  rfl

lemma jointArray_limit_reindex {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    (e : ℕ → ℕ) (hE : ∀ k, (L k : Measure JointArray).map (permuteJointArray e) = L k) :
    (μ : Measure JointArray).map (permuteJointArray e) = μ := by
  have hc := (ProbabilityMeasure.continuous_map (continuous_permuteJointArray e)).tendsto μ
  have he : (fun k => (L k).map (permuteJointArray e)) = L := by
    funext k
    exact Subtype.ext (hE k)
  have ht := hc.comp hL
  change Tendsto (fun k => (L k).map (permuteJointArray e)) _ _ at ht
  rw [he] at ht
  have h := tendsto_nhds_unique ht hL
  exact congrArg Subtype.val h

lemma scalar_of_joint_exchangeable {μ : ProbabilityMeasure JointArray}
    (hE : ∀ e : Equiv.Perm ℕ, (μ : Measure JointArray).map (permuteJointArray e) = μ)
    (f : JointEntry → ℝ) (hf : Measurable f) :
    WeaklyExchangeable (fun x i j => f (x (i,j))) (μ : Measure JointArray) := by
  intro e _
  have hm : Measurable (fun x : JointArray => fun i j => f (x (i,j))) := by fun_prop
  refine ⟨hm.aemeasurable,(hm.comp (continuous_permuteJointArray e).measurable).aemeasurable,?_⟩
  calc
    _ = ((μ : Measure JointArray).map (permuteJointArray e)).map (fun x i j => f (x (i,j))) :=
      congrArg (Measure.map (fun x i j => f (x (i,j)))) (hE e).symm
    _ = _ := Measure.map_map hm (continuous_permuteJointArray e).measurable

lemma ae_closed_of_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {L : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hL : Tendsto L atTop (𝓝 μ)) {S : Set X} (hS : IsClosed S)
    (hA : ∀ k, ∀ᵐ x ∂(L k : Measure X), x ∈ S) : ∀ᵐ x ∂(μ : Measure X), x ∈ S := by
  have he : ∀ k, (L k : Measure X) S = 1 := fun k => by
    simpa using (ae_iff_measure_eq (μ := (L k : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mp (hA k)
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hL hS
  simp only [he,limsup_const] at hh
  apply (ae_iff_measure_eq (μ := (μ : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mpr
  rw [measure_univ]
  exact le_antisymm prob_le_one hh

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix
namespace IsingPerceptron

lemma HasGhirlandaGuerra.congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {B C : Ω → RealArray} {μ : Measure Ω} (h : HasGhirlandaGuerra B μ) (he : B =ᵐ[μ] C) :
    HasGhirlandaGuerra C μ := by
  have hm (P : RealArray → Prop) : μ.real {ω | P (C ω)} = μ.real {ω | P (B ω)} := by
    apply measureReal_congr
    filter_upwards [he] with ω hω
    rw [hω]
  intro n hn i A hA t ht
  change μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i n ∈ t} =
    (μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A} * μ.real {ω | C ω 0 1 ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) / n
  rw [hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i n ∈ t),
    hm (fun b => (fun j k : Fin n => b j k) ∈ A), hm (fun b => b 0 1 ∈ t)]
  have hs : (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) =
      ∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => B ω j k) ∈ A ∧ B ω i j ∈ t} := by
    apply Finset.sum_congr rfl
    intro j _
    exact hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i j ∈ t)
  rw [hs]
  exact h n hn i A hA t ht

def GramDiagonal (D : ℝ) (B : RealArray) : Prop :=
  (∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)) ∧ ∀ i, B i i = D

lemma isClosed_gramDiagonal (D : ℝ) : IsClosed {B | GramDiagonal D B} := by
  change IsClosed ({B : RealArray | ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)} ∩
    {B | ∀ i, B i i = D})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    exact (isClosed_setOf_posSemidef n).preimage (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_eq (by fun_prop) continuous_const)

lemma GramDiagonal.symm {D : ℝ} {B : RealArray} (h : GramDiagonal D B) (i j : ℕ) : B i j = B j i := by
  let n := max i j+1
  let ii : Fin n := ⟨i,by omega⟩
  let jj : Fin n := ⟨j,by omega⟩
  exact real_posSemidef_symm (h.1 n) ii jj

lemma GramDiagonal.default {D : ℝ} (hD : 0 ≤ D) :
    GramDiagonal D (fun i j => if i=j then D else 0) := by
  constructor
  · intro n
    have he : (fun i j : Fin n => if (i:ℕ)=(j:ℕ) then D else 0) =
        Matrix.diagonal (fun _ : Fin n => D) := by
      ext i j
      simp only [Matrix.diagonal_apply,Fin.val_inj]
    rw [he]
    exact Matrix.PosSemidef.diagonal (fun _ => hD)
  · intro i
    simp

 

lemma gg_ultrametric_ae {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ) (hgg : HasGhirlandaGuerra B μ)
    {D : ℝ} (hD : 0 ≤ D) (hG : ∀ᵐ ω ∂μ, GramDiagonal D (B ω)) :
    ∀ᵐ ω ∂μ, IsUltrametricArray (B ω) := by
  classical
  let C : Ω → RealArray := fun ω => if GramDiagonal D (B ω) then B ω else fun i j => if i=j then D else 0
  have hc : Measurable C := hm.ite ((isClosed_gramDiagonal D).measurableSet.preimage hm) measurable_const
  have he : B =ᵐ[μ] C := hG.mono (fun ω hω => by simp only [C,ite_eq_left hω])
  have hCG : ∀ ω, GramDiagonal D (C ω) := by
    intro ω
    by_cases h : GramDiagonal D (B ω)
    · simpa only [C,ite_eq_left h] using h
    · simpa only [C,ite_eq_right h] using GramDiagonal.default hD
  have hcwe : WeaklyExchangeable C μ := by
    intro e hefin
    have ht := (IdentDistrib.of_ae_eq hm.aemeasurable he).comp
      (u := permuteArray e) (by unfold permuteArray; fun_prop)
    exact (IdentDistrib.of_ae_eq hm.aemeasurable he).symm.trans ((hwe e hefin).trans ht)
  have ht := gg_ultrametric hc (fun ω => (hCG ω).symm) hcwe (hgg.congr_ae he)
    (fun ω => (hCG ω).1) (fun ω => (hCG ω).2)
  filter_upwards [ht,he] with ω ht he
  simpa only [he] using ht

 
lemma gg_pair_nonnegative_ae {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hgg : HasGhirlandaGuerra B μ)
    {D : ℝ} (hD : 0 ≤ D) (hG : ∀ᵐ ω ∂μ, GramDiagonal D (B ω)) :
    ∀ᵐ ω ∂μ, 0 ≤ B ω 0 1 := by
  classical
  let C : Ω → RealArray := fun ω => if GramDiagonal D (B ω) then B ω else fun i j => if i=j then D else 0
  have hc : Measurable C := hm.ite ((isClosed_gramDiagonal D).measurableSet.preimage hm) measurable_const
  have he : B =ᵐ[μ] C := hG.mono (fun ω hω => by simp only [C,ite_eq_left hω])
  have hCG : ∀ ω, GramDiagonal D (C ω) := by
    intro ω
    by_cases h : GramDiagonal D (B ω)
    · simpa only [C,ite_eq_left h] using h
    · simpa only [C,ite_eq_right h] using GramDiagonal.default hD
  have ht := gg_pair_nonnegative (fun i j => by fun_prop) (fun ω => (hCG ω).symm)
    (hgg.congr_ae he) (ae_of_all _ (fun ω => (hCG ω).1)) (ae_of_all _ (fun ω => (hCG ω).2))
  filter_upwards [ht,he] with ω ht he
  simpa only [he] using ht

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

def spinArray (x : JointArray) : RealArray := fun i j => (x (i,j)).1.1
def treeArray (x : JointArray) : RealArray := fun i j => (x (i,j)).2.1

lemma continuous_spinArray : Continuous spinArray := by unfold spinArray; fun_prop
lemma continuous_treeArray : Continuous treeArray := by unfold treeArray; fun_prop

lemma isClosed_ultrametricArray : IsClosed {B : RealArray | IsUltrametricArray B} := by
  change IsClosed {B : RealArray | ∀ i j k, min (B i k) (B j k) ≤ B i j}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun k =>
    isClosed_le (by fun_prop) (by fun_prop))))

def JointGeometry (n : ℕ) (x : JointArray) : Prop :=
  GramDiagonal 1 (spinArray x) ∧ GramDiagonal ((n:ℝ)/(n+1:ℕ)) (treeArray x) ∧
    IsUltrametricArray (treeArray x)

lemma isClosed_jointGeometry (n : ℕ) : IsClosed {x | JointGeometry n x} :=
  ((isClosed_gramDiagonal 1).preimage continuous_spinArray).inter
    (((isClosed_gramDiagonal ((n:ℝ)/(n+1:ℕ))).preimage continuous_treeArray).inter
      (isClosed_ultrametricArray.preimage continuous_treeArray))

lemma sampledJoint_geometry {N : ℕ} (hN : 0 < N) (n : ℕ)
    (σ : ℕ → Spin N × LabeledLeaf n) :
    JointGeometry n (sampledOverlapArray (enrichedJointEntry n) σ) := by
  constructor
  · constructor
    · intro m
      exact spinOverlap_posSemidef (fun i : Fin m => (σ i).1)
    · intro i
      exact spinOverlap_self hN _
  · constructor
    · constructor
      · intro m
        exact treeOverlap_posSemidef n (fun i : Fin m => (σ i).2)
      · intro i
        exact treeOverlap_self n _
    · exact treeOverlap_ultra n (fun i => (σ i).2)

lemma enrichedArrayLaw_geometry {N : ℕ} (hN : 0 < N) {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    ∀ᵐ x ∂(enrichedArrayLaw P r n b h u ν hm : Measure JointArray), JointGeometry n x := by
  apply (ae_map_iff (measurable_sampledOverlapArray (enrichedJointEntry n)).aemeasurable
    (isClosed_jointGeometry n).measurableSet).mpr
  exact ae_of_all _ (sampledJoint_geometry hN n)

lemma enrichedArrayLaw_reindex {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) (e : ℕ → ℕ) (he : Function.Injective e) :
    (enrichedArrayLaw P r n b h u ν hm : Measure JointArray).map (permuteJointArray e) =
      enrichedArrayLaw P r n b h u ν hm :=
  overlapArrayLaw_map_reindex _ _ _ _ e he

lemma jointGeometry_sum {n : ℕ} {x : JointArray} (hx : JointGeometry n x) :
    GramDiagonal (1+(n:ℝ)/(n+1:ℕ)) (fun i j => spinArray x i j + treeArray x i j) := by
  exact ⟨fun m => (hx.1.1 m).add (hx.2.1.1 m),fun i => by
    change spinArray x i i + treeArray x i i = _
    rw [hx.1.2 i,hx.2.1.2 i]⟩

 

lemma joint_limit_support_ordered {n : ℕ} {μ : ProbabilityMeasure JointArray}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (μ : Measure JointArray))
    (hG : ∀ᵐ x ∂(μ : Measure JointArray), JointGeometry n x)
    (hE : ∀ e : Equiv.Perm ℕ, (μ : Measure JointArray).map (permuteJointArray e) = μ) :
    let ν := (μ : Measure JointArray).map (fun x => (spinArray x 0 1,treeArray x 0 1))
    ∀ x ∈ ν.support, ∀ y ∈ ν.support, x.1 < y.1 → x.2 ≤ y.2 := by
  have hr := gg_ultrametric_ae continuous_spinArray.measurable
    (scalar_of_joint_exchangeable hE (fun x => x.1.1) (by fun_prop))
    (hgg.real_map (f := fun x => x.1.1) (by fun_prop)) (by norm_num : (0:ℝ) ≤ 1)
    (hG.mono (fun _ h => h.1))
  have hmS : Measurable (fun x i j => spinArray x i j + treeArray x i j) := by
    unfold spinArray treeArray; fun_prop
  have hs := gg_ultrametric_ae hmS
    (scalar_of_joint_exchangeable hE (fun x => x.1.1+x.2.1) (by fun_prop))
    (hgg.real_map (f := fun x => x.1.1+x.2.1) (by fun_prop)) (by positivity : (0:ℝ) ≤ 1+(n:ℝ)/(n+1:ℕ))
    (hG.mono (fun _ h => jointGeometry_sum h))
  exact jointGG_support_ordered continuous_spinArray.measurable continuous_treeArray.measurable
    (hgg.map (f := fun x => (x.1.1,x.2.1)) (by fun_prop)) hr (hG.mono (fun _ h => h.2.2)) hs
    (hG.mono (fun _ h => h.1.symm)) (hG.mono (fun _ h => h.2.1.symm))

lemma joint_limit_pair_nonnegative {n : ℕ} {μ : ProbabilityMeasure JointArray}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (μ : Measure JointArray))
    (hG : ∀ᵐ x ∂(μ : Measure JointArray), JointGeometry n x) :
    ∀ᵐ x ∂(μ : Measure JointArray), 0 ≤ spinArray x 0 1 :=
  gg_pair_nonnegative_ae continuous_spinArray.measurable
    (hgg.real_map (f := fun x => x.1.1) (by fun_prop)) (by norm_num : (0:ℝ) ≤ 1)
    (hG.mono (fun _ h => h.1))

lemma enrichedArrayLaw_limit_geometry
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (n : ℕ) (b : ℕ → ℝ)
    (h : ℕ → ℕ → ℝ) (u : (k : ℕ) → Fin (N k) → ℝ)
    (ν : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (ν k)]
    (A : ℕ → Type*) [∀ k, MeasurableSpace (A k)]
    (P : (k : ℕ) → Measure (A k)) [∀ k, IsProbabilityMeasure (P k)]
    (φ : (k : ℕ) → A k → Spin (N k) → ℝ) (hm : ∀ k, Measurable (φ k))
    (r : ℕ → ℝ≥0) (μ : ProbabilityMeasure JointArray)
    (hL : Tendsto (fun k => enrichedArrayLaw (P k) (r k) n b (h k) (u k) (ν k) (hm k)) atTop (𝓝 μ)) :
    (∀ᵐ x ∂(μ : Measure JointArray), JointGeometry n x) ∧
      ∀ e : Equiv.Perm ℕ, (μ : Measure JointArray).map (permuteJointArray e) = μ := by
  constructor
  · exact ae_closed_of_weak_limit hL (isClosed_jointGeometry n)
      (fun k => enrichedArrayLaw_geometry (hN k) (P k) (r k) n b (h k) (u k) (ν k) (hm k))
  · intro e
    exact jointArray_limit_reindex hL e (fun k =>
      enrichedArrayLaw_reindex (P k) (r k) n b (h k) (u k) (ν k) (hm k) e e.injective)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

theorem enriched_minimizers_ordered
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Icc (1:ℝ) 2)
    (ν : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (ν k)]
    (A : ℕ → Type*) [∀ k, MeasurableSpace (A k)]
    (P : (k : ℕ) → Measure (A k)) [∀ k, IsProbabilityMeasure (P k)]
    (φ : (k : ℕ) → A k → Spin (N k) → ℝ) (hm : ∀ k, Measurable (φ k))
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ k y x, |φ k y x| ≤ K)
    (r : ℕ → ℝ≥0) (α : ℝ) (hr : ∀ k, (r k:ℝ) ≤ α*N k)
    (hmin : ∀ k (v : Fin (N k) → ℝ), (∀ j, v j ∈ Icc (1:ℝ) 2) →
      enrichedPerturbationObjective (P k) (r k) n b (h k) (ν k) (φ k) (u k) ≤
        enrichedPerturbationObjective (P k) (r k) n b (h k) (ν k) (φ k) v)
    (μ : ProbabilityMeasure JointArray)
    (hL : Tendsto (fun k => enrichedArrayLaw (P k) (r k) n b (h k) (u k) (ν k) (hm k)) atTop (𝓝 μ)) :
    (∀ᵐ x ∂(μ : Measure JointArray), 0 ≤ spinArray x 0 1) ∧
      let ν₂ := (μ : Measure JointArray).map (fun x => (spinArray x 0 1,treeArray x 0 1))
      ∀ x ∈ ν₂.support, ∀ y ∈ ν₂.support, x.1 < y.1 → x.2 ≤ y.2 := by
  have hgg := enriched_minimizers_jointGG N hN hNlim n b hb h hh h0 H hH u hu ν A P φ hm K hK hφ r α hr hmin μ hL
  obtain ⟨hG,hE⟩ := enrichedArrayLaw_limit_geometry N hN n b h u ν A P φ hm r μ hL
  exact ⟨joint_limit_pair_nonnegative hgg hG,joint_limit_support_ordered hgg hG hE⟩

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

def overlapQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Icc (0:ℝ) 1 ∧ u ≤ cdf μ x}

lemma cdf_one_of_unit_support {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) : cdf μ 1 = 1 := by
  rw [cdf_eq_real]
  have he : μ (Iic (1:ℝ)) = 1 := by
    have he' := (ae_iff_measure_eq (μ := μ) (p := fun x : ℝ => x ∈ Iic (1:ℝ)) measurableSet_Iic.nullMeasurableSet).mp
      (hs.mono (fun _ h => h.2))
    rw [measure_univ] at he'
    exact he' 
  simp [Measure.real,he]

lemma quantileSet_nonempty {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ≤ 1) :
    {x : ℝ | x ∈ Icc (0:ℝ) 1 ∧ u ≤ cdf μ x}.Nonempty :=
  ⟨1,⟨by norm_num,by simpa only [cdf_one_of_unit_support hs] using hu⟩⟩

lemma quantileSet_bddBelow (μ : Measure ℝ) (u : ℝ) :
    BddBelow {x : ℝ | x ∈ Icc (0:ℝ) 1 ∧ u ≤ cdf μ x} := ⟨0,fun _ h => h.1.1⟩

lemma overlapQuantile_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ≤ 1) :
    overlapQuantile μ u ∈ Icc (0:ℝ) 1 := by
  exact ⟨le_csInf (quantileSet_nonempty hs hu) (fun _ h => h.1.1),
    (csInf_le (quantileSet_bddBelow μ u) (quantileSet_nonempty hs hu).choose_spec).trans
      (quantileSet_nonempty hs hu).choose_spec.1.2⟩

lemma le_cdf_overlapQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ≤ 1) :
    u ≤ cdf μ (overlapQuantile μ u) := by
  rw [← (cdf μ).iInf_Ioi_eq]
  apply le_ciInf
  intro y
  obtain ⟨x,hx,hxy⟩ := exists_lt_of_csInf_lt (quantileSet_nonempty hs hu) y.2
  exact hx.2.trans ((monotone_cdf μ) hxy.le)

lemma overlapQuantile_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hx : x ∈ Icc (0:ℝ) 1) : overlapQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  constructor
  · intro h
    exact (le_cdf_overlapQuantile hs hu.2.le).trans ((monotone_cdf μ) h)
  · intro h
    exact csInf_le (quantileSet_bddBelow μ u) ⟨hx,h⟩

lemma monotoneOn_overlapQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) : MonotoneOn (overlapQuantile μ) (Ioo (0:ℝ) 1) := by
  intro u hu v hv huv
  exact csInf_le_csInf (quantileSet_bddBelow μ u) (quantileSet_nonempty hs hv.2.le)
    (fun x hx => ⟨hx.1,huv.trans hx.2⟩)

 
def quantileFunction (μ : Measure ℝ) (u : ℝ) : ℝ := overlapQuantile μ (min u 1)

lemma monotone_quantileFunction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) : Monotone (quantileFunction μ) := by
  intro u v huv
  exact csInf_le_csInf (quantileSet_bddBelow μ (min u 1))
    (quantileSet_nonempty hs (min_le_right v 1))
    (fun x hx => ⟨hx.1,(min_le_min_right 1 huv).trans hx.2⟩)

lemma quantileFunction_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ) : quantileFunction μ u ∈ Icc (0:ℝ) 1 :=
  overlapQuantile_mem hs (min_le_right u 1)

lemma cdf_of_lt_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {x : ℝ} (hx : x < 0) : cdf μ x = 0 := by
  rw [cdf_eq_real,Measure.real]
  have he : μ (Iic x) = 0 := by
    apply measure_mono_null (t := {y : ℝ | ¬y ∈ Icc (0:ℝ) 1}) _ (ae_iff.mp hs)
    intro y hy hy'
    exact (not_le.mpr (hx.trans_le hy'.1)) hy
  rw [he,ENNReal.toReal_zero]

lemma quantileFunction_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    quantileFunction μ u ≤ x ↔ u ≤ cdf μ x := by
  by_cases hx : x < 0
  · rw [cdf_of_lt_zero hs hx]
    exact iff_of_false (not_le.mpr (hx.trans_le (quantileFunction_mem hs u).1))
      (not_le.mpr hu.1)
  · by_cases hx' : x ≤ 1
    · simpa only [quantileFunction,min_eq_left hu.2.le] using overlapQuantile_le_iff hs hu ⟨le_of_not_gt hx,hx'⟩
    · have hc : cdf μ x = 1 := le_antisymm (cdf_le_one μ x)
        (by simpa only [cdf_one_of_unit_support hs] using (monotone_cdf μ) (le_of_not_ge hx'))
      rw [hc]
      exact iff_of_true ((quantileFunction_mem hs u).2.trans (le_of_not_ge hx')) hu.2.le

def unitUniform : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform,Real.volume_Ioo]

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

lemma quantile_preimage_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (x : ℝ) :
    quantileFunction μ ⁻¹' Iic x =ᵐ[unitUniform] Iic (cdf μ x) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact propext (quantileFunction_le_iff hs hu)

 
lemma quantileFunction_law {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) : unitUniform.map (quantileFunction μ) = μ := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (monotone_quantileFunction hs).measurable measurableSet_Iic,
    measure_congr (quantile_preimage_Iic hs x),unitUniform_Iic ⟨cdf_nonneg μ x,cdf_le_one μ x⟩,
    ofReal_cdf]

end IsingPerceptron

end

end OAI
