import OAI.Analysis.KadisonKastler.MatrixVonNeumann
import OAI.Analysis.KadisonKastler.HilbertMatrix
import OAI.Analysis.KadisonKastler.PublishedKaplansky
import OAI.Analysis.FactorGeneration.Bicommutant

namespace OAI

/-! # Finite matrix algebras and von Neumann generation

These elementary finite-sum arguments are independent of spatial tensor
products and perturbation theorems. -/

namespace KadisonKastler

open Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance matrixGenerationOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixGenerationStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The finite matrices whose entries belong to a specified star algebra. -/
def entryMatrixAlgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (CStarMatrix ι ι (H →L[ℂ] H)) where
  carrier := {X | ∀ i j, X i j ∈ S}
  zero_mem' := fun _ _ => S.zero_mem
  one_mem' := by
    intro i j
    change (if i = j then 1 else 0) ∈ S
    split_ifs <;> simp
  add_mem' hX hY i j := S.add_mem (hX i j) (hY i j)
  mul_mem' hX hY i j := S.sum_mem fun k _ => S.mul_mem (hX i k) (hY k j)
  algebraMap_mem' c := by
    intro i j
    change (if i = j then algebraMap ℂ (H →L[ℂ] H) c else 0) ∈ S
    split_ifs <;> simp
  star_mem' hX i j := S.star_mem' (hX j i)

/-- The same finite matrices acting on the finite Hilbert sum. -/
def matrixOperatorAlgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) :=
  (entryMatrixAlgebra (ι := ι) S).map hilbertMatrixHom

omit [CompleteSpace H] in
@[simp]
theorem operatorEntry_hilbertMatrix
    (X : CStarMatrix ι ι (H →L[ℂ] H)) (i j : ι) :
    operatorEntry (hilbertMatrix X) i j = X i j := by
  ext ξ
  simp [operatorEntry, hilbertMatrix_apply, tupleSingle_apply, Pi.single_apply, apply_ite]

omit [CompleteSpace H] in
theorem hilbertMatrix_operatorEntries (T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) :
    hilbertMatrix (CStarMatrix.ofMatrix fun i j => operatorEntry T i j) = T := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  change hilbertMatrix (CStarMatrix.ofMatrix fun i j => operatorEntry T i j) ξ i = T ξ i
  rw [hilbertMatrix_apply]
  change (∑ j, T (tupleSingle j (ξ j)) i) = T ξ i
  have h := congrArg (fun η => T η i) (tuple_eq_sum_single ξ)
  simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] using h.symm

theorem mem_matrixOperatorAlgebra_iff (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) :
    T ∈ matrixOperatorAlgebra (ι := ι) S ↔ ∀ i j, operatorEntry T i j ∈ S := by
  constructor
  · rintro ⟨X, hX, rfl⟩ i j
    change operatorEntry (hilbertMatrix X) i j ∈ S
    rw [operatorEntry_hilbertMatrix]
    exact hX i j
  · intro hT
    exact ⟨CStarMatrix.ofMatrix (fun i j => operatorEntry T i j), hT,
      hilbertMatrix_operatorEntries T⟩

theorem matrixOperatorAlgebra_mono {S T : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hST : S ≤ T) : matrixOperatorAlgebra (ι := ι) S ≤ matrixOperatorAlgebra T := by
  intro a ha
  rw [mem_matrixOperatorAlgebra_iff] at ha ⊢
  exact fun i j => hST (ha i j)

/-- Finite matrix amplification commutes with von Neumann generation. -/
theorem generated_matrixOperatorAlgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    generatedVonNeumannAlgebra (matrixOperatorAlgebra (ι := ι) S) =
      matrixVonNeumann (ι := ι) (generatedVonNeumannAlgebra S) := by
  classical
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    intro T hT
    change T ∈ matrixVonNeumann (ι := ι) (generatedVonNeumannAlgebra S)
    rw [mem_matrixVonNeumann_iff_entries]
    exact fun i j => subset_generatedVonNeumannAlgebra S
      ((mem_matrixOperatorAlgebra_iff S T).mp hT i j)
  · intro T hT
    have he : ∀ i j, operatorEntry T i j ∈
        Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
      intro i j
      have h := (mem_matrixVonNeumann_iff_entries _ T).mp hT i j
      change operatorEntry T i j ∈ (generatedVonNeumannAlgebra S : Set _) at h
      rwa [generatedVonNeumannAlgebra_coe] at h
    choose a ha using fun i j => bicommutant_exists_strong_net S (operatorEntry T i j) (he i j)
    let X (d : Finset H × ℕ) : CStarMatrix ι ι (H →L[ℂ] H) :=
      CStarMatrix.ofMatrix fun i j => (a i j d).val
    let b (d : Finset H × ℕ) : Algebra
        (generatedVonNeumannAlgebra (matrixOperatorAlgebra (ι := ι) S)) :=
      ⟨hilbertMatrix (X d), subset_generatedVonNeumannAlgebra _
        (show hilbertMatrix (X d) ∈ matrixOperatorAlgebra S from
          ⟨X d, fun i j => (a i j d).property, rfl⟩)⟩
    apply Generator.Tracial.weak_operator_limit_mem
      (l := (atTop : Filter (Finset H × ℕ))) _ b
    intro ξ η
    have hc (i : ι) : Tendsto (fun d => ∑ j, (a i j d).val (ξ j)) atTop
        (𝓝 (∑ j, operatorEntry T i j (ξ j))) :=
      tendsto_finsetSum _ (fun j _ => ha i j (ξ j))
    have hi (i : ι) : Tendsto
        (fun d => inner ℂ (η i) (∑ j, (a i j d).val (ξ j))) atTop
        (𝓝 (inner ℂ (η i) (∑ j, operatorEntry T i j (ξ j)))) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp (hc i)
    have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
    have hrec (i : ι) : (∑ j, operatorEntry T i j (ξ j)) = T ξ i := by
      change (∑ j, T (tupleSingle j (ξ j)) i) = T ξ i
      have h := congrArg (fun ζ => T ζ i) (tuple_eq_sum_single ξ)
      simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] using h.symm
    have happ (d : Finset H × ℕ) (i : ι) :
        ((hilbertMatrix (X d)) ξ).ofLp i = ∑ j, (a i j d).val (ξ j) :=
      hilbertMatrix_apply (X d) ξ i
    change Tendsto (fun d => inner ℂ η ((hilbertMatrix (X d)) ξ)) atTop
      (𝓝 (inner ℂ η (T ξ)))
    simpa only [PiLp.inner_apply, happ, hrec] using hs

/-- Increasing unions also commute with finite matrix amplification. -/
theorem matrixOperatorAlgebra_iSup (S : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : Monotone S) :
    matrixOperatorAlgebra (ι := ι) (⨆ n, S n) = ⨆ n, matrixOperatorAlgebra (ι := ι) (S n) := by
  classical
  apply le_antisymm
  · intro T hT
    have he := (mem_matrixOperatorAlgebra_iff _ T).mp hT
    have hex : ∀ i j, ∃ n, operatorEntry T i j ∈ S n := by
      intro i j
      have h := he i j
      change operatorEntry T i j ∈ ((⨆ n, S n : StarSubalgebra ℂ (H →L[ℂ] H)) : Set _) at h
      rw [StarSubalgebra.coe_iSup_of_directed hS.directed_le] at h
      exact Set.mem_iUnion.mp h
    choose f hf using hex
    let m : ℕ := Finset.univ.sup fun i : ι => Finset.univ.sup (f i)
    apply (le_iSup (fun n => matrixOperatorAlgebra (ι := ι) (S n)) m)
    rw [mem_matrixOperatorAlgebra_iff]
    intro i j
    apply hS (show f i j ≤ m from
      (Finset.le_sup (s := Finset.univ) (f := f i) (Finset.mem_univ j)).trans
        (Finset.le_sup (s := Finset.univ)
          (f := fun i => Finset.univ.sup (f i)) (Finset.mem_univ i)))
    exact hf i j
  · exact iSup_le fun n => matrixOperatorAlgebra_mono (le_iSup S n)

end

end KadisonKastler

end OAI
