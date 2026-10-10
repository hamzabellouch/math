import OAI.MeasureTheory.Falconer.Estimates.ScalarBinaryParameters

namespace OAI

/-! The binary alternative compared directly with a covering bound for the
 original repeated sumset. This avoids multiplying a regularization loss
 by the number of summands in a Pluennecke estimate. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_nsmul_subset (n : ℕ) {A B : Finset ℝ} (h : A ⊆ B) : n • A ⊆ n • B := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [succ_nsmul] using Finset.add_subset_add ih h

namespace Regularization

 theorem scalar_nonporous_cover_bound {B M copies J F C : ℕ} {U : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hF : 4*(J:ℝ)*U ≤ (F:ℝ)) (hcopies : (2*F+1)*J ≤ copies)
    (A : Finset ℝ) (hQA : Q.image scalarPathCenter ⊆ A) :
    (J+1)^(scalarNonporousLevels M B C k n).card ≤
      (scalarCells ((1/2:ℝ)^(B*M)) (copies • A)).card := by
  let S := scalarNonporousLevels M B C k n
  obtain ⟨g,hm,hg,hb⟩ := scalar_level_enumeration M S (Finset.filter_subset _ _)
  obtain ⟨E,hE,hcard,hsep⟩ := scalar_nonporous_growth Q hQ hne k n hlevel S.card g hg hb
    (fun i hi => (Finset.mem_filter.mp (hm i hi)).2.1)
    (fun i hi => (Finset.mem_filter.mp (hm i hi)).2.2) hU hJ hcontract hF hcopies
  rw [← hcard,← Finset.card_image_of_injOn (scalarCells_injective (by positivity) hsep)]
  exact Finset.card_le_card (Finset.image_subset_image (hE.trans (scalar_nsmul_subset copies hQA)))

 theorem scalar_porous_count_of_sumset {B M copies J F C : ℕ} {U κ : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hF : 4*(J:ℝ)*U ≤ (F:ℝ)) (hcopies : (2*F+1)*J ≤ copies)
    (A : Finset ℝ) (hQA : Q.image scalarPathCenter ⊆ A)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 0 < B)
    (hlogJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Real.log (J+1:ℝ))
    (hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M)) (copies • A)).card:ℝ) ≤
      (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2) :
    (κ/2)*(M:ℝ) ≤ ((scalarPorousLevels M B C k n).card:ℝ) := by
  have hraw := scalar_nonporous_cover_bound Q hQ hne k n hlevel hU hJ hcontract hF hcopies A hQA
  have hrawR : (J+1:ℝ)^(scalarNonporousLevels M B C k n).card ≤
      ((scalarCells ((1/2:ℝ)^(B*M)) (copies • A)).card:ℝ) := by exact_mod_cast hraw
  have hl := Real.log_le_log (by positivity : (0:ℝ) < (J+1:ℝ)^
    (scalarNonporousLevels M B C k n).card) hrawR
  rw [Real.log_pow] at hl
  apply scalar_porous_count_from_entropy k n hκ hκ1 hB hlogJ
    (le_refl ((κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2))
    (le_refl ((1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2))
  calc
    _ ≤ (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := hl.trans hsmall
    _ = _ := by ring

end Regularization
end Falconer

end OAI
