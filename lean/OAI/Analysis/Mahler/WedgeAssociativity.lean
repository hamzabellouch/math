import OAI.Analysis.Mahler.WedgeDecomposition

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J ι κ ν : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

lemma domDomCongr_sum {A B Q : Type*} [Fintype Q] (e : A ≃ B)
    (f : Q → T [⋀^A]→ₗ[ℝ] ℂ) :
    (∑ q, f q).domDomCongr e = ∑ q, (f q).domDomCongr e := by
  exact map_sum (AlternatingMap.domDomCongrₗ ℂ e) f Finset.univ

lemma covectorVolume_domDomCongr (l : ι → T →ₗ[ℝ] ℂ) (e : ι ≃ κ) :
    (covectorVolume l).domDomCongr e = covectorVolume (l ∘ e.symm) := by
  ext v
  simpa only [AlternatingMap.domDomCongr_apply, Equiv.symm_symm] using
    (covectorVolume_reindex_apply l e.symm v).symm

/-- Associativity of the actual shuffle product, with the ordered slot
reassociation made explicit. -/
theorem wedge_assoc (basis : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) (c : T [⋀^ν]→ₗ[ℝ] ℂ) :
    (wedge (wedge a b) c).domDomCongr (Equiv.sumAssoc ι κ ν) = wedge a (wedge b c) := by
  rw [alternating_basis_expansion_normalized basis a,
    alternating_basis_expansion_normalized basis b,
    alternating_basis_expansion_normalized basis c]
  simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    domDomCongr_sum, AlternatingMap.domDomCongr_smul, wedge_covectorVolume, Finset.smul_sum, smul_smul, mul_assoc]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [covectorVolume_domDomCongr]
  congr 1
  funext i
  rcases i with i | i | i <;> rfl

/-- Swapping blocks means reindexing by the actual block swap; signs arise
when both sides are subsequently put into the same Fin order. -/
theorem wedge_swap (basis : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    (wedge a b).domDomCongr (Equiv.sumComm ι κ) = wedge b a := by
  rw [alternating_basis_expansion_normalized basis a,
    alternating_basis_expansion_normalized basis b]
  simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    domDomCongr_sum, AlternatingMap.domDomCongr_smul, wedge_covectorVolume, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_comm]
  congr 1
  rw [covectorVolume_domDomCongr]
  congr 1
  funext i
  cases i <;> rfl

end Mahler

end OAI
