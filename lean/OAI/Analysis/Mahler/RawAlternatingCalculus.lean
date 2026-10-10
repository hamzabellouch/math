import OAI.Analysis.Mahler.RawExteriorPower

namespace OAI

open Equiv
namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Full alternatization commutes with any explicit slot identification. -/
theorem raw_alternatization_reindex
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ) (e : ι ≃ κ) :
    (a.domDomCongr e).alternatization = a.alternatization.domDomCongr e := by
  ext v
  rw [MultilinearMap.alternatization_apply]
  rw [← Equiv.sum_comp e.permCongr]
  simp only [AlternatingMap.domDomCongr_apply, MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro σ _
  simp [Equiv.Perm.sign_permCongr, MultilinearMap.domDomCongr_apply,
    Equiv.permCongr_apply, Function.comp_def]

/-- A symmetric pair of raw slots contributes zero to an exterior form. -/
theorem raw_alternatization_zero_of_swap
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ) {i j : ι} (hij : i ≠ j)
    (h : a.domDomCongr (Equiv.swap i j) = a) : a.alternatization = 0 := by
  have he := raw_alternatization_reindex a (Equiv.swap i j)
  rw [h, AlternatingMap.domDomCongr_perm, Equiv.Perm.sign_swap hij] at he
  ext v
  have hv := congrArg (fun b => b v) he
  simp only [Units.smul_def, Units.val_neg, Units.val_one,
    neg_smul, one_smul, AlternatingMap.neg_apply] at hv
  change a.alternatization v = 0
  linear_combination (1/2 : ℂ) * hv

end
end Mahler

end OAI
