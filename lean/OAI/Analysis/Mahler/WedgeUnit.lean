import OAI.Analysis.Mahler.WedgeEven
import OAI.Analysis.Mahler.WedgeOne
import OAI.Analysis.Mahler.SphereFluxIntegral

namespace OAI

namespace Mahler
variable {T J ι : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]
  [Fintype ι] [DecidableEq ι]

def emptyRightEquiv (ι : Type*) : ι ⊕ Fin 0 ≃ ι where
  toFun := Sum.elim id Fin.elim0
  invFun := Sum.inl
  left_inv := by intro s; cases s with
    | inl i => rfl
    | inr i => exact Fin.elim0 i
  right_inv := fun _ => rfl

lemma wedge_unit_right (basis : Module.Basis J ℝ T) (A : T [⋀^ι]→ₗ[ℝ] ℂ) :
    (wedge A (AlternatingMap.constOfIsEmpty ℝ T (Fin 0) 1)).domDomCongr
      (emptyRightEquiv ι) = A := by
  have hu : AlternatingMap.constOfIsEmpty ℝ T (Fin 0) (1 : ℂ) =
      covectorVolume (fun i : Fin 0 => Fin.elim0 i) := by
    ext v
    rw [covectorVolume_apply, Matrix.det_isEmpty]
    rfl
  rw [hu, alternating_basis_expansion_normalized basis A]
  simp only [wedge_sum_left, wedge_smul_left, wedge_covectorVolume,
    domDomCongr_sum, AlternatingMap.domDomCongr_smul, covectorVolume_domDomCongr]
  apply Finset.sum_congr rfl
  intro q hq
  congr 2

lemma powerFinEquiv_one : powerFinEquiv 1 = emptyRightEquiv (Fin 2) := by
  ext s
  cases s with
  | inl i => rfl
  | inr i => exact Fin.elim0 i

lemma wedgePower_one_fin (basis : Module.Basis J ℝ T) (A : T [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    (wedgePower A 1).domDomCongr (powerFinEquiv 1) = A := by
  rw [powerFinEquiv_one]
  unfold wedgePower
  rw [show wedgePowerSlotsDecidableEq 0 =
    (inferInstance : DecidableEq (Fin 0)) from Subsingleton.elim _ _]
  exact wedge_unit_right basis A

lemma prependFinEquiv_eq (n : ℕ) : prependFinEquiv n =
    (finSumFinEquiv.trans (finCongr (show 1+n = n+1 by omega))) := by
  ext s
  cases s with
  | inl i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  | inr i =>
    simp [prependFinEquiv]

lemma boundaryFinEquiv_factor (k : ℕ) : boundaryFinEquiv k =
    (Equiv.sumCongr (Equiv.refl (Fin 1)) (powerFinEquiv k)).trans
      (prependFinEquiv (2*k)) := by
  rw [prependFinEquiv_eq]
  rfl

lemma wedge_power_one_boundary (basis : Module.Basis J ℝ T)
    (a : T [⋀^Fin 1]→ₗ[ℝ] ℂ) (A : T [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    (wedge a (wedgePower A 1)).domDomCongr (boundaryFinEquiv 1) =
      (wedge a A).domDomCongr (prependFinEquiv 2) := by
  rw [boundaryFinEquiv_factor, AlternatingMap.domDomCongr_trans,
    wedge_reindex basis, wedgePower_one_fin basis]
  rfl

end Mahler

end OAI
