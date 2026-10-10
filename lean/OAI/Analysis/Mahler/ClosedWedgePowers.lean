import OAI.Analysis.Mahler.ExteriorLeibnizTwo
import OAI.Analysis.Mahler.HomogeneousSmoothForms

namespace OAI

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma continuousReindex_finCongr_extDeriv [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {p q : ℕ} (h : p = q)
    (A : E → E [⋀^Fin p]→L[ℝ] ℂ) (x : E) :
    extDeriv (fun y => continuousReindex (finCongr h) (A y)) x =
      continuousReindex (finCongr (congrArg (·+1) h)) (extDeriv A x) := by
  subst q
  rfl

noncomputable def basisContinuousWedgePower (basis : Module.Basis J ℝ E)
    (A : E [⋀^Fin 2]→L[ℝ] ℂ) : (k : ℕ) → E [⋀^Fin (2*k)]→L[ℝ] ℂ
  | 0 => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1
  | k+1 => continuousReindex (finCongr (by omega))
      (continuousWedgeFin basis A (basisContinuousWedgePower basis A k))

lemma basisContinuousWedgePower_toAlternatingMap (basis : Module.Basis J ℝ E)
    (A : E [⋀^Fin 2]→L[ℝ] ℂ) (k : ℕ) :
    (basisContinuousWedgePower basis A k).toAlternatingMap =
      (wedgePower A.toAlternatingMap k).domDomCongr (powerFinEquiv k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [basisContinuousWedgePower, continuousReindex_toAlternatingMap,
      continuousWedgeFin_toAlternatingMap, ih, powerFinEquiv]
    have he := wedge_reindex basis (Equiv.refl (Fin 2)) (powerFinEquiv k)
      A.toAlternatingMap (wedgePower A.toAlternatingMap k)
    simp only [AlternatingMap.domDomCongr_refl] at he
    rw [← he]
    rfl

lemma contDiffAt_basisContinuousWedgePower (basis : Module.Basis J ℝ E)
    {q : WithTop ℕ∞} {A : E → E [⋀^Fin 2]→L[ℝ] ℂ} {x : E}
    (hA : ContDiffAt ℝ q A x) (k : ℕ) :
    ContDiffAt ℝ q (fun y => basisContinuousWedgePower basis (A y) k) x := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih =>
    exact (continuousReindex (E := E) (finCongr (show 2+2*k=2*(k+1) by omega))).contDiff.contDiffAt.comp x
      (contDiffAt_continuousWedgeFin basis hA ih)

lemma differentiableAt_basisContinuousWedgePower (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^Fin 2]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (k : ℕ) :
    DifferentiableAt ℝ (fun y => basisContinuousWedgePower basis (A y) k) x := by
  induction k with
  | zero => exact differentiableAt_const _
  | succ k ih =>
    exact (continuousReindex (finCongr (by omega))).differentiableAt.comp x
      (differentiableAt_continuousWedgeFin basis hA ih)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma wedge_power_zero_right [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : E [⋀^ι]→ₗ[ℝ] ℂ) :
    wedge A (0 : E [⋀^κ]→ₗ[ℝ] ℂ) = 0 := by
  simpa only [zero_smul] using wedge_smul_right 0 A (0 : E [⋀^κ]→ₗ[ℝ] ℂ)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma wedge_power_zero_left [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : E [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (0 : E [⋀^ι]→ₗ[ℝ] ℂ) A = 0 := by
  simpa only [zero_smul] using wedge_smul_left 0 (0 : E [⋀^ι]→ₗ[ℝ] ℂ) A

/-- Every power of an actual closed differentiable two-form is closed. -/
theorem extDeriv_basisContinuousWedgePower (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^Fin 2]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hclosed : extDeriv A x = 0) (k : ℕ) :
    extDeriv (fun y => basisContinuousWedgePower basis (A y) k) x = 0 := by
  induction k with
  | zero =>
    simp only [basisContinuousWedgePower, extDeriv, fderiv_fun_const]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
  | succ k ih =>
    change extDeriv (fun y => continuousReindex (finCongr (by omega))
      (continuousWedgeFin basis (A y) (basisContinuousWedgePower basis (A y) k))) x = 0
    rw [continuousReindex_finCongr_extDeriv]
    have he := extDeriv_continuousWedge_two basis hA
      (differentiableAt_basisContinuousWedgePower basis hA k)
    rw [hclosed, ih] at he
    simp only [ContinuousAlternatingMap.toAlternatingMap_zero, wedge_power_zero_left,
      wedge_power_zero_right, AlternatingMap.domDomCongr_zero, add_zero] at he
    have hz : extDeriv (fun y => continuousWedgeFin basis (A y)
        (basisContinuousWedgePower basis (A y) k)) x = 0 := by
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      exact he
    rw [hz, map_zero]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma contDiffAt_extDeriv_power_order [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {p : ℕ} {A : E → E [⋀^Fin p]→L[ℝ] ℂ}
    {x : E} (q : ℕ) (hA : ContDiffAt ℝ (q+1) A x) :
    ContDiffAt ℝ q (extDeriv A) x :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x
    (hA.fderiv_right (by norm_cast))

end Mahler

end OAI
