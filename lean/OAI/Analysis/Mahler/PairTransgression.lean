import OAI.Analysis.Mahler.WedgeOne
import OAI.Analysis.Mahler.HomogeneousDensityVariation

namespace OAI

open Complex ContinuousAlternatingMap

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The actual ordered two-form alpha wedge beta, as a continuous form. -/
noncomputable def pairExterior (a b : E →L[ℝ] ℂ) : E [⋀^Fin 2]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
      (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.mul ℝ ℂ).bilinearComp a b))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma pairExterior_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a b : E →L[ℝ] ℂ) (v : Fin 2 → E) :
    pairExterior a b v = a (v 0) * b (v 1) - a (v 1) * b (v 0) := by
  simp [pairExterior, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, Fin.removeNth, sub_eq_add_neg]

lemma pairExterior_toAlternatingMap (a b : E →L[ℝ] ℂ) :
    (pairExterior a b).toAlternatingMap = covectorVolume ![a.toLinearMap,b.toLinearMap] := by
  ext v
  rw [covectorVolume_apply, Matrix.det_fin_two]
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, pairExterior_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
  ring

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma differentiableAt_pairExterior [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    DifferentiableAt ℝ (fun y => pairExterior (a y) (b y)) x := by
  unfold pairExterior ContinuousLinearMap.bilinearComp
  change DifferentiableAt ℝ
    (fun y => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
        (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((((ContinuousLinearMap.mul ℝ ℂ).comp (a y)).flip.comp (b y)).flip))) x
  apply (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).differentiableAt.comp x
  have hf1 := (ContinuousLinearMap.flipₗᵢ ℝ E ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.differentiable
  have hf2 := (ContinuousLinearMap.flipₗᵢ ℝ E E ℂ).toContinuousLinearEquiv.toContinuousLinearMap.differentiable
  change Differentiable ℝ (fun L : E →L[ℝ] ℂ →L[ℝ] ℂ => L.flip) at hf1
  change Differentiable ℝ (fun L : E →L[ℝ] E →L[ℝ] ℂ => L.flip) at hf2
  fun_prop

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_pairExterior [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a b : E → E →L[ℝ] ℂ} {x : E} (q : ℕ)
    (ha : ContDiffAt ℝ q a x) (hb : ContDiffAt ℝ q b x) :
    ContDiffAt ℝ q (fun y => pairExterior (a y) (b y)) x := by
  unfold pairExterior ContinuousLinearMap.bilinearComp
  change ContDiffAt ℝ q
    (fun y => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
        (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((((ContinuousLinearMap.mul ℝ ℂ).comp (a y)).flip.comp (b y)).flip))) x
  have hA : ContDiff ℝ (q : WithTop ℕ∞)
      (fun L : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℂ =>
        ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ E ℂ L) :=
    ContinuousLinearMap.contDiff _
  apply hA.contDiffAt.comp x
  let L1 : (E →L[ℝ] ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  let L2 : (E →L[ℝ] E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hf1 : ContDiff ℝ q L1 := ContinuousLinearMap.contDiff _
  have hf2 : ContDiff ℝ q L2 := ContinuousLinearMap.contDiff _
  change ContDiff ℝ q (fun L : E →L[ℝ] ℂ →L[ℝ] ℂ => L.flip) at hf1
  change ContDiff ℝ q (fun L : E →L[ℝ] E →L[ℝ] ℂ => L.flip) at hf2
  fun_prop

lemma fderiv_pairExterior_eval {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (v : Fin 2 → E) (u : E) :
    fderiv ℝ (fun y => pairExterior (a y) (b y) v) x u =
      fderiv ℝ a x u (v 0) * b x (v 1) + a x (v 0) * fderiv ℝ b x u (v 1) -
      (fderiv ℝ a x u (v 1) * b x (v 0) + a x (v 1) * fderiv ℝ b x u (v 0)) := by
  have hh := ((ha.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)).mul
    (hb.hasFDerivAt.clm_apply (hasFDerivAt_const (v 1) x))).sub
    ((ha.hasFDerivAt.clm_apply (hasFDerivAt_const (v 1) x)).mul
      (hb.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)))
  convert congrArg (fun L : E →L[ℝ] ℂ => L u) hh.fderiv using 1 <;>
    simp [pairExterior_apply] <;> first | rfl | ring

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma covectorVolume_one [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a : E →L[ℝ] ℂ) :
    covectorVolume (fun _ : Fin 1 => a.toLinearMap) =
      (oneForm (fun _ : E => a) 0).toAlternatingMap := by
  ext v
  simp [covectorVolume_apply, Matrix.det_unique, oneForm_apply]

/-- The negative-sign exterior Leibniz identity for two actual one-forms.
All derivatives are exterior derivatives, and the shuffle order is
identified explicitly with the standard three slots. -/
theorem extDeriv_pairExterior {J : Type*} [Fintype J]
    (basis : Module.Basis J ℝ E) {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    (extDeriv (fun y => pairExterior (a y) (b y)) x).toAlternatingMap =
      (wedge (oneForm b x).toAlternatingMap (extDeriv (oneForm a) x).toAlternatingMap).domDomCongr
        (prependFinEquiv 2) -
      (wedge (oneForm a x).toAlternatingMap (extDeriv (oneForm b) x).toAlternatingMap).domDomCongr
        (prependFinEquiv 2) := by
  ext v
  have hvol (c : E → E →L[ℝ] ℂ) :
      (oneForm c x).toAlternatingMap = covectorVolume (fun _ : Fin 1 => (c x).toLinearMap) := by
    rw [covectorVolume_one]
    rfl
  simp only [AlternatingMap.sub_apply, hvol, wedge_one_eval basis,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [extDeriv_apply (differentiableAt_pairExterior ha hb)]
  simp only [fderiv_pairExterior_eval ha hb]
  have hev (c : E → E →L[ℝ] ℂ) (hc : DifferentiableAt ℝ c x) (w u : E) :
      fderiv ℝ (fun y => c y w) x u = fderiv ℝ c x u w := by
    simpa using congrArg (fun L : E →L[ℝ] ℂ => L u)
      (hc.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv
  have hd (c : E → E →L[ℝ] ℂ) (hc : DifferentiableAt ℝ c x) (w : Fin 2 → E) :
      extDeriv (oneForm c) x w =
        fderiv ℝ c x (w 0) (w 1) - fderiv ℝ c x (w 1) (w 0) := by
    have he : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
    rw [he, extDeriv_oneForm hc, hev c hc, hev c hc]
    rfl
  simp only [hd a ha, hd b hb,
    ContinuousLinearMap.coe_coe]
  simp [Fin.sum_univ_three, Fin.removeNth, Fin.succAbove]
  ring

end Mahler

end OAI
