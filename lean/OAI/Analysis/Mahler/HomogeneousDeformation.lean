import OAI.Analysis.Mahler.SourceHomogeneous

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The deformation beta, represented as a real-linear one-form. -/
noncomputable def betaLinear (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ)
    (x : E) : E →L[ℝ] ℂ := dcLinear (logTau f) x - (m : ℝ) • dcLinear (logTau g) x

/-- The actual one-form alpha_t = m alpha_0 + t beta. -/
noncomputable def alphaPath (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ)
    (t : ℝ) (x : E) : E →L[ℝ] ℂ :=
  (m : ℝ) • dcLinear (logTau g) x + t • betaLinear f g m x

omit [FiniteDimensional ℂ E] in
lemma betaLinear_circle [FiniteDimensional ℂ E] {f : ι → E → ℂ} {g : κ → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (htf : 0 < tau f x)
    (hfg : ∀ j (c : ℂ), f j (c • x) = c^m * f j x)
    (hg : ∀ j, DifferentiableAt ℂ (g j) x) (htg : 0 < tau g x)
    (hgg : ∀ j (c : ℂ), g j (c • x) = c^1 * g j x) :
    betaLinear f g m x (I • x) = 0 := by
  simp only [betaLinear, _root_.sub_apply, _root_.smul_apply,
    dcLinear_apply, homogeneous_dc_circle hf htf hfg, homogeneous_dc_circle hg htg hgg]
  simp [Complex.real_smul, div_eq_mul_inv]

omit [FiniteDimensional ℂ E] in
/-- The bundled beta is exactly d^c(log T - m log |z|^2)
when g is the coordinate map. -/
lemma betaLinear_eq_dc [FiniteDimensional ℂ E] {f : ι → E → ℂ} {g : κ → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (htf : 0 < tau f x)
    (hg : ∀ j, DifferentiableAt ℂ (g j) x) (htg : 0 < tau g x) (v : E) :
    betaLinear f g m x v = dc (fun y => logTau f y - (m : ℂ) * logTau g y) x v := by
  have hg' : DifferentiableAt ℝ (fun y => (m : ℂ) * logTau g y) x :=
    (differentiableAt_const (m : ℂ)).mul (differentiable_logTau hg htg)
  rw [dc_sub (differentiable_logTau hf htf) hg',
    dc_const_mul _ (differentiable_logTau hg htg)]
  simp [betaLinear, Complex.real_smul]

lemma alphaPath_circle {f : ι → E → ℂ} {g : κ → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (htf : 0 < tau f x)
    (hfg : ∀ j (c : ℂ), f j (c • x) = c^m * f j x)
    (hg : ∀ j, DifferentiableAt ℂ (g j) x) (htg : 0 < tau g x)
    (hgg : ∀ j (c : ℂ), g j (c • x) = c^1 * g j x) (t : ℝ) :
    alphaPath f g m t x (I • x) = (m : ℂ) / 2 := by
  simp only [alphaPath, _root_.add_apply, _root_.smul_apply,
    betaLinear_circle hf htf hfg hg htg hgg, smul_zero, add_zero, dcLinear_apply,
    homogeneous_dc_circle hg htg hgg]
  simp [Complex.real_smul, div_eq_mul_inv]

omit [FiniteDimensional ℂ E] in
lemma homogeneous_dcLinear_rotation [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, Differentiable ℂ (f j)) (ht : 0 < tau f x)
    (hh : ∀ j (y : E) (c : ℂ), f j (c • y) = c^m * f j y)
    {c : ℂ} (hc : normSq c = 1) (v : E) :
    dcLinear (logTau f) (c • x) (c • v) = dcLinear (logTau f) x v := by
  apply dcLinear_rotation
  · apply differentiable_logTau (fun j => (hf j).differentiableAt)
    simpa [tau_homogeneous (fun j c => hh j x c), hc] using ht
  · intro y
    exact logTau_circle_invariant (fun j c => hh j y c) hc

omit [FiniteDimensional ℂ E] in
lemma tau_continuousAt [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) : ContinuousAt (tau f) x := by
  have h := Complex.continuous_re.continuousAt.comp (differentiable_energy hf).continuousAt
  simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using h

/-- Circle horizontality for the actual whole deformation, for every real t.
The only regularity hypotheses are first-order holomorphicity. -/
theorem alphaPath_extDeriv_horizontal {f : ι → E → ℂ} {g : κ → E → ℂ}
    {x : E} {m : ℕ}
    (hf : ∀ j, Differentiable ℂ (f j)) (htf : 0 < tau f x)
    (hfg : ∀ j (y : E) (c : ℂ), f j (c • y) = c^m * f j y)
    (hg : ∀ j, Differentiable ℂ (g j)) (htg : 0 < tau g x)
    (hgg : ∀ j (y : E) (c : ℂ), g j (c • y) = c^1 * g j y)
    (t : ℝ) (v : E) :
    extDeriv (oneForm (alphaPath f g m t)) x ![I • x, v] = 0 := by
  have hdf := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ
    (Set.mem_univ x) (fun j => (hf j).differentiableOn) htf)
  have hdg := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ
    (Set.mem_univ x) (fun j => (hg j).differentiableOn) htg)
  apply extDeriv_circle_horizontal (q := (m : ℂ) / 2)
    ((hdg.const_smul (m : ℝ)).add ((hdf.sub (hdg.const_smul (m : ℝ))).const_smul t))
  · intro s w
    have hc : normSq (circleMap 0 1 s) = 1 := by rw [Complex.normSq_eq_norm_sq]; simp
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, _root_.add_apply,
      _root_.sub_apply, _root_.smul_apply]
    rw [homogeneous_dcLinear_rotation hf htf hfg hc,
      homogeneous_dcLinear_rotation hg htg hgg hc]
  · have hcf := tau_continuousAt (x := x) (fun j => (hf j).differentiableAt)
    have hcg := tau_continuousAt (x := x) (fun j => (hg j).differentiableAt)
    filter_upwards [hcf.eventually (lt_mem_nhds htf), hcg.eventually (lt_mem_nhds htg)] with y hyf hyg
    exact alphaPath_circle (fun j => (hf j).differentiableAt) hyf (fun j c => hfg j y c)
      (fun j => (hg j).differentiableAt) hyg (fun j c => hgg j y c) t

end Mahler

end OAI
