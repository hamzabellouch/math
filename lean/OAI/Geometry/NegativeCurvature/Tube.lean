import Mathlib

namespace OAI

/-! Epigraph tube coordinates, holomorphic descent, and curvature of coordinate metrics. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace OneSidedNegative

abbrev ComplexSpace (m : ℕ) := Fin m → ℂ
abbrev RealSpace (m : ℕ) := Fin m → ℝ

def DiffeomorphicToRealSpace {m : ℕ} (T : Set (ComplexSpace m)) : Prop :=
  ∃ (F : RealSpace (2 * m) → ComplexSpace m)
    (G : ComplexSpace m → RealSpace (2 * m)),
    ContDiff ℝ ∞ F ∧ ContDiffOn ℝ ∞ G T ∧
    range F = T ∧ Function.LeftInverse G F ∧
    ∀ z ∈ T, F (G z) = z

def HolomorphicLiouville {m : ℕ} (T : Set (ComplexSpace m)) : Prop :=
  ∀ f : ComplexSpace m → ℂ, DifferentiableOn ℂ f T →
    (∃ C : ℝ, ∀ z ∈ T, ‖f z‖ ≤ C) →
    ∃ c : ℂ, ∀ z ∈ T, f z = c

section CoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure CoordinateMetric (T : Set E) where
  tensor : E → E →L[ℝ] E →L[ℝ] ℝ
  smooth_tensor : ContDiffOn ℝ ∞ tensor T
  symmetric : ∀ x ∈ T, ∀ u v, tensor x u v = tensor x v u
  positive : ∀ x ∈ T, ∀ u, u ≠ 0 → 0 < tensor x u u
  connection : E → E →L[ℝ] E →L[ℝ] E
  smooth_connection : ContDiffOn ℝ ∞ connection T
  torsion_free : ∀ x ∈ T, ∀ u v, connection x u v = connection x v u
  compatible : ∀ x ∈ T, ∀ u v w,
    (fderiv ℝ tensor x u) v w =
      tensor x (connection x u v) w + tensor x v (connection x u w)

namespace CoordinateMetric

variable {T : Set E} (g : CoordinateMetric T)

def curvature (x u v w : E) : E :=
  (fderiv ℝ g.connection x u) v w -
    (fderiv ℝ g.connection x v) u w +
    g.connection x u (g.connection x v w) -
    g.connection x v (g.connection x u w)

def sectionalCurvature (x u v : E) : ℝ :=
  g.tensor x (g.curvature x u v v) u /
    (g.tensor x u u * g.tensor x v v - (g.tensor x u v) ^ 2)

def pathLength (γ : ℝ → E) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt (g.tensor (γ t) (deriv γ t) (deriv γ t)))

def lengthDistance (x y : E) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → E) (_ : ContDiffOn ℝ 1 γ (Icc 0 1))
    (_ : MapsTo γ (Icc 0 1) T) (_ : γ 0 = x) (_ : γ 1 = y),
    g.pathLength γ

def IsComplete : Prop :=
  ∀ x : ℕ → T,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      g.lengthDistance (x i) (x j) < ENNReal.ofReal ε) →
    ∃ p : T, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N,
      g.lengthDistance (x i) p < ENNReal.ofReal ε

def SectionalAtMost (c : ℝ) : Prop :=
  ∀ x ∈ T, ∀ u v : E, LinearIndependent ℝ ![u, v] →
    g.sectionalCurvature x u v ≤ c

def SectionalUnboundedBelow : Prop :=
  ∀ c : ℝ, ∃ x ∈ T, ∃ u v : E,
    LinearIndependent ℝ ![u, v] ∧ g.sectionalCurvature x u v < c

end CoordinateMetric
end CoordinateMetric

def IsKahler {m : ℕ} {T : Set (ComplexSpace m)} (g : CoordinateMetric T) : Prop :=
  (∀ x ∈ T, ∀ u v, g.tensor x (Complex.I • u) (Complex.I • v) = g.tensor x u v) ∧
  (∀ x ∈ T, ∀ u v w,
    (fderiv ℝ g.tensor x u) (Complex.I • v) w +
    (fderiv ℝ g.tensor x v) (Complex.I • w) u +
    (fderiv ℝ g.tensor x w) (Complex.I • u) v = 0)

namespace CoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : Set E} (g : CoordinateMetric T)

theorem koszul_formula {x : E} (hx : x ∈ T) (u v w : E) :
    2 * g.tensor x (g.connection x u v) w =
      (fderiv ℝ g.tensor x u) v w + (fderiv ℝ g.tensor x v) u w -
        (fderiv ℝ g.tensor x w) u v := by
  rw [g.compatible x hx u v w, g.compatible x hx v u w, g.compatible x hx w u v]
  rw [g.symmetric x hx v (g.connection x u w),
    g.symmetric x hx u (g.connection x v w),
    g.symmetric x hx u (g.connection x w v)]
  rw [g.torsion_free x hx v u, g.torsion_free x hx w u, g.torsion_free x hx w v]
  ring

theorem eq_of_tensor_eq {x u v : E} (hx : x ∈ T)
    (h : ∀ w, g.tensor x u w = g.tensor x v w) : u = v := by
  by_contra huv
  have hp := g.positive x hx (u - v) (sub_ne_zero.mpr huv)
  have hz : g.tensor x (u - v) (u - v) = 0 := by
    rw [(g.tensor x).map_sub u v, sub_apply, h (u - v), sub_self]
  linarith

theorem connection_unique (h : CoordinateMetric T) (hgh : g.tensor = h.tensor)
    {x : E} (hx : x ∈ T) (u v : E) :
    g.connection x u v = h.connection x u v := by
  apply g.eq_of_tensor_eq hx
  intro w
  have hg := g.koszul_formula hx u v w
  have hh := h.koszul_formula hx u v w
  rw [← hgh] at hh
  linarith

theorem curvature_unique (h : CoordinateMetric T) (hgh : g.tensor = h.tensor)
    (hT : IsOpen T) {x : E} (hx : x ∈ T) (u v w : E) :
    g.curvature x u v w = h.curvature x u v w := by
  have hc : ∀ y ∈ T, g.connection y = h.connection y := by
    intro y hy
    ext a b
    exact g.connection_unique h hgh hy a b
  have hnhds : g.connection =ᶠ[𝓝 x] h.connection := by
    filter_upwards [hT.mem_nhds hx] with y hy
    exact hc y hy
  simp only [curvature, hnhds.fderiv_eq, hc x hx]

theorem gram_determinant_pos {x u v : E} (hx : x ∈ T)
    (hli : LinearIndependent ℝ ![u, v]) :
    0 < g.tensor x u u * g.tensor x v v - (g.tensor x u v) ^ 2 := by
  have hi := linearIndependent_fin2.mp hli
  have hv : v ≠ 0 := hi.1
  let t := g.tensor x u v / g.tensor x v v
  have hn : u - t • v ≠ 0 := fun h => hi.2 t (sub_eq_zero.mp h).symm
  have hp := g.positive x hx (u - t • v) hn
  have hc := g.positive x hx v hv
  have hc0 : g.tensor x v v ≠ 0 := ne_of_gt hc
  have ht : t * g.tensor x v v = g.tensor x u v := by
    dsimp [t]
    field_simp
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at hp
  rw [g.symmetric x hx v u] at hp
  have hprod := mul_pos hc hp
  nlinarith

end CoordinateMetric

section Tube

variable {E : Type*}

def tube (ℓ : E → ℝ) : Set (E × ℂ) := {p | ℓ p.1 < p.2.im}

def tubeParam (ℓ : E → ℝ) (q : E × (ℝ × ℝ)) : E × ℂ :=
  (q.1, (q.2.1 : ℂ) + (ℓ q.1 + Real.exp q.2.2 : ℝ) * Complex.I)

def tubeParamInv (ℓ : E → ℝ) (p : E × ℂ) : E × (ℝ × ℝ) :=
  (p.1, (p.2.re, Real.log (p.2.im - ℓ p.1)))

@[simp] theorem tubeParam_mem (ℓ : E → ℝ) (q : E × (ℝ × ℝ)) :
    tubeParam ℓ q ∈ tube ℓ := by
  simp [tube, tubeParam, Complex.exp_ofReal_re, Real.exp_pos]

@[simp] theorem tubeParamInv_tubeParam (ℓ : E → ℝ) (q : E × (ℝ × ℝ)) :
    tubeParamInv ℓ (tubeParam ℓ q) = q := by
  simp [tubeParam, tubeParamInv, Complex.exp_ofReal_re]

@[simp] theorem tubeParam_tubeParamInv (ℓ : E → ℝ) {p : E × ℂ}
    (hp : p ∈ tube ℓ) : tubeParam ℓ (tubeParamInv ℓ p) = p := by
  have hb : 0 < p.2.im - ℓ p.1 := sub_pos.mpr hp
  refine Prod.ext rfl ?_
  apply Complex.ext <;> simp [tubeParam, tubeParamInv, Real.exp_log hb]

@[simp] theorem range_tubeParam (ℓ : E → ℝ) : range (tubeParam ℓ) = tube ℓ := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact tubeParam_mem ℓ q
  · intro hp
    exact ⟨tubeParamInv ℓ p, tubeParam_tubeParamInv ℓ hp⟩

variable [NormedAddCommGroup E]

theorem isOpen_tube {ℓ : E → ℝ} (hℓ : Continuous ℓ) : IsOpen (tube ℓ) :=
  isOpen_lt (hℓ.comp continuous_fst) (Complex.continuous_im.comp continuous_snd)

theorem continuous_tubeParam {ℓ : E → ℝ} (hℓ : Continuous ℓ) :
    Continuous (tubeParam ℓ) := by
  unfold tubeParam
  fun_prop

variable [NormedSpace ℝ E]

theorem isConnected_tube {ℓ : E → ℝ} (hℓ : Continuous ℓ) : IsConnected (tube ℓ) := by
  rw [← range_tubeParam]
  exact isConnected_range (continuous_tubeParam hℓ)

theorem contDiff_tubeParam {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    ContDiff ℝ ∞ (tubeParam ℓ) := by
  unfold tubeParam
  have hc : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  fun_prop

theorem contDiffOn_tubeParamInv {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    ContDiffOn ℝ ∞ (tubeParamInv ℓ) (tube ℓ) := by
  have hre : ContDiff ℝ ∞ (fun p : E × ℂ => p.2.re) :=
    Complex.reCLM.contDiff.comp contDiff_snd
  have hgap : ContDiff ℝ ∞ (fun p : E × ℂ => p.2.im - ℓ p.1) :=
    (Complex.imCLM.contDiff.comp contDiff_snd).sub (hℓ.comp contDiff_fst)
  exact contDiffOn_fst.prodMk (hre.contDiffOn.prodMk
    (hgap.contDiffOn.log (fun p hp => ne_of_gt (sub_pos.mpr hp))))

theorem tube_smooth_coordinates {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    IsOpen (tube ℓ) ∧ IsConnected (tube ℓ) ∧
    ∃ (F : E × (ℝ × ℝ) → E × ℂ) (G : E × ℂ → E × (ℝ × ℝ)),
      ContDiff ℝ ∞ F ∧ ContDiffOn ℝ ∞ G (tube ℓ) ∧
      range F = tube ℓ ∧ Function.LeftInverse G F ∧
      ∀ p ∈ tube ℓ, F (G p) = p := by
  exact ⟨isOpen_tube hℓ.continuous, isConnected_tube hℓ.continuous,
    tubeParam ℓ, tubeParamInv ℓ, contDiff_tubeParam hℓ, contDiffOn_tubeParamInv hℓ,
    range_tubeParam ℓ, tubeParamInv_tubeParam ℓ, fun _ hp => tubeParam_tubeParamInv ℓ hp⟩

end Tube

section AnalyticDescent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ℓ : E → ℝ} {f : E × ℂ → ℂ}

theorem fiber_constant_of_vertical_deriv_zero
    (hf : DifferentiableOn ℂ f (tube ℓ))
    (hv : ∀ p ∈ tube ℓ, deriv (fun w => f (p.1, w)) p.2 = 0)
    {z : E} {w₁ w₂ : ℂ} (h₁ : ℓ z < w₁.im) (h₂ : ℓ z < w₂.im) :
    f (z, w₁) = f (z, w₂) := by
  have ho : IsOpen {w : ℂ | ℓ z < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hd : DifferentiableOn ℂ (fun w => f (z, w)) {w : ℂ | ℓ z < w.im} :=
    hf.comp ((differentiable_const z).prodMk differentiable_id).differentiableOn
      (fun _ hw => hw)
  exact ho.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt (ℓ z)).isPreconnected
    hd (fun w hw => hv (z, w) hw) h₁ h₂

theorem holomorphic_descent_on_tube (hℓ : Continuous ℓ)
    (hf : DifferentiableOn ℂ f (tube ℓ))
    (hb : ∃ C : ℝ, ∀ p ∈ tube ℓ, ‖f p‖ ≤ C)
    (hc : ∀ z : E, ∀ w₁ w₂ : ℂ, ℓ z < w₁.im → ℓ z < w₂.im →
      f (z, w₁) = f (z, w₂)) :
    ∃ F : E → ℂ, Differentiable ℂ F ∧ Bornology.IsBounded (range F) ∧
      ∀ p ∈ tube ℓ, f p = F p.1 := by
  let W : E → ℂ := fun z => (ℓ z + 1 : ℝ) * Complex.I
  have hW (z : E) : ℓ z < (W z).im := by simp [W]
  let F : E → ℂ := fun z => f (z, W z)
  have hF : Differentiable ℂ F := by
    intro z
    have hlocal : DifferentiableAt ℂ (fun z' => f (z', W z)) z :=
      (hf.differentiableAt ((isOpen_tube hℓ).mem_nhds (hW z))).comp z
        (differentiableAt_id.prodMk (differentiableAt_const (W z)))
    apply hlocal.congr_of_eventuallyEq
    have hnbhd : ∀ᶠ z' in 𝓝 z, ℓ z' < (W z).im :=
      hℓ.continuousAt.preimage_mem_nhds (eventually_lt_nhds (hW z))
    filter_upwards [hnbhd] with z' hz'
    exact hc z' (W z') (W z) (hW z') hz'
  refine ⟨F, hF, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hb
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C, ?_⟩
    rintro v ⟨z, rfl⟩
    exact hC (z, W z) (hW z)
  · intro p hp
    exact hc p.1 p.2 (W p.1) hp (hW p.1)

theorem constant_of_bounded_holomorphic_vertical_deriv_zero (hℓ : Continuous ℓ)
    (hf : DifferentiableOn ℂ f (tube ℓ))
    (hb : ∃ C : ℝ, ∀ p ∈ tube ℓ, ‖f p‖ ≤ C)
    (hv : ∀ p ∈ tube ℓ, deriv (fun w => f (p.1, w)) p.2 = 0) :
    ∃ c : ℂ, ∀ p ∈ tube ℓ, f p = c := by
  obtain ⟨F, hF, hFb, hfF⟩ := holomorphic_descent_on_tube hℓ hf hb
    (fun _ _ _ h₁ h₂ => fiber_constant_of_vertical_deriv_zero hf hv h₁ h₂)
  obtain ⟨c, hc⟩ := hF.exists_const_forall_eq_of_bounded hFb
  exact ⟨c, fun p hp => (hfF p hp).trans (hc p.1)⟩

end AnalyticDescent

def complexTubeEquiv (n : ℕ) : ComplexSpace (n + 1) ≃L[ℂ] (ComplexSpace n × ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [ComplexSpace, Module.finrank_prod])

def realTubeEquiv (n : ℕ) : RealSpace (2 * (n + 1)) ≃L[ℝ]
    (ComplexSpace n × (ℝ × ℝ)) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [ComplexSpace, RealSpace, Module.finrank_prod, Module.finrank_pi_fintype,
      Complex.finrank_real_complex]
    omega)

def tubeInCoordinates {n : ℕ} (ℓ : ComplexSpace n → ℝ) : Set (ComplexSpace (n + 1)) :=
  complexTubeEquiv n ⁻¹' tube ℓ

theorem tubeInCoordinates_topology {n : ℕ} {ℓ : ComplexSpace n → ℝ}
    (hℓ : ContDiff ℝ ∞ ℓ) :
    IsOpen (tubeInCoordinates ℓ) ∧ IsConnected (tubeInCoordinates ℓ) ∧
      DiffeomorphicToRealSpace (tubeInCoordinates ℓ) := by
  let e := complexTubeEquiv n
  let a := realTubeEquiv n
  have he : ContDiff ℝ ∞ e := e.contDiff.restrict_scalars ℝ
  have hei : ContDiff ℝ ∞ e.symm := e.symm.contDiff.restrict_scalars ℝ
  refine ⟨(isOpen_tube hℓ.continuous).preimage e.continuous,
    e.toHomeomorph.isConnected_preimage.mpr (isConnected_tube hℓ.continuous), ?_⟩
  refine ⟨fun t => e.symm (tubeParam ℓ (a t)),
    fun z => a.symm (tubeParamInv ℓ (e z)),
    hei.comp ((contDiff_tubeParam hℓ).comp a.contDiff),
    a.symm.contDiff.comp_contDiffOn ((contDiffOn_tubeParamInv hℓ).comp he.contDiffOn
      (fun _ hz => hz)), ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨t, rfl⟩
      change e (e.symm (tubeParam ℓ (a t))) ∈ tube ℓ
      rw [e.apply_symm_apply]
      exact tubeParam_mem ℓ (a t)
    · intro hz
      refine ⟨a.symm (tubeParamInv ℓ (e z)), ?_⟩
      have hz' : e z ∈ tube ℓ := hz
      simp [tubeParam_tubeParamInv ℓ hz']
  · intro t
    simp
  · intro z hz
    have hz' : e z ∈ tube ℓ := hz
    simp [tubeParam_tubeParamInv ℓ hz']

theorem unbounded_below_of_negative_linear_term {κ B : ℝ} (hκ : κ < 0)
    {K : ℝ → ℝ} (hK : ∀ b > 0, K b ≤ B + b * κ) :
    ∀ A : ℝ, ∃ b > 0, K b < A := by
  intro A
  let b := max 0 ((A - B) / κ) + 1
  have hb : 0 < b := by
    dsimp [b]
    linarith [le_max_left (0 : ℝ) ((A - B) / κ)]
  have hlarge : (A - B) / κ < b := by
    dsimp [b]
    linarith [le_max_right (0 : ℝ) ((A - B) / κ)]
  have hprod : b * κ < A - B := (div_lt_iff_of_neg hκ).mp hlarge
  exact ⟨b, hb, lt_of_le_of_lt (hK b hb) (by linarith)⟩

theorem CoordinateMetric.unboundedBelow_of_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : Set E}
    (g : CoordinateMetric T) {κ B : ℝ} (hκ : κ < 0) (x u v : ℝ → E)
    (hx : ∀ b > 0, x b ∈ T)
    (hplane : ∀ b > 0, LinearIndependent ℝ ![u b, v b])
    (hsec : ∀ b > 0, g.sectionalCurvature (x b) (u b) (v b) ≤ B + b * κ) :
    g.SectionalUnboundedBelow := by
  intro A
  obtain ⟨b, hb, hA⟩ := unbounded_below_of_negative_linear_term hκ hsec A
  exact ⟨x b, hx b hb, u b, v b, hplane b hb, hA⟩

end OneSidedNegative

end

end OAI
