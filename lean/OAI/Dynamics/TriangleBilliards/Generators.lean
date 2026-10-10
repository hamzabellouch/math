import OAI.Dynamics.TriangleBilliards.HilbertFlow

namespace OAI

universe uA

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis
open scoped Topology

abbrev DoubleL2 (Q : Triangle) := Lp ℂ 2 (doubleMeasure Q)

/-- The actual unitary geodesic dynamics on the oriented double. -/
def geodesicHilbertFlow (Q : Triangle) : HilbertFlow (DoubleL2 Q) where
  act := koopman (doubleFlow Q) (measurePreserving_doubleFlow Q)
  zero u := by
    apply Lp.ext
    filter_upwards [coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) 0 u] with z hz
    simpa only [doubleFlow_zero] using hz
  add s t u := by
    apply Lp.ext
    have h₁ := coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) (s + t) u
    have h₂ := coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) s
      (koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) t u)
    have h₃ := (measurePreserving_doubleFlow Q s).quasiMeasurePreserving.ae
      (coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) t u)
    have hc := doubleFlow_cocycle Q t s
    rw [add_comm t s] at hc
    filter_upwards [h₁, h₂, h₃, hc] with z h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    rfl
  continuous u :=
    (continuous_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q)
      (ae_continuousAt_doubleFlow Q)).comp (continuous_id.prodMk continuous_const)

lemma geodesic_koopman_ae (Q : Triangle) (t : ℝ) (u : DoubleL2 Q) :
    (geodesicHilbertFlow Q).act t u =ᵐ[doubleMeasure Q] (fun z => u (doubleFlow Q t z)) :=
  coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) t u

/-- Pullback from the billiard phase space preserves L² exactly. -/
def doubleLift (Q : Triangle) : Lp ℂ 2 (phaseMeasure Q) →ₗᵢ[ℂ] DoubleL2 Q :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst
    (by simpa only [doubleMeasure] using
      (measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)))

lemma doubleLift_ae (Q : Triangle) (f : Lp ℂ 2 (phaseMeasure Q)) :
    (doubleLift Q f : DoublePhase → ℂ) =ᵐ[doubleMeasure Q] (fun z => f z.1) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma doubleLift_invariant (Q : Triangle) (f : Lp ℂ 2 (phaseMeasure Q))
    (hf : ∀ t, (fun z => f (billiardFlow Q t z)) =ᵐ[phaseMeasure Q] f) :
    ∀ t, (geodesicHilbertFlow Q).act t (doubleLift Q f) = doubleLift Q f := by
  intro t
  apply Lp.ext
  have h₁ := geodesic_koopman_ae Q t (doubleLift Q f)
  have h₂ := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae (doubleLift_ae Q f)
  have h₃ : ∀ᵐ z ∂doubleMeasure Q, f (billiardFlow Q t z.1) = f z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (hf t)
  filter_upwards [h₁, h₂, h₃, doubleLift_ae Q f] with z h1 h2 h3 h4
  rw [h1, h2, h4]
  exact h3

end TriangularBilliards

namespace TriangularBilliards
open Analysis
open scoped Topology

lemma continuous_doubleRotate_angle (z : DoublePhase) :
    Continuous (fun θ : ℝ => doubleRotate (Circle.exp θ) z) := by
  by_cases hz : z.2 = 0
  · simp only [doubleRotate, hz, ite_true]
    fun_prop
  · simp only [doubleRotate, hz, ite_false]
    fun_prop

lemma ae_continuousAt_doubleRotate_angle (Q : Triangle) (t : ℝ) :
    ∀ᵐ z ∂doubleMeasure Q, ContinuousAt (fun θ : ℝ => doubleRotate (Circle.exp θ) z) t :=
  Filter.Eventually.of_forall fun z => (continuous_doubleRotate_angle z).continuousAt

lemma continuous_angular_koopman (Q : Triangle) (u : DoubleL2 Q) :
    Continuous (fun θ : ℝ => koopman (fun θ => doubleRotate (Circle.exp θ))
      (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ)) θ u) :=
  continuous_koopman_time (fun θ => doubleRotate (Circle.exp θ))
    (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ))
    (ae_continuousAt_doubleRotate_angle Q) u

/-- Rotation of the oriented tangent fiber, not a rotation of the physical
velocity with the same sign on both copies. -/
def angularHilbertFlow (Q : Triangle) : HilbertFlow (DoubleL2 Q) where
  act := koopman (fun θ => doubleRotate (Circle.exp θ))
    (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ))
  zero u := by
    apply Lp.ext
    filter_upwards [coe_koopman (fun θ => doubleRotate (Circle.exp θ))
      (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ)) 0 u] with z hz
    simpa only [Circle.exp_zero, doubleRotate_one] using hz
  add s t u := by
    apply Lp.ext
    let R := fun θ => doubleRotate (Circle.exp θ)
    let hm := fun θ => measurePreserving_doubleRotate Q (Circle.exp θ)
    have h₁ := coe_koopman R hm (s + t) u
    have h₂ := coe_koopman R hm s (koopman R hm t u)
    have h₃ := (hm s).quasiMeasurePreserving.ae (coe_koopman R hm t u)
    filter_upwards [h₁, h₂, h₃] with z h1 h2 h3
    rw [h1, h2, h3]
    change u (doubleRotate (Circle.exp (s + t)) z) =
      u (doubleRotate (Circle.exp t) (doubleRotate (Circle.exp s) z))
    rw [← doubleRotate_mul, ← Circle.exp_add, add_comm s t]
  continuous := continuous_angular_koopman Q

/-- The transverse geodesic flow is actual geodesic motion after a quarter
turn and restoration of the direction, with no global commutation assumed. -/
def transverseHilbertFlow (Q : Triangle) : HilbertFlow (DoubleL2 Q) :=
  (geodesicHilbertFlow Q).conjugate (angularHilbertFlow Q) (Real.pi / 2)

end TriangularBilliards

namespace TriangularBilliards
open Filter
open scoped Topology ContDiff NNReal

/-- Seam gluing in the two planar sheets: reflection of base and velocity
changes the sheet. This is a local equality, not an assumption of transport
invariance or of an analytic estimate. -/
def SeamCompatible (Q : Triangle) (f : DoublePhase → ℂ) : Prop :=
  ∀ (i : Fin 3) (x : ℂ), x ∈ Q.side i → ∀ (v : Circle) (b : ZMod 2),
    ∀ᶠ y in 𝓝 x, f ((wallReflection Q i y, reflectedDirection Q i v), b + 1) = f ((y, v), b)

/-- Horizontal derivative in the actual unit velocity direction. -/
def xDerivative (f : DoublePhase → ℂ) (z : DoublePhase) : ℂ :=
  fderiv ℝ (fun x => f ((x, z.1.2), z.2)) z.1.1 (z.1.2 : ℂ)

lemma wallReflection_add_smul (Q : Triangle) (i : Fin 3) (x v : ℂ) (t : ℝ) :
    wallReflection Q i (x + t • v) = wallReflection Q i x + t • reflect (Q.tangent i) v := by
  have h := wallReflection_sub Q i (x + t • v) x
  rw [add_sub_cancel_left, reflect_real_smul] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

lemma FlightChain.reflected_direction_previous {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) (n : ℤ) :
    reflectedDirection Q (c.wall n) (c.direction n) = c.direction (n - 1) := by
  apply Subtype.ext
  change reflect (Q.tangent (c.wall n)) (c.direction n : ℂ) = _
  rw [c.specular n, reflect_involutive (Q.tangent_ne_zero _)]

lemma FlightChain.reflected_outgoing_line {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) (n : ℤ) (s : ℝ) :
    wallReflection Q (c.wall n) (c.point n + (s - c.time n) • (c.direction n : ℂ)) =
      c.point (n - 1) + (s - c.time (n - 1)) • (c.direction (n - 1) : ℂ) := by
  rw [wallReflection_add_smul, wallReflection_fixed_side Q (c.on_side n),
    c.specular n, reflect_involutive (Q.tangent_ne_zero _), c.previous_line]

/-- A seam-compatible field has one smooth planar formula through each
collision. Thus no trace at a vertex and no angular regularity is needed
for the ordinary one-variable calculus along a nonsingular orbit. -/
lemma seam_orbit_eventually_line {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (t : ℝ) :
    ∃ n : ℤ, c.time n ≤ t ∧ t < c.time (n + 1) ∧
      (fun s => f (doubleFlow Q s z)) =ᶠ[𝓝 t]
        (fun s => f ((c.point n + (s - c.time n) • (c.direction n : ℂ), c.direction n),
          (n : ZMod 2) + z.2)) := by
  let n := collisionIndex Q t z.1
  have hn := collisionIndex_spec c t
  refine ⟨n, hn.1, hn.2, ?_⟩
  by_cases he : c.time n = t
  · let p : ℝ → ℂ := fun s => c.point n + (s - c.time n) • (c.direction n : ℂ)
    have hp : Tendsto p (𝓝 t) (𝓝 (c.point n)) := by
      have hc : Continuous p := by fun_prop
      simpa only [ContinuousAt, p, ← he, sub_self, zero_smul, add_zero] using hc.continuousAt (x := t)
    have hs := hp.eventually (hf (c.wall n) (c.point n) (c.on_side n)
      (c.direction n) ((n : ZMod 2) + z.2))
    have hi : Ioo (c.time (n - 1)) (c.time (n + 1)) ∈ 𝓝 t := by
      rw [← he]
      exact isOpen_Ioo.mem_nhds ⟨c.increasing (by omega), c.increasing (by omega)⟩
    filter_upwards [hs, hi] with s hs hi
    by_cases hsn : c.time n ≤ s
    · rw [doubleFlow_on_flight c ⟨hsn, hi.2⟩]
    · have hprev : c.time (n - 1) ≤ s ∧ s < c.time ((n - 1) + 1) :=
        ⟨hi.1.le, by simpa only [sub_add_cancel] using lt_of_not_ge hsn⟩
      rw [doubleFlow_on_flight c hprev]
      have hb : ((n : ZMod 2) + z.2) + 1 = ((n - 1 : ℤ) : ZMod 2) + z.2 := by
        push_cast
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        linear_combination h2
      simpa only [p, c.reflected_outgoing_line, c.reflected_direction_previous, hb] using hs
  · have hi : Ioo (c.time n) (c.time (n + 1)) ∈ 𝓝 t :=
      isOpen_Ioo.mem_nhds ⟨lt_of_le_of_ne hn.1 he, hn.2⟩
    filter_upwards [hi] with s hs
    rw [doubleFlow_on_flight c ⟨hs.1.le, hs.2⟩]

lemma seam_orbit_hasDerivAt {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b))) (t : ℝ) :
    HasDerivAt (fun s => f (doubleFlow Q s z)) (xDerivative f (doubleFlow Q t z)) t := by
  obtain ⟨n, hn₀, hn₁, he⟩ := seam_orbit_eventually_line c hf t
  have hp : HasDerivAt (fun s => c.point n + (s - c.time n) • (c.direction n : ℂ))
      (c.direction n : ℂ) t := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id t).sub_const (c.time n)).smul_const
      (c.direction n : ℂ)).const_add (c.point n)
  have h := ((hd (c.direction n) ((n : ZMod 2) + z.2) _).hasFDerivAt).comp_hasDerivAt t hp
  have hx : xDerivative f (doubleFlow Q t z) =
      fderiv ℝ (fun x => f ((x, c.direction n), (n : ZMod 2) + z.2))
        (c.point n + (t - c.time n) • (c.direction n : ℂ)) (c.direction n : ℂ) := by
    rw [doubleFlow_on_flight c ⟨hn₀, hn₁⟩]
    rfl
  rw [hx]
  exact h.congr_of_eventuallyEq he

lemma seam_orbit_norm_deriv_le {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) (t : ℝ) :
    ‖deriv (fun s => f (doubleFlow Q s z)) t‖ ≤ C := by
  rw [(seam_orbit_hasDerivAt c hf hd t).deriv]
  unfold xDerivative
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  rw [Circle.norm_coe, mul_one]
  exact hC _ _ _

lemma seam_orbit_lipschitz {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) :
    LipschitzWith C (fun t => f (doubleFlow Q t z)) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (seam_orbit_hasDerivAt c hf hd t).differentiableAt)
  intro t
  exact_mod_cast seam_orbit_norm_deriv_le c hf hd hC t

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Filter
open scoped Topology NNReal

variable {A : Type uA} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]

/-- Dominated passage from pointwise orbit derivatives to an actual L²
strong derivative. A uniform Lipschitz bound is supplied by the genuine
seam-glued spatial calculus; no generator identity is assumed. -/
lemma koopman_hasDerivAt_zero
    (F : ℝ → A → A) (hm : ∀ t, MeasurePreserving (F t) μ μ)
    (hzero : ∀ x, F 0 x = x)
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {C : ℝ≥0}
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun t => f (F t x)) (g x) 0)
    (hbound : ∀ᵐ x ∂μ, LipschitzWith C (fun t => f (F t x)))
    (hgC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    HasDerivAt (fun t => koopman F hm t (hf.toLp f)) (hg.toLp g) 0 := by
  let u := hf.toLp f
  let v := hg.toLp g
  have hu : (u : A → ℂ) =ᵐ[μ] f := hf.coeFn_toLp
  have hv : (v : A → ℂ) =ᵐ[μ] g := hg.coeFn_toLp
  have huf (t : ℝ) : (koopman F hm t u : A → ℂ) =ᵐ[μ] (fun x => f (F t x)) :=
    (coe_koopman F hm t u).trans ((hm t).quasiMeasurePreserving.ae hu)
  have he0 : koopman F hm 0 u = u := by
    apply Lp.ext
    exact (huf 0).trans (by simpa only [hzero] using hu.symm)
  let q : ℝ → A → ℂ := fun t x => t⁻¹ • (f (F t x) - f x) - g x
  have hq (t : ℝ) : AEStronglyMeasurable (q t) μ :=
    (((hf.aestronglyMeasurable.comp_measurePreserving (hm t)).sub hf.aestronglyMeasurable).const_smul
      (t⁻¹ : ℝ)).sub hg.aestronglyMeasurable
  have he (t : ℝ) : ‖t⁻¹ • (koopman F hm t u - u) - v‖ ^ 2 = ∫ x, ‖q t x‖ ^ 2 ∂μ := by
    rw [norm_sq_L2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((t⁻¹ : ℝ) • (koopman F hm t u - u)) v,
      Lp.coeFn_smul (t⁻¹ : ℝ) (koopman F hm t u - u),
      Lp.coeFn_sub (koopman F hm t u) u, huf t, hu, hv] with x ha hb hc hft hfu hgv
    simp only [ha, hb, hc, Pi.sub_apply, Pi.smul_apply, hft, hfu, hgv, q]
  have hi : Tendsto (fun t : ℝ => ∫ x, ‖q t x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => ∫ x, ‖q t x‖ ^ 2 ∂μ) (𝓝[≠] 0)
        (𝓝 (∫ _x : A, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Eventually.of_forall fun t => (hq t).norm.pow 2
      · refine ⟨(2 * (C : ℝ)) ^ 2, Eventually.of_forall fun t => ?_⟩
        filter_upwards [hbound, hgC] with x hx hgx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        have hdiff : ‖(t⁻¹ : ℝ) • (f (F t x) - f x)‖ ≤ C := by
          by_cases ht : t = 0
          · simp only [ht, inv_zero, zero_smul, norm_zero, NNReal.coe_nonneg]
          rw [norm_smul, norm_inv]
          have hh := hx.norm_sub_le t 0
          rw [hzero, sub_zero] at hh
          calc
            _ ≤ ‖t‖⁻¹ * ((C : ℝ) * ‖t‖) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (norm_nonneg _))
            _ = C := by field_simp
        calc
          ‖q t x‖ ≤ ‖(t⁻¹ : ℝ) • (f (F t x) - f x)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ 2 * (C : ℝ) := by linarith
      · filter_upwards [hd] with x hx
        have hh := hx.tendsto_slope_zero
        simp only [zero_add, hzero] at hh
        have hl := ((hh.sub_const (g x)).norm.pow 2)
        simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, q]
          using hl
    simpa only [integral_zero] using hh
  have hn : Tendsto (fun t => ‖t⁻¹ • (koopman F hm t u - u) - v‖) (𝓝[≠] 0) (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hi
    simpa only [Function.comp_def, ← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using h
  change HasDerivAt (fun t => koopman F hm t u) v 0
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add, he0] using tendsto_iff_norm_sub_tendsto_zero.mpr hn

end TriangularBilliards.Analysis

end
end
end
end
end

end OAI
