import Mathlib
import OAI.Probability.SLE.LoewnerReflection

namespace OAI

/-! Boundary Density for chordal SLE. -/

section
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

noncomputable def smoothPositiveGap (a x : ℝ) : ℝ :=
  a + (x-a)*(1-Real.smoothTransition ((2*a-x)/a))

lemma smoothPositiveGap_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 < smoothPositiveGap a x := by
  by_cases hx : x ≤ a
  · have he : 1 ≤ (2*a-x)/a := (le_div_iff₀ ha).mpr (by linarith)
    simp only [smoothPositiveGap,Real.smoothTransition.one_of_one_le he,sub_self,mul_zero,add_zero]
    exact ha
  · have ht := Real.smoothTransition.le_one ((2*a-x)/a)
    have hm : 0 ≤ (x-a)*(1-Real.smoothTransition ((2*a-x)/a)) := mul_nonneg (by linarith) (by linarith)
    unfold smoothPositiveGap
    linarith

lemma smoothPositiveGap_eq {a x : ℝ} (ha : 0 < a) (hx : 2*a ≤ x) :
    smoothPositiveGap a x = x := by
  have he : (2*a-x)/a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  simp only [smoothPositiveGap,Real.smoothTransition.zero_of_nonpos he,sub_zero,mul_one]
  ring

lemma smoothPositiveGap_contDiff (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPositiveGap a) := by
  unfold smoothPositiveGap
  fun_prop

noncomputable def boundaryDensity (κ α β : ℝ) (q : ℂ) (b : ℝ) : ℝ :=
  Real.exp (-β*α*q.im - β*Real.log (q.re-Real.sqrt κ*b))

noncomputable def smoothBoundaryDensity (κ α β a : ℝ) (q : ℂ) (b : ℝ) : ℝ :=
  Real.exp (-β*α*q.im - β*Real.log (smoothPositiveGap a (q.re-Real.sqrt κ*b)))

lemma smoothBoundaryDensity_contDiff (κ α β : ℝ) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => smoothBoundaryDensity κ α β a p.1 p.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => p.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => p.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => smoothPositiveGap a (p.1.re-Real.sqrt κ*p.2)) :=
    (smoothPositiveGap_contDiff a).comp (hre.sub (contDiff_const.mul contDiff_snd))
  exact ((contDiff_const.mul him).sub (contDiff_const.mul
    (hg.log (fun p => (smoothPositiveGap_pos ha _).ne')))).exp

lemma smoothBoundaryDensity_eq {κ α β a : ℝ} {q : ℂ} {b : ℝ}
    (ha : 0 < a) (hx : 2*a ≤ q.re-Real.sqrt κ*b) :
    smoothBoundaryDensity κ α β a q b = boundaryDensity κ α β q b := by
  simp only [smoothBoundaryDensity,boundaryDensity,smoothPositiveGap_eq ha hx]

lemma smoothBoundaryDensity_eventuallyEq (κ α β : ℝ) {a : ℝ} (ha : 0 < a)
    (p : ℂ × ℝ) (hp : 2*a < p.1.re-Real.sqrt κ*p.2) :
    (fun q : ℂ × ℝ => smoothBoundaryDensity κ α β a q.1 q.2) =ᶠ[𝓝 p]
      (fun q : ℂ × ℝ => boundaryDensity κ α β q.1 q.2) := by
  have he : ∀ᶠ q : ℂ × ℝ in 𝓝 p, 2*a < q.1.re-Real.sqrt κ*q.2 :=
    ((Complex.continuous_re.comp continuous_fst).sub
      (continuous_const.mul continuous_snd)).continuousAt.eventually (lt_mem_nhds hp)
  filter_upwards [he] with q hq
  simp only [smoothBoundaryDensity,boundaryDensity,smoothPositiveGap_eq ha hq.le]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma boundaryDensity_contDiffAt (κ α β : ℝ) (p : ℂ × ℝ)
    (hp : p.1.re-Real.sqrt κ*p.2 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => boundaryDensity κ α β r.1 r.2) p := by
  have hre : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => r.1.re) p :=
    (Complex.reCLM.contDiff.comp contDiff_fst).contDiffAt
  have him : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => r.1.im) p :=
    (Complex.imCLM.contDiff.comp contDiff_fst).contDiffAt
  exact ((contDiffAt_const.mul him).sub (contDiffAt_const.mul
    ((hre.sub (contDiffAt_const.mul contDiffAt_snd)).log hp))).exp

lemma boundaryDensity_spatial_derivative (κ α β : ℝ) (q : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    HasDerivAt (boundaryDensity κ α β q)
      (boundaryDensity κ α β q b*(β*Real.sqrt κ/(q.re-Real.sqrt κ*b))) b := by
  have hX := (hasDerivAt_const b q.re).sub ((hasDerivAt_id b).const_mul (Real.sqrt κ))
  have hd := ((hasDerivAt_const b (-β*α*q.im)).sub ((hX.log hp).const_mul β)).exp
  convert hd using 1 <;> try rfl
  dsimp only [boundaryDensity,Pi.sub_apply,Pi.mul_apply,Pi.div_apply,Function.comp_def,id_eq]
  ring

lemma boundaryDensity_spatial_second (κ α β : ℝ) (hκ : 0 ≤ κ) (q : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    iteratedDeriv 2 (boundaryDensity κ α β q) b =
      boundaryDensity κ α β q b*κ*β*(β+1)/(q.re-Real.sqrt κ*b)^2 := by
  have hn : ∀ᶠ y : ℝ in 𝓝 b, q.re-Real.sqrt κ*y ≠ 0 :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne hp
  have hd : deriv (boundaryDensity κ α β q) =ᶠ[𝓝 b]
      (fun y => boundaryDensity κ α β q y*(β*Real.sqrt κ/(q.re-Real.sqrt κ*y))) := by
    filter_upwards [hn] with y hy
    exact (boundaryDensity_spatial_derivative κ α β q y hy).deriv
  have hX := (hasDerivAt_const b q.re).sub ((hasDerivAt_id b).const_mul (Real.sqrt κ))
  have hh := (boundaryDensity_spatial_derivative κ α β q b hp).mul
    ((hasDerivAt_const b (β*Real.sqrt κ)).div hX hp)
  dsimp only [Pi.mul_apply,Pi.div_apply,Pi.sub_apply,id_eq] at hh
  change HasDerivAt (fun y => boundaryDensity κ α β q y*(β*Real.sqrt κ/(q.re-Real.sqrt κ*y))) _ b at hh
  rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,hd.deriv_eq,hh.deriv]
  have hs := Real.sq_sqrt hκ
  generalize boundaryDensity κ α β q b = f
  generalize q.re-Real.sqrt κ*b = X
  generalize Real.sqrt κ = r at *
  rw [← hs]
  field_simp
  ring

lemma boundaryDensity_directional (κ α β : ℝ) (q v : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b) (v,0) =
      boundaryDensity κ α β q b * (-β*α*v.im - β*v.re/(q.re-Real.sqrt κ*b)) := by
  have hr : HasDerivAt (fun t : ℝ => (q+t • v).re) v.re 0 := by
    simpa only [Complex.add_re,Complex.smul_re,smul_eq_mul,id_eq,one_mul] using
      ((hasDerivAt_id (0:ℝ)).mul_const v.re).const_add q.re
  have hi : HasDerivAt (fun t : ℝ => (q+t • v).im) v.im 0 := by
    simpa only [Complex.add_im,Complex.smul_im,smul_eq_mul,id_eq,one_mul] using
      ((hasDerivAt_id (0:ℝ)).mul_const v.im).const_add q.im
  have hd := ((hi.const_mul (-β*α)).sub
    (((hr.sub_const (Real.sqrt κ*b)).log (by simpa only [zero_smul,add_zero] using hp)).const_mul β)).exp
  have hline : HasDerivAt (fun t : ℝ => boundaryDensity κ α β (q+t • v) b)
      (boundaryDensity κ α β q b * (-β*α*v.im-β*v.re/(q.re-Real.sqrt κ*b))) 0 := by
    convert hd using 1 <;> try rfl
    simp only [zero_smul,add_zero,boundaryDensity,Pi.sub_apply]
    ring
  have haff : HasDerivAt (fun t : ℝ => (q+t • v,b)) (v,0) 0 := by
    simpa only [id_eq,one_smul] using (((hasDerivAt_id (0:ℝ)).smul_const v).const_add q).prodMk (hasDerivAt_const 0 b)
  have hfd : HasFDerivAt (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2)
      (fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b)) (q+(0:ℝ) • v,b) := by
    simpa only [zero_smul,add_zero] using ((boundaryDensity_contDiffAt κ α β (q,b) hp).differentiableAt (by simp)).hasFDerivAt
  have hh := hfd.comp_hasDerivAt 0 haff
  exact hh.unique hline

lemma boundaryDensity_generator (κ α β : ℝ) (hκ : 0 ≤ κ) (q : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b)
      (((2/(q.re-Real.sqrt κ*b):ℝ):ℂ) + (((q.re-Real.sqrt κ*b)⁻¹^2:ℝ):ℂ)*I,0) +
      (1/2:ℝ)*iteratedDeriv 2 (boundaryDensity κ α β q) b =
      boundaryDensity κ α β q b * β * (-α-2+κ*(β+1)/2)/(q.re-Real.sqrt κ*b)^2 := by
  rw [boundaryDensity_directional κ α β q _ b hp,boundaryDensity_spatial_second κ α β hκ q b hp]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
    Complex.I_re,mul_zero,add_zero,zero_add,Complex.add_re,Complex.mul_re,sub_zero]
  field_simp

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma exists_compact_boundary_field (κ α β a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) :
    ∃ φ : ℂ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q b, ‖(q,b)‖ ≤ R → 2*a < q.re-Real.sqrt κ*b → φ (q,b) = boundaryDensity κ α β q b) ∧
      (∀ q b, ‖(q,b)‖ ≤ R → 2*a < q.re-Real.sqrt κ*b →
        fderiv ℝ φ (q,b) = fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b)) ∧
      (∀ q b, ‖(q,b)‖ ≤ R → 2*a < q.re-Real.sqrt κ*b →
        iteratedDeriv 2 (fun x => φ (q,x)) b = iteratedDeriv 2 (boundaryDensity κ α β q) b) := by
  let cut : ContDiffBump (0 : ℂ × ℝ) := ⟨R+1,R+2,by linarith,by linarith⟩
  let φ (p : ℂ × ℝ) := cut p*smoothBoundaryDensity κ α β a p.1 p.2
  have hnear (p : ℂ × ℝ) (hball : ‖p‖ ≤ R) (hp : 2*a < p.1.re-Real.sqrt κ*p.2) :
      φ =ᶠ[𝓝 p] (fun z : ℂ × ℝ => boundaryDensity κ α β z.1 z.2) := by
    have hb : p ∈ Metric.ball (0:ℂ × ℝ) cut.rIn := by
      simpa only [Metric.mem_ball,dist_zero_right] using (show ‖p‖ < R+1 by linarith)
    filter_upwards [cut.eventuallyEq_one_of_mem_ball hb,smoothBoundaryDensity_eventuallyEq κ α β ha p hp] with z hz he
    simp only [φ,hz,Pi.one_apply,one_mul,he]
  refine ⟨φ,cut.contDiff.mul (smoothBoundaryDensity_contDiff κ α β ha),cut.hasCompactSupport.mul_right,
    (fun q b h h' => (hnear (q,b) h h').eq_of_nhds),?_,?_⟩
  · intro q b h h'
    exact (hnear (q,b) h h').fderiv_eq
  · intro q b h h'
    exact ((hnear (q,b) h h').comp_tendsto ((continuous_const.prodMk continuous_id).tendsto b)).iteratedDeriv_eq 2

lemma compact_boundary_drift_zero (κ α β a : ℝ) (hκ : 0 < κ) (ha : 0 < a)
    (hβ : -α-2+κ*(β+1)/2 = 0) (φ : ℂ × ℝ → ℝ) (q : ℂ) (b : ℝ)
    (hD : fderiv ℝ φ (q,b) = fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b))
    (h2 : iteratedDeriv 2 (fun x => φ (q,x)) b = iteratedDeriv 2 (boundaryDensity κ α β q) b)
    (hx : 2*a < q.re-Real.sqrt κ*b) :
    fderiv ℝ φ (q,b) (boundaryClockField a (Real.sqrt κ*b) q,0) +
      (1/2:ℝ)*iteratedDeriv 2 (fun x => φ (q,x)) b = 0 := by
  have hgap : a ≤ q.re-Real.sqrt κ*b := by linarith
  have he : boundaryClockField a (Real.sqrt κ*b) q =
      ((2/(q.re-Real.sqrt κ*b):ℝ):ℂ) + (((q.re-Real.sqrt κ*b)⁻¹^2:ℝ):ℂ)*I := by
    simp only [boundaryClockField,positiveBoundaryField_eq hgap,max_eq_right hgap]
  rw [hD,h2,he,boundaryDensity_generator κ α β hκ.le q b (by linarith),hβ,mul_zero,zero_div]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

theorem BoundaryClockSolution.stopped_boundary_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ a : ℝ} {q₀ : ℂ}
    (c : BoundaryClockSolution B hm κ a q₀)
    (hκ : 0 < κ) (ha : 0 < a) (α β : ℝ)
    (hβ : -α-2+κ*(β+1)/2 = 0)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ 2*a < (c.Q t ω).re-Real.sqrt κ*B t ω) :
    Integrable (fun ω => boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        boundaryDensity κ α β q₀ 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_boundary_field κ α β a R ha hR
  let L₀ : ℝ≥0 := ⟨2*a⁻¹+a⁻¹^2,by positivity⟩
  have hL₀ := boundaryClockField_bound ha
  let V (t : ℝ) (ω : Ω) :=
    boundaryClockField a (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair : Measurable (fun p : ℝ × Ω =>
      (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)) := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × ℂ => boundaryClockField a p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_boundaryClockField ha).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let drift (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hzero (ω : Ω) (u : ℝ) (hu : 0 ≤ u) (hut : u < (τ ω : ℝ)) :
      brownianFieldDrift B F drift u ω = 0 := by
    have ht : u.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr hut.le
    obtain ⟨hball, hgap⟩ := hinside ω u.toNNReal ht
    change fderiv ℝ φ (c.Q (u.toNNReal : ℝ) ω, B u.toNNReal ω)
      (V (u.toNNReal : ℝ) ω, 0) + _ = 0
    dsimp only [V]
    rw [Real.toNNReal_coe]
    exact compact_boundary_drift_zero κ α β a hκ ha hβ φ _ _
      (hφD _ _ hball hgap) (hφ2 _ _ hball hgap) hgap
  have hopt := brownian_time_field_optional hB hm hBm hBc K F drift hfield τ hτ T hb hzero
  have hτm := stopping_time_measurable_nnreal hτ
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hQmτ : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hfm : Measurable (fun ω => F (τ ω) ω (B (τ ω) ω)) :=
    hφ.continuous.measurable.comp (hQmτ.prodMk hBmτ)
  have hfi : Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using
        hfield.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)
  have hfeq (ω : Ω) : F (τ ω) ω (B (τ ω) ω) =
      boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1 (hinside ω (τ ω) le_rfl).2
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  calc
    _ = ∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hfeq ω).symm)
    _ = ∫ ω, F 0 ω (B 0 ω) ∂P := hopt
    _ = ∫ _, boundaryDensity κ α β q₀ 0 ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
      change φ (c.Q 0 ω, B 0 ω) = _
      have hh : ‖(c.Q 0 ω, B 0 ω)‖ ≤ R := by
        simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
      rw [hφeq _ _ hh (hinside ω 0 zero_le).2, c.initial ω, hB0]
    _ = boundaryDensity κ α β q₀ 0 := by simp

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

lemma continuous_hittingBtwn_mem {Ω : Type*} (H : ℝ≥0 → Ω → ℝ)
    (hHc : ∀ ω, Continuous (fun t => H t ω)) (T : ℝ≥0) (ω : Ω)
    (he : ∃ j ∈ Icc 0 T, H j ω ∈ ({0} : Set ℝ)) :
    H (hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω) ω = 0 := by
  have hc : IsClosed (Icc 0 T ∩ {t : ℝ≥0 | H t ω ∈ ({0} : Set ℝ)}) :=
    isClosed_Icc.inter (isClosed_singleton.preimage (hHc ω))
  have hn : (Icc 0 T ∩ {t : ℝ≥0 | H t ω ∈ ({0} : Set ℝ)}).Nonempty := by
    obtain ⟨j, hj, hh⟩ := he
    exact ⟨j, hj, hh⟩
  have hh := hc.csInf_mem hn (bddBelow_Icc.inter_of_left)
  simpa only [hittingBtwn_def, ite_eq_left he, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff] using hh.2

lemma continuous_zero_iff_dense
    (H : ℝ≥0 → ℝ) (hHc : Continuous H) (hHn : ∀ t, 0 ≤ H t) (t : ℝ≥0) :
    (∃ s ≤ t, H s = 0) ↔
      ∀ n : ℕ, ∃ k : ℕ,
        H (TopologicalSpace.denseSeq (Iic t) k) < 1 / ((n : ℝ) + 1) := by
  let : Nonempty (Iic t) := ⟨⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩⟩
  constructor
  · rintro ⟨s, hs, he⟩ n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact (TopologicalSpace.denseRange_denseSeq (Iic t)).exists_mem_open
      (isOpen_lt (hHc.comp continuous_subtype_val) continuous_const)
      ⟨⟨s, hs⟩, by simpa only [mem_ofPred_eq, Function.comp_apply, he] using hpos⟩
  · intro he
    have hcc : IsCompact (Iic t) := by
      have heq : Iic t = Icc 0 t := by ext s; simp
      rw [heq]
      exact isCompact_Icc
    obtain ⟨s, hs, hmin⟩ := hcc.exists_isMinOn
      ⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩ hHc.continuousOn
    refine ⟨s, hs, le_antisymm ?_ (hHn s)⟩
    apply ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact Eventually.of_forall fun n => by
      obtain ⟨k, hk⟩ := he n
      exact (hmin (TopologicalSpace.denseSeq (Iic t) k).property).trans hk.le

theorem continuous_nonnegative_first_zero_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    (H : ℝ≥0 → Ω → ℝ) (hHa : Adapted f H)
    (hHc : ∀ ω, Continuous (fun t => H t ω))
    (hHn : ∀ t ω, 0 ≤ H t ω) (T : ℝ≥0) :
    IsStoppingTime f (fun ω => ((hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω : ℝ≥0) : WithTop ℝ≥0)) ∧
    (∀ ω, hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω ≤ T) ∧
    (∀ ω t, t < hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω → 0 < H t ω) ∧
    (∀ ω, hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω < T → H (hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω) ω = 0) := by
  classical
  have hb (ω : Ω) := hittingBtwn_le (u := H) (s := ({0} : Set ℝ)) (n := 0) (m := T) ω
  have hmem (ω : Ω) (h : hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω < T) :
      H (hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω) ω = 0 := by
    apply continuous_hittingBtwn_mem H hHc T ω
    by_contra he
    simp only [hittingBtwn_def, ite_eq_right he] at h
    exact lt_irrefl _ h
  refine ⟨?_, hb, ?_, hmem⟩
  · intro t
    by_cases hT : T ≤ t
    · have he : {ω : Ω | ((hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true, WithTop.coe_le_coe]
        exact (hb ω).trans hT
      rw [he]
      exact MeasurableSet.univ
    · have ht : t < T := lt_of_not_ge hT
      let : Nonempty (Iic t) := ⟨⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩⟩
      have he (ω : Ω) : hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω ≤ t ↔ ∃ s ≤ t, H s ω = 0 := by
        constructor
        · intro h
          exact ⟨_, h, hmem ω (h.trans_lt ht)⟩
        · rintro ⟨s, hs, h0⟩
          exact (hittingBtwn_le_of_mem (zero_le) (hs.trans ht.le) (by simpa using h0)).trans hs
      have hset : {ω : Ω | ((hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
          ⋂ n : ℕ, ⋃ k : ℕ, {ω : Ω | H (TopologicalSpace.denseSeq (Iic t) k) ω < 1 / ((n : ℝ) + 1)} := by
        ext ω
        simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_iInter, mem_iUnion]
        exact (he ω).trans (continuous_zero_iff_dense (fun s => H s ω) (hHc ω) (fun s => hHn s ω) t)
      rw [hset]
      apply MeasurableSet.iInter
      intro n
      apply MeasurableSet.iUnion
      intro k
      have hm := (hHa (TopologicalSpace.denseSeq (Iic t) k)).mono
        (f.mono (TopologicalSpace.denseSeq (Iic t) k).property) le_rfl
      exact measurableSet_lt hm measurable_const
  · intro ω t ht
    have hn := notMem_of_lt_hittingBtwn ht (zero_le)
    exact lt_of_le_of_ne (hHn t ω) (by simpa only [mem_singleton_iff, ne_eq, eq_comm] using hn)

end SLEExactGauge
end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def logRadiusClock (η₀ : ℝ) (q : ℂ × ℝ) : ℝ :=
  η₀ - q.1.im + q.2

noncomputable def logAngleSq (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) : ℝ :=
  Real.exp (2 * q.1.im) / greenLogNormSq κ q b

noncomputable def logClockRate (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) : ℝ :=
  4 * Real.exp (2 * q.1.im) / greenLogNormSq κ q b ^ 2

lemma logAngleSq_pos (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 < logAngleSq κ q b :=
  div_pos (Real.exp_pos _) (greenLogNormSq_pos κ q b)

lemma logAngleSq_le_one (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    logAngleSq κ q b ≤ 1 := by
  apply (div_le_one (greenLogNormSq_pos κ q b)).mpr
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma continuous_logAngleSq (κ : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => logAngleSq κ p.1 p.2) := by
  have hi : Continuous (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) :=
    Complex.continuous_im.comp (continuous_fst.fst)
  have hr : Continuous (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) :=
    Complex.continuous_re.comp (continuous_fst.fst)
  exact (Real.continuous_exp.comp (continuous_const.mul hi)).div
    (((hr.sub (continuous_const.mul continuous_snd)).pow 2).add
      (Real.continuous_exp.comp (continuous_const.mul hi)))
    (fun p => (greenLogNormSq_pos κ p.1 p.2).ne')

lemma continuous_logRadiusClock (η₀ : ℝ) : Continuous (logRadiusClock η₀) :=
  (continuous_const.sub (Complex.continuous_im.comp continuous_fst)).add continuous_snd

lemma greenLogDensity_radius_angle (κ η₀ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    greenLogDensity κ q b =
      Real.exp (codimension κ * (logRadiusClock η₀ q - Real.log 2 - η₀)) *
        (logAngleSq κ q b) ^ (greenExponent κ / 2) := by
  rw [Real.rpow_def_of_pos (logAngleSq_pos κ q b), ← Real.exp_add]
  unfold logAngleSq
  rw [Real.log_div (Real.exp_ne_zero _) (greenLogNormSq_pos κ q b).ne', Real.log_exp]
  unfold greenLogDensity logRadiusClock
  congr 1
  ring

lemma codimension_pos (κ : ℝ) (hκ8 : κ < 8) : 0 < codimension κ := by
  dsimp [codimension, dimension]
  linarith

lemma greenExponent_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < greenExponent κ := by
  unfold greenExponent
  have : 1 < 8 / κ := (lt_div_iff₀ hκ).mpr (by simpa using hκ8)
  linarith

lemma greenLogDensity_le_at_angular_exit
    (κ η₀ u ε : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (q : ℂ × ℝ) (b : ℝ)
    (hclock : logRadiusClock η₀ q ≤ u) (hangle : logAngleSq κ q b ≤ ε) :
    greenLogDensity κ q b ≤
      Real.exp (codimension κ * (u - Real.log 2 - η₀)) * ε ^ (greenExponent κ / 2) := by
  rw [greenLogDensity_radius_angle κ η₀ q b]
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith)
      (codimension_pos κ hκ8).le)
  · exact Real.rpow_le_rpow (logAngleSq_pos κ q b).le hangle
      (div_nonneg (greenExponent_pos κ hκ hκ8).le (by norm_num))
  · exact Real.rpow_nonneg (logAngleSq_pos κ q b).le _
  · exact (Real.exp_pos _).le

lemma logClockRate_pos (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 < logClockRate κ q b := by
  unfold logClockRate
  exact div_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (sq_pos_of_pos (greenLogNormSq_pos κ q b))

lemma logClockRate_angle (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    logClockRate κ q b = 4 * logAngleSq κ q b ^ 2 / Real.exp (2 * q.1.im) := by
  unfold logClockRate logAngleSq
  field_simp [(Real.exp_pos (2 * q.1.im)).ne', (greenLogNormSq_pos κ q b).ne']

lemma log_ode_im_derivative {Q : ℝ → ℂ × ℝ} {D : Set ℝ} {t κ b : ℝ}
    (hQ : HasDerivWithinAt Q (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)) D t) :
    HasDerivWithinAt (fun s => (Q s).1.im) (-2 / greenLogNormSq κ (Q t) b) D t := by
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hQ.fst
  simpa only [Function.comp_def, Complex.imCLM_apply,
    (physicalLogLoewnerField_components κ (Q t) b).2.1] using hi

lemma log_ode_clock_derivative {Q : ℝ → ℂ × ℝ} {D : Set ℝ} {t κ b : ℝ}
    (η₀ : ℝ)
    (hQ : HasDerivWithinAt Q (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)) D t) :
    HasDerivWithinAt (fun s => logRadiusClock η₀ (Q s))
      (logClockRate κ (Q t) b) D t := by
  have hs : HasDerivWithinAt (fun s => (Q s).2)
      (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)).2 D t := hQ.snd
  have hd : HasDerivWithinAt (fun s => η₀ - (Q s).1.im + (Q s).2)
      (-(-2 / greenLogNormSq κ (Q t) b) +
        (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)).2) D t :=
    ((log_ode_im_derivative hQ).const_sub η₀).add hs
  have he : -(-2 / greenLogNormSq κ (Q t) b) +
      (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)).2 = logClockRate κ (Q t) b := by
    rw [(physicalLogLoewnerField_components κ (Q t) b).2.2]
    unfold logClockRate
    have hN := (greenLogNormSq_pos κ (Q t) b).ne'
    field_simp
    unfold greenLogNormSq
    ring
  simpa only [he, logRadiusClock, Pi.add_apply] using hd

lemma log_height_clock_derivative_nonneg
    (κ ε : ℝ) (hε : 0 < ε) (q : ℂ × ℝ) (b : ℝ)
    (ha : ε ≤ logAngleSq κ q b) :
    0 ≤ -2 / greenLogNormSq κ q b + logClockRate κ q b / (2 * ε) := by
  have hN := greenLogNormSq_pos κ q b
  have h1 : 1 ≤ logAngleSq κ q b / ε := (le_div_iff₀ hε).mpr (by simpa using ha)
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / greenLogNormSq κ q b by positivity)
  have he : logClockRate κ q b / (2 * ε) =
      (2 / greenLogNormSq κ q b) * (logAngleSq κ q b / ε) := by
    unfold logClockRate logAngleSq
    field_simp
    ring
  rw [he, neg_div]
  simpa only [mul_one, sub_eq_add_neg, add_comm] using sub_nonneg.mpr h2

lemma log_clock_rate_lower (κ ε η₀ : ℝ) (hε : 0 < ε) (q : ℂ × ℝ) (b : ℝ)
    (ha : ε ≤ logAngleSq κ q b) (hi : q.1.im ≤ η₀) :
    4 * ε ^ 2 / Real.exp (2 * η₀) ≤ logClockRate κ q b := by
  rw [logClockRate_angle]
  have hs : ε ^ 2 ≤ logAngleSq κ q b ^ 2 := sq_le_sq₀ hε.le (logAngleSq_pos κ q b).le |>.mpr ha
  have he : Real.exp (2 * q.1.im) ≤ Real.exp (2 * η₀) :=
    Real.exp_le_exp.mpr (by linarith)
  exact div_le_div₀ (by positivity) (by nlinarith) (Real.exp_pos _) he

 

theorem log_loewner_height_clock_bounds
    {Q : ℝ → ℂ × ℝ} {B : ℝ → ℝ} {κ T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hQ0 : (Q 0).2 = 0)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (physicalLogLoewnerField (Real.sqrt κ * B t) (Q t)) (Icc 0 T) t)
    (hangle : ∀ t ∈ Icc 0 T, ε ≤ logAngleSq κ (Q t) (B t)) :
    (Q T).1.im ≤ (Q 0).1.im ∧
    (Q 0).1.im - logRadiusClock (Q 0).1.im (Q T) / (2 * ε) ≤ (Q T).1.im ∧
    (4 * ε ^ 2 / Real.exp (2 * (Q 0).1.im)) * T ≤ logRadiusClock (Q 0).1.im (Q T) := by
  let η₀ := (Q 0).1.im
  let c := 4 * ε ^ 2 / Real.exp (2 * η₀)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousWithinAt
  have hi : AntitoneOn (fun t => (Q t).1.im) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hQc))
      (fun t ht => (log_ode_im_derivative (hQ t (interior_subset ht))).mono interior_subset)
    intro t ht
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (greenLogNormSq_pos κ (Q t) (B t)).le
  have hib (t : ℝ) (ht : t ∈ Icc 0 T) : (Q t).1.im ≤ η₀ := hi h0 ht ht.1
  have hS0 : logRadiusClock η₀ (Q 0) = 0 := by simp [logRadiusClock, η₀, hQ0]
  have hSc : ContinuousOn (fun t => logRadiusClock η₀ (Q t)) (Icc 0 T) :=
    (continuous_logRadiusClock η₀).comp_continuousOn hQc
  have hlo : MonotoneOn (fun t => (Q t).1.im +
      logRadiusClock η₀ (Q t) / (2 * ε)) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      ((Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hQc)).add
        (hSc.div_const _))
      (fun t ht => ((log_ode_im_derivative (hQ t (interior_subset ht))).add
        ((log_ode_clock_derivative η₀ (hQ t (interior_subset ht))).div_const _)).mono interior_subset)
    intro t ht
    exact log_height_clock_derivative_nonneg κ ε hε (Q t) (B t) (hangle t (interior_subset ht))
  have hrate : MonotoneOn (fun t => logRadiusClock η₀ (Q t) - c * t) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (hSc.sub (continuous_const.mul continuous_id).continuousOn)
      (fun t ht => ((log_ode_clock_derivative η₀ (hQ t (interior_subset ht))).sub
        ((hasDerivWithinAt_id t (Icc 0 T)).const_mul c)).mono interior_subset)
    intro t ht
    have hb := log_clock_rate_lower κ ε η₀ hε (Q t) (B t)
      (hangle t (interior_subset ht)) (hib t (interior_subset ht))
    change 0 ≤ logClockRate κ (Q t) (B t) - c * 1
    simpa only [mul_one] using sub_nonneg.mpr hb
  refine ⟨hib T hTT, ?_, ?_⟩
  · have hh := hlo h0 hTT hT
    dsimp only at hh
    rw [hS0, zero_div, add_zero] at hh
    linarith
  · have hh := hrate h0 hTT hT
    dsimp only at hh
    rw [hS0, mul_zero, sub_zero] at hh
    linarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure ClippedLogSolution {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) where
  L : ℝ≥0
  Q : ℝ → Ω → ℂ × ℝ
  measurable : Measurable (fun p : ℝ × Ω => Q p.1 p.2)
  lipschitz : ∀ ω, LipschitzWith L (fun t => Q t ω)
  initial : ∀ ω, Q 0 ω = q₀
  derivative : ∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
    (clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (Q t ω))
    (Ici 0) t
  adapted : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun t : ℝ≥0 => Q t)

lemma exists_clippedLogSolution
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) :
    Nonempty (ClippedLogSolution B hm κ lo hi hle q₀) := by
  let U (t : ℝ≥0) (ω : Ω) := Real.sqrt κ * B t ω
  have hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2) := hBm.const_mul _
  have hUc (ω : Ω) : Continuous (fun t => U t ω) := (hBc ω).const_mul _
  obtain ⟨L, Q, hQm, hQl, hQ0, hQd, hQaU⟩ :=
    clipped_log_loewner_global_adapted_solution U hUm hUc lo hi hle q₀
  have hBa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  refine ⟨⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩⟩
  intro t
  apply (hQaU t).mono _ le_rfl
  change (⨆ j ≤ t, MeasurableSpace.comap (U j) (borel ℝ)) ≤ _
  refine iSup₂_le fun j hj => ?_
  exact ((hBa.measurable_le hj).const_mul (Real.sqrt κ)).comap_le

lemma compact_green_drift_zero
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (lo hi : ℝ) (hle : lo ≤ hi)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (q : ℂ × ℝ) (x : ℝ)
    (hφD : fderiv ℝ φ (q, x) =
      fderiv ℝ (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) (q, x))
    (hφ2 : iteratedDeriv 2 (fun y => φ (q, y)) x =
      iteratedDeriv 2 (greenLogDensity κ q) x)
    (hq : q.1.im ∈ Icc lo hi) :
    fderiv ℝ φ (q, x)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * x) q, 0) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (fun y => φ (q, y)) x = 0 := by
  rw [hφD, hφ2, greenLogDensity_pair_directional,
    clippedLogLoewnerField_eq_physical lo hi hle _ _ hq]
  exact green_physical_generator_zero κ hκ hκ8 q x

 

theorem ClippedLogSolution.stopped_green
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        greenLogDensity κ q₀ 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_green_field κ R hR
  obtain ⟨L₀, K₀, hL₀, _⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) :=
    clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair : Measurable (fun p : ℝ × Ω =>
      (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)) := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hzero (ω : Ω) (u : ℝ) (hu : 0 ≤ u) (hut : u < (τ ω : ℝ)) :
      brownianFieldDrift B F a u ω = 0 := by
    have ht : u.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr hut.le
    obtain ⟨hball, hlo, hhi⟩ := hinside ω u.toNNReal ht
    change fderiv ℝ φ (c.Q (u.toNNReal : ℝ) ω, B u.toNNReal ω)
      (V (u.toNNReal : ℝ) ω, 0) + _ = 0
    dsimp only [V]
    rw [Real.toNNReal_coe]
    exact compact_green_drift_zero κ hκ hκ8 lo hi hle φ _ _
      (hφD _ _ hball) (hφ2 _ _ hball) ⟨hlo, hhi⟩
  have hopt := brownian_time_field_optional hB hm hBm hBc K F a hfield τ hτ T hb hzero
  have hτm := stopping_time_measurable_nnreal hτ
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hQmτ : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hfm : Measurable (fun ω => F (τ ω) ω (B (τ ω) ω)) :=
    hφ.continuous.measurable.comp (hQmτ.prodMk hBmτ)
  have hfi : Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using
        hfield.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)
  have hfeq (ω : Ω) : F (τ ω) ω (B (τ ω) ω) =
      greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  calc
    _ = ∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hfeq ω).symm)
    _ = ∫ ω, F 0 ω (B 0 ω) ∂P := hopt
    _ = ∫ _, greenLogDensity κ q₀ 0 ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
      change φ (c.Q 0 ω, B 0 ω) = _
      have hh : ‖(c.Q 0 ω, B 0 ω)‖ ≤ R := by
        simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
      rw [hφeq _ _ hh, c.initial ω, hB0]
    _ = greenLogDensity κ q₀ 0 := by simp

end SLEExactGauge
end

 
end

end OAI
