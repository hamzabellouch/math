import Mathlib
import OAI.Geometry.BallPacking.Annuli.CircleHandleBump

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def annularMean (a : ℝ) (B : P × Plane → ℝ) (p : P) : ℝ :=
  ∫ t in (0:ℝ)..1, B (p,(a,t))

theorem annularMean_smooth {V : Set P} {I : Set ℝ} (hV : IsOpen V)
    {a : ℝ} (ha : a ∈ I) {B : P × Plane → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) :
    ContDiffOn ℝ ∞ (annularMean a B) V := by
  have hf : ContDiffOn ℝ ∞ (fun q : P × ℝ => B (q.1,(a,q.2))) (V ×ˢ univ) :=
    hB.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn
      (fun _ hq => ⟨hq.1,ha,hq.2⟩)
  exact (contDiffOn_parameter_segment_integral hV isOpen_univ convex_univ
    (0:ℝ) (mem_univ _) hf).comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun _ hp => ⟨hp,mem_univ (1:ℝ)⟩)

def annularNormalized (a : ℝ) (B : P × Plane → ℝ) (β : ℝ → ℝ)
    (q : P × Plane) : ℝ := B q-annularMean a B q.1*β q.2.2

theorem annularNormalized_smooth {V : Set P} {I : Set ℝ} (hV : IsOpen V)
    {a : ℝ} (ha : a ∈ I) {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) (hβ : ContDiff ℝ ∞ β) :
    ContDiffOn ℝ ∞ (annularNormalized a B β) (V ×ˢ (I ×ˢ univ)) :=
  hB.sub (((annularMean_smooth hV ha hB).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)).mul (hβ.comp (contDiff_snd.comp contDiff_snd)).contDiffOn)

omit [FiniteDimensional ℝ P] in

theorem annularNormalized_fderiv_radial {V : Set P} {I : Set ℝ}
    (hI : IsOpen I) {a : ℝ} {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) (hβ : ContDiff ℝ ∞ β)
    {p : P} (hp : p ∈ V) {q : Plane} (hq : q.1 ∈ I) :
    fderiv ℝ (fun z => annularNormalized a B β (p,z)) q (1,0) =
      fderiv ℝ (fun z => B (p,z)) q (1,0) := by
  have hB' : ContDiffOn ℝ ∞ (fun z => B (p,z)) (I ×ˢ univ) :=
    hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
  have hdB := ((hB'.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hq,mem_univ _⟩)).differentiableAt
    (by simp)).hasFDerivAt
  have hdβ := ((hβ.comp contDiff_snd).differentiable (by simp) q).hasFDerivAt
  have hβ0 : fderiv ℝ (β ∘ (Prod.snd : Plane → ℝ)) q (1,0) = 0 := by
    rw [fderiv_comp q (hβ.differentiable (by simp) q.2) differentiableAt_snd]
    rw [(hasFDerivAt_snd (𝕜 := ℝ) (p := q)).fderiv]
    simp
  have hd := hdB.sub (hdβ.const_mul (annularMean a B p))
  change fderiv ℝ ((fun z => B (p,z)) - fun z => annularMean a B p * (β ∘ Prod.snd) z) q (1,0) = _
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,hβ0,smul_zero,sub_zero]

omit [FiniteDimensional ℝ P] in

theorem annularNormalized_zero_period {V : Set P} {I : Set ℝ}
    {a : ℝ} (ha : a ∈ I) {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) (hβ : ContDiff ℝ ∞ β)
    (hβint : (∫ t in (0:ℝ)..1, β t) = 1) {p : P} (hp : p ∈ V) :
    (∫ t in (0:ℝ)..1, annularNormalized a B β (p,(a,t))) = 0 := by
  have hBt : Continuous (fun t : ℝ => B (p,(a,t))) := by
    apply continuousOn_univ.mp
    exact hB.continuousOn.comp (continuous_const.prodMk
      (continuous_const.prodMk continuous_id)).continuousOn
        (fun _ ht => ⟨hp,ha,ht⟩)
  simp only [annularNormalized]
  rw [intervalIntegral.integral_sub (hBt.intervalIntegrable 0 1)
    ((hβ.continuous.const_mul _).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul,hβint,mul_one]
  exact sub_self _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem annularNormalized_periodic {V : Set P} {I : Set ℝ}
    {a : ℝ} {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hpB : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => B (p,(s,t))) 1)
    (hpβ : Periodic β 1) {p : P} (hp : p ∈ V) {s : ℝ} (hs : s ∈ I) :
    Periodic (fun t => annularNormalized a B β (p,(s,t))) 1 := by
  intro t
  dsimp only [annularNormalized]
  have h := hpB p hp s hs t
  dsimp only at h
  rw [h,hpβ t]


end

section
open scoped ContDiff Topology
open Set Function Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_local_identity {U : Set E} {x : E} (hU : U ∈ 𝓝 x) :
    ∃ r : E → E, ContDiff ℝ ∞ r ∧ (∀ y, r y ∈ U) ∧ r =ᶠ[𝓝 x] id := by
  obtain ⟨a,ha,haU⟩ := Metric.mem_nhds_iff.mp hU
  let χ : ContDiffBump x := ⟨a/2,a,by positivity,by linarith⟩
  let r : E → E := fun y => x + χ y • (y-x)
  refine ⟨r,contDiff_const.add (χ.contDiff.smul (contDiff_id.sub contDiff_const)),?_,?_⟩
  · intro y
    apply haU
    by_cases hy : y ∈ ball x a
    · rw [mem_ball_iff_norm]
      change ‖x + χ y • (y-x) - x‖ < a
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg χ.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans_lt (mem_ball_iff_norm.mp hy)
    · have hz : χ y = 0 := χ.zero_of_le_dist (not_lt.mp hy)
      simp only [r,hz,zero_smul,add_zero]
      exact mem_ball_self ha
  · filter_upwards [χ.eventuallyEq_one] with y hy
    change x + χ y • (y-x) = y
    rw [hy,Pi.one_apply,one_smul,add_sub_cancel]


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiffOn_fixed_integral {U : Set P} (hU : IsOpen U) {f : ℝ × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p => ∫ s in (0:ℝ)..1, f (s,p)) U := by
  intro p hp
  obtain ⟨r,hr,hrU,hre⟩ := exists_smooth_local_identity (hU.mem_nhds hp)
  have hg : ContDiff ℝ ∞ (fun q : ℝ × P => f (q.1,r q.2)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact (hf.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hrU q.2⟩)).comp q
      (contDiff_fst.prodMk (hr.comp contDiff_snd)).contDiffAt
  apply ((contDiff_fixed_integral hg).contDiffAt.congr_of_eventuallyEq _).contDiffWithinAt
  filter_upwards [hre] with q hq
  change (∫ s in (0:ℝ)..1, f (s,q)) = ∫ s in (0:ℝ)..1, f (s,r q)
  rw [show r q = q from hq]

omit [CompleteSpace F] in

theorem hasFDerivAt_fixed_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f) (x : P) :
    HasFDerivAt (fun p => ∫ s in (0:ℝ)..1, f (s,p))
      (∫ s in (0:ℝ)..1, fderiv ℝ (fun p => f (s,p)) x) x := by
  let D : ℝ × P → P →L[ℝ] F := fun q => (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ P)
  have hD : Continuous D := (hf.fderiv_right (m := ∞) (by simp)).continuous.clm_comp continuous_const
  have hd (s : ℝ) (p : P) : HasFDerivAt (fun q => f (s,q)) (D (s,p)) p := by
    convert! ((hf.differentiable (by simp) (s,p)).hasFDerivAt.comp p
      ((hasFDerivAt_const s p).prodMk (hasFDerivAt_id p))) using 1
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x (1:ℝ))).exists_bound_of_continuousOn hD.continuousOn
  have hi : HasFDerivAt (fun p => ∫ s in (0:ℝ)..1, f (s,p))
      (∫ s in (0:ℝ)..1, D (s,x)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (s := Metric.closedBall x 1) (bound := fun _ => C) (Metric.closedBall_mem_nhds x zero_lt_one)
    · exact Filter.Eventually.of_forall fun p =>
        (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    · exact (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      intro p hp
      rw [uIoc_of_le zero_le_one] at hs
      exact hC (s,p) ⟨⟨hs.1.le,hs.2⟩,hp⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s p _ => hd s p
  convert! hi using 1
  apply intervalIntegral.integral_congr
  intro s _
  exact (hd s x).fderiv

omit [CompleteSpace F] in

theorem hasFDerivAt_fixed_integral_on {U : Set P} (hU : IsOpen U) {f : ℝ × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) {x : P} (hx : x ∈ U) :
    HasFDerivAt (fun p => ∫ s in (0:ℝ)..1, f (s,p))
      (∫ s in (0:ℝ)..1, fderiv ℝ (fun p => f (s,p)) x) x := by
  obtain ⟨r,hr,hrU,hre⟩ := exists_smooth_local_identity (hU.mem_nhds hx)
  have hg : ContDiff ℝ ∞ (fun q : ℝ × P => f (q.1,r q.2)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact (hf.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hrU q.2⟩)).comp q
      (contDiff_fst.prodMk (hr.comp contDiff_snd)).contDiffAt
  have hd := hasFDerivAt_fixed_integral hg x
  have hi : (fun p => ∫ s in (0:ℝ)..1, f (s,p)) =ᶠ[𝓝 x]
      (fun p => ∫ s in (0:ℝ)..1, f (s,r p)) := by
    filter_upwards [hre] with p hp
    rw [show r p = p from hp]
  have hD (s : ℝ) : fderiv ℝ (fun p => f (s,p)) x = fderiv ℝ (fun p => f (s,r p)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hre] with p hp
    rw [show r p = p from hp]
  simpa only [hD] using hd.congr_of_eventuallyEq hi


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_interval_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (x : P) : HasFDerivAt (fun p => ∫ s in a..b, f (s,p))
      (∫ s in a..b, fderiv ℝ (fun p => f (s,p)) x) x := by
  let D : ℝ × P → P →L[ℝ] F := fun q => (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ P)
  have hD : Continuous D := (hf.fderiv_right (m := ∞) (by simp)).continuous.clm_comp continuous_const
  have hd (s : ℝ) (p : P) : HasFDerivAt (fun q => f (s,q)) (D (s,p)) p := by
    convert! ((hf.differentiable (by simp) (s,p)).hasFDerivAt.comp p
      ((hasFDerivAt_const s p).prodMk (hasFDerivAt_id p))) using 1
  obtain ⟨C,hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall x (1:ℝ))).exists_bound_of_continuousOn hD.continuousOn
  have hi : HasFDerivAt (fun p => ∫ s in a..b, f (s,p)) (∫ s in a..b, D (s,x)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (s := Metric.closedBall x 1) (bound := fun _ => C) (Metric.closedBall_mem_nhds x zero_lt_one)
    · exact Filter.Eventually.of_forall fun p =>
        (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
    · exact (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      intro p hp
      exact hC (s,p) ⟨uIoc_subset_uIcc hs,hp⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s p _ => hd s p
  convert! hi using 1
  apply intervalIntegral.integral_congr
  intro s _
  exact (hd s x).fderiv

theorem hasFDerivAt_interval_integral_local {f : ℝ × P → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ℝ) (x : P)
    (hseg : ∀ s ∈ uIcc a b, (s,x) ∈ U) :
    HasFDerivAt (fun p => ∫ s in a..b, f (s,p))
      (∫ s in a..b, fderiv ℝ (fun p => f (s,p)) x) x := by
  let K : Set (ℝ × P) := (fun s : ℝ => (s,x)) '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image (continuous_id.prodMk continuous_const)
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK hU
    (by rintro _ ⟨s,hs,rfl⟩; exact hseg s hs) hf
  let g : ℝ × P → F := fun q => χ q • f q
  have hnear : ∀ᶠ p in 𝓝 x, ∀ s ∈ uIcc a b, g (s,p) = f (s,p) := by
    apply isCompact_uIcc.eventually_forall_of_forall_eventually
    intro s hs
    have hk : (s,x) ∈ K := ⟨s,hs,rfl⟩
    exact ((continuous_swap : Continuous (Prod.swap : P × ℝ → ℝ × P)).continuousAt (x := (x,s))).eventually
      (he.filter_mono (nhds_le_nhdsSet hk))
  have hD (s : ℝ) (hs : s ∈ uIcc a b) :
      fderiv ℝ (fun p => g (s,p)) x = fderiv ℝ (fun p => f (s,p)) x := by
    exact Filter.EventuallyEq.fderiv_eq (hnear.mono fun _ hp => hp s hs)
  have hi := hasFDerivAt_interval_integral hg a b x
  apply hi.congr_of_eventuallyEq ?_ |>.congr_fderiv ?_
  · filter_upwards [hnear] with p hp
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hp s hs).symm
  · apply intervalIntegral.integral_congr
    exact hD

theorem hasDerivAt_interval_integral_local {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b x : ℝ)
    (hseg : ∀ s ∈ uIcc a b, (s,x) ∈ U) :
    HasDerivAt (fun p => ∫ s in a..b, f (s,p))
      (∫ s in a..b, deriv (fun p => f (s,p)) x) x := by
  have hd := (hasFDerivAt_interval_integral_local hU hf a b x hseg).hasDerivAt
  have he (s : ℝ) : fderiv ℝ (fun p => f (s,p)) x =
      deriv (fun p => f (s,p)) x • (ContinuousLinearMap.id ℝ ℝ) := by
    ext
    simp only [← toSpanSingleton_deriv,ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    ring
  simpa only [he,intervalIntegral.integral_smul_const,smul_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,mul_one] using hd

theorem hasDerivAt_primitive_on {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {f : ℝ → ℝ} (hf : ContinuousOn f I) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    HasDerivAt (fun t => ∫ s in a..t, f s) (f b) b := by
  have hseg : uIcc a b ⊆ I := by
    rw [← segment_eq_uIcc]
    exact hc.segment_subset ha hb
  exact intervalIntegral.integral_hasDerivAt_right
    ((hf.mono hseg).intervalIntegrable) (hf.stronglyMeasurableAtFilter hI b hb)
    (hf.continuousAt (hI.mem_nhds hb))


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

theorem stripPrimitive_hasDerivAt_second {I : Set ℝ} {a : ℝ} {A B : Plane → ℝ}
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ)) {s : ℝ} (hs : s ∈ I) (t : ℝ) :
    HasDerivAt (fun u => stripPrimitive a A B (s,u)) (B (s,t)) t := by
  have hBt : ContDiff ℝ ∞ (fun u : ℝ => B (s,u)) := by
    apply contDiffOn_univ.mp
    exact hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨hs,mem_univ _⟩)
  have hd := intervalIntegral.integral_hasDerivAt_right (hBt.continuous.intervalIntegrable 0 t)
    hBt.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hBt.continuous.continuousAt
  exact hd.const_add (∫ x in a..s, A (x,0))

theorem stripPrimitive_hasDerivAt_first {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    {s : ℝ} (hs : s ∈ I) (t : ℝ) :
    HasDerivAt (fun u => stripPrimitive a A B (u,t)) (A (s,t)) s := by
  have hA0 : ContinuousOn (fun u : ℝ => A (u,0)) I :=
    hA.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu => ⟨hu,mem_univ _⟩)
  have hd₀ := hasDerivAt_primitive_on hI hc hA0 ha hs
  have hBf : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => B (q.2,q.1)) (univ ×ˢ I) :=
    hB.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => ⟨hq.2,hq.1⟩)
  have hd₁ := hasDerivAt_interval_integral_local (isOpen_univ.prod hI) hBf 0 t s
    (fun _ _ => ⟨mem_univ _,hs⟩)
  have hAt : ContDiff ℝ ∞ (fun u : ℝ => A (s,u)) := by
    apply contDiffOn_univ.mp
    exact hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨hs,mem_univ _⟩)
  have he (u : ℝ) : deriv (fun x => B (x,u)) s = deriv (fun x => A (s,x)) u := by
    have hdB := ((hB.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hs,mem_univ u⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s u))
    have hdA := ((hA.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hs,mem_univ u⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt u
        ((hasDerivAt_const u s).prodMk (hasDerivAt_id u))
    dsimp only [Function.comp_def,id_eq] at hdB hdA
    rw [hdB.deriv,hdA.deriv,hclosed s hs u]
  have hi : (∫ u in (0:ℝ)..t, deriv (fun x => B (x,u)) s) = A (s,t)-A (s,0) := by
    simp only [he]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun u _ => hAt.differentiable (by simp) u)
      ((hAt.continuous_deriv (by simp)).intervalIntegrable 0 t)
  have hd := hd₀.add hd₁
  rw [hi] at hd
  exact hd.congr_deriv (by ring)

theorem stripPrimitive_fderiv {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    {q : Plane} (hq : q.1 ∈ I) (v : Plane) :
    fderiv ℝ (stripPrimitive a A B) q v = A q*v.1+B q*v.2 := by
  have hd : DifferentiableAt ℝ (stripPrimitive a A B) q :=
    ((stripPrimitive_smooth hI hc ha hA hB).contDiffAt
    ((hI.prod isOpen_univ).mem_nhds ⟨hq,mem_univ q.2⟩)).differentiableAt (by simp)
  have h₁ : fderiv ℝ (stripPrimitive a A B) q (1,0) = A q := by
    have hd' := hd.hasFDerivAt.comp_hasDerivAt q.1
        ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
    dsimp only [Function.comp_def,id_eq] at hd'
    exact hd'.unique (stripPrimitive_hasDerivAt_first hI hc ha hA hB hclosed hq q.2)
  have h₂ : fderiv ℝ (stripPrimitive a A B) q (0,1) = B q := by
    have hd' := hd.hasFDerivAt.comp_hasDerivAt q.2
        ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
    dsimp only [Function.comp_def,id_eq] at hd'
    exact hd'.unique (stripPrimitive_hasDerivAt_second (a := a) (A := A) hB hq q.2)
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add,map_smul,h₁,h₂,smul_eq_mul]
  ring




theorem strip_period_eq {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    (hpA : ∀ s ∈ I, Periodic (fun t => A (s,t)) 1) {s : ℝ} (hs : s ∈ I) :
    (∫ t in (0:ℝ)..1, B (s,t)) = ∫ t in (0:ℝ)..1, B (a,t) := by
  let c : ℝ → ℝ := fun s => ∫ t in (0:ℝ)..1, B (s,t)
  have he : (fun s => stripPrimitive a A B (s,1)-stripPrimitive a A B (s,0)) = c := by
    funext s
    simp only [stripPrimitive,intervalIntegral.integral_same,add_zero,c,add_sub_cancel_left]
  have hd (s : ℝ) (hs : s ∈ I) : HasDerivAt c 0 s := by
    have h := (stripPrimitive_hasDerivAt_first hI hc ha hA hB hclosed hs 1).sub
      (stripPrimitive_hasDerivAt_first hI hc ha hA hB hclosed hs 0)
    change HasDerivAt (fun u => stripPrimitive a A B (u,1)-stripPrimitive a A B (u,0)) _ s at h
    rw [he] at h
    have hp := hpA s hs 0
    simp only [zero_add] at hp
    simpa only [hp,sub_self] using h
  exact hI.is_const_of_deriv_eq_zero hc.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) hs ha

theorem stripPrimitive_periodic {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    (hpA : ∀ s ∈ I, Periodic (fun t => A (s,t)) 1)
    (hpB : ∀ s ∈ I, Periodic (fun t => B (s,t)) 1)
    (hz : (∫ t in (0:ℝ)..1, B (a,t)) = 0) {s : ℝ} (hs : s ∈ I) :
    Periodic (fun t => stripPrimitive a A B (s,t)) 1 := by
  have hc0 := (strip_period_eq hI hc ha hA hB hclosed hpA hs).trans hz
  have hBt : Continuous (fun t : ℝ => B (s,t)) := by
    apply continuousOn_univ.mp
    exact hB.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hs,mem_univ _⟩)
  intro t
  dsimp only [stripPrimitive]
  rw [(hpB s hs).intervalIntegral_add_eq_add 0 t (fun a b => hBt.intervalIntegrable a b)]
  simp only [zero_add,hc0,add_zero]


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def normalizedAnnularPrimitive (a : ℝ) (A B : P × Plane → ℝ)
    (β : ℝ → ℝ) : P × Plane → ℝ :=
  annularPrimitive a A (annularNormalized a B β)

theorem annular_normalization {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1, β t) = 1)
    (hpA : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => B (p,(s,t))) 1)
    (hclosed : ∀ p ∈ V, ∀ s ∈ I, ∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1) =
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0)) :
    ContDiffOn ℝ ∞ (normalizedAnnularPrimitive a A B β) (V ×ˢ (I ×ˢ univ)) ∧
      (∀ p ∈ V, ∀ s ∈ I,
        Periodic (fun t => normalizedAnnularPrimitive a A B β (p,(s,t))) 1) ∧
      (∀ p ∈ V, ∀ q : Plane, q.1 ∈ I → ∀ v : Plane,
        fderiv ℝ (fun z => normalizedAnnularPrimitive a A B β (p,z)) q v =
          A (p,q)*v.1+(B (p,q)-annularMean a B p*β q.2)*v.2) := by
  have hBn := annularNormalized_smooth hV ha hB hβ
  refine ⟨annularPrimitive_smooth hV hI hc ha hA hBn,?_,?_⟩
  · intro p hp s hs
    have hAp : ContDiffOn ℝ ∞ (fun z => A (p,z)) (I ×ˢ univ) :=
      hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    have hBp : ContDiffOn ℝ ∞ (fun z => annularNormalized a B β (p,z)) (I ×ˢ univ) :=
      hBn.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    apply stripPrimitive_periodic hI hc ha hAp hBp ?_ (hpA p hp) ?_ ?_ hs
    · intro u hu t
      rw [annularNormalized_fderiv_radial hI hB hβ hp hu]
      exact hclosed p hp u hu t
    · intro u hu
      exact annularNormalized_periodic hpB hpβ hp hu
    · exact annularNormalized_zero_period ha hB hβ hβint hp
  · intro p hp q hq v
    have hAp : ContDiffOn ℝ ∞ (fun z => A (p,z)) (I ×ˢ univ) :=
      hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    have hBp : ContDiffOn ℝ ∞ (fun z => annularNormalized a B β (p,z)) (I ×ˢ univ) :=
      hBn.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    exact stripPrimitive_fderiv hI hc ha hAp hBp
      (fun u hu t => by
        rw [annularNormalized_fderiv_radial hI hB hβ hp hu]
        exact hclosed p hp u hu t) hq v


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def annularScalarDescent (F : P × Plane → ℝ) : (P × ℝ) × Circle → ℝ :=
  circleFamilyDescent (fun q => F (q.1.1,(q.1.2,q.2)))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem annularScalarDescent_turn {F : P × Plane → ℝ} {p : P} {s : ℝ}
    (hp : Periodic (fun t => F (p,(s,t))) 1) (t : ℝ) :
    annularScalarDescent F ((p,s),circleTurn t)=F (p,(s,t)) :=
  circleFamilyDescent_turn hp t

theorem annularScalarDescent_smoothOn {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hp : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => F (p,(s,t))) 1) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent F) ((V ×ˢ I) ×ˢ univ) := by
  apply circleFamilyDescent_smoothOn (hV.prod hI)
  · apply hF.comp
      ((contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)).contDiffOn)
    intro q hq
    exact ⟨hq.1.1,hq.1.2,hq.2⟩
  · intro q hq
    exact hp q.1 hq.1 q.2 hq.2

def parameterAnnulusCover (p : P) (q : Plane) : (P × ℝ) × Circle :=
  ((p,q.1),circleTurn q.2)

theorem parameterAnnulusCover_smooth (p : P) :
    ContMDiff 𝓘(ℝ,Plane) ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) ∞
      (parameterAnnulusCover p) :=
  ((contDiff_const.prodMk (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Plane → ℝ))).contMDiff).prodMk
    (circleTurn_smooth.comp
      (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Plane → ℝ)).contMDiff)

theorem annularScalarDescent_pullback {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hp : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => F (p,(s,t))) 1)
    {p : P} (hpV : p∈V) {q : Plane} (hq : q.1∈I) (v : Plane) :
    mfderiv ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ)
      (annularScalarDescent F) (parameterAnnulusCover p q)
      (mfderiv 𝓘(ℝ,Plane) ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel))
        (parameterAnnulusCover p) q v)=
      fderiv ℝ (fun z => F (p,z)) q v := by
  have hs := (annularScalarDescent_smoothOn hV hI hF hp).contMDiffAt
    (((hV.prod hI).prod isOpen_univ).mem_nhds (show parameterAnnulusCover p q∈_
      from ⟨⟨hpV,hq⟩,mem_univ _⟩))
  have he : (annularScalarDescent F ∘ parameterAnnulusCover p) =ᶠ[𝓝 q]
      (fun z => F (p,z)) := by
    filter_upwards [(hI.prod isOpen_univ).mem_nhds (show q∈I ×ˢ univ
      from ⟨hq,mem_univ _⟩)] with z hz
    exact annularScalarDescent_turn (hp p hpV z.1 hz.1) z.2
  have hd := mfderiv_comp q (hs.mdifferentiableAt (by simp))
    ((parameterAnnulusCover_smooth p).mdifferentiableAt (by simp))
  have hv := congrArg (fun L : Plane →L[ℝ] ℝ => L v) hd
  rw [mfderiv_eq_fderiv] at hv
  rw [he.fderiv_eq] at hv
  exact hv.symm

variable [FiniteDimensional ℝ P]

theorem exists_normalized_annular_scalar {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1, β t)=1)
    (hpA : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => B (p,(s,t))) 1)
    (hclosed : ∀ p ∈ V, ∀ s ∈ I, ∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0)) :
    ∃ F : (P × ℝ) × Circle → ℝ,
      ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
        F ((V ×ˢ I) ×ˢ univ) ∧
      (∀ p ∈ V, ∀ q : Plane, q.1∈I → ∀ v : Plane,
        mfderiv ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ)
          F (parameterAnnulusCover p q)
          (mfderiv 𝓘(ℝ,Plane) ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel))
            (parameterAnnulusCover p) q v)=
        A (p,q)*v.1+(B (p,q)-annularMean a B p*β q.2)*v.2) := by
  obtain ⟨hF,hFp,hFd⟩ := annular_normalization hV hI hc ha hA hB hβ hpβ hβint hpA hpB hclosed
  refine ⟨annularScalarDescent (normalizedAnnularPrimitive a A B β),
    annularScalarDescent_smoothOn hV hI hF hFp,?_⟩
  intro p hp q hq v
  rw [annularScalarDescent_pullback hV hI hF hFp hp hq]
  exact hFd p hp q hq v



end PackingSufficiencySupport.Hamiltonian
end

end OAI
