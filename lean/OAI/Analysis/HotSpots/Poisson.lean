import OAI.Analysis.HotSpots.Trace
import OAI.Analysis.HotSpots.BoundaryKernel

namespace OAI

section DouglasLipschitzBase
noncomputable section
section DouglasBoundaryClassCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma planeSeries_boundary (f : C(AddCircle τ, ℂ))
    (h : Summable (fun m => ‖fourierCoeff f m‖)) (s : AddCircle τ) :
    planeSeries (fourierCoeff f) (complexIso s.toCircle) = (f s).re := by
  simp only [planeSeries,LinearIsometryEquiv.symm_apply_apply,harmonicSeries_fourier_boundary f h]




theorem harmonicSeries_boundary_class (f : C(AddCircle τ, ℂ))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖fourierCoeff f m‖))
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hb : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (f s).re) :
    (planeSeries_gradient (summable_norm_of_firstMoment h1) h1).toH1 -
      (smooth_memH1 (by norm_num : (1:ℝ) < 2) hφ.contDiffOn).toH1 ∈ h10Submodule (show IsOpen disk from isOpen_ball) := by
  let a := fourierCoeff f
  have h0 := summable_norm_of_firstMoment h1
  let hu := planeSeries_gradient h0 h1
  let hv := smooth_memH1 (by norm_num : (1:ℝ) < 2) hφ.contDiffOn
  have hs := planeSeries_contDiffOn h0
  have hsub : HasH1Gradient disk (planeSeries a - φ) (gradient (planeSeries a - φ)) := by
    apply (hu.sub hv).congr (ae_of_all _ (fun _ => rfl))
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [gradient,Pi.sub_apply]
    rw [fderiv_sub (((hs x hx).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      (hφ.differentiable (by simp) x),map_sub]
  have hhc : ContinuousOn (planeSeries a - φ) (closure disk) := by
    have hc := (planeSeries_continuousOn h0).sub hφ.continuous.continuousOn
    simpa only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0)] using hc
  have hz : ∀ x ∈ frontier disk, (planeSeries a - φ) x = 0 := by
    intro x hx
    have hn : ‖x‖ = 1 := by
      simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_sphere_zero_iff_norm] using hx
    let c : Circle := ⟨complexIso.symm x, by
      change complexIso.symm x ∈ sphere (0:ℂ) 1
      simpa only [mem_sphere_zero_iff_norm,LinearIsometryEquiv.norm_map] using hn⟩
    obtain ⟨s,hs⟩ := (AddCircle.homeomorphCircle (by positivity : τ ≠ 0)).surjective c
    have hsc : (s.toCircle:ℂ) = complexIso.symm x := by
      have he := congrArg (fun c : Circle => (c:ℂ)) hs
      simpa only [AddCircle.homeomorphCircle_apply,c] using he
    have hxc : complexIso s.toCircle = x := by rw [hsc]; exact complexIso.apply_symm_apply x
    rw [← hxc]
    exact sub_eq_zero.mpr ((planeSeries_boundary f h0 s).trans (hb s).symm)
  have hm := interior_smooth_zero_trace_memH10 (Ω:=disk) isOpen_ball (hs.sub hφ.contDiffOn) hhc hsub
    isBounded_ball hz
  have he : hu.toH1 - hv.toH1 = hsub.toH1 := by
    apply H1.value_injective (Ω:=disk) isOpen_ball
    rw [map_sub,H1.value_toH1,H1.value_toH1,H1.value_toH1]
    apply Lp.ext
    filter_upwards [hu.1.coeFn_toLp,hv.1.coeFn_toLp,hsub.1.coeFn_toLp,
      Lp.coeFn_sub (hu.1.toLp _) (hv.1.toLp _)] with x hux hvx hsx hdiff
    rw [hdiff,Pi.sub_apply,hux,hvx,hsx]
    rfl
  exact he.symm ▸ hm



theorem C3_boundary_class (f0 f1 f2 f3 : C(AddCircle τ, ℂ))
    (h01 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f0 t) (f1 t) t)
    (h12 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f1 t) (f2 t) t)
    (h23 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f2 t) (f3 t) t)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hb : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (f0 s).re) :
    let h1 := summable_firstMoment_fourierCoeff f0 f1 f2 f3 h01 h12 h23
    (planeSeries_gradient (summable_norm_of_firstMoment h1) h1).toH1 -
      (smooth_memH1 (by norm_num : (1:ℝ) < 2) hφ.contDiffOn).toH1 ∈ h10Submodule (show IsOpen disk from isOpen_ball) := by
  exact harmonicSeries_boundary_class f0
    (summable_firstMoment_fourierCoeff f0 f1 f2 f3 h01 h12 h23) hφ hb

end StrictHotSpots.Douglas
end DouglasBoundaryClassCombinedLayer

section SubcriticalExtensionCombinedLayer
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)
local instance : NormedSpace ℝ (H10 ho) := (H10.innerProductSpace ho).toNormedSpace
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace

def observe : H1 Ω →L[ℝ] Lp ℝ 2 ν :=
  (Lp.LpToLpOfMeasureLeSMul hC hν).comp H1.value

def solve : Lp ℝ 2 ν →L[ℝ] H10 ho :=
  DirichletOperator.solution (H10.energy ho) (H10.energy_coercive ho hb)
    (H10.weightedValue ho hC hν)

lemma solve_spec (f : Lp ℝ 2 ν) (v : H10 ho) :
    inner ℝ (H10.grad ho (solve ho hb hC hν f)) (H10.grad ho v) =
      inner ℝ f (H10.weightedValue ho hC hν v) := by
  exact DirichletOperator.solution_spec (H10.energy ho) (H10.energy_coercive ho hb)
    (H10.weightedValue ho hC hν) f v

lemma observe_coe (v : H10 ho) : observe hC hν v.val = H10.weightedValue ho hC hν v := rfl
lemma observe_solve (f : Lp ℝ 2 ν) :
    observe hC hν (solve ho hb hC hν f).val = H10.greenOperator ho hb hC hν f := rfl

lemma grad_add_coe (A : H1 Ω) (v : H10 ho) :
    H1.grad (A+v.val) = H1.grad A + H10.grad ho v := H1.grad.map_add A v.val
lemma observe_add_coe (A : H1 Ω) (v : H10 ho) :
    observe hC hν (A+v.val) = observe hC hν A + H10.weightedValue ho hC hν v :=
  (observe hC hν).map_add A v.val


def extension (A : H1 Ω) : H1 Ω := A + (solve ho hb hC hν
  (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A))).val

def Harmonic (A : H1 Ω) : Prop :=
  ∀ v : H10 ho, inner ℝ (H1.grad A) (H10.grad ho v) = 0

lemma extension_observe (hT : ‖H10.greenOperator ho hb hC hν‖ < 1) (A : H1 Ω) :
    observe hC hν (extension ho hb hC hν A) =
      BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A) := by
  let T := H10.greenOperator ho hb hC hν
  let f := observe hC hν A
  have hh := congrArg (fun B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => B f)
    (BanachResolvent.resolvent_left T hT)
  change (BanachResolvent.resolvent T) f - T ((BanachResolvent.resolvent T) f) = f at hh
  change observe hC hν (A + (solve ho hb hC hν ((BanachResolvent.resolvent T) f)).val) = _
  rw [observe_add_coe]
  change f + T ((BanachResolvent.resolvent T) f) = _
  exact eq_sub_iff_add_eq.mp hh.symm

lemma extension_grad (A : H1 Ω) :
    H1.grad (extension ho hb hC hν A) = H1.grad A +
      H10.grad ho (solve ho hb hC hν
        (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A))) := by
  exact H1.grad.map_add A _

lemma extension_weak (hT : ‖H10.greenOperator ho hb hC hν‖ < 1)
    (A : H1 Ω) (hA : Harmonic ho A) (v : H10 ho) :
    inner ℝ (H1.grad (extension ho hb hC hν A)) (H10.grad ho v) =
      inner ℝ (observe hC hν (extension ho hb hC hν A)) (H10.weightedValue ho hC hν v) := by
  let w := solve ho hb hC hν
    (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A))
  have hg : H1.grad (extension ho hb hC hν A) = H1.grad A + H10.grad ho w :=
    extension_grad ho hb hC hν A
  have hi := congrArg (fun z : Lp Plane 2 (volume.restrict Ω) => inner ℝ z (H10.grad ho v)) hg
  have hs := solve_spec ho hb hC hν
    (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A)) v
  have he := extension_observe ho hb hC hν hT A
  calc
    _ = inner ℝ (H1.grad A + H10.grad ho w) (H10.grad ho v) := hi
    _ = inner ℝ (H1.grad A) (H10.grad ho v) + inner ℝ (H10.grad ho w) (H10.grad ho v) :=
      inner_add_left _ _ _
    _ = 0 + inner ℝ (H10.grad ho w) (H10.grad ho v) :=
      congrArg (fun r : ℝ => r + inner ℝ (H10.grad ho w) (H10.grad ho v)) (hA v)
    _ = inner ℝ (H10.grad ho w) (H10.grad ho v) := zero_add _
    _ = inner ℝ (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A))
        (H10.weightedValue ho hC hν v) := hs
    _ = _ := congrArg (fun z : Lp ℝ 2 ν => inner ℝ z (H10.weightedValue ho hC hν v)) he.symm

end StrictHotSpots.SubcriticalExtension
end SubcriticalExtensionCombinedLayer

section HarmonicLiftCombinedLayer
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
local instance : NormedSpace ℝ (H10 ho) := (H10.innerProductSpace ho).toNormedSpace
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace



def harmonicLift (F : H1 Ω) : H1 Ω := F -
  (DirichletOperator.solution (H10.energy ho) (H10.energy_coercive ho hb)
    (H10.grad ho) (H1.grad F)).val

lemma harmonicLift_difference (F : H1 Ω) :
    ∃ v : H10 ho, harmonicLift ho hb F - F = v.val := by
  refine ⟨-(DirichletOperator.solution (H10.energy ho) (H10.energy_coercive ho hb)
    (H10.grad ho) (H1.grad F)), ?_⟩
  change (F-(DirichletOperator.solution (H10.energy ho) (H10.energy_coercive ho hb)
    (H10.grad ho) (H1.grad F)).val)-F = -_
  abel

lemma harmonicLift_harmonic (F : H1 Ω) : Harmonic ho (harmonicLift ho hb F) := by
  let v := DirichletOperator.solution (H10.energy ho) (H10.energy_coercive ho hb)
    (H10.grad ho) (H1.grad F)
  have hv (w : H10 ho) : inner ℝ (H10.grad ho v) (H10.grad ho w) =
      inner ℝ (H1.grad F) (H10.grad ho w) :=
    DirichletOperator.solution_spec (H10.energy ho) (H10.energy_coercive ho hb)
      (H10.grad ho) (H1.grad F) w
  intro w
  have hg : H1.grad (harmonicLift ho hb F) = H1.grad F - H10.grad ho v :=
    H1.grad.map_sub F v.val
  calc
    _ = inner ℝ (H1.grad F - H10.grad ho v) (H10.grad ho w) :=
      congrArg (fun g : Lp Plane 2 (volume.restrict Ω) => inner ℝ g (H10.grad ho w)) hg
    _ = inner ℝ (H1.grad F) (H10.grad ho w) - inner ℝ (H10.grad ho v) (H10.grad ho w) :=
      inner_sub_left _ _ _
    _ = 0 := sub_eq_zero.mpr (hv w).symm

include hb in
lemma h10_eq_zero_of_grad_norm_sq (v : H10 ho) (hv : ‖H10.grad ho v‖^2 = 0) : v = 0 := by
  obtain ⟨K,hK,h⟩ := H10.energy_coercive ho hb
  have he : H10.energy ho v v = 0 := (real_inner_self_eq_norm_sq _).trans hv
  have hm : K * ‖v‖^2 ≤ 0 := by
    calc
      _ = K * ‖v‖ * ‖v‖ := by ring
      _ ≤ H10.energy ho v v := h v
      _ = 0 := he
  have : ‖v‖^2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _)))

include hb in
lemma harmonic_zero_class (F : H1 Ω) (hF : Harmonic ho F)
    (hv : ∃ v : H10 ho, F = v.val) : F = 0 := by
  obtain ⟨v,rfl⟩ := hv
  have he : ‖H10.grad ho v‖^2 = 0 := (real_inner_self_eq_norm_sq _).symm.trans (hF v)
  have hz := h10_eq_zero_of_grad_norm_sq ho hb v he
  exact congrArg (fun v : H10 ho => v.val) hz

lemma harmonic_sub (F G : H1 Ω) (hF : Harmonic ho F) (hG : Harmonic ho G) :
    Harmonic ho (F-G) := by
  intro v
  have hg := H1.grad.map_sub F G
  calc
    _ = inner ℝ (H1.grad F-H1.grad G) (H10.grad ho v) :=
      congrArg (fun g : Lp Plane 2 (volume.restrict Ω) => inner ℝ g (H10.grad ho v)) hg
    _ = inner ℝ (H1.grad F) (H10.grad ho v) - inner ℝ (H1.grad G) (H10.grad ho v) :=
      inner_sub_left _ _ _
    _ = 0 := by linarith [hF v,hG v]

lemma harmonicLift_unique (F G : H1 Ω) (hG : Harmonic ho G)
    (hGF : ∃ v : H10 ho, G-F = v.val) : G = harmonicLift ho hb F := by
  apply sub_eq_zero.mp
  apply harmonic_zero_class ho hb (G-harmonicLift ho hb F)
    (harmonic_sub ho G (harmonicLift ho hb F) hG (harmonicLift_harmonic ho hb F))
  obtain ⟨v,hv⟩ := hGF
  obtain ⟨w,hw⟩ := harmonicLift_difference ho hb F
  refine ⟨v-w, ?_⟩
  change G-harmonicLift ho hb F = v.val-w.val
  calc
    _ = (G-F)-(harmonicLift ho hb F-F) := by abel
    _ = _ := congrArg₂ (fun a b : H1 Ω => a-b) hv hw
end StrictHotSpots.SubcriticalExtension
end HarmonicLiftCombinedLayer

section DouglasHarmonicLiftCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff InnerProductSpace Laplacian

namespace StrictHotSpots.PlaneGreen
lemma poissonAverage_harmonic {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) :
    InnerProductSpace.HarmonicOnNhd
      (fun z => Real.circleAverage (poissonKernel 0 z • f) 0 1) (ball 0 1) := by
  have hfc : CircleIntegrable (fun z => (f z : ℂ)) 0 1 := by
    simp only [CircleIntegrable,intervalIntegrable_iff] at hf ⊢
    exact Complex.ofRealCLM.integrable_comp hf
  have hball : ball (0 : ℂ) 1 ⊆ (sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, abs_one, Metric.mem_sphere]
    exact ne_of_lt (Metric.mem_ball.mp hz)
  have ha := (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hfc).mono hball
  intro z hz
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₂ := fun z =>
    (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (f ζ : ℂ)) 0 1).re) ?_).2
  · exact (ha z hz).harmonicAt_re
  · filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    rw [re_circleAverage_herglotzRieszKernel_smul hf (hball hw)]
    congr 1
    funext ζ
    simp only [poissonKernel_eq_re_herglotzRieszKernel]

lemma harmonicAt_comp_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (g : E ≃ₗᵢ[ℝ] F) {f : F → ℝ} {x : E}
    (hf : InnerProductSpace.HarmonicAt f (g x)) :
    InnerProductSpace.HarmonicAt (f ∘ g) x := by
  refine ⟨hf.1.comp x g.contDiff.contDiffAt,?_⟩
  filter_upwards [g.continuous.continuousAt.eventually hf.2] with y hy
  change Δ (f ∘ g) y = 0
  exact (laplacian_comp_linearIsometryEquiv g f y).trans hy

end StrictHotSpots.PlaneGreen
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10 SubcriticalExtension
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma harmonicSeries_re_harmonic {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    InnerProductSpace.HarmonicOnNhd (fun z => (harmonicSeries a z).re) (ball 0 1) := by
  have hc := Complex.continuous_re.comp_continuousOn
    ((harmonicSeries_continuousOn ha).mono sphere_subset_closedBall)
  have hh := PlaneGreen.poissonAverage_harmonic (hc.circleIntegrable (by norm_num : (0:ℝ) ≤ 1))
  intro z hz
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₂ := fun w =>
    Real.circleAverage (poissonKernel 0 w • (fun ζ => (harmonicSeries a ζ).re)) 0 1) ?_).2 (hh z hz)
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (harmonicSeries_re_poisson ha hw).symm

lemma planeSeries_harmonic {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    InnerProductSpace.HarmonicOnNhd (planeSeries a) disk := by
  intro x hx
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact harmonicAt_comp_linearIsometryEquiv complexIso.symm (harmonicSeries_re_harmonic ha _ hz)

lemma planeSeries_weak_harmonic {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    Harmonic (show IsOpen disk from isOpen_ball) (planeSeries_gradient h0 h1).toH1 := by
  intro v
  rw [H1.grad_toH1]
  have hp : ∀ x ∈ disk, Laplacian.laplacian (planeSeries a) x = -(0:ℝ)*planeSeries a x := by
    intro x hx
    simpa using (planeSeries_harmonic h0 x hx).2.self_of_nhds
  simpa using H10.helmholtz_pair (Ω:=disk) isOpen_ball (planeSeries_contDiffOn h0)
    (planeSeries_gradient h0 h1).1 (planeSeries_gradient h0 h1).2.1 hp v



theorem harmonicSeries_eq_harmonicLift (f : C(AddCircle τ, ℂ))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖fourierCoeff f m‖))
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hb : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (f s).re) :
    (planeSeries_gradient (summable_norm_of_firstMoment h1) h1).toH1 =
      harmonicLift (show IsOpen disk from isOpen_ball) isBounded_ball
        (smooth_memH1 (by norm_num : (1:ℝ) < 2) hφ.contDiffOn).toH1 := by
  apply harmonicLift_unique (Ω:=disk) isOpen_ball isBounded_ball _ _
    (planeSeries_weak_harmonic (summable_norm_of_firstMoment h1) h1)
  exact ⟨⟨_,harmonicSeries_boundary_class f h1 hφ hb⟩,rfl⟩

end StrictHotSpots.Douglas
end DouglasHarmonicLiftCombinedLayer

section CircleMollifierCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function ContinuousLinearMap
open scoped Topology ComplexConjugate ContDiff Convolution
namespace StrictHotSpots.Douglas
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma chord_translate (s t u : AddCircle τ) :
    ‖((s-u).toCircle:ℂ)-((t-u).toCircle:ℂ)‖ = ‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ := by
  rw [show s-u=s+(-u) from sub_eq_add_neg s u,show t-u=t+(-u) from sub_eq_add_neg t u]
  simp only [AddCircle.toCircle_add,Circle.coe_mul,← sub_mul,norm_mul,Circle.norm_coe,mul_one]


def angleSmooth (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) : ℝ → ℂ :=
  φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun t : ℝ => f t)

lemma angleSmooth_smooth (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    ContDiff ℝ ∞ (angleSmooth φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    (f.continuous.comp (AddCircle.continuous_mk' τ)).locallyIntegrable

lemma angleSmooth_periodic (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    Periodic (angleSmooth φ f) τ := by
  intro t
  unfold angleSmooth
  simp only [convolution_def,lsmul_apply]
  apply integral_congr_ae (ae_of_all _ fun u => ?_)
  congr 2
  rw [show t+τ-u = (t-u)+τ by ring,AddCircle.coe_add,AddCircle.coe_period,add_zero]

lemma angleSmooth_integrable (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) (t : ℝ) :
    Integrable (fun u : ℝ => φ.normed volume u • f ((t-u:ℝ):AddCircle τ)) := by
  exact φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) φ.integrable_normed.locallyIntegrable
    (f.continuous.comp (AddCircle.continuous_mk' τ)) t

lemma angleSmooth_chordLipschitz (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ))
    {K : ℝ} (h : ChordLipschitz K f) (s t : ℝ) :
    ‖angleSmooth φ f s-angleSmooth φ f t‖ ≤
      K*‖(AddCircle.toCircle (s:AddCircle τ):ℂ)-(AddCircle.toCircle (t:AddCircle τ):ℂ)‖ := by
  have hi := (angleSmooth_integrable φ f s).sub (angleSmooth_integrable φ f t)
  have hp (u : ℝ) : ‖φ.normed volume u • f ((s-u:ℝ):AddCircle τ) -
      φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ ≤
      φ.normed volume u * (K*‖(AddCircle.toCircle (s:AddCircle τ):ℂ)-(AddCircle.toCircle (t:AddCircle τ):ℂ)‖) := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed u)]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed u)
    have hh := h ((s-u:ℝ):AddCircle τ) ((t-u:ℝ):AddCircle τ)
    simpa only [AddCircle.coe_sub,chord_translate] using hh
  change ‖(∫ u : ℝ, φ.normed volume u • f ((s-u:ℝ):AddCircle τ))-
    (∫ u : ℝ, φ.normed volume u • f ((t-u:ℝ):AddCircle τ))‖ ≤ _
  rw [← integral_sub (angleSmooth_integrable φ f s) (angleSmooth_integrable φ f t)]
  calc
    _ ≤ ∫ u : ℝ, ‖φ.normed volume u • f ((s-u:ℝ):AddCircle τ) -
        φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, φ.normed volume u *
        (K*‖(AddCircle.toCircle (s:AddCircle τ):ℂ)-(AddCircle.toCircle (t:AddCircle τ):ℂ)‖) :=
      integral_mono hi.norm (φ.integrable_normed.mul_const _) hp
    _ = _ := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma periodic_lift_continuous {g : ℝ → ℂ} (hg : Periodic g τ) (hc : Continuous g) :
    Continuous hg.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples τ)).continuous_iff.2
  exact hc


def circleSmooth (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) : C(AddCircle τ,ℂ) :=
  ⟨(angleSmooth_periodic φ f).lift,
    periodic_lift_continuous _ (angleSmooth_smooth φ f).continuous⟩

lemma circleSmooth_coe (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) (t : ℝ) :
    circleSmooth φ f t = angleSmooth φ f t := rfl

lemma circleSmooth_chordLipschitz (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ))
    {K : ℝ} (h : ChordLipschitz K f) : ChordLipschitz K (circleSmooth φ f) := by
  intro s t
  induction s using QuotientAddGroup.induction_on with | H s =>
    induction t using QuotientAddGroup.induction_on with | H t =>
      exact angleSmooth_chordLipschitz φ f h s t

lemma circleSmooth_tendsto {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    Tendsto (fun i => circleSmooth (φ i) f s) l (𝓝 (f s)) := by
  induction s using QuotientAddGroup.induction_on with | H t =>
    exact ContDiffBump.convolution_tendsto_right_of_continuous hφ
      (f.continuous.comp (AddCircle.continuous_mk' τ)) t

end StrictHotSpots.Douglas
end CircleMollifierCombinedLayer

section CircleSmoothFourierCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma periodic_deriv {g : ℝ → ℂ} (hg : Periodic g τ) : Periodic (deriv g) τ := by
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun h : ℝ → ℂ => deriv h t) (funext hg)

lemma angleLift_periodic (f : C(AddCircle τ,ℂ)) : Periodic (fun t : ℝ => f t) τ := by
  intro t
  dsimp only
  rw [AddCircle.coe_add,AddCircle.coe_period,add_zero]



theorem summable_firstMoment_of_smooth_lift (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    Summable (fun m : ℤ => (m.natAbs:ℝ)*‖fourierCoeff f m‖) := by
  let g : ℝ → ℂ := fun t => f t
  have hp : Periodic g τ := angleLift_periodic f
  have h1 : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hf).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv g)) := (contDiff_infty_iff_deriv.mp h1).2
  have h3 : ContDiff ℝ ∞ (deriv (deriv (deriv g))) := (contDiff_infty_iff_deriv.mp h2).2
  let f1 : C(AddCircle τ,ℂ) := ⟨(periodic_deriv hp).lift,
    periodic_lift_continuous _ h1.continuous⟩
  let f2 : C(AddCircle τ,ℂ) := ⟨(periodic_deriv (periodic_deriv hp)).lift,
    periodic_lift_continuous _ h2.continuous⟩
  let f3 : C(AddCircle τ,ℂ) := ⟨(periodic_deriv (periodic_deriv (periodic_deriv hp))).lift,
    periodic_lift_continuous _ h3.continuous⟩
  apply summable_firstMoment_fourierCoeff f f1 f2 f3
  · intro t
    exact (hf.differentiable (by simp) t).hasDerivAt
  · intro t
    exact (h1.differentiable (by simp) t).hasDerivAt
  · intro t
    exact (h2.differentiable (by simp) t).hasDerivAt

lemma circleSmooth_firstMoment (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    Summable (fun m : ℤ => (m.natAbs:ℝ)*‖fourierCoeff (circleSmooth φ f) m‖) :=
  summable_firstMoment_of_smooth_lift _ (angleSmooth_smooth φ f)


theorem douglas_smooth_lift (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    diskEnergy (poissonExtension f) = (1/τ)*boundaryEnergy f := by
  have h1 := summable_firstMoment_of_smooth_lift f hf
  have h0 := summable_norm_of_firstMoment h1
  have he : EqOn (poissonExtension f) (harmonicSeries (fourierCoeff f)) (ball 0 1) :=
    fun z hz => poissonExtension_eq_harmonicSeries f h0 hz
  have hE : diskEnergy (poissonExtension f) = diskEnergy (harmonicSeries (fourierCoeff f)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    have hd := (he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).fderiv_eq (𝕜:=ℝ)
    dsimp only
    rw [hd]
  rw [hE,douglas_series h0 h1]
  have hb : (fun s : AddCircle τ => harmonicSeries (fourierCoeff f) s.toCircle) = f :=
    funext (harmonicSeries_fourier_boundary f h0)
  rw [hb]




theorem smooth_poisson_energy_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → ContDiffBump (0:ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun i => diskEnergy (poissonExtension (circleSmooth (φ i) f))) l
      (𝓝 ((1/τ)*boundaryEnergy f)) := by
  have hb := boundaryEnergy_tendsto_filter hK
    (fun i => (circleSmooth (φ i) f).continuous)
    (fun i => circleSmooth_chordLipschitz (φ i) f h) (circleSmooth_tendsto hφ f)
  have he (i : ι) : diskEnergy (poissonExtension (circleSmooth (φ i) f)) =
      (1/τ)*boundaryEnergy (circleSmooth (φ i) f) :=
    douglas_smooth_lift _ (angleSmooth_smooth (φ i) f)
  simpa only [he] using hb.const_mul (1/τ)

end StrictHotSpots.Douglas
end CircleSmoothFourierCombinedLayer

section CircleApproximationCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma chordLipschitz_sub {T : ℝ} {f g : AddCircle T → ℂ} {K L : ℝ}
    (hf : ChordLipschitz K f) (hg : ChordLipschitz L g) :
    ChordLipschitz (K+L) (fun s => f s-g s) := by
  intro s t
  rw [show (f s-g s)-(f t-g t) = (f s-f t)-(g s-g t) by ring]
  exact (norm_sub_le _ _).trans ((add_le_add (hf s t) (hg s t)).trans_eq (add_mul _ _ _).symm)

@[simp] lemma boundaryEnergy_zero {T : ℝ} [Fact (0 < T)] : boundaryEnergy (fun _ : AddCircle T => (0:ℂ)) = 0 := by
  simp [boundaryEnergy,boundaryDifference]




theorem circleSmooth_boundaryError_tendsto {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {φ : ι → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (f : C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun i => boundaryEnergy (fun s => circleSmooth (φ i) f s-f s))
      l (𝓝 0) := by
  have hh := boundaryEnergy_tendsto_filter (add_nonneg hK hK)
    (fun i => (circleSmooth (φ i) f).continuous.sub f.continuous)
    (fun i => chordLipschitz_sub (circleSmooth_chordLipschitz (φ i) f h) h)
    (fun s => (circleSmooth_tendsto hφ f s).sub_const (f s))
  convert hh using 1
  simp only [sub_self,boundaryEnergy_zero]




theorem circleSmooth_poisson_cauchy {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {φ : ι → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (f : C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun p : ι × ι => diskEnergy (poissonExtension
      (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f))) (l ×ˢ l) (𝓝 0) := by
  have hh := boundaryEnergy_tendsto_filter (add_nonneg hK hK)
    (l:=l ×ˢ l)
    (fun p : ι × ι => (circleSmooth (φ p.1) f).continuous.sub (circleSmooth (φ p.2) f).continuous)
    (fun p : ι × ι => chordLipschitz_sub (circleSmooth_chordLipschitz (φ p.1) f h)
      (circleSmooth_chordLipschitz (φ p.2) f h))
    (fun s => ((circleSmooth_tendsto hφ f s).comp tendsto_fst).sub
      ((circleSmooth_tendsto hφ f s).comp tendsto_snd))
  have hz : Tendsto (fun p : ι × ι => (1/τ)*boundaryEnergy
      (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f)) (l ×ˢ l) (𝓝 0) := by
    simpa only [Pi.sub_apply, ContinuousMap.coe_sub, sub_self,boundaryEnergy_zero,mul_zero] using hh.const_mul (1/τ)
  apply hz.congr'
  exact Eventually.of_forall fun p => (douglas_smooth_lift
    (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f)
    ((angleSmooth_smooth (φ p.1) f).sub (angleSmooth_smooth (φ p.2) f))).symm

end StrictHotSpots.Douglas
end CircleApproximationCombinedLayer

section CirclePoissonConvergenceCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma angleSmooth_norm_le (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) (t : ℝ) :
    ‖angleSmooth φ f t‖ ≤ ‖f‖ := by
  change ‖∫ u : ℝ, φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ ≤ ‖f‖
  calc
    _ ≤ ∫ u : ℝ, ‖φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, φ.normed volume u * ‖f‖ := by
      apply integral_mono (angleSmooth_integrable φ f t).norm (φ.integrable_normed.mul_const _)
      intro u
      dsimp only
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed u)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (φ.nonneg_normed u)
    _ = ‖f‖ := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma circleSmooth_norm_le (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    ‖circleSmooth φ f s‖ ≤ ‖f‖ := by
  induction s using QuotientAddGroup.induction_on with | H s => exact angleSmooth_norm_le φ f s



theorem circleSmooth_poisson_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → ContDiffBump (0:ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    Tendsto (fun i => poissonExtension (circleSmooth (φ i) f) z) l
      (𝓝 (poissonExtension f z)) := by
  have hk := poissonKernel_continuousOn_sphere hz
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn hk
  have hmap (t : ℝ) : circleMap (0:ℂ) 1 t ∈ sphere 0 1 :=
    circleMap_mem_sphere (0:ℂ) (by norm_num) t
  have hkc : Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
    hk.comp_continuous (continuous_circleMap 0 1) hmap
  unfold poissonExtension
  apply Filter.Tendsto.smul tendsto_const_nhds
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C*‖f‖)
  · exact Eventually.of_forall fun i =>
      (hkc.smul ((circleSmooth (φ i) f).continuous.comp (AddCircle.continuous_mk' τ))).aestronglyMeasurable
  · exact Eventually.of_forall fun i => ae_of_all _ fun t _ => by
      rw [norm_smul]
      exact mul_le_mul (hC _ (hmap t)) (circleSmooth_norm_le (φ i) f t)
        (norm_nonneg _) (le_trans (norm_nonneg _) (hC _ (hmap t)))
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ => tendsto_const_nhds.smul (circleSmooth_tendsto hφ f t)

end StrictHotSpots.Douglas
end CirclePoissonConvergenceCombinedLayer

section DouglasRealEnergyCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10

lemma real_component_gradient_bound (L : ℂ →L[ℝ] ℂ) :
    ‖(InnerProductSpace.toDual ℝ Plane).symm ((Complex.reCLM.comp L).comp
      complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖^2 ≤
      ‖L 1‖^2+‖L Complex.I‖^2 := by
  let v : Plane := (InnerProductSpace.toDual ℝ Plane).symm ((Complex.reCLM.comp L).comp
    complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hi (z : ℂ) : inner ℝ v (complexIso z) = (L z).re := by
    rw [show v = (InnerProductSpace.toDual ℝ Plane).symm ((Complex.reCLM.comp L).comp
      complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap) from rfl,
      InnerProductSpace.toDual_symm_apply]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply,Complex.reCLM_apply]
  have hi' (z : ℂ) : inner ℝ (complexIso z) v = (L z).re := by
    rw [real_inner_comm]
    exact hi z
  have he := (Complex.orthonormalBasisOneI.map complexIso).sum_inner_mul_inner v v
  simp only [Fin.sum_univ_two,OrthonormalBasis.map_apply,Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he
  simp only [hi,hi',real_inner_self_eq_norm_sq] at he
  change ‖v‖^2 ≤ _
  rw [← he,← sq,← sq]
  exact add_le_add (by simpa only [Complex.normSq_eq_norm_sq,pow_two] using Complex.re_sq_le_normSq (L 1))
    (by simpa only [Complex.normSq_eq_norm_sq,pow_two] using Complex.re_sq_le_normSq (L Complex.I))



theorem planeSeries_energy_le {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    (∫ x : Plane in disk, ‖gradient (planeSeries a) x‖^2) ≤ diskEnergy (harmonicSeries a) := by
  have hm (x : Plane) (hx : x ∈ disk) :
      ‖gradient (planeSeries a) x‖^2 ≤
      ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) 1‖^2+
        ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) Complex.I‖^2 := by
    have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
      simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
    rw [(harmonicSeries_hasFDerivAt h0 h1 hz).fderiv]
    have hp := (planeSeries_hasFDerivAt h0 h1 hx).fderiv
    simp only [gradient]
    rw [hp]
    exact real_component_gradient_bound (harmonicD a (complexIso.symm x))
  have hI : Integrable (fun x : Plane =>
      ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) 1‖^2+
      ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) Complex.I‖^2) (volume.restrict disk) := by
    have hi : Integrable (fun x : Plane => ‖harmonicD a (complexIso.symm x) 1‖^2+
        ‖harmonicD a (complexIso.symm x) Complex.I‖^2) (volume.restrict disk) := by
      have hc : ContinuousOn (fun x : Plane => harmonicD a (complexIso.symm x))
          (closedBall 0 1) := (harmonicD_continuousOn h1).comp complexIso.symm.continuous.continuousOn (by
        intro x hx
        simpa only [mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx)
      have he : ContinuousOn (fun x : Plane => ‖harmonicD a (complexIso.symm x) 1‖^2+
          ‖harmonicD a (complexIso.symm x) Complex.I‖^2) (closedBall 0 1) :=
        ((hc.clm_apply continuousOn_const).norm.pow 2).add
          ((hc.clm_apply continuousOn_const).norm.pow 2)
      exact (he.integrableOn_compact (isCompact_closedBall (0:Plane) 1)).mono_set ball_subset_closedBall
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
      simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
    rw [(harmonicSeries_hasFDerivAt h0 h1 hz).fderiv]
    rfl
  calc
    _ ≤ ∫ x : Plane in disk,
        ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) 1‖^2+
        ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) Complex.I‖^2 :=
      integral_mono_ae ((memLp_two_iff_integrable_sq_norm
        (planeSeries_gradient h0 h1).2.1.aestronglyMeasurable).mp (planeSeries_gradient h0 h1).2.1)
        hI ((ae_restrict_mem measurableSet_ball).mono fun x hx => hm x hx)
    _ = _ := complexIso_disk_preserving.integral_comp complexIso.symm.toHomeomorph.measurableEmbedding
      (fun z : ℂ => ‖fderiv ℝ (harmonicSeries a) z 1‖^2+‖fderiv ℝ (harmonicSeries a) z Complex.I‖^2)

end StrictHotSpots.Douglas
end DouglasRealEnergyCombinedLayer
end
end DouglasLipschitzBase


end OAI
