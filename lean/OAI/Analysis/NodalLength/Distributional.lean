import OAI.Analysis.NodalLength.Regularization

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

theorem uniform_secondTaylor_remainder {f : Plane → ℝ} (hf : Smooth f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 0≤C ∧ ∀ x y,
    |f (x+y)-secondTaylorPolynomial f x (x+y)|≤C*‖y‖^3 := by
  have hd : Continuous (iteratedFDeriv ℝ 3 f) :=
    (hf.iteratedFDeriv_right (i:=3) (m:=0) (by exact WithTop.coe_le_coe.mpr (le_top : (3:ℕ∞)≤⊤))).continuous
  obtain ⟨M,hM⟩ := hd.norm.bddAbove_range_of_hasCompactSupport (hc.iteratedFDeriv (𝕜:=ℝ) 3).norm
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro x y
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n:=2) (x:=x) (y:=y)
    (fun t _ => (hf.of_le (WithTop.coe_le_coe.mpr (le_top : (3:ℕ∞)≤⊤))).contDiffAt)
  have heq : f (x+y)-secondTaylorPolynomial f x (x+y)=
      (1/2:ℝ)*(∫ t in (0:ℝ)..1, (1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)) := by
    simp only [show (2+1:ℕ)=3 from rfl,Finset.sum_range_succ,Finset.sum_range_zero,
      Nat.factorial_zero,Nat.factorial_one,Nat.factorial_two,zero_add,Nat.cast_one,Nat.cast_ofNat,
      inv_one,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,
      iteratedFDeriv_two_apply,smul_eq_mul] at ht
    dsimp only [secondTaylorPolynomial,centeredQuadratic]
    simp only [add_sub_cancel_left]
    linarith [ht]
  rw [heq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hi : |∫ t in (0:ℝ)..1, (1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)|
      ≤ max 0 M*‖y‖^3 := by
    rw [← Real.norm_eq_abs]
    have hb : ∀ t ∈ uIoc (0:ℝ) 1,
        ‖(1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)‖≤ max 0 M*‖y‖^3 := by
      intro t ht
      simp only [uIoc_of_le (by norm_num : (0:ℝ)≤1),mem_Ioc] at ht
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      have hder := (iteratedFDeriv ℝ 3 f (x+t • y)).le_opNorm (fun _ => y)
      have hnorm : ‖iteratedFDeriv ℝ 3 f (x+t • y)‖≤ max 0 M := (hM (mem_range_self (x+t • y))).trans (le_max_right _ _)
      have hs : (1-t)^2≤1 := by nlinarith [ht.1,ht.2]
      calc
        (1-t)^2*|iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)|
          ≤ 1*(max 0 M*‖y‖^3) := mul_le_mul hs (by simpa [Real.norm_eq_abs] using hder.trans (mul_le_mul_of_nonneg_right hnorm (by positivity))) (abs_nonneg _) (by positivity)
        _ = _ := one_mul _
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hpos : 0≤ max 0 M*‖y‖^3 := by positivity
  linarith
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def planeCircleAverage (f : Plane → ℝ) (a : Plane) (r : ℝ) : ℝ :=
  Real.circleAverage (f∘planeComplex.symm) (planeComplex a) r

lemma planeCircleAverage_harmonic {f : Plane → ℝ} (hf : Smooth f)
    (hΔ : ∀x,euclideanLaplacian f x=0) (a : Plane) (r : ℝ) :
    planeCircleAverage f a r=f a := by
  have hg : ContDiff ℝ ∞ (f∘planeComplex.symm) :=
    hf.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hgΔ : ∀z,(Δ (f∘planeComplex.symm)) z=0 := by
    rw [laplacian_comp_isometry planeComplex.symm hf,← plane_laplacian_eq_mathlib hf]
    exact fun z => hΔ (planeComplex.symm z)
  have hh : HarmonicOnNhd (f∘planeComplex.symm) (Metric.closedBall (planeComplex a) |r|) := by
    intro z _
    refine ⟨hg.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤)),?_⟩
    exact Filter.Eventually.of_forall hgΔ
  simpa only [planeCircleAverage,Function.comp_def,planeComplex.symm_apply_apply] using hh.circleAverage_eq

lemma planeCircleAverage_radiusSquare (a : Plane) (r : ℝ) :
    planeCircleAverage (radiusSquare a) a r=r^2 := by
  apply Real.circleAverage_const_on_circle
  intro z hz
  change ‖planeComplex.symm z-a‖^2=r^2
  rw [← dist_eq_norm,← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
  rw [Metric.mem_sphere.mp hz,sq_abs]

lemma planeCircleAverage_secondTaylor {f : Plane → ℝ} (hf : Smooth f) (a : Plane) (r : ℝ) :
    planeCircleAverage (secondTaylorPolynomial f a) a r=
      f a+(r^2/4)*euclideanLaplacian f a := by
  let T := secondTaylorPolynomial f a
  let L := euclideanLaplacian f a
  have hT : Smooth T := smooth_secondTaylorPolynomial f a
  have hL (x : Plane) : euclideanLaplacian T x=L := by
    change euclideanLaplacian (quadraticAffine (f a) (fderiv ℝ f a)
      (fderiv ℝ (fderiv ℝ f) a) a) x=euclideanLaplacian f a
    rw [laplacian_quadraticAffine (symmetric_hessian hf a)]
    unfold formTrace euclideanLaplacian
    apply Finset.sum_congr rfl
    intro i _
    exact hessian_on_basis hf a i i
  let q := fun x => T x+(-L/4)*radiusSquare a x
  have hq : Smooth q := hT.add (contDiff_const.mul (smooth_radiusSquare a))
  have hqΔ (x : Plane) : euclideanLaplacian q x=0 := by
    rw [show q=(fun x => T x+(-L/4)*radiusSquare a x) from rfl,
      laplacian_add hT (contDiff_const.mul (smooth_radiusSquare a)),
      laplacian_const_mul (smooth_radiusSquare a),hL]
    dsimp only
    rw [laplacian_radiusSquare]
    ring
  have havg := planeCircleAverage_harmonic hq hqΔ a r
  have hsplit : planeCircleAverage q a r=planeCircleAverage T a r+(-L/4)*r^2 := by
    unfold planeCircleAverage
    change Real.circleAverage (fun z => T (planeComplex.symm z)+(-L/4)*radiusSquare a (planeComplex.symm z)) _ r=_
    have h1 : CircleIntegrable (fun z => T (planeComplex.symm z)) (planeComplex a) r :=
      (hT.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    have h2 : CircleIntegrable (fun z => (-L/4)*radiusSquare a (planeComplex.symm z)) (planeComplex a) r :=
      ((contDiff_const.mul (smooth_radiusSquare a) : Smooth (fun x => (-L/4)*radiusSquare a x)).continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    rw [Real.circleAverage_fun_add h1 h2]
    change _+Real.circleAverage ((-L/4) • (fun z => radiusSquare a (planeComplex.symm z))) (planeComplex a) r=_
    rw [Real.circleAverage_smul]
    change _+(-L/4)*planeCircleAverage (radiusSquare a) a r=_
    rw [planeCircleAverage_radiusSquare]
    rfl
  have hqa : q a=f a := by simp [q,T,secondTaylorPolynomial_self,radiusSquare]
  rw [hsplit,hqa] at havg
  change planeCircleAverage T a r=f a+r^2/4*L
  linarith
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma planeCircleAverage_uniform_second_order {f : Plane → ℝ} (hf : Smooth f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 0≤C ∧ ∀ a r,
      |planeCircleAverage f a r-f a-(r^2/4)*euclideanLaplacian f a|≤C*|r|^3 := by
  obtain ⟨C,hC,hrem⟩ := uniform_secondTaylor_remainder hf hc
  refine ⟨C,hC,?_⟩
  intro a r
  let T := secondTaylorPolynomial f a
  have hT : Smooth T := smooth_secondTaylorPolynomial f a
  have he : planeCircleAverage f a r-f a-r^2/4*euclideanLaplacian f a =
    Real.circleAverage (fun z => f (planeComplex.symm z)-T (planeComplex.symm z)) (planeComplex a) r := by
    have h1 : CircleIntegrable (fun z => f (planeComplex.symm z)) (planeComplex a) r :=
      (hf.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    have h2 : CircleIntegrable (fun z => T (planeComplex.symm z)) (planeComplex a) r :=
      (hT.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    rw [Real.circleAverage_fun_sub h1 h2]
    change planeCircleAverage f a r-f a-r^2/4*euclideanLaplacian f a=
      planeCircleAverage f a r-planeCircleAverage (secondTaylorPolynomial f a) a r
    rw [planeCircleAverage_secondTaylor hf]
    ring
  rw [he]
  apply Real.abs_circleAverage_le_circleAverage_abs.trans
  apply Real.circleAverage_mono_on_of_le_circle
  · exact (((hf.continuous.sub hT.continuous).comp planeComplex.symm.continuous).abs).continuousOn.circleIntegrable'
  intro z hz
  have hr' : ‖planeComplex.symm z-a‖=|r| := by
    rw [← dist_eq_norm,← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    exact Metric.mem_sphere.mp hz
  simpa only [Pi.abs_apply,add_sub_cancel,hr',T] using hrem a (planeComplex.symm z-a)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma submean_dual_lintegral {T : Type*} [MeasurableSpace T] {ν : Measure T} [SFinite ν]
    {f g : Plane → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {v : T → Plane} (hv : Measurable v)
    (hsub : ∀x,g x≠0 → (∫⁻ t,f (x+v t) ∂ν)≤f x) :
    (∫⁻ x,f x*(∫⁻ t,g (x-v t) ∂ν))≤∫⁻ x,f x*g x := by
  calc
    _ = ∫⁻ x,∫⁻ t,f x*g (x-v t) ∂ν := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ (hg.comp (measurable_const.sub hv))).symm
    _ = ∫⁻ t,(∫⁻ x,f x*g (x-v t)) ∂ν := by
      apply lintegral_lintegral_swap
      exact ((hf.comp measurable_fst).mul (hg.comp (measurable_fst.sub (hv.comp measurable_snd)))).aemeasurable
    _ = ∫⁻ t,(∫⁻ x,f (x+v t)*g x) ∂ν := by
      apply lintegral_congr
      intro t
      rw [← lintegral_add_right_eq_self (fun x => f x*g (x-v t)) (v t)]
      simp only [add_sub_cancel_right]
    _ = ∫⁻ x,∫⁻ t,f (x+v t)*g x ∂ν := by
      apply lintegral_lintegral_swap
      exact ((hf.comp (measurable_snd.add (hv.comp measurable_fst))).mul (hg.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x,(∫⁻ t,f (x+v t) ∂ν)*g x := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const _ (hf.comp (measurable_const.add hv))
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : g x=0
      · simp [hx]
      · exact mul_le_mul' (hsub x hx) le_rfl
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def circleVector (r t : ℝ) : Plane := planeComplex.symm (circleMap 0 r t)

lemma circleVector_continuous (r : ℝ) : Continuous (circleVector r) :=
  planeComplex.symm.continuous.comp (continuous_circleMap 0 r)

lemma circleVector_norm (r t : ℝ) : ‖circleVector r t‖=|r| := by
  rw [circleVector,planeComplex.symm.norm_map]
  simpa only [zero_add] using norm_circleMap_zero r t

lemma planeCircleAverage_eq_integral (f : Plane → ℝ) (a : Plane) (r : ℝ) :
    planeCircleAverage f a r=∫t,f (a+circleVector r t) ∂circleParameterMeasure := by
  rw [planeCircleAverage,circleAverage_eq_integral_parameter]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Function.comp_def]
  congr 1
  simp [circleMap,circleVector]

instance circleParameter_isProbability : IsProbabilityMeasure circleParameterMeasure := by
  constructor
  rw [circleParameterMeasure,Measure.smul_apply,Measure.restrict_apply_univ,
    Real.volume_Ioc,smul_eq_mul,sub_zero,← ENNReal.ofReal_mul (by positivity),inv_mul_cancel₀ (by positivity)]
  simp

lemma planeCircleAverage_continuous {f : Plane → ℝ} (hf : Continuous f) (r : ℝ) :
    Continuous (fun a => planeCircleAverage f a r) := by
  unfold planeCircleAverage Real.circleAverage
  change Continuous (((2*Real.pi)⁻¹:ℝ) • (fun a => ∫θ in (0:ℝ)..2*Real.pi, f (planeComplex.symm (circleMap (planeComplex a) r θ))))
  apply Continuous.const_smul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf.comp (planeComplex.symm.continuous.comp (by fun_prop [circleMap]))

lemma planeCircleAverage_abs_le {f : Plane → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x,|f x|≤M) (a : Plane) (r : ℝ) : |planeCircleAverage f a r|≤M := by
  apply Real.abs_circleAverage_le_circleAverage_abs.trans
  apply Real.circleAverage_mono_on_of_le_circle
  · exact (hf.comp planeComplex.symm.continuous).abs.continuousOn.circleIntegrable'
  intro z _
  exact hM (planeComplex.symm z)

lemma integrable_mul_continuous_compact {w f : Plane → ℝ} (hw : Integrable w)
    (hf : Continuous f) (hc : HasCompactSupport f) : Integrable (fun x => w x*f x) := by
  obtain ⟨M,hM⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  exact hw.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall fun x => hM (mem_range_self x))

lemma integrable_mul_planeCircleAverage {w f : Plane → ℝ} (hw : Integrable w)
    (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    Integrable (fun x => w x*planeCircleAverage f x r) := by
  obtain ⟨M,hM⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  apply hw.mul_bdd (planeCircleAverage_continuous hf r).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact planeCircleAverage_abs_le hf (fun y => by simpa only [← Real.norm_eq_abs] using hM (mem_range_self y)) x r

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem distributional_laplacian_nonpos_of_dual {w ψ : Plane → ℝ}
    (hw : Integrable w) (hwpos : ∀ᵐx,w x≥0) (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
    {δ : ℝ} (hδ : 0<δ)
    (hdual : ∀r,0<r → r<δ →
      (∫x,w x*planeCircleAverage ψ x r)≤∫x,w x*ψ x) :
    (∫x,w x*euclideanLaplacian ψ x)≤0 := by
  obtain ⟨C,hC,herr⟩ := planeCircleAverage_uniform_second_order hψ hcψ
  have hiψ := integrable_mul_continuous_compact hw hψ.continuous hcψ
  have hiΔ := integrable_mul_continuous_compact hw (smooth_laplacian hψ).continuous (compact_laplacian hcψ)
  have hbound (r : ℝ) (hr : 0<r) (hrδ : r<δ) :
      (∫x,w x*euclideanLaplacian ψ x)≤4*C*r*(∫x,w x) := by
    have hi := integrable_mul_planeCircleAverage hw hψ.continuous hcψ r
    have hpoint : ∀ᵐx,(r^2/4)*(w x*euclideanLaplacian ψ x)≤
        (w x*planeCircleAverage ψ x r-w x*ψ x)+(C*r^3)*w x := by
      filter_upwards [hwpos] with x hx
      have he := (abs_le.mp (herr x r)).1
      rw [abs_of_pos hr] at he
      have hh : r^2/4*euclideanLaplacian ψ x≤planeCircleAverage ψ x r-ψ x+C*r^3 := by linarith
      have hh' := mul_le_mul_of_nonneg_left hh hx
      nlinarith [hh']
    have hb := integral_mono_ae (hiΔ.const_mul (r^2/4)) ((hi.sub hiψ).add (hw.const_mul (C*r^3))) hpoint
    rw [integral_add' (hi.sub hiψ) (hw.const_mul (C*r^3)),integral_sub' hi hiψ,
      integral_const_mul,integral_const_mul] at hb
    have hd := hdual r hr hrδ
    apply (mul_le_mul_iff_of_pos_left (show 0<r^2/4 by positivity)).mp
    calc
      (r^2/4)*(∫x,w x*euclideanLaplacian ψ x)≤C*r^3*(∫x,w x) := by linarith
      _ = (r^2/4)*(4*C*r*(∫x,w x)) := by ring
  have hlim : Tendsto (fun r : ℝ => 4*C*r*(∫x,w x)) (𝓝[>]0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => 4*C*r*(∫x,w x)) (𝓝 0) (𝓝 (4*C*0*(∫x,w x))) :=
      ((tendsto_const_nhds.mul (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0))).mul_const (∫x,w x))
    simpa using h.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr hrδ
  exact hbound r hr hrδ

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma circleVector_neg (r t : ℝ) : circleVector (-r) t= -circleVector r t := by
  simp [circleVector,circleMap]

lemma planeCircleAverage_eq_integral_sub (f : Plane → ℝ) (a : Plane) (r : ℝ) :
    planeCircleAverage f a r=∫t,f (a-circleVector r t) ∂circleParameterMeasure := by
  have hn : planeCircleAverage f a (-r)=planeCircleAverage f a r := by
    exact Real.circleAverage_neg_radius
  rw [← hn,planeCircleAverage_eq_integral]
  simp only [circleVector_neg,sub_eq_add_neg]

lemma lintegral_mul_ofReal_toReal {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (hfFin : (∫⁻x,f x)≠⊤) {g : Plane → ℝ}
    (hig : Integrable (fun x => (f x).toReal*g x)) (hgpos : ∀x,0≤g x) :
    (∫⁻x,f x*ENNReal.ofReal (g x))=ENNReal.ofReal (∫x,(f x).toReal*g x) := by
  rw [ofReal_integral_eq_lintegral_ofReal hig (Eventually.of_forall fun x => mul_nonneg ENNReal.toReal_nonneg (hgpos x))]
  apply lintegral_congr_ae
  filter_upwards [ae_lt_top' hf.aemeasurable hfFin] with x hx
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hx.ne]

lemma submean_dual_real {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (hfFin : (∫⁻x,f x)≠⊤) {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hψpos : ∀x,0≤ψ x) (r : ℝ)
    (hsub : ∀x,ψ x≠0 → (∫⁻t,f (x+circleVector r t) ∂circleParameterMeasure)≤f x) :
    (∫x,(f x).toReal*planeCircleAverage ψ x r)≤∫x,(f x).toReal*ψ x := by
  have hw : Integrable (fun x => (f x).toReal) := integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfFin
  have havgpos (x : Plane) : 0≤planeCircleAverage ψ x r :=
    Real.circleAverage_nonneg_of_nonneg (fun z _ => hψpos (planeComplex.symm z))
  have hlin := submean_dual_lintegral hf (ENNReal.continuous_ofReal.comp hψ).measurable
    (circleVector_continuous r).measurable (fun x hx => hsub x (by contrapose! hx; simp [hx]))
  have hiψ := integrable_mul_continuous_compact hw hψ hcψ
  have hiavg := integrable_mul_planeCircleAverage hw hψ hcψ r
  have havg (x : Plane) : (∫⁻t,ENNReal.ofReal (ψ (x-circleVector r t)) ∂circleParameterMeasure)=
      ENNReal.ofReal (planeCircleAverage ψ x r) := by
    rw [planeCircleAverage_eq_integral_sub]
    exact (ofReal_integral_eq_lintegral_ofReal (circleParameter_integrable
      (hψ.comp (continuous_const.sub (circleVector_continuous r))))
      (Eventually.of_forall fun t => hψpos (x-circleVector r t))).symm
  simp only [Function.comp_def] at hlin
  simp_rw [havg] at hlin
  rw [lintegral_mul_ofReal_toReal hf hfFin hiavg havgpos,
    lintegral_mul_ofReal_toReal hf hfFin hiψ hψpos] at hlin
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (havgpos x)),
    ENNReal.toReal_ofReal (integral_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (hψpos x))] using h

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma usc_density_indicator_measurable {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) :
    Measurable (Ω.indicator (fun x => (-V x).toENNReal)) := by
  apply measurable_of_restrict_of_restrict_compl hΩ
  · have he : Ω.domRestrict (Ω.indicator (fun x => (-V x).toENNReal)) =
        (fun x : Ω => (-V x).toENNReal) := by
      funext x
      simp [Set.domRestrict]
    rw [he]
    exact EReal.continuous_toENNReal.measurable.comp
      (upperSemicontinuousOn_iff_restrict.mpr hV).measurable.neg
  · have he : Ωᶜ.domRestrict (Ω.indicator (fun x => (-V x).toENNReal)) =
        (fun _ : ↥(Ωᶜ) => (0:ℝ≥0∞)) := by
      funext x
      change Ω.indicator (fun y => (-V y).toENNReal) (x:Plane)=0
      exact Set.indicator_of_notMem x.property _
    rw [he]
    exact measurable_const

theorem profile_distribution_D6 {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) (hball : Metric.ball (0:Plane) 8⊆Ω)
    (hfin : (∫⁻x in Metric.ball (0:Plane) 8,(-V x).toENNReal)≠⊤)
    {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ⊆Metric.ball 0 6) (hψpos : ∀x,0≤ψ x) :
    0≤∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x := by
  let f := (Metric.ball (0:Plane) 8).indicator (fun x => (-V x).toENNReal)
  have hfm : Measurable f := usc_density_indicator_measurable measurableSet_ball (hV.mono hball)
  have hff : (∫⁻x,f x)≠⊤ := by simpa only [f,lintegral_indicator measurableSet_ball] using hfin
  have hiw : Integrable (fun x => (f x).toReal) := integrable_toReal_of_lintegral_ne_top hfm.aemeasurable hff
  have hd (r : ℝ) (hr : 0<r) (hr1 : r<1) :
      (∫x,(f x).toReal*planeCircleAverage ψ x r)≤∫x,(f x).toReal*ψ x := by
    apply submean_dual_real hfm hff hψ.continuous hcψ hψpos r
    intro x hx
    have hx6 : x∈Metric.ball (0:Plane) 6 := hsψ (subset_tsupport ψ hx)
    have hb : Metric.closedBall x r⊆Metric.ball (0:Plane) 8 :=
      Metric.closedBall_subset_ball' (by change dist x 0<6 at hx6; linarith)
    have hx8 : x∈Metric.ball (0:Plane) 8 := hb (Metric.mem_closedBall_self hr.le)
    have hpt (t : ℝ) : planeComplex.symm (circleMap (planeComplex x) r t)=x+circleVector r t := by
      simp [circleVector,circleMap]
    have hm (t : ℝ) : x+circleVector r t∈Metric.closedBall x r := by
      rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,circleVector_norm,abs_of_pos hr]
    have hh := circle_submean hV hneg htest hr (hb.trans hball)
    simp_rw [hpt] at hh
    simpa only [f,Set.indicator_of_mem hx8,Set.indicator_of_mem (hb (hm _))] using hh
  have hh := distributional_laplacian_nonpos_of_dual hiw
    (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hψ hcψ (by norm_num : (0:ℝ)<1) hd
  have he : (∫x,(f x).toReal*euclideanLaplacian ψ x)=
      -(∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x) := by
    rw [← integral_neg,← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) 8
    · simp only [f,Set.indicator_of_mem hx]
      rw [EReal.toReal_toENNReal (by simpa using EReal.neg_le_neg_iff.mpr (hneg x (hball hx))),EReal.toReal_neg_eq]
      ring
    · simp only [f,Set.indicator_of_notMem hx,ENNReal.toReal_zero,zero_mul]
  rw [he] at hh
  exact neg_nonpos.mp hh

end SharpNodal.Profiles

end
end
end
end
end
end
end
end

end OAI
