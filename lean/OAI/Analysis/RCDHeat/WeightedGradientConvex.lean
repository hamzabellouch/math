import Mathlib
import OAI.Analysis.RCDHeat.EntropyWassersteinGeodesic
import OAI.Analysis.RCDHeat.CompactKantorovich
import OAI.Analysis.RCDHeat.SobolevTestPlan
import OAI.Analysis.RCDHeat.KantorovichRadius

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedGradientConvex, WeightedGradientDerivative, KantorovichVariationBound, KantorovichVariation. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

 

 theorem convex_summand_differentiable {F H : ℝ → ℝ}
    (hF : ConvexOn ℝ univ F) (hH : ConvexOn ℝ univ H) {x : ℝ}
    (hd : DifferentiableAt ℝ (fun t => F t+H t) x) : DifferentiableAt ℝ F x := by
  have hx : x ∈ interior (univ : Set ℝ) := by simp
  have hFL := hF.hasDerivWithinAt_leftDeriv_of_mem_interior hx
  have hFR := hF.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  have hHL := hH.hasDerivWithinAt_leftDeriv_of_mem_interior hx
  have hHR := hH.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  have heL := (hFL.add hHL).derivWithin (uniqueDiffWithinAt_Iio x)
  have heR := (hFR.add hHR).derivWithin (uniqueDiffWithinAt_Ioi x)
  have heLd := hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)
  have heRd := hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)
  change derivWithin (fun t => F t+H t) (Iio x) x = _ at heL
  change derivWithin (fun t => F t+H t) (Ioi x) x = _ at heR
  have hleF := hF.leftDeriv_le_rightDeriv_of_mem_interior hx
  have hleH := hH.leftDeriv_le_rightDeriv_of_mem_interior hx
  have he : derivWithin F (Iio x) x = derivWithin F (Ioi x) x := by linarith
  have hder : HasDerivAt F (derivWithin F (Ioi x) x) x := by
    apply hasDerivAt_iff_tendsto_slope_left_right.mpr
    rw [he] at hFL
    exact ⟨(hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hFL,
      (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hFR⟩
  exact hder.differentiableAt

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

noncomputable def weightedGradientSquare (ν : Measure X) (f : SobolevSpace μ hQ) : ℝ :=
  ∫x, SobolevSpace.minimalSlope μ hQ f x^2 ∂ν

 theorem weightedGradientSquare_integrable {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f : SobolevSpace μ hQ) :
    Integrable (fun x => SobolevSpace.minimalSlope μ hQ f x^2) ν := by
  have hm := ((Lp.memLp (SobolevSpace.minimalSlope μ hQ f)).smul_measure hC).mono_measure hν
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm

 theorem weightedGradientSquare_self (f : SobolevSpace μ hQ) :
    weightedGradientSquare μ hQ μ f = 2*SobolevSpace.energy μ hQ f := by
  rw [weightedGradientSquare,integral_sq_Lp,SobolevSpace.minimalSlope_norm_sq]

variable [ProperSpace X]

 theorem weightedGradientSquare_convex {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) :
    ConvexOn ℝ univ (weightedGradientSquare μ hQ ν) := by
  refine ⟨convex_univ,?_⟩
  intro f _ g _ a b ha hb hab
  have hn (u : SobolevSpace μ hQ) : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.minimalSlope μ hQ u x :=
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u)
  have htri := SobolevSpace.minimalSlope_add_le μ hQ (a • f) (b • g)
  rw [SobolevSpace.minimalSlope_smul,SobolevSpace.minimalSlope_smul,
    abs_of_nonneg ha,abs_of_nonneg hb] at htri
  have hpoint : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (a • f+b • g) x^2 ≤
      a*SobolevSpace.minimalSlope μ hQ f x^2+b*SobolevSpace.minimalSlope μ hQ g x^2 := by
    filter_upwards [(Lp.coeFn_le _ _).mpr htri,hn f,hn g,hn (a • f+b • g),
      Lp.coeFn_add (a • SobolevSpace.minimalSlope μ hQ f) (b • SobolevSpace.minimalSlope μ hQ g),
      Lp.coeFn_smul a (SobolevSpace.minimalSlope μ hQ f),
      Lp.coeFn_smul b (SobolevSpace.minimalSlope μ hQ g)] with x ht hf hg hfg hadd hsm hsm'
    simp only [hadd,Pi.add_apply,hsm,hsm',Pi.smul_apply,smul_eq_mul] at ht
    have hs := (sq_le_sq₀ hfg (add_nonneg (mul_nonneg ha hf) (mul_nonneg hb hg))).mpr ht
    have he : a*SobolevSpace.minimalSlope μ hQ f x^2+b*SobolevSpace.minimalSlope μ hQ g x^2 -
        (a*SobolevSpace.minimalSlope μ hQ f x+b*SobolevSpace.minimalSlope μ hQ g x)^2 =
        a*b*(SobolevSpace.minimalSlope μ hQ f x-SobolevSpace.minimalSlope μ hQ g x)^2 := by
      have hb' : b = 1-a := by linarith
      rw [hb']
      ring
    nlinarith only [hs,he,mul_nonneg (mul_nonneg ha hb)
      (sq_nonneg (SobolevSpace.minimalSlope μ hQ f x-SobolevSpace.minimalSlope μ hQ g x))]
  have hi := weightedGradientSquare_integrable μ hQ hC hν
  have hh := integral_mono_ae (hi (a • f+b • g)) (((hi f).const_mul a).add ((hi g).const_mul b))
    (hpoint.filter_mono (Measure.absolutelyContinuous_of_le_smul hν).ae_le)
  simpa only [weightedGradientSquare,Pi.add_apply,integral_add ((hi f).const_mul a) ((hi g).const_mul b),
    integral_const_mul,smul_eq_mul] using hh

 theorem weightedGradientSquare_line_convex {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    ConvexOn ℝ univ (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • g)) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have hh := (weightedGradientSquare_convex μ hQ hC hν).2 (mem_univ (f+x • g))
    (mem_univ (f+y • g)) ha hb hab
  have he : a • (f+x • g)+b • (f+y • g) = f+(a*x+b*y) • g := by
    calc
      _ = (a+b) • f+(a*x+b*y) • g := by module
      _ = _ := by rw [hab,one_smul]
  simpa only [he,smul_eq_mul] using hh
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem weightedGradientSquare_line_differentiable {ν : Measure X} [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) (x : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • g)) x := by
  let ζ : Measure X := C • μ-ν
  have hζ : ζ ≤ C • μ := Measure.sub_le
  have hsum (t : ℝ) : weightedGradientSquare μ hQ ν (f+t • g)+
      weightedGradientSquare μ hQ ζ (f+t • g) =
      C.toReal*(2*SobolevSpace.energy μ hQ f+2*t*energyForm μ hQ f g+
        2*t^2*SobolevSpace.energy μ hQ g) := by
    have hiν := weightedGradientSquare_integrable μ hQ hC hν (f+t • g)
    have hiζ := weightedGradientSquare_integrable μ hQ hC hζ (f+t • g)
    have hmeas : ν+ζ = C • μ := by
      rw [add_comm]
      exact Measure.sub_add_cancel_of_le hν
    rw [weightedGradientSquare,weightedGradientSquare,←integral_add_measure hiν hiζ,hmeas,
      integral_smul_measure]
    change C.toReal*weightedGradientSquare μ hQ μ (f+t • g) = _
    rw [weightedGradientSquare_self]
    have hh := form_sub_smul μ hQ f g (-t)
    simp only [neg_smul,sub_neg_eq_add,neg_sq] at hh
    rw [hh]
    ring
  apply convex_summand_differentiable
    (weightedGradientSquare_line_convex μ hQ hC hν f g)
    (weightedGradientSquare_line_convex μ hQ hC hζ f g)
  have he : (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • g)+
      weightedGradientSquare μ hQ ζ (f+t • g)) =
      (fun t : ℝ => C.toReal*(2*SobolevSpace.energy μ hQ f+2*t*energyForm μ hQ f g+
        2*t^2*SobolevSpace.energy μ hQ g)) := funext hsum
  rw [he]
  fun_prop

 

noncomputable def weightedGradientPair (ν : Measure X) (f g : SobolevSpace μ hQ) : ℝ :=
  deriv (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • g)) 0/2

 theorem weightedGradientSquare_hasDerivAt_zero {ν : Measure X} [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    HasDerivAt (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • g))
      (2*weightedGradientPair μ hQ ν f g) 0 := by
  have he : 2*weightedGradientPair μ hQ ν f g =
      deriv (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • g)) 0 := by
    unfold weightedGradientPair
    ring
  rw [he]
  exact (weightedGradientSquare_line_differentiable μ hQ hC hν f g 0).hasDerivAt

 theorem weightedGradientPair_neg_right {ν : Measure X} [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    weightedGradientPair μ hQ ν f (-g) = -weightedGradientPair μ hQ ν f g := by
  have hi : HasDerivAt (fun t : ℝ => -t) (-1) (0:ℝ) := (hasDerivAt_id (0:ℝ)).neg
  have ho : HasDerivAt (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • g))
      (2*weightedGradientPair μ hQ ν f g) (-(0:ℝ)) := by
    simpa only [neg_zero] using weightedGradientSquare_hasDerivAt_zero μ hQ hC hν f g
  have hd := ho.comp 0 hi
  have he : (fun t : ℝ => weightedGradientSquare μ hQ ν (f+(-t) • g)) =
      (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • (-g))) := by
    funext t
    rw [neg_smul,smul_neg]
  change HasDerivAt (fun t : ℝ => weightedGradientSquare μ hQ ν (f+(-t) • g)) _ _ at hd
  rw [he] at hd
  have hh := hd.deriv
  have hh' := (weightedGradientSquare_hasDerivAt_zero μ hQ hC hν f (-g)).deriv
  linarith
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def planInitialSecant (π : Measure C(Time,X)) (g : X → ℝ) (t : ℝ) : ℝ :=
  (∫γ : C(Time,X),g (geodesicExtension γ t)-g (γ 0) ∂π)/t

 theorem kantorovich_perturbation_increment (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (u g : Lp ℝ 2 μ) {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (ε : ℝ) (t : Time) :
    ((t:ℝ)-(t:ℝ)^2/2)*(∫γ : C(Time,X),dist (γ 0) (γ 1)^2 ∂π) ≤
      ε*(∫γ : C(Time,X),g (γ t)-g (γ 0) ∂π)+
      ∫γ : C(Time,X),|(u+ε • g) (γ t)-(u+ε • g) (γ 0)| ∂π := by
  have hrep (s : Time) : ∀ᵐ γ ∂π, φ (γ s) = u (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp s)).ae_eq hu)
  have hsum (s : Time) : ∀ᵐ γ ∂π, (u+ε • g) (γ s) = u (γ s)+ε*g (γ s) := by
    have hh : ∀ᵐ x ∂μ, (u+ε • g) x = u x+ε*g x := by
      filter_upwards [Lp.coeFn_add u (ε • g),Lp.coeFn_smul ε g] with x ha hs
      simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul]
    exact ae_of_ae_map (measurable_path_eval s).aemeasurable
      (hh.filter_mono (Measure.absolutelyContinuous_of_le_smul (hcomp s)).ae_le)
  have hi (v : Lp ℝ 2 μ) (s : Time) : Integrable (fun γ : C(Time,X) => v (γ s)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) v).integrable (by norm_num)
  have hd2 := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  have hInt := integral_add
    (((hi g t).sub (hi g 0)).const_mul ε) (((hi (u+ε • g) t).sub (hi (u+ε • g) 0)).abs)
  simp only [Pi.sub_apply] at hInt
  rw [←integral_const_mul,←integral_const_mul,←hInt]
  apply integral_mono_ae (hd2.const_mul _)
    ((((hi g t).sub (hi g 0)).const_mul ε).add (((hi (u+ε • g) t).sub (hi (u+ε • g) 0)).abs))
  filter_upwards [hgeo,hc,hrep 0,hrep t,hsum 0,hsum t] with γ hg hc h0 ht hs0 hst
  have hh := hg.kantorovich_increment had hc t
  rw [h0,ht] at hh
  simp only [Pi.add_apply,Pi.sub_apply,hst,hs0]
  have hb := neg_le_abs ((u (γ t)+ε*g (γ t))-(u (γ 0)+ε*g (γ 0)))
  linarith

variable [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem kantorovich_directional_lower_bound
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (f g : SobolevSpace μ hQ) {φ ψ : X → ℝ} (hf : φ =ᵐ[μ] SobolevSpace.toLp μ hQ f)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      ((∫γ : C(Time,X),dist (γ 0) (γ 1)^2 ∂π)-
        weightedGradientSquare μ hQ (π.map (fun γ => γ 0)) (f+ε • g))/(2*ε)-δ <
      planInitialSecant π (SobolevSpace.toLp μ hQ g) t := by
  let v := f+ε • g
  let A := ∫γ : C(Time,X),dist (γ 0) (γ 1)^2 ∂π
  let J := ∫γ : C(Time,X),dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ hQ v (γ 0) ∂π
  let E := weightedGradientSquare μ hQ (π.map (fun γ => γ 0)) v
  have hiG : MemLp (fun γ : C(Time,X) => SobolevSpace.minimalSlope μ hQ v (γ 0)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) _
  have hiD2 := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  have hiG2 := (memLp_two_iff_integrable_sq hiG.aestronglyMeasurable).mp hiG
  have hEmap : E = ∫γ : C(Time,X),SobolevSpace.minimalSlope μ hQ v (γ 0)^2 ∂π := by
    exact integral_map (measurable_path_eval 0).aemeasurable
      (((Lp.stronglyMeasurable _).pow 2).aestronglyMeasurable)
  have hJ : J ≤ (A+E)/2 := by
    have hh := integral_mono ((hD.integrable_mul hiG).const_mul 2) (hiD2.add hiG2)
      (fun γ => show 2*(dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ hQ v (γ 0)) ≤
        dist (γ 0) (γ 1)^2+SobolevSpace.minimalSlope μ hQ v (γ 0)^2 by
          nlinarith only [sq_nonneg (dist (γ 0) (γ 1)-SobolevSpace.minimalSlope μ hQ v (γ 0))])
    simp only [integral_const_mul,integral_add hiD2 hiG2,Pi.add_apply] at hh
    rw [←hEmap] at hh
    change 2*J ≤ A+E at hh
    linarith
  have htend : Tendsto (fun t : ℝ => ((1-t/2)*A-J)/ε) (𝓝[>] (0:ℝ)) (𝓝 ((A-J)/ε)) := by
    have hcont : Continuous (fun t : ℝ => ((1-t/2)*A-J)/ε) := by fun_prop
    simpa only [zero_div,sub_zero,one_mul] using
      (hcont.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ t in 𝓝[>] (0:ℝ), (A-J)/ε-δ/2 < ((1-t/2)*A-J)/ε :=
    htend.eventually (lt_mem_nhds (by linarith))
  have hbound := (SobolevSpace.minimalSlope_isRelaxed μ hQ v).testPlan_initial_bound
    μ π hgeo hC hcomp hD (show 0 < ε*δ/2 by positivity)
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear,hbound,hsmall,self_mem_nhdsWithin] with t ht hb ht1 ht0
  change 0 < t at ht0
  have h01 : t ∈ Icc (0:ℝ) 1 := ⟨ht0.le,ht1.le⟩
  have hge (γ : C(Time,X)) : geodesicExtension γ t = γ (⟨t,h01⟩:Time) :=
    geodesicExtension_eq γ (⟨t,h01⟩:Time)
  have hi := kantorovich_perturbation_increment μ π hgeo hC hcomp hD
    (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g) hf had hc ε (⟨t,h01⟩:Time)
  have hv : SobolevSpace.toLp μ hQ v = SobolevSpace.toLp μ hQ f+ε • SobolevSpace.toLp μ hQ g := by
    simp only [v,map_add,map_smul]
  rw [hv] at hb
  simp_rw [hge] at hb
  have hi' := (div_le_div_of_nonneg_right hi ht0.le)
  change ((t-t^2/2)*A)/t ≤ _ at hi'
  rw [add_div] at hi'
  have hefac : (t-t^2/2)*A/t = (1-t/2)*A := by field_simp [ht0.ne']
  rw [hefac,mul_div_assoc ε] at hi'
  change (A-E)/(2*ε)-δ < _
  dsimp only [planInitialSecant]
  simp_rw [hge]
  have hleft : (A-E)/(2*ε) ≤ (A-J)/ε := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*ε) hε).mpr
    nlinarith
  have hht := (lt_div_iff₀ hε).mp ht
  have hb' : (∫γ : C(Time,X),|(SobolevSpace.toLp μ hQ f+ε • SobolevSpace.toLp μ hQ g) (γ (⟨t,h01⟩:Time))-
      (SobolevSpace.toLp μ hQ f+ε • SobolevSpace.toLp μ hQ g) (γ 0)| ∂π)/t < J+ε*δ/2 := hb
  have hmid : (A-J)/ε-δ <
      (∫γ : C(Time,X),SobolevSpace.toLp μ hQ g (γ (⟨t,h01⟩:Time))-SobolevSpace.toLp μ hQ g (γ 0) ∂π)/t := by
    apply (mul_lt_mul_iff_of_pos_left hε).mp
    nlinarith [div_mul_cancel₀ (A-J) hε.ne']
  exact (sub_le_sub_right hleft δ).trans_lt hmid
end

 
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

omit [μ.Regular] in
 theorem weightedGradientPair_secant_limit {ν : Measure X} [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) :
    Tendsto (fun ε : ℝ => (weightedGradientSquare μ hQ ν f-
      weightedGradientSquare μ hQ ν (f+ε • g))/(2*ε))
      (𝓝[>] (0:ℝ)) (𝓝 (-weightedGradientPair μ hQ ν f g)) := by
  have hd := (weightedGradientSquare_hasDerivAt_zero μ hQ hC hν f g).tendsto_slope
  rw [slope_fun_def_field] at hd
  simp only [sub_zero,zero_smul,add_zero] at hd
  have ht := (hd.neg.div_const 2).mono_left
    (nhdsWithin_mono (0:ℝ) (show Ioi (0:ℝ) ⊆ {(0:ℝ)}ᶜ from fun _ hx => ne_of_gt hx))
  convert ht using 1
  · funext ε
    ring
  · congr 1
    ring

 theorem kantorovich_directional_eventually_gt
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (f g : SobolevSpace μ hQ) {φ ψ : X → ℝ} (hf : φ =ᵐ[μ] SobolevSpace.toLp μ hQ f)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hE : weightedGradientSquare μ hQ (π.map (fun γ => γ 0)) f =
      ∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π)
    {a : ℝ} (ha : a < -weightedGradientPair μ hQ (π.map (fun γ => γ 0)) f g) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), a < planInitialSecant π (SobolevSpace.toLp μ hQ g) t := by
  let ν := π.map (fun γ => γ 0)
  let b := -weightedGradientPair μ hQ ν f g
  let δ := (b-a)/2
  have hδ : 0 < δ := by dsimp only [δ,b,ν]; linarith
  have ht := weightedGradientPair_secant_limit μ hQ hC (hcomp 0) f g
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), a+δ < (weightedGradientSquare μ hQ ν f-
      weightedGradientSquare μ hQ ν (f+ε • g))/(2*ε) :=
    ht.eventually (lt_mem_nhds (by dsimp only [δ]; change a+(b-a)/2 < b; linarith))
  have hpos : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hεpos,hε⟩ := (hpos.and hev).exists
  have hh := kantorovich_directional_lower_bound μ hQ π hgeo hC hcomp hD f g hf had hc hεpos hδ
  rw [hE] at hε
  filter_upwards [hh] with t ht
  linarith

omit [ProperSpace X] [μ.Regular] in
 theorem planInitialSecant_neg_sobolev
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (g : SobolevSpace μ hQ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    planInitialSecant π (SobolevSpace.toLp μ hQ (-g)) t =
      -planInitialSecant π (SobolevSpace.toLp μ hQ g) t := by
  have hp (s : Time) : ∀ᵐ γ ∂π, SobolevSpace.toLp μ hQ (-g) (γ s) =
      -SobolevSpace.toLp μ hQ g (γ s) := by
    have hh : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ (-g) x = -SobolevSpace.toLp μ hQ g x := by
      rw [map_neg]
      exact Lp.coeFn_neg _
    exact ae_of_ae_map (measurable_path_eval s).aemeasurable
      (hh.filter_mono (Measure.absolutelyContinuous_of_le_smul (hcomp s)).ae_le)
  have he : (fun γ : C(Time,X) => SobolevSpace.toLp μ hQ (-g) (geodesicExtension γ t)-
      SobolevSpace.toLp μ hQ (-g) (γ 0)) =ᵐ[π]
    (fun γ : C(Time,X) => -(SobolevSpace.toLp μ hQ g (geodesicExtension γ t)-
      SobolevSpace.toLp μ hQ g (γ 0))) := by
    filter_upwards [hp (⟨t,ht⟩:Time),hp 0] with γ hγ h0
    rw [geodesicExtension_eq γ (⟨t,ht⟩:Time),hγ,h0]
    ring
  dsimp only [planInitialSecant]
  rw [integral_congr_ae he,integral_neg,neg_div]

 

 theorem kantorovich_signed_first_variation
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (f g : SobolevSpace μ hQ) {φ ψ : X → ℝ} (hf : φ =ᵐ[μ] SobolevSpace.toLp μ hQ f)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ f (γ 0) ≤ dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π (SobolevSpace.toLp μ hQ g)) (𝓝[>] (0:ℝ))
      (𝓝 (-weightedGradientPair μ hQ (π.map (fun γ => γ 0)) f g)) := by
  have hid := (SobolevSpace.minimalSlope_isRelaxed μ hQ f).kantorovich_gradient_eq_displacement
    μ π hgeo hC hcomp hD hf had hc hb
  have hE : weightedGradientSquare μ hQ (π.map (fun γ => γ 0)) f =
      ∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π := by
    calc
      _ = ∫γ : C(Time,X), SobolevSpace.minimalSlope μ hQ f (γ 0)^2 ∂π := by
        exact integral_map (measurable_path_eval 0).aemeasurable
          (((Lp.stronglyMeasurable _).pow 2).aestronglyMeasurable)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hid] with γ hγ
        rw [hγ]
  apply tendsto_order.mpr
  refine ⟨fun a ha => kantorovich_directional_eventually_gt μ hQ π hgeo hC hcomp hD f g hf had hc hE ha,?_⟩
  intro a ha
  have haa : -a < -weightedGradientPair μ hQ (π.map (fun γ => γ 0)) f (-g) := by
    rw [weightedGradientPair_neg_right μ hQ hC (hcomp 0)]
    linarith
  have hh := kantorovich_directional_eventually_gt μ hQ π hgeo hC hcomp hD f (-g) hf had hc hE haa
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hh,hsmall,self_mem_nhdsWithin] with t ht ht1 ht0
  rw [planInitialSecant_neg_sobolev μ hQ π hcomp g ⟨ht0.le,ht1.le⟩] at ht
  linarith

end RegularPointCoordinates

end OAI
