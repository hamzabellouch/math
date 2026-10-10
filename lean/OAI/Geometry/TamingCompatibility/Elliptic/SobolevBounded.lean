import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ClosedGraphLift
import OAI.Geometry.TamingCompatibility.Elliptic.SchwartzSobolev

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def boundedToLpTop : (E →ᵇ F) →L[ℂ] Lp F ⊤ (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun f => (f.memLp_top (μ := volume)).toLp f
      map_add' := fun f g => by
        ext1
        filter_upwards [(f+g).memLp_top.coeFn_toLp,f.memLp_top.coeFn_toLp,
          g.memLp_top.coeFn_toLp,Lp.coeFn_add (f.memLp_top.toLp f) (g.memLp_top.toLp g)] with x h1 h2 h3 h4
        simp only [h1,h4,Pi.add_apply,h2,h3,BoundedContinuousFunction.add_apply]
      map_smul' := fun c f => by
        ext1
        filter_upwards [(c • f).memLp_top.coeFn_toLp,f.memLp_top.coeFn_toLp,
          Lp.coeFn_smul c (f.memLp_top.toLp f)] with x h1 h2 h3
        simp only [h1,h3,Pi.smul_apply,h2,BoundedContinuousFunction.smul_apply,RingHom.id_apply] }
    1 (fun f => by
      change ‖(f.memLp_top (μ := volume)).toLp f‖ ≤ 1 * ‖f‖
      rw [one_mul,Lp.norm_toLp,
        eLpNorm_exponent_top (f.memLp_top (μ := volume)).aestronglyMeasurable]
      have hle := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure E))
        (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
      exact (ENNReal.toReal_mono (by finiteness) hle).trans_eq
        (ENNReal.toReal_ofReal (norm_nonneg f)))

omit [CompleteSpace F] in
lemma boundedToLpTop_injective : Function.Injective (boundedToLpTop (E := E) (F := F)) := by
  intro f g h
  apply DFunLike.coe_injective
  apply (f.continuous.ae_eq_iff_eq (volume : Measure E) g.continuous).mp
  have he := Lp.ext_iff.mp h
  exact f.memLp_top.coeFn_toLp.symm.trans (he.trans g.memLp_top.coeFn_toLp)

def boundedDistributionCLM : (E →ᵇ F) →L[ℂ] 𝓢'(E,F) :=
  (Lp.toTemperedDistributionCLM F volume ⊤).comp boundedToLpTop

lemma boundedDistributionCLM_apply (f : E →ᵇ F) :
    boundedDistributionCLM f = boundedDistribution f := rfl

lemma boundedDistributionCLM_injective :
    Function.Injective (boundedDistributionCLM (E := E) (F := F)) := by
  intro f g h
  apply boundedToLpTop_injective
  exact (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) h

def sobolevToBounded (s : ℝ) (hs : Module.finrank ℝ E < 2*s) :
    HilbertSobolev.H E F s →L[ℂ] (E →ᵇ F) :=
  InjectiveLinearLift.continuousLift boundedDistributionCLM boundedDistributionCLM_injective
    (HilbertSobolev.toDistribution E F s) (fun u => by
      obtain ⟨g,hg⟩ := exists_boundedContinuous_representative hs
        (HilbertSobolev.toDistribution_memSobolev s u)
      exact ⟨g,hg.symm⟩)

lemma sobolevToBounded_spec (s : ℝ) (hs : Module.finrank ℝ E < 2*s)
    (u : HilbertSobolev.H E F s) :
    boundedDistribution (sobolevToBounded s hs u) = HilbertSobolev.toDistribution E F s u := by
  change boundedDistributionCLM (sobolevToBounded s hs u) = _
  exact InjectiveLinearLift.continuousLift_spec _ _ _ _ _
end TamingCompatibility.EuclideanSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma boundedDistribution_schwartz (f : 𝓢(E,F)) :
    boundedDistribution f.toBoundedContinuousFunction = (f : 𝓢'(E,F)) := by
  ext φ
  rw [boundedDistribution_apply,SchwartzMap.toTemperedDistributionCLM_apply_apply volume f φ]
  rfl

lemma sobolevToBounded_schwartz (s : ℝ) (hs : Module.finrank ℝ E < 2*s) (f : 𝓢(E,F)) :
    sobolevToBounded s hs (schwartzToH s f) = f.toBoundedContinuousFunction := by
  apply boundedDistributionCLM_injective
  rw [boundedDistributionCLM_apply,boundedDistributionCLM_apply,sobolevToBounded_spec,
    schwartzToH_spec,boundedDistribution_schwartz]

lemma schwartz_sobolev_bound (s : ℝ) (hs : Module.finrank ℝ E < 2*s) (f : 𝓢(E,F)) (x : E) :
    ‖f x‖ ≤ ‖sobolevToBounded (E := E) (F := F) s hs‖ * ‖schwartzToH s f‖ := by
  calc
    ‖f x‖ ≤ ‖f.toBoundedContinuousFunction‖ := f.toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖sobolevToBounded s hs (schwartzToH s f)‖ := congrArg norm (sobolevToBounded_schwartz s hs f).symm
    _ ≤ _ := (sobolevToBounded (E := E) (F := F) s hs).le_opNorm (schwartzToH s f)

lemma schwartzToH_derivative (s : ℝ) (v : E) (f : 𝓢(E,F)) :
    schwartzToH (s-1) (∂_{v} f) = derivative s v (schwartzToH s f) := by
  apply toDistribution_injective (s-1)
  rw [schwartzToH_spec,toDistribution_derivative,schwartzToH_spec]
  exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq f v).symm

lemma schwartz_second_derivative_bound (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1-1)) (v w : E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖(∂_{w} (∂_{v} f)) x‖ ≤ K * ‖schwartzToH s f‖ := by
  let T := (sobolevToBounded (E := E) (F := F) (s-1-1) hs).comp
    ((derivative (s-1) w).comp (derivative s v))
  refine ⟨‖T‖,norm_nonneg T,fun f x => ?_⟩
  have he : sobolevToBounded (s-1-1) hs
      (derivative (s-1) w (derivative s v (schwartzToH s f))) =
      (∂_{w} (∂_{v} f)).toBoundedContinuousFunction := by
    rw [← schwartzToH_derivative,← schwartzToH_derivative]
    exact sobolevToBounded_schwartz (s-1-1) hs _
  calc
    ‖(∂_{w} (∂_{v} f)) x‖ ≤ ‖(∂_{w} (∂_{v} f)).toBoundedContinuousFunction‖ :=
      (∂_{w} (∂_{v} f)).toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖T (schwartzToH s f)‖ := congrArg norm he.symm
    _ ≤ _ := T.le_opNorm _

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_first_derivative_bound (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1)) (v : E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖(∂_{v} f) x‖ ≤ K * ‖schwartzToH s f‖ := by
  let T := (sobolevToBounded (E := E) (F := F) (s-1) hs).comp (derivative s v)
  refine ⟨‖T‖,norm_nonneg T,fun f x => ?_⟩
  have he : sobolevToBounded (s-1) hs (derivative s v (schwartzToH s f)) =
      (∂_{v} f).toBoundedContinuousFunction := by
    rw [← schwartzToH_derivative]
    exact sobolevToBounded_schwartz (s-1) hs _
  calc
    ‖(∂_{v} f) x‖ ≤ ‖(∂_{v} f).toBoundedContinuousFunction‖ :=
      (∂_{v} f).toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖T (schwartzToH s f)‖ := congrArg norm he.symm
    _ ≤ _ := T.le_opNorm _

lemma schwartz_two_jet_bound {ι : Type*} [Fintype ι] (v : ι → E) (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1-1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖f x‖ + ∑ i, ‖(∂_{v i} f) x‖ + ∑ i, ∑ j, ‖(∂_{v j} (∂_{v i} f)) x‖ ≤
        K * ‖schwartzToH s f‖ := by
  classical
  have hs₀ : Module.finrank ℝ E < 2*s := by linarith
  have hs₁ : Module.finrank ℝ E < 2*(s-1) := by linarith
  let C := ‖sobolevToBounded (E := E) (F := F) s hs₀‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  choose K₁ hK₁ hb₁ using fun i => schwartz_first_derivative_bound (F := F) s hs₁ (v i)
  choose K₂ hK₂ hb₂ using fun i j => schwartz_second_derivative_bound (F := F) s hs (v i) (v j)
  refine ⟨C + ∑ i, K₁ i + ∑ i, ∑ j, K₂ i j,
    add_nonneg (add_nonneg hC (Finset.sum_nonneg (fun i _ => hK₁ i)))
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hK₂ i j))),fun f x => ?_⟩
  have h0 := schwartz_sobolev_bound s hs₀ f x
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb₁ i f x)
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb₂ i j f x))
  calc
    _ ≤ C * ‖schwartzToH s f‖ + (∑ i, K₁ i * ‖schwartzToH s f‖) +
        ∑ i, ∑ j, K₂ i j * ‖schwartzToH s f‖ := add_le_add (add_le_add h0 h1) h2
    _ = _ := by simp only [add_mul,Finset.sum_mul]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
