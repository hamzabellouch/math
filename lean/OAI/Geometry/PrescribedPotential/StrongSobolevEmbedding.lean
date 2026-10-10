import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevEmbedding
import OAI.Geometry.PrescribedPotential.SobolevParametrix

namespace OAI

/-! Strong Sobolev Embedding. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction ContDiff
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def boundedToLinfLinear : (E →ᵇ ℂ) →ₗ[ℂ] Lp ℂ ⊤ (volume : Measure E) where
  toFun f := f.memLp_top.toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma boundedToLinf_norm (f : E →ᵇ ℂ) : ‖boundedToLinfLinear f‖ ≤ ‖f‖ := by
  rw [show boundedToLinfLinear f = f.memLp_top.toLp f from rfl, Lp.norm_toLp,
    eLpNorm_exponent_top f.memLp_top.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
    (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall f.norm_coe_le_norm))

def boundedToLinf : (E →ᵇ ℂ) →L[ℂ] Lp ℂ ⊤ (volume : Measure E) :=
  boundedToLinfLinear.mkContinuous 1 (fun f => by simpa using boundedToLinf_norm f)

lemma boundedToLinf_injective : Function.Injective (boundedToLinf (E := E)) := by
  intro f g h
  apply DFunLike.coe_injective
  apply (f.continuous.ae_eq_iff_eq volume g.continuous).mp
  exact (f.memLp_top.coeFn_toLp).symm.trans ((show
    (f.memLp_top.toLp f : E → ℂ) =ᵐ[volume] (g.memLp_top.toLp g : E → ℂ) by rw [show
      f.memLp_top.toLp f = g.memLp_top.toLp g from h]).trans g.memLp_top.coeFn_toLp)

def boundedDistributionCLM : (E →ᵇ ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  Lp.toTemperedDistributionCLM ℂ volume ⊤ ∘L boundedToLinf

lemma boundedDistributionCLM_apply (f : E →ᵇ ℂ) :
    boundedDistributionCLM f = boundedDistribution f := rfl

lemma boundedDistribution_injective : Function.Injective (boundedDistributionCLM (E := E)) :=
  (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (E := E) (μ := volume) (p := ⊤))).comp boundedToLinf_injective

lemma strong_representation (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s) (u : L2 E) :
    ∃ f : E →ᵇ ℂ, boundedDistributionCLM f = realize s u := by
  obtain ⟨v,hv⟩ := (realize_memSobolev s u).fourier_memL1 hs
  refine ⟨Real.Lp.fourierTransformInv v, ?_⟩
  rw [boundedDistributionCLM_apply, fourierInv_L1_distribution, ← hv, fourierInv_fourier_eq]

def strongRepresentative (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s) (u : L2 E) : E →ᵇ ℂ :=
  (strong_representation s hs u).choose

lemma strongRepresentative_distribution (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s) (u : L2 E) :
    boundedDistributionCLM (strongRepresentative s hs u) = realize s u :=
  (strong_representation s hs u).choose_spec

def strongRepresentativeLinear (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s) :
    L2 E →ₗ[ℂ] (E →ᵇ ℂ) where
  toFun := strongRepresentative s hs
  map_add' u v := by
    apply boundedDistribution_injective
    simp only [strongRepresentative_distribution, map_add]
  map_smul' c u := by
    apply boundedDistribution_injective
    simp only [strongRepresentative_distribution, map_smul, RingHom.id_apply]

 
def strongEmbedding (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s) :
    L2 E →L[ℂ] (E →ᵇ ℂ) where
  toLinearMap := strongRepresentativeLinear s hs
  cont := by
    apply LinearMap.continuous_of_seq_closed_graph
    intro u x y hu hv
    apply boundedDistribution_injective
    have h₁ := ((boundedDistributionCLM (E := E)).continuous.tendsto y).comp hv
    have h₂ := ((realize (E := E) s).continuous.tendsto x).comp hu
    change Tendsto (fun n => boundedDistributionCLM (strongRepresentative s hs (u n)))
      atTop (nhds (boundedDistributionCLM y)) at h₁
    simp_rw [strongRepresentative_distribution] at h₁
    exact (tendsto_nhds_unique h₁ h₂).trans (strongRepresentative_distribution s hs x).symm

lemma strongEmbedding_distribution (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s) (u : L2 E) :
    boundedDistributionCLM (strongEmbedding s hs u) = realize s u :=
  strongRepresentative_distribution s hs u

lemma strongEmbedding_norm (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s) (u : L2 E) (x : E) :
    ‖strongEmbedding s hs u x‖ ≤ ‖strongEmbedding (E := E) s hs‖ * ‖u‖ :=
  ((strongEmbedding s hs u).norm_coe_le_norm x).trans ((strongEmbedding s hs).le_opNorm u)

end SobolevChart

end
end

end OAI
