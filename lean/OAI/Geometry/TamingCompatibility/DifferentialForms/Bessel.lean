import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalInverse

namespace OAI

noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction
namespace TamingCompatibility.RellichWeight
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bessel (s : ℝ) (hs : 0 ≤ s) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ((1+‖x‖^2)^(-s/2) : ℝ)) (Complex.continuous_ofReal.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-s/2)).1.continuous) 1 (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith))

lemma bessel_decay (s : ℝ) (hs : 0 < s) :
    ∀ ε > 0, ∃ R ≥ 0, ∀ ξ : E, R < ‖ξ‖ → ‖bessel s hs.le ξ‖ ≤ ε := by
  intro ε hε
  have ht : Tendsto (fun r : ℝ => (1+r^2)^(-s/2)) atTop (𝓝 0) := by
    have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
    convert (tendsto_rpow_neg_atTop (div_pos hs (by norm_num : (0:ℝ)<2))).comp hp using 1
    simp only [Function.comp_def, neg_div]
  obtain ⟨R,hR⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro ξ hξ
  change ‖(((1+‖ξ‖^2)^(-s/2) : ℝ) : ℂ)‖ ≤ ε
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (hR ‖ξ‖ ((le_max_left _ _).trans hξ.le)).le

end TamingCompatibility.RellichWeight

end

noncomputable section
namespace TamingCompatibility.LocalRellich
open MeasureTheory HilbertSobolev LocalRestriction
open scoped ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def realize (K : Set E) (hK : MeasurableSet K) {s : ℝ} (hs : 0 ≤ s) :
    H E F s →L[ℝ] Lp F 2 (localMeasure volume K) :=
  restrict volume K hK ∘L (inclusion hs).restrictScalars ℝ

theorem realize_compact [ProperSpace F] (K : Set E) (hK : IsCompact K)
    {s : ℝ} (hs : 0 < s) : IsCompactOperator (realize (F := F) K hK.measurableSet hs.le) := by
  have hc := localInverse_compact_of_decay (F := F) K hK
    (RellichWeight.bessel (E := E) s hs.le) (RellichWeight.bessel_decay s hs)
  have hcomp := hc.comp_clm
    ((Lp.fourierTransformₗᵢ E F).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
  convert hcomp using 1
  funext u
  change restrict volume K hK.measurableSet
      ((Lp.fourierTransformₗᵢ E F).symm
        (((weight_memLp_top (E := E) (sub_nonpos.mpr hs.le)).toLp (weight (E := E) (0 - s))) •
          (Lp.fourierTransformₗᵢ E F) u)) =
    restrict volume K hK.measurableSet
      ((Lp.fourierTransformₗᵢ E F).symm
        ((((RellichWeight.bessel (E := E) s hs.le).memLp_top (μ := volume)).toLp (RellichWeight.bessel (E := E) s hs.le)) •
          (Lp.fourierTransformₗᵢ E F) u))
  congr 3
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (weight_memLp_top (E := E) (sub_nonpos.mpr hs.le)),
    MemLp.coeFn_toLp ((RellichWeight.bessel (E := E) s hs.le).memLp_top (μ := volume))] with ξ h1 h2
  rw [h1, h2]
  simp [weight, RellichWeight.bessel]

end TamingCompatibility.LocalRellich

namespace TamingCompatibility.LocalRestriction
open MeasureTheory Set
open scoped RealInnerProductSpace
variable {E F : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def restore (μ : Measure E) (K : Set E) (hK : MeasurableSet K) :
    Lp F 2 (localMeasure μ K) →L[ℝ] Lp F 2 μ :=
  ContinuousLinearMap.adjoint (restrict μ K hK)

lemma restore_restrict (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (u : Lp F 2 μ) (hu : ∀ᵐ x ∂μ, x ∉ K → u x = 0) :
    restore μ K hK (restrict μ K hK u) = u := by
  apply ext_inner_left ℝ
  intro v
  rw [restore, ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
  calc
    (∫ x : K, ⟪restrict μ K hK v x, restrict μ K hK u x⟫ ∂localMeasure μ K) =
        ∫ x : K, ⟪v x, u x⟫ ∂localMeasure μ K := by
      apply integral_congr_ae
      filter_upwards [restrict_coe μ K hK v, restrict_coe μ K hK u] with x hv hx
      rw [hv, hx]
    _ = ∫ x in K, ⟪v x, u x⟫ ∂μ := integral_subtype_comap (μ := μ) hK (fun x => ⟪v x, u x⟫)
    _ = ∫ x, ⟪v x, u x⟫ ∂μ := by
      rw [← integral_indicator hK]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      by_cases h : x ∈ K
      · exact indicator_of_mem h _
      · rw [indicator_of_notMem h, hx h, inner_zero_right]

end TamingCompatibility.LocalRestriction


namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma liftOperator_exists {s t : ℝ} (A : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hA : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (A u)) (u : H E F s) :
    ∃ v : H E F t, toDistribution E F t v = A (toDistribution E F s u) := by
  change A (toDistribution E F s u) ∈ Set.range (toDistribution E F t)
  rw [range_toDistribution]
  exact hA _ (toDistribution_memSobolev s u)

def liftOperator {s t : ℝ} (A : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hA : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (A u)) :
    H E F s →L[ℂ] H E F t := by
  let hex := liftOperator_exists A hA
  let L : H E F s →ₗ[ℂ] H E F t :=
    { toFun := fun u => (hex u).choose
      map_add' := fun u v => by
        apply toDistribution_injective t
        rw [(hex (u+v)).choose_spec, map_add, map_add, map_add,
          (hex u).choose_spec, (hex v).choose_spec]
      map_smul' := fun c u => by
        apply toDistribution_injective t
        rw [(hex (c • u)).choose_spec, map_smul, map_smul, map_smul,
          (hex u).choose_spec]
        rfl }
  apply ContinuousLinearMap.ofIsClosedGraph (g := L)
  have hg : (L.graph : Set (H E F s × H E F t)) =
      {p | toDistribution E F t p.2 = A (toDistribution E F s p.1)} := by
    ext p
    change p.2 = L p.1 ↔ toDistribution E F t p.2 = A (toDistribution E F s p.1)
    rw [← (hex p.1).choose_spec]
    exact (toDistribution_injective t).eq_iff.symm
  rw [hg]
  exact isClosed_eq ((toDistribution E F t).continuous.comp continuous_snd)
    (A.continuous.comp ((toDistribution E F s).continuous.comp continuous_fst))

lemma toDistribution_liftOperator {s t : ℝ} (A : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hA : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (A u)) (u : H E F s) :
    toDistribution E F t (liftOperator A hA u) = A (toDistribution E F s u) := by
  dsimp only [liftOperator, ContinuousLinearMap.ofIsClosedGraph,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact (liftOperator_exists A hA u).choose_spec

open scoped LineDeriv

def derivative (s : ℝ) (v : E) : H E F s →L[ℂ] H E F (s-1) :=
  liftOperator (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E,F) v) (fun _ h => h.lineDerivOp)

lemma toDistribution_derivative (s : ℝ) (v : E) (u : H E F s) :
    toDistribution E F (s-1) (derivative s v u) = ∂_{v} (toDistribution E F s u) :=
  toDistribution_liftOperator _ _ _

end TamingCompatibility.HilbertSobolev

end

end OAI
