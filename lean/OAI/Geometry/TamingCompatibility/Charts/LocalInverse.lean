import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.SobolevSpace
import OAI.Geometry.TamingCompatibility.DifferentialForms.Kernel
import OAI.Geometry.TamingCompatibility.Currents.LocalMeasure

namespace OAI

section
section
section
section
noncomputable section
namespace TamingCompatibility.LocalRellich
open LocalRestriction HilbertSobolev FourierCutoff FourierIdentification
open MeasureTheory FourierTransform
open scoped ENNReal RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def localInverse (K : Set E) (hK : MeasurableSet K)
    (g : Lp ℂ ∞ (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℝ] Lp F 2 (localMeasure volume K) :=
  restrict volume K hK ∘L
    ((Lp.fourierTransformₗᵢ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) ∘L
      (multiplyLp g).restrictScalars ℝ

lemma localInverse_norm_le (K : Set E) (hK : MeasurableSet K)
    (g : Lp ℂ ∞ (volume : Measure E)) (u : Lp F 2 (volume : Measure E)) :
    ‖localInverse K hK g u‖ ≤ ‖g‖ * ‖u‖ := by
  change ‖restrict volume K hK (𝓕⁻ (g • u : Lp F 2 (volume : Measure E)))‖ ≤ _
  apply (restrict_norm_le volume K hK _).trans
  change ‖(Lp.fourierTransformₗᵢ E F).symm (g • u)‖ ≤ _
  rw [(Lp.fourierTransformₗᵢ E F).symm.norm_map]
  exact Lp.norm_smul_le g u

theorem localInverse_compact_of_support [ProperSpace F]
    (K : Set E) (hK : IsCompact K)
    (g : Lp ℂ ∞ (volume : Measure E)) (g₂ : Lp ℂ 2 (volume : Measure E))
    (heq : g₂ =ᵐ[volume] g) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g₂ ξ = 0) :
    IsCompactOperator (localInverse (F := F) K hK.measurableSet g) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (localMeasure (volume : Measure E) K) :=
    finite_localMeasure volume K hK.measurableSet hK.measure_lt_top
  let loc : C(K,E) := ⟨Subtype.val, continuous_subtype_val⟩
  let A := CompactKernel.operator (kernel (F := F) loc g₂ hR hs)
  let B := BoundedContinuousFunction.toLp (E := F) 2 (localMeasure (volume : Measure E) K) ℝ
  have hA : IsCompactOperator (A.restrictScalars ℝ) := compact_inverse_cutoff loc g₂ hR hs
  have hcomp : IsCompactOperator (B ∘L A.restrictScalars ℝ) := hA.clm_comp B
  convert hcomp using 1
  ext u
  have hmult : multiply g₂ u =ᵐ[volume] multiplyLp g u := by
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) g₂ u,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) g u, heq] with ξ h1 h2 h3
    change (g₂ • u : Lp F 1 (volume : Measure E)) ξ =
      (g • u : Lp F 2 (volume : Measure E)) ξ
    rw [h1,h2]
    change g₂ ξ • u ξ = g ξ • u ξ
    rw [h3]
  have hi := inverse_L1_L2 (multiply g₂ u) (multiplyLp g u) hmult
  have hil := (measurePreserving_subtype_coe (μa := (volume : Measure E))
    hK.measurableSet).quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hi)
  filter_upwards [restrict_coe volume K hK.measurableSet
    (𝓕⁻ (g • u : Lp F 2 (volume : Measure E))),
    BoundedContinuousFunction.coeFn_toLp 2 (localMeasure (volume : Measure E) K) ℝ (A u),
    hil] with x h1 h2 h3
  change restrict volume K hK.measurableSet (𝓕⁻ (g • u : Lp F 2 (volume : Measure E))) x = B (A u) x
  rw [h1,h2]
  exact h3.symm.trans (inverse_cutoff_apply loc g₂ hR hs u x).symm

end TamingCompatibility.LocalRellich

end

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace TamingCompatibility.RellichTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cutoff (g : E →ᵇ ℂ) (R : ℝ) : E → ℂ := (Metric.closedBall 0 R).indicator g

lemma cutoff_memLp_top (g : E →ᵇ ℂ) (R : ℝ) :
    MemLp (cutoff g R) ∞ (volume : Measure E) :=
  g.memLp_top.indicator measurableSet_closedBall

lemma cutoff_memLp_two (g : E →ᵇ ℂ) (R : ℝ) :
    MemLp (cutoff g R) 2 (volume : Measure E) := by
  apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
  let : IsFiniteMeasure ((volume : Measure E).restrict (Metric.closedBall 0 R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall (0 : E) R).measure_lt_top⟩
  exact MemLp.of_bound (g.continuous.aestronglyMeasurable) ‖g‖
    (Eventually.of_forall g.norm_coe_le_norm)

lemma cutoff_support (g : E →ᵇ ℂ) (R : ℝ) :
    ∀ᵐ ξ ∂(volume : Measure E), R < ‖ξ‖ → (cutoff_memLp_two g R).toLp (cutoff g R) ξ = 0 := by
  filter_upwards [(cutoff_memLp_two g R).coeFn_toLp] with ξ hξ h
  rw [hξ]
  exact Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using not_le.mpr h) _

lemma cutoff_lp_eq (g : E →ᵇ ℂ) (R : ℝ) :
    (cutoff_memLp_two g R).toLp (cutoff g R) =ᵐ[volume]
      (cutoff_memLp_top g R).toLp (cutoff g R) :=
  (cutoff_memLp_two g R).coeFn_toLp.trans (cutoff_memLp_top g R).coeFn_toLp.symm

lemma tail_norm_le {g : E →ᵇ ℂ} {R ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ ξ, R < ‖ξ‖ → ‖g ξ‖ ≤ ε) :
    ‖(g.memLp_top (μ := (volume : Measure E))).toLp g -
      (cutoff_memLp_top g R).toLp (cutoff g R)‖ ≤ ε := by
  rw [← MemLp.toLp_sub, Lp.norm_toLp,
    eLpNorm_exponent_top
      (g.continuous.aestronglyMeasurable.sub (cutoff_memLp_top g R).aestronglyMeasurable)]
  have hb : ∀ ξ, ‖g ξ - cutoff g R ξ‖ ≤ ε := by
    intro ξ
    by_cases hm : ξ ∈ Metric.closedBall (0 : E) R
    · simp [cutoff, Set.indicator_of_mem hm, hε]
    · simpa [cutoff, Set.indicator_of_notMem hm] using
        h ξ (lt_of_not_ge (by simpa [Metric.mem_closedBall, dist_zero_right] using hm))
  have he := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure E))
    (Eventually.of_forall hb)
  exact (ENNReal.toReal_mono (by finiteness) he).trans_eq (ENNReal.toReal_ofReal hε)

end TamingCompatibility.RellichTail

end
noncomputable section

namespace TamingCompatibility.LocalRellich
open LocalRestriction HilbertSobolev FourierCutoff FourierIdentification RellichTail
open MeasureTheory FourierTransform Filter
open scoped ENNReal RealInnerProductSpace BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma localInverse_sub (K : Set E) (hK : MeasurableSet K)
    (g h : Lp ℂ ∞ (volume : Measure E)) :
    localInverse (F := F) K hK (g-h) = localInverse K hK g - localInverse K hK h := by
  apply ContinuousLinearMap.ext
  intro u
  change restrict volume K hK ((Lp.fourierTransformₗᵢ E F).symm ((g-h) • u)) =
    restrict volume K hK ((Lp.fourierTransformₗᵢ E F).symm (g • u)) -
    restrict volume K hK ((Lp.fourierTransformₗᵢ E F).symm (h • u))
  rw [sub_eq_add_neg, Lp.smul_add, Lp.neg_smul, map_add, map_neg, map_add, map_neg]
  exact (sub_eq_add_neg _ _).symm

lemma localInverse_sub_norm_le (K : Set E) (hK : MeasurableSet K)
    (g h : Lp ℂ ∞ (volume : Measure E)) :
    ‖localInverse (F := F) K hK g - localInverse K hK h‖ ≤ ‖g-h‖ := by
  rw [← localInverse_sub]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (localInverse_norm_le K hK (g-h))

theorem localInverse_compact_of_decay [ProperSpace F]
    (K : Set E) (hK : IsCompact K) (g : E →ᵇ ℂ)
    (hd : ∀ ε > 0, ∃ R ≥ 0, ∀ ξ : E, R < ‖ξ‖ → ‖g ξ‖ ≤ ε) :
    IsCompactOperator (localInverse (F := F) K hK.measurableSet (g.memLp_top.toLp g)) := by
  have hc : _root_.IsClosed {f : Lp F 2 (volume : Measure E) →L[ℝ]
      Lp F 2 (localMeasure volume K) | IsCompactOperator f} :=
    isClosed_setOfPred_isCompactOperator
  refine hc.closure_subset ((Metric.mem_closure_iff
    (α := Lp F 2 (volume : Measure E) →L[ℝ] Lp F 2 (localMeasure volume K))
    (s := {f | IsCompactOperator f})).mpr ?_)
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hd (ε/2) (half_pos hε)
  let c := (cutoff_memLp_top g R).toLp (cutoff g R)
  refine ⟨localInverse (F := F) K hK.measurableSet c, ?_, ?_⟩
  · exact localInverse_compact_of_support (F := F) K hK c
      ((cutoff_memLp_two g R).toLp (cutoff g R)) (cutoff_lp_eq g R) hR (cutoff_support g R)
  · have hh : ‖localInverse K hK.measurableSet (g.memLp_top.toLp g) -
        localInverse (F := F) K hK.measurableSet c‖ < ε := by
      apply lt_of_le_of_lt (localInverse_sub_norm_le K hK.measurableSet _ _)
      exact (tail_norm_le (le_of_lt (half_pos hε)) ht).trans_lt (half_lt_self hε)
    have he : dist (localInverse (F := F) K hK.measurableSet (g.memLp_top.toLp g))
        (localInverse K hK.measurableSet c) =
        ‖localInverse K hK.measurableSet (g.memLp_top.toLp g) -
          localInverse (F := F) K hK.measurableSet c‖ := dist_eq_norm
      (localInverse (F := F) K hK.measurableSet (g.memLp_top.toLp g))
      (localInverse (F := F) K hK.measurableSet c)
    rw [he]
    exact hh

end TamingCompatibility.LocalRellich

end

noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction

end
end
end
end
end

end OAI
