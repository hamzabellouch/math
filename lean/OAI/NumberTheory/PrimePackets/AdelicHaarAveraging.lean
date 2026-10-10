import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicAveraging

namespace OAI

noncomputable section
open scoped Topology Pointwise ENNReal
open Module Filter Set MeasureTheory
namespace PrimeDegreePackets.Adelic.PacketTorusParametrization
variable {d : ℕ} {K Q : Type*} [Field K] [NumberField K]
  [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [MeasurableSpace Q] [BorelSpace Q] {M : FullLattice (d+1) K}
  {σ : OrderedEmbeddings (d+1) K} (P : PacketTorusParametrization Q M σ)
include P

lemma average_orbitProbability (θ : Measure (LogCoordinates d)) [IsProbabilityMeasure θ]
    (hθ : ∀ q : Q, Measure.map (orbitMap (P.point q)) θ = orbitProbability (P.point q))
    (ν : Measure Q) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]
    (a : Q) (S : Set (X (d+1))) (hS : MeasurableSet S) :
    Measurable (fun q => orbitProbability (P.point (q*a)) S) ∧
      (∫⁻ q, orbitProbability (P.point (q*a)) S ∂ν) = (Measure.map P.point ν) S := by
  have hInd : Measurable (S.indicator (1 : X (d+1) → ℝ≥0∞)) := measurable_const.indicator hS
  let F : Q → LogCoordinates d → ℝ≥0∞ := fun q u =>
    S.indicator 1 (P.point (q*a*P.liftFlow u))
  have hF : Measurable (Function.uncurry F) :=
    hInd.comp (P.continuous_point.comp
      ((continuous_fst.mul continuous_const).mul
        (P.continuous_liftFlow.comp continuous_snd))).measurable
  have hinner (q : Q) : (∫⁻ u, F q u ∂θ) = orbitProbability (P.point (q*a)) S := by
    rw [← hθ (q*a),← lintegral_indicator_one hS,
      lintegral_map hInd (continuous_orbitMap _).measurable]
    apply lintegral_congr
    intro u
    dsimp [F]
    rw [P.flow_eq]
  have hright (u : LogCoordinates d) :
      (∫⁻ q, F q u ∂ν) = (Measure.map P.point ν) S := by
    rw [← lintegral_indicator_one hS,
      lintegral_map hInd P.continuous_point.measurable]
    have hmf : Measurable (fun q => S.indicator (1 : X (d+1) → ℝ≥0∞) (P.point q)) :=
      hInd.comp P.continuous_point.measurable
    have hmg : Measurable (fun q : Q => (a*P.liftFlow u)*q) :=
      (continuous_const.mul continuous_id).measurable
    calc
      _ = ∫⁻ q, S.indicator 1 (P.point ((a*P.liftFlow u)*q)) ∂ν := by
        apply lintegral_congr
        intro q
        dsimp [F]
        congr 2
        ac_rfl
      _ = ∫⁻ q, S.indicator 1 (P.point q) ∂(Measure.map (fun q => (a*P.liftFlow u)*q) ν) :=
        (lintegral_map hmf hmg).symm
      _ = _ := by rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self]
  refine ⟨?_,?_⟩
  · simpa only [hinner] using hF.lintegral_prod_right (ν := θ)
  · calc
      _ = ∫⁻ q, ∫⁻ u, F q u ∂θ ∂ν := lintegral_congr (fun q => (hinner q).symm)
      _ = ∫⁻ u, ∫⁻ q, F q u ∂ν ∂θ := lintegral_lintegral_swap hF.aemeasurable
      _ = ∫⁻ u, (Measure.map P.point ν) S ∂θ := lintegral_congr hright
      _ = _ := by simp

 

theorem map_invariant_probability [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (hodd : Odd (d+1))
    (ν : Measure Q) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν] :
    Measure.map P.point ν = packetMeasure M σ := by
  let := (packetOrbits_finite M σ hn hodd).fintype
  obtain ⟨O,hO⟩ := packetOrbits_nonempty M σ
  let O₀ : packetOrbits M σ := ⟨O,hO⟩
  have : Nonempty (packetOrbits M σ) := ⟨O₀⟩
  obtain ⟨θ,hθprob,hθ⟩ := P.exists_common_average hn hodd
  let := hθprob
  rw [P.packetMeasure_eq_uniform hn hodd O₀]
  apply Measure.ext
  intro S hS
  have hsum : (Fintype.card (packetOrbits M σ) : ℝ≥0∞) * (Measure.map P.point ν) S =
      (∑ O : packetOrbits M σ, orbitProbability (orbitBasepoint O)) S := by
    calc
      _ = ∑ O : packetOrbits M σ, ∫⁻ q, orbitProbability (P.point (q*P.select O)) S ∂ν := by
        simp only [(P.average_orbitProbability θ hθ ν _ S hS).2,Finset.sum_const,
          Finset.card_univ,nsmul_eq_mul]
      _ = ∫⁻ q, ∑ O : packetOrbits M σ, orbitProbability (P.point (q*P.select O)) S ∂ν := by
        symm
        apply lintegral_finsetSum
        intro O _
        exact (P.average_orbitProbability θ hθ ν _ S hS).1
      _ = ∫⁻ q, (∑ O : packetOrbits M σ, orbitProbability (orbitBasepoint O)) S ∂ν := by
        apply lintegral_congr
        intro q
        rw [← Measure.finsetSum_apply, P.sum_translated_orbitProbabilities]
      _ = _ := by simp
  rw [Measure.smul_apply,smul_eq_mul,← hsum]
  symm
  apply ENNReal.inv_mul_cancel_left
  · exact_mod_cast (ne_of_gt (Fintype.card_pos (α := packetOrbits M σ)))
  · exact ENNReal.natCast_ne_top _

end PrimeDegreePackets.Adelic.PacketTorusParametrization

end

end OAI
