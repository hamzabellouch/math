import OAI.Analysis.IrrationalRotation.Model.CircleOrderedCoupling
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingOrder
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitMarginalLaws
import OAI.Analysis.IrrationalRotation.Analysis.L2UniformAbsoluteContinuity
import OAI.Analysis.IrrationalRotation.Analysis.UniformAbsoluteContinuity
import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleCocycle
import OAI.Analysis.IrrationalRotation.Analysis.InfiniteRatioCaps

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Invariant233.CircleCoupling
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
lemma finiteHybridPoint_eq (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (N : ℕ) (ω : Sample) :
    finiteHybridPoint p hr N ω = MixedRadix.circleValue
      (MixedRadix.hybrid (digits p hr false ω) (digits p hr true ω) (N + 1)) := by
  change MixedRadix.circleValue (hybridDigits p hr (finiteHybridChoice N) ω) = _
  congr 1
  funext i
  simp only [hybridDigits, finiteHybridChoice, MixedRadix.hybrid]
  by_cases hi : i < N + 1 <;> simp [hi, digits]

lemma measurable_finiteHybridPoint (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    Measurable (finiteHybridPoint p hr N) := measurable_hybridPoint hp hr _

lemma tendsto_finiteHybridPoint (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ω : Sample) :
    Tendsto (fun N => finiteHybridPoint p hr N ω) atTop (𝓝 (point p hr true ω)) := by
  simp_rw [finiteHybridPoint_eq]
  exact (MixedRadix.tendsto_circleValue_hybrid
    (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible)
    (digits p hr false ω) (digits p hr true ω)).comp (tendsto_add_atTop_nat 1)

lemma uniformlyAbsolutelyContinuous_hybrids
    (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun ε : ℕ → Bool => (law p j).map (hybridPoint p hr ε)) := by
  apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities
    circleMeasure _ marginalBound
  intro ε
  obtain ⟨H, hH, hn, _, hb, he⟩ := (digitMarginalLaws hp hr).2 j ε
  change MemLp H 2 circleMeasure at hH
  change (0 ≤ᵐ[circleMeasure] H) at hn
  change eLpNorm H 2 circleMeasure ≤ ENNReal.ofReal marginalBound at hb
  change (law p j).map (hybridPoint p hr ε) =
    circleMeasure.withDensity (fun x => ENNReal.ofReal (H x)) at he
  refine ⟨hH.toLp H, ?_, ?_, ?_⟩
  · filter_upwards [hH.coeFn_toLp, hn] with x hx hnx
    rwa [hx]
  · rw [he]
    apply withDensity_congr_ae
    filter_upwards [hH.coeFn_toLp] with x hx
    rw [hx]
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hb

lemma hybridPoint_absolutelyContinuous (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    (law p j).map (hybridPoint p hr ε) ≪ circleMeasure :=
  (uniformlyAbsolutelyContinuous_hybrids hp j hr).absolutelyContinuous ε

lemma point_absolutelyContinuous (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    (law p j).map (point p hr side) ≪ circleMeasure :=
  hybridPoint_absolutelyContinuous hp j hr (fun _ => side)

lemma coordinate_circleValue_eq_tail
    (_hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (d : MixedRadix.Digits (MixedRadix.radices p.q)) (hd : MixedRadix.Nonterminal d) (i : ℕ) :
    p.coordinate i (MixedRadix.circleValue d) = MixedRadix.tailValue d i := by
  unfold coordinate MixedRadix.circleValue
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  change CircleParameterData.rep (((p.q i : ℝ) * MixedRadix.ofDigits d : ℝ) : Circle) = _
  rw [show CircleParameterData.rep = (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) from rfl,
    CircleCharacterDynamics.representative_coe]
  exact MixedRadix.coordinate_eq_tailValue hp.frequency_zero hp.q_pos
    hp.frequency_increasing hp.frequency_divisible d hd i

lemma ae_finiteHybrid_coordinates_ordered (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    ∀ᵐ ω ∂law p j, ∀ i,
      p.coordinate i (point p hr false ω) ≤ p.coordinate i (finiteHybridPoint p hr N ω) := by
  filter_upwards [ae_digits_ordered hp j hr, ae_nonterminal_digits hp j hr false] with ω horder hx
  intro i
  rw [finiteHybridPoint_eq, coordinate_point_eq_tail hp hr false ω hx i,
    coordinate_circleValue_eq_tail hp hr _
      (MixedRadix.nonterminal_hybrid _ _ hx (N + 1)) i]
  exact MixedRadix.tailValue_mono hr (fun n => (MixedRadix.hybrid_ordered horder (N + 1) n).1) i

lemma ae_ratio_cap_of_order (j : ℕ) (x y : Sample → Circle)
    (hx : Measurable x) (hy : Measurable y)
    (hax : (law p j).map x ≪ circleMeasure) (hay : (law p j).map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂law p j, ∀ i, p.coordinate i (x ω) ≤ p.coordinate i (y ω)) :
    ∀ᵐ ω ∂law p j, ∀ k : ℤ,
      0 < p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ∧
      p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ 1 := by
  obtain ⟨s, _, hs, _, hfinite, _⟩ := hp.exists_parameter_cocycle_set
  have hsx := ae_of_ae_map hx.aemeasurable (hax.ae_le hs)
  have hsy := ae_of_ae_map hy.aemeasurable (hay.ae_le hs)
  filter_upwards [horder, hsx, hsy] with ω ho hxs hys
  intro k
  refine ⟨div_pos (p.floorCocycle_pos θ k _) (p.floorCocycle_pos θ k _), ?_⟩
  have hcap := CircleWeights.cocycle_ratio_cap_finite_exceptions θ
    p.coordFrequency p.coordCost k (x ω) (y ω) ∅
    (fun i => (hp.coordCost_pos i).le)
    (fun i _ => by simpa only [p.coord_coordinate_eq] using ho i.2)
    (by simpa only [p.coord_coordinate_eq, p.coord_phase_eq] using hfinite _ hxs k)
    (by simpa only [p.coord_coordinate_eq, p.coord_phase_eq] using hfinite _ hys k)
  simpa only [floorCocycle, Finset.sum_empty, Real.exp_zero] using hcap

lemma ae_endpoint_ratio_cap (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ k : ℤ,
      0 < p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ∧
      p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ≤ 1 :=
  ae_ratio_cap_of_order hp j _ _ (measurable_point hp hr false) (measurable_point hp hr true)
    (point_absolutelyContinuous hp j hr false) (point_absolutelyContinuous hp j hr true)
    (ae_coordinates_ordered hp j hr)

lemma ae_finiteHybrid_ratio_cap (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    ∀ᵐ ω ∂law p j, ∀ k : ℤ,
      0 < p.floorCocycle θ k (finiteHybridPoint p hr N ω) / p.floorCocycle θ k (point p hr false ω) ∧
      p.floorCocycle θ k (finiteHybridPoint p hr N ω) / p.floorCocycle θ k (point p hr false ω) ≤ 1 :=
  ae_ratio_cap_of_order hp j _ _ (measurable_point hp hr false) (measurable_finiteHybridPoint hp hr N)
    (point_absolutelyContinuous hp j hr false) (hybridPoint_absolutelyContinuous hp j hr _)
    (ae_finiteHybrid_coordinates_ordered hp j hr N)

end Invariant233.CircleCoupling

end

end OAI
