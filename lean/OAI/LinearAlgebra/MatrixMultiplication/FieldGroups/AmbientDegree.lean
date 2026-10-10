import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.StageCGibbs
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.TargetRate
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveCapacity
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AmbientEntropy
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AmbientRateLimit

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAmbientDegree

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldGroupTargetRate JointPopulation JointAmbientDegree
open JointAmbientEntropy JointGibbsApproximation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def potential {K : ℕ} (w : PlacedWork K) (s : Fin 3) (k : Fin 17) : ℝ :=
  match w.1 with
  | .stageA h => AllFieldActiveGibbs.physicalPotential positiveInitial tableP
      (initialShape h.val) w.2 s k
  | .stageB h => AllFieldActiveGibbs.physicalPotential positiveSecond tablep
      (aShape h.val) w.2 s k
  | .stageC h => AllFieldStageCGibbs.physicalPotential h w.2 s k

def logNormalizer {K : ℕ} (w : PlacedWork K) : ℝ :=
  match w.1 with
  | .stageA h => AllFieldActiveGibbs.splitLogNormalizer positiveInitial tableP
      (initialShape h.val)
  | .stageB h => AllFieldActiveGibbs.splitLogNormalizer positiveSecond tablep
      (aShape h.val)
  | .stageC _ => 0

theorem placedLaw_log {K : ℕ} (w : PlacedWork K) (a : JointPopulation.Shape)
    (ha : 0 < (placedLaw w).mass a) :
    Real.log ((placedLaw w).mass a) = potential w 0 (shapeSide 0 a) +
      potential w 1 (shapeSide 1 a) + potential w 2 (shapeSide 2 a) -
        logNormalizer w := by
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h => exact AllFieldActiveGibbs.placedLaw_stageA_log h phi a ha
  | stageB h => exact AllFieldActiveGibbs.placedLaw_stageB_log h phi a ha
  | stageC h => exact AllFieldStageCGibbs.placedLaw_stageC_log h phi a ha

theorem localAllowed_positive {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → JointPopulation.Shape → ℕ) (total : H → ℕ) (h : H)
    (word : Positions counts h → JointPopulation.Shape)
    (hw : localAllowed counts total h word) {K : ℕ} (w : PlacedWork K)
    (htotal : total h = 2 * w.1.halfLength)
    (hcounts : ∀ a, 0 < counts h a → 0 < (placedLaw w).mass a) :
    ∀ i, 0 < (placedLaw w).mass (word i) := by
  have hb := fun a ha =>
    AllFieldStageCGibbs.placedLaw_positive_parent_bounds w a (hcounts a ha)
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA a =>
      apply JointMarginalSupport.localAllowed_positive_reference counts total h word hw
        (physicalShape phi (initialShape a.val)) _ hb
      intro u hu hle
      exact AllFieldActiveGibbs.placedLaw_stageA_positive a phi u
        (hu.trans htotal) hle
  | stageB a =>
      apply JointMarginalSupport.localAllowed_positive_reference counts total h word hw
        (physicalShape phi (aShape a.val)) _ hb
      intro u hu hle
      exact AllFieldActiveGibbs.placedLaw_stageB_positive a phi u
        (hu.trans htotal) hle
  | stageC a =>
      exact AllFieldStageCGibbs.localAllowed_positive_reference counts total h word hw
        a phi htotal hcounts

variable {K tick : ℕ} {sigma : Placement}

def orderTotal (h : ActiveOrder K tick sigma) : ℕ := 2 * h.val.val.1.halfLength

theorem canonicalLaw_mass_eq (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma)
    (hpos : 0 < Fintype.card (Positions (orderCounts allocation m) h)) :
    (canonicalLaw (orderCounts allocation m) h).mass = (orderLaw h).mass := by
  have hcard : Fintype.card (Positions (orderCounts allocation m) h) =
      population allocation m (h.val.val.1.source, h.val.val.2) := by
    simpa only [Positions, Fintype.card_fin] using orderCounts_sum allocation m h
  funext a
  rw [canonicalLaw_mass_of_pos _ h hpos, hcard]
  change (jointCounts allocation m h.val.val a : ℝ) /
    population allocation m (h.val.val.1.source, h.val.val.2) = _
  rw [jointCounts_cast]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (hcard ▸ hpos).ne')

theorem localAllowed_entropy_le (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma)
    (word : Positions (orderCounts allocation m) h → JointPopulation.Shape)
    (hw : localAllowed (orderCounts allocation m) orderTotal h word) :
    finiteEntropy (fun a => (wordPopulation word a : ℝ) /
      Fintype.card (Positions (orderCounts allocation m) h)) ≤
        finiteEntropy (orderLaw h).mass := by
  by_cases hpos : 0 < Fintype.card (Positions (orderCounts allocation m) h)
  · have hs := localAllowed_positive (orderCounts allocation m) orderTotal h word hw
      h.val.val rfl (fun a ha =>
        AllFieldStageCGibbs.jointCounts_positive_reference allocation m h.val.val a ha)
    have he := localAllowed_entropy_le_of_word_support (orderCounts allocation m)
      orderTotal h word (orderLaw h) (potential h.val.val 0) (potential h.val.val 1)
      (potential h.val.val 2) (logNormalizer h.val.val) hs
      (placedLaw_log h.val.val) hw
    have hc := canonicalLaw_mass_eq allocation m h hpos
    simpa only [gibbsCap, marginalError, FiniteLaw.map_mass, hc, sub_self, abs_zero,
      zero_mul, Finset.sum_const_zero, add_zero] using he
  · have hz := Nat.eq_zero_of_not_pos hpos
    simpa only [hz, Nat.cast_zero, div_zero, finiteEntropy, entropyTerm_zero,
      Finset.sum_const_zero] using (orderLaw h).entropy_nonneg

theorem tendsto_firstExponent (allocation : Allocation) (sigma : Placement) :
    Tendsto (fun m : ℕ => (∑ h : ActiveOrder K tick sigma,
      classExponent (orderCounts allocation m) (sigma 0)
        (triple (orderCounts allocation m) (canonicalTarget (orderCounts allocation m))) h
        (finiteEntropy (orderLaw h).mass)) / (m : ℝ)) atTop
      (𝓝 (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)) := by
  have hsize (h : ActiveOrder K tick sigma) :=
    JointPopulationRates.tendsto_total_div_of_coordinate_rates
      (fun m => orderCounts allocation m h)
      ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
      (orderLaw h).mass (orderLaw h).total (orderCounts_dilation_rate allocation h)
  have hside (h : ActiveOrder K tick sigma) :=
    JointPopulationRates.tendsto_weighted_target_side_entropy
      (fun m => orderCounts allocation m)
      (fun m => canonicalTarget (orderCounts allocation m))
      (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
      (fun h => (orderLaw h).mass) (fun h => (orderLaw h).total)
      (orderCounts_dilation_rate allocation) h (sigma 0)
  have hr := JointAmbientRateLimit.tendsto_sum_classExponent_div_nat
    (fun m => orderCounts allocation m) (sigma 0)
    (fun _ h => finiteEntropy (orderLaw h).mass)
    (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
    (fun h => ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass)
    (fun h => ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma 0)))
    hsize (fun h => (hsize h).mul_const (finiteEntropy (orderLaw h).mass))
    (fun h => by simpa only [Positions, Fintype.card_fin] using hside h)
  simpa only [orderNativeDegree, order_first_capacity, mul_sub] using hr

theorem eventually_sharedAmbient_first_card_le (allocation : Allocation)
    (sigma : Placement) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ e : Target
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m),
      ((sharedAmbient (orderCounts allocation m) orderTotal (sigma 0)
        (triple (orderCounts allocation m) e)).card : ℝ) ≤
      Real.exp ((m : ℝ) *
        (orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + ε)) := by
  filter_upwards [(tendsto_order.1
      (tendsto_firstExponent (K := K) (tick := tick) allocation sigma)).2
      (orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + ε)
      (lt_add_of_pos_right _ hε), eventually_gt_atTop (0 : ℕ)] with m hm hmp
  intro e
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmp
  have hb := sharedAmbient_card_le (orderCounts allocation m) orderTotal (sigma 0)
    (triple (orderCounts allocation m) e) (fun h => finiteEntropy (orderLaw h).mass)
    (fun h word hw => localAllowed_entropy_le allocation m h word hw)
  apply hb.trans
  simp_rw [classBound_eq_exp]
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  simp_rw [classExponent_target_eq]
  simpa only [mul_comm] using (div_le_iff₀ hmr).mp hm.le

end MatrixMultiplication.AllFieldGroupAmbientDegree

end

end OAI
