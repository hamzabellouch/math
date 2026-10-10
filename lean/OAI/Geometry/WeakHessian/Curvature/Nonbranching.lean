import Mathlib
import OAI.Geometry.WeakHessian.Entropy.LocalGradientParallelogramCheeger
import OAI.Geometry.WeakHessian.Transport.VariationQuotient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.contact_first_variation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {φ ψ f : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hf : LipschitzWith T f)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    Tendsto (fun t : ℝ => (∫ γ, f (γ timeZero)-f (evalReal γ t) ∂π)/t)
      (𝓝[>] 0) (𝓝 (∫ γ, gamma m φ f (γ timeZero) ∂π)) :=
  hπ.contact_first_variation hfin (hcd.global_localGradientParallelogram hfin o h)
    hb hgeo hφ hf hdual hcontact
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X]

def Nonbranching : Prop :=
  ∀ σ τ : Curve X, IsGeodesic σ → IsGeodesic τ →
    (∃ a : Time, 0 < (a : ℝ) ∧ ∀ t : Time, (t : ℝ) ≤ (a : ℝ) → σ t = τ t) →
    σ = τ

@[simp] theorem clampTime_coe (t : Time) : clampTime (t : ℝ) = t := by
  apply Subtype.ext
  simp only [clampTime, min_eq_right t.property.2, max_eq_right t.property.1]
@[simp] theorem evalReal_zero (γ : Curve X) : evalReal γ 0 = γ timeZero :=
  evalReal_coe γ timeZero

@[simp] theorem evalReal_one (γ : Curve X) : evalReal γ 1 = γ timeOne :=
  evalReal_coe γ timeOne

theorem IsGeodesic.lipschitzWith {γ : Curve X} (hγ : IsGeodesic γ) :
    LipschitzWith (nndist (γ timeZero) (γ timeOne)) γ := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [Subtype.dist_eq, Real.dist_eq, coe_nndist, mul_comm] using (hγ s t).le

theorem IsGeodesic.evalReal_lipschitzWith {γ : Curve X} (hγ : IsGeodesic γ) :
    LipschitzWith (nndist (γ timeZero) (γ timeOne)) (evalReal γ) := by
  change LipschitzWith _ (γ ∘ Set.projIcc 0 1 zero_le_one)
  simpa only [mul_one] using
    hγ.lipschitzWith.comp (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 by norm_num))

theorem isGeodesic_of_dist_le (γ : Curve X)
    (h : ∀ s t : Time, dist (γ s) (γ t) ≤
      |(s : ℝ) - (t : ℝ)| * dist (γ timeZero) (γ timeOne)) : IsGeodesic γ := by
  have ordered (s t : Time) (hst : (s : ℝ) ≤ (t : ℝ)) :
      dist (γ s) (γ t) = |(s : ℝ) - (t : ℝ)| * dist (γ timeZero) (γ timeOne) := by
    apply le_antisymm (h s t)
    have h0s := h timeZero s
    have ht1 := h t timeOne
    change dist (γ timeZero) (γ s) ≤ |0 - (s : ℝ)| * _ at h0s
    change dist (γ t) (γ timeOne) ≤ |(t : ℝ) - 1| * _ at ht1
    rw [zero_sub, abs_neg, abs_of_nonneg s.property.1] at h0s
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub] at ht1
    have htriangle := (dist_triangle (γ timeZero) (γ s) (γ timeOne)).trans
      (add_le_add le_rfl (dist_triangle (γ s) (γ t) (γ timeOne)))
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    nlinarith
  intro s t
  rcases le_total (s : ℝ) (t : ℝ) with hst | hts
  · exact ordered s t hst
  · rw [dist_comm, ordered t s hts, abs_sub_comm]

theorem lipschitzWith_if_le {L : ℝ≥0} {f g : ℝ → X} (c : ℝ)
    (hf : LipschitzWith L f) (hg : LipschitzWith L g) (hfg : f c = g c) :
    LipschitzWith L (fun t => if t ≤ c then f t else g t) := by
  have ordered (s t : ℝ) (hst : s ≤ t) :
      dist (if s ≤ c then f s else g s) (if t ≤ c then f t else g t) ≤
        (L : ℝ) * (t - s) := by
    by_cases hs : s ≤ c
    · by_cases ht : t ≤ c
      · simpa only [ite_eq_left hs, ite_eq_left ht, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hf.dist_le_mul s t
      · simp only [ite_eq_left hs, ite_eq_right ht]
        have hct : c ≤ t := (lt_of_not_ge ht).le
        calc
          dist (f s) (g t) ≤ dist (f s) (f c) + dist (f c) (g t) :=
            dist_triangle _ _ _
          _ = dist (f s) (f c) + dist (g c) (g t) := by rw [hfg]
          _ ≤ (L : ℝ) * (c - s) + (L : ℝ) * (t - c) := by
            apply add_le_add
            · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs), neg_sub]
                using hf.dist_le_mul s c
            · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hct), neg_sub]
                using hg.dist_le_mul c t
          _ = (L : ℝ) * (t - s) := by ring
    · have ht : ¬t ≤ c := fun ht => hs (hst.trans ht)
      simpa only [ite_eq_right hs, ite_eq_right ht, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hg.dist_le_mul s t
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rcases le_total s t with hst | hts
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      using ordered s t hst
  · rw [dist_comm]
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)] using ordered t s hts

theorem IsGeodesic.stretch_lipschitzWith {τ : Curve X} (hτ : IsGeodesic τ)
    (a b : ℝ) (hab : a < b) {L : ℝ≥0}
    (hlen : dist (τ timeZero) (τ timeOne) = (b - a) * (L : ℝ)) :
    LipschitzWith L (fun t : ℝ => evalReal τ ((t - a) / (b - a))) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  calc
    dist (evalReal τ ((s - a) / (b - a))) (evalReal τ ((t - a) / (b - a))) ≤
        ((b - a) * (L : ℝ)) * |(s - a) / (b - a) - (t - a) / (b - a)| := by
      simpa only [coe_nndist, hlen, Real.dist_eq] using
        hτ.evalReal_lipschitzWith.dist_le_mul ((s - a) / (b - a)) ((t - a) / (b - a))
    _ = (L : ℝ) * dist s t := by
      have heq : (s - a) / (b - a) - (t - a) / (b - a) = (s - t) / (b - a) := by ring
      rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab), Real.dist_eq]
      field_simp [ne_of_gt (sub_pos.mpr hab)]

def splicedFunction (σ τ : Curve X) (a b t : ℝ) : X :=
  if t ≤ a then evalReal σ t
  else if t ≤ b then evalReal τ ((t - a) / (b - a))
  else evalReal σ t

theorem splicedFunction_lipschitzWith {σ τ : Curve X}
    (hσ : IsGeodesic σ) (hτ : IsGeodesic τ) (a b : Time)
    (hab : (a : ℝ) < (b : ℝ))
    (hstart : τ timeZero = σ a) (hend : τ timeOne = σ b) :
    LipschitzWith (nndist (σ timeZero) (σ timeOne))
      (splicedFunction σ τ (a : ℝ) (b : ℝ)) := by
  have hlen : dist (τ timeZero) (τ timeOne) =
      ((b : ℝ) - (a : ℝ)) * (nndist (σ timeZero) (σ timeOne) : ℝ) := by
    rw [hstart, hend, hσ a b, abs_of_neg (sub_neg.mpr hab), neg_sub, coe_nndist]
  have hg := hτ.stretch_lipschitzWith (a : ℝ) (b : ℝ) hab hlen
  have hb : evalReal τ (((b : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) =
      evalReal σ (b : ℝ) := by
    rw [div_self (ne_of_gt (sub_pos.mpr hab)), evalReal_one, evalReal_coe, hend]
  have hright := lipschitzWith_if_le (b : ℝ) hg hσ.evalReal_lipschitzWith hb
  have ha : evalReal σ (a : ℝ) =
      (if (a : ℝ) ≤ (b : ℝ) then
        evalReal τ (((a : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)))
      else evalReal σ (a : ℝ)) := by
    rw [ite_eq_left hab.le, sub_self, zero_div, evalReal_zero, evalReal_coe, hstart]
  exact lipschitzWith_if_le (a : ℝ) hσ.evalReal_lipschitzWith hright ha

theorem Nonbranching.unique_strict_subsegment (hnb : Nonbranching (X := X))
    {σ τ : Curve X} (hσ : IsGeodesic σ) (hτ : IsGeodesic τ)
    (a b : Time) (ha : 0 < (a : ℝ)) (hab : (a : ℝ) < (b : ℝ)) (hb : (b : ℝ) < 1)
    (hstart : τ timeZero = σ a) (hend : τ timeOne = σ b) :
    ∀ u : Time, τ u = σ (affineTime a b u) := by
  have hLip := splicedFunction_lipschitzWith hσ hτ a b hab hstart hend
  let ρ : Curve X := ⟨fun t => splicedFunction σ τ (a : ℝ) (b : ℝ) (t : ℝ),
    hLip.continuous.comp continuous_subtype_val⟩
  have hρ0 : ρ timeZero = σ timeZero := by
    change (if (0 : ℝ) ≤ (a : ℝ) then evalReal σ 0 else _) = σ timeZero
    rw [ite_eq_left a.property.1, evalReal_zero]
  have hρ1 : ρ timeOne = σ timeOne := by
    change (if (1 : ℝ) ≤ (a : ℝ) then _ else
      if (1 : ℝ) ≤ (b : ℝ) then _ else evalReal σ 1) = σ timeOne
    rw [ite_eq_right (not_le.mpr (hab.trans hb)), ite_eq_right (not_le.mpr hb), evalReal_one]
  have hρ : IsGeodesic ρ := by
    apply isGeodesic_of_dist_le
    intro s t
    rw [hρ0, hρ1]
    simpa only [ρ, ContinuousMap.coe_mk, coe_nndist, Real.dist_eq, mul_comm]
      using hLip.dist_le_mul (s : ℝ) (t : ℝ)
  have heq : σ = ρ := hnb σ ρ hσ hρ ⟨a, ha, by
    intro t ht
    change σ t = splicedFunction σ τ (a : ℝ) (b : ℝ) (t : ℝ)
    simp only [splicedFunction, ite_eq_left ht, evalReal_coe]⟩
  intro u
  by_cases hu : (u : ℝ) = 0
  · have hu' : u = timeZero := Subtype.ext hu
    subst u
    simpa only [affineTime_zero] using hstart
  · have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm hu)
    have hpa : (a : ℝ) < (affineTime a b u : ℝ) := by
      dsimp only [affineTime]
      nlinarith [mul_pos (sub_pos.mpr hab) hu0]
    have hpb : (affineTime a b u : ℝ) ≤ (b : ℝ) := by
      dsimp only [affineTime]
      nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr u.property.2)]
    have hquot : ((affineTime a b u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) = (u : ℝ) := by
      dsimp only [affineTime]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring
    have heval : ρ (affineTime a b u) = τ u := by
      change splicedFunction σ τ (a : ℝ) (b : ℝ) (affineTime a b u : ℝ) = τ u
      rw [splicedFunction, ite_eq_right (not_le.mpr hpa), ite_eq_left hpb, hquot, evalReal_coe]
    exact heval.symm.trans (congrArg (fun γ : Curve X => γ (affineTime a b u)) heq).symm

theorem isCompact_curve_family (S : Set (Curve X)) (hS : IsClosed S)
    (Q : Set X) (hQ : IsCompact Q) (L : ℝ≥0)
    (hQs : ∀ γ ∈ S, ∀ t : Time, γ t ∈ Q)
    (hL : ∀ γ ∈ S, LipschitzWith L γ) : IsCompact S := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact Time X
  have hb : IsClosed (e '' S) := e.toHomeomorph.isClosedMap S hS
  have hc : IsCompact (e '' S) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ Q hQ (e '' S) hb
    · rintro f t ⟨γ, hγ, rfl⟩
      exact hQs γ hγ t
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (L : ℝ) * r)
        (by simpa only [id_eq, mul_zero] using
          (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (L : ℝ))
      intro s t f
      obtain ⟨γ, hγ, he⟩ := f.property
      have hed : (f.val : Time → X) = γ := by rw [← he]; rfl
      change dist (f.val s) (f.val t) ≤ (L : ℝ) * dist s t
      rw [congrFun hed s, congrFun hed t]
      exact (hL γ hγ).dist_le_mul s t
  exact e.toHomeomorph.isCompact_image.mp hc

lemma isClosed_isGeodesic : IsClosed {γ : Curve X | IsGeodesic γ} := by
  simp only [IsGeodesic, ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  exact isClosed_eq ((continuous_eval_const s).dist (continuous_eval_const t))
    (((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).const_mul _)

def endpointTube (a b : X) : Set (Curve X) :=
  {γ | IsGeodesic γ ∧ dist (γ timeZero) a ≤ 1 ∧ dist (γ timeOne) b ≤ 1}

lemma isClosed_endpointTube (a b : X) : IsClosed (endpointTube a b) := by
  exact isClosed_isGeodesic.inter
    ((isClosed_le ((continuous_eval_const timeZero).dist continuous_const) continuous_const).inter
      (isClosed_le ((continuous_eval_const timeOne).dist continuous_const) continuous_const))

lemma endpointTube_length_le {a b : X} {γ : Curve X} (hγ : γ ∈ endpointTube a b) :
    dist (γ timeZero) (γ timeOne) ≤ dist a b + 2 := by
  have h := (dist_triangle (γ timeZero) a (γ timeOne)).trans
    (add_le_add le_rfl (dist_triangle a b (γ timeOne)))
  rw [dist_comm b (γ timeOne)] at h
  linarith [hγ.2.1, hγ.2.2]

lemma endpointTube_range {a b : X} {γ : Curve X} (hγ : γ ∈ endpointTube a b)
    (t : Time) : γ t ∈ Metric.closedBall a (dist a b + 3) := by
  rw [Metric.mem_closedBall]
  have he := hγ.1 t timeZero
  change dist (γ t) (γ timeZero) = |(t : ℝ) - 0| * _ at he
  rw [sub_zero, abs_of_nonneg t.property.1] at he
  have hle : dist (γ t) (γ timeZero) ≤ dist (γ timeZero) (γ timeOne) := by
    rw [he]
    exact mul_le_of_le_one_left dist_nonneg t.property.2
  have htri := dist_triangle (γ t) (γ timeZero) a
  linarith [endpointTube_length_le hγ, hγ.2.1]

theorem isCompact_endpointTube [ProperSpace X] (a b : X) :
    IsCompact (endpointTube a b) := by
  apply isCompact_curve_family _ (isClosed_endpointTube a b)
    (Metric.closedBall a (dist a b + 3)) (isCompact_closedBall _ _)
    (nndist a b + 2)
  · exact fun _ hγ t => endpointTube_range hγ t
  · intro γ hγ
    apply hγ.1.lipschitzWith.weaken
    change dist (γ timeZero) (γ timeOne) ≤ (nndist a b + 2 : ℝ≥0)
    simpa only [NNReal.coe_add, NNReal.coe_ofNat, coe_nndist] using endpointTube_length_le hγ

theorem unique_geodesic_endpoint_stability [ProperSpace X] (τ : Curve X)
    (hunique : ∀ γ : Curve X, IsGeodesic γ → γ timeZero = τ timeZero →
      γ timeOne = τ timeOne → γ = τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ γ : Curve X, IsGeodesic γ →
      dist (γ timeZero) (τ timeZero) < δ → dist (γ timeOne) (τ timeOne) < δ →
        dist γ τ < ε := by
  let B : Set (Curve X) := endpointTube (τ timeZero) (τ timeOne) ∩ {γ | ε ≤ dist γ τ}
  have hB : IsCompact B := (isCompact_endpointTube (τ timeZero) (τ timeOne)).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hf : Continuous (fun γ : Curve X =>
      dist (γ timeZero) (τ timeZero) + dist (γ timeOne) (τ timeOne)) :=
    ((continuous_eval_const timeZero).dist continuous_const).add
      ((continuous_eval_const timeOne).dist continuous_const)
  have hp : ∀ γ ∈ B, 0 < dist (γ timeZero) (τ timeZero) +
      dist (γ timeOne) (τ timeOne) := by
    intro γ hγ
    by_contra hn
    have hd₀ : dist (γ timeZero) (τ timeZero) = 0 := by
      have hd₁ := dist_nonneg (x := γ timeOne) (y := τ timeOne)
      have hd₀ := dist_nonneg (x := γ timeZero) (y := τ timeZero)
      linarith
    have hd₁ : dist (γ timeOne) (τ timeOne) = 0 := by
      have hd₁ := dist_nonneg (x := γ timeOne) (y := τ timeOne)
      linarith
    have he := hunique γ hγ.1.1 (dist_eq_zero.mp hd₀) (dist_eq_zero.mp hd₁)
    have hb : ε ≤ dist γ τ := hγ.2
    rw [he, dist_self] at hb
    linarith
  obtain ⟨η, hη, hmin⟩ := hB.exists_forall_le' hf.continuousOn hp
  refine ⟨min 1 (η/2), lt_min zero_lt_one (half_pos hη), min_le_left _ _, ?_⟩
  intro γ hγ h₀ h₁
  by_contra hn
  have hmem : γ ∈ B := ⟨⟨hγ,
    h₀.le.trans (min_le_left _ _), h₁.le.trans (min_le_left _ _)⟩, not_lt.mp hn⟩
  have hb := hmin γ hmem
  have ha₀ := h₀.trans_le (min_le_right 1 (η/2))
  have ha₁ := h₁.trans_le (min_le_right 1 (η/2))
  linarith

theorem integral_tendsto_of_endpoint_concentration [ProperSpace X]
    (τ : Curve X)
    (hunique : ∀ γ : Curve X, IsGeodesic γ → γ timeZero = τ timeZero →
      γ timeOne = τ timeOne → γ = τ)
    (π : ℕ → Measure (Curve X)) (hprob : ∀ n, IsProbabilityMeasure (π n))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (htracks : ∀ n, ∀ᵐ γ ∂π n, IsGeodesic γ ∧
      dist (γ timeZero) (τ timeZero) ≤ r n ∧ dist (γ timeOne) (τ timeOne) ≤ r n)
    {Φ : Curve X → ℝ} (hΦ : Continuous Φ) :
    Tendsto (fun n => ∫ γ, Φ γ ∂π n) atTop (𝓝 (Φ τ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hηΦ⟩ := Metric.continuousAt_iff.mp hΦ.continuousAt (ε/2) (half_pos hε)
  obtain ⟨δ, hδ, _, hδτ⟩ := unique_geodesic_endpoint_stability τ hunique hη
  have hev : ∀ᶠ n in atTop, r n < δ := (tendsto_order.mp hr).2 δ hδ
  filter_upwards [hev] with n hn
  let _ : IsProbabilityMeasure (π n) := hprob n
  have hb : ∀ᵐ γ ∂π n, ‖Φ γ - Φ τ‖ ≤ ε/2 := by
    filter_upwards [htracks n] with γ hγ
    exact (hηΦ (hδτ γ hγ.1 (hγ.2.1.trans_lt hn) (hγ.2.2.trans_lt hn))).le
  have hd : Integrable (fun γ => Φ γ - Φ τ) (π n) :=
    (integrable_const (ε/2)).mono' (hΦ.sub continuous_const).aestronglyMeasurable hb
  have hi : Integrable Φ (π n) := by
    have hsum : Integrable (fun γ => (Φ γ - Φ τ) + Φ τ) (π n) :=
      hd.add (integrable_const (Φ τ))
    simpa only [sub_add_cancel] using hsum
  have he : (∫ γ, Φ γ - Φ τ ∂π n) = (∫ γ, Φ γ ∂π n) - Φ τ := by
    rw [integral_sub hi (integrable_const (Φ τ)), integral_const]
    simp
  rw [dist_eq_norm, ← he]
  have hle := norm_integral_le_of_norm_le_const hb
  have hle' : ‖∫ γ, Φ γ - Φ τ ∂π n‖ ≤ ε/2 := by simpa using hle
  exact hle'.trans_lt (half_lt_self hε)

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
