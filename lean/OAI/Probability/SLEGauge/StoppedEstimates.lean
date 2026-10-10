import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.EulerMoments

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem expected_stopped_local {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (f : E × ℝ → ℝ) (K O : Set (E × ℝ))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (g : Driver → ℝ → E) (z : E) {L M T t : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖)
    (hg0 : ∀ b, g b 0 = z)
    (hder : ∀ b u, u ∈ Icc 0 T → HasDerivWithinAt (g b) (v (g b u) (b u.toNNReal)) (Icc 0 T) u)
    (hcf : ∀ b, ContinuousOn (fun u => v (g b u) (b u.toNNReal)) (Icc 0 T))
    (τ : (ℝ≥0 → ℝ) → ℝ) (mτ : Measurable τ)
    (hτpast : ∀ (s : ℝ≥0) b c, (∀ u ≤ s, b u = c u) → ((s:ℝ) < τ b ↔ (s:ℝ) < τ c))
    (hτ : ∀ b : Driver, 0 ≤ τ b ∧ τ b < T)
    (hD : ∀ b : Driver, ∃ ε > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < ε → (x,b u.toNNReal) ∈ K)
    (hgen : ∀ q ∈ K,
      fderiv ℝ (fun x => f (x,q.2)) q.1 (v q.1 q.2) +
        deriv (deriv (fun b => f (q.1,b))) q.2 / 2 ≤ 0)
    (hz : (z,0) ∈ K) (ht : 0 ≤ t) :
    (∫ b : Driver, f (g b (min t (τ b)), b (min t (τ b)).toNNReal) ∂W) ≤ f (z,0) := by
  obtain ⟨G,hG,hGc,hGeq⟩ := Localization.compact_extension hK hO hKO f hf
  obtain ⟨A,hA⟩ := exists_smoothTest_of_compact G hG hGc
  have heq (q : E × ℝ) (hq : q ∈ K) : A.F q.1 q.2 = f q := by
    rw [hA]
    exact (hGeq q hq).self_of_nhds
  have hDgen (q : E × ℝ) (hq : q ∈ K) :
      A.D q.1 q.2 (v q.1 q.2)+deriv (deriv (A.F q.1)) q.2/2 ≤ 0 := by
    have hx : (fun x => A.F x q.2) =ᶠ[𝓝 q.1] fun x => f (x,q.2) := by
      rw [hA]
      exact (hGeq q hq).comp_tendsto (continuousAt_id.prodMk continuousAt_const)
    have hb : A.F q.1 =ᶠ[𝓝 q.2] fun b => f (q.1,b) := by
      rw [hA]
      exact (hGeq q hq).comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    rw [← (A.hD q.1 q.2).fderiv, hx.fderiv_eq, hb.deriv.deriv_eq]
    exact hgen q hq
  have hineq := expected_stopped_smooth hW A v mv g z hL hM hv hlip hg0 hder hcf
    τ mτ hτpast hτ K hK.measurableSet hD hDgen ht
  rw [heq (z,0) hz] at hineq
  convert hineq using 1
  apply integral_congr_ae
  filter_upwards [] with b
  symm
  apply heq (g b (min t (τ b)), b (min t (τ b)).toNNReal)
  obtain ⟨ε,hε,hDb⟩ := hD b
  exact hDb (min t (τ b)) ⟨le_min ht (hτ b).1,min_le_right _ _⟩ _ (by simpa using hε)

end SLEExactGauge.BrownianCalculus

 

noncomputable section
namespace SLEExactGauge

 
structure Parameter where
  κ : ℝ
  κ_pos : 0 < κ
  κ_lt_eight : κ < 8

namespace Parameter

def a (P : Parameter) : ℝ := 2 / P.κ
def d (P : Parameter) : ℝ := 1 + 1 / (4 * P.a)
def α (P : Parameter) : ℝ := 2 - P.d
def p (P : Parameter) : ℝ := 4 * P.a - 1
 
def q (P : Parameter) : ℝ := (1 / 2 : ℝ) * min 1 P.p
def η (P : Parameter) : ℝ := (1 - P.q) / (2 - P.q)
def M (P : Parameter) : ℝ := (1 + P.η) / (1 - 2 * P.η)
def β (P : Parameter) : ℝ := min 1 (P.a / (4 * P.M))
def k (P : Parameter) : ℝ := P.q * (P.p - P.q) / 2
def A (P : Parameter) : ℝ := P.p / 2 + (P.p - P.q) * (1 + P.q) / 2 + 2
def h₀ (P : Parameter) : ℝ := (P.k / (2 * P.A)) ^ (1 / (2 - P.q))
def C₁ (P : Parameter) : ℝ := P.A * P.h₀ ^ (-P.p)
def c₁ (P : Parameter) : ℝ := P.k / 2

def δ (P : Parameter) (U u : ℝ) : ℝ := Real.exp (-P.β * min u (U - u))
 
def f (P : Parameter) (δ s : ℝ) : ℝ := s ^ P.p + δ * (1 + s ^ P.q)
def D (P : Parameter) (δ s : ℝ) : ℝ := δ / P.f δ s * s ^ (P.q - 2)
 
def drift (P : Parameter) (δ s σ : ℝ) : ℝ :=
  δ / P.f δ s * (P.p / 2 + (P.p - P.q) * (1 + P.q) / 2 * s ^ P.q -
    P.k * s ^ (P.q - 2) + σ * (1 + s ^ P.q))

lemma a_gt_quarter (P : Parameter) : (1 / 4 : ℝ) < P.a := by
  unfold a
  apply (lt_div_iff₀ P.κ_pos).2
  linarith [P.κ_lt_eight]

lemma p_pos (P : Parameter) : 0 < P.p := by
  unfold p
  linarith [P.a_gt_quarter]

lemma q_pos (P : Parameter) : 0 < P.q := by
  unfold q
  exact mul_pos (by norm_num) (lt_min (by norm_num) P.p_pos)

lemma q_le_half (P : Parameter) : P.q ≤ 1 / 2 := by
  unfold q
  linarith [min_le_left (1 : ℝ) P.p]

lemma q_lt_one (P : Parameter) : P.q < 1 := by
  linarith [P.q_le_half]

lemma q_lt_p (P : Parameter) : P.q < P.p := by
  unfold q
  linarith [min_le_right (1 : ℝ) P.p, P.p_pos]

lemma k_pos (P : Parameter) : 0 < P.k := by
  unfold k
  exact div_pos (mul_pos P.q_pos (sub_pos.mpr P.q_lt_p)) (by norm_num)

lemma A_pos (P : Parameter) : 0 < P.A := by
  unfold A
  have := mul_pos (sub_pos.mpr P.q_lt_p) (by linarith [P.q_pos] : 0 < 1 + P.q)
  linarith [P.p_pos]

lemma β_le_one (P : Parameter) : P.β ≤ 1 := min_le_left _ _

lemma h₀_pos (P : Parameter) : 0 < P.h₀ := by
  unfold h₀
  exact Real.rpow_pos_of_pos (div_pos P.k_pos (by linarith [P.A_pos])) _

lemma h₀_lt_one (P : Parameter) : P.h₀ < 1 := by
  have hbase : P.k / (2 * P.A) < 1 := by
    apply (div_lt_one (by linarith [P.A_pos])).2
    unfold k A
    have hprod := mul_pos (sub_pos.mpr P.q_lt_p)
      (by linarith [P.q_pos] : 0 < 2 + P.q)
    nlinarith [P.p_pos]
  exact Real.rpow_lt_one (div_nonneg P.k_pos.le (by linarith [P.A_pos])) hbase
    (one_div_pos.mpr (by linarith [P.q_lt_one]))

lemma h₀_power (P : Parameter) : P.h₀ ^ (P.q - 2) = 2 * P.A / P.k := by
  have hb : 0 ≤ P.k / (2 * P.A) :=
    div_nonneg P.k_pos.le (by linarith [P.A_pos])
  have hq : 2 - P.q ≠ 0 := by linarith [P.q_lt_one]
  have hexp : (1 / (2 - P.q)) * (P.q - 2) = (-1 : ℝ) := by
    field_simp
    ring
  unfold h₀
  rw [← Real.rpow_mul hb, hexp, Real.rpow_neg_one]
  simp only [inv_div]

lemma f_pos (P : Parameter) {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    0 < P.f δ s := by
  unfold f
  positivity

 
def RegularizedDriftObligation : Prop :=
  ∀ (P : Parameter) (δ s σ : ℝ), 0 < δ → δ ≤ 1 → 0 < s → s ≤ 1 →
    |σ| ≤ P.β → P.drift δ s σ ≤ P.C₁ * δ - P.c₁ * P.D δ s

 
theorem regularized_drift_bound : RegularizedDriftObligation := by
  intro P δ s σ hδ _ hs hs_one hσ
  have hf : 0 < P.f δ s := P.f_pos hδ hs
  have hδf : 0 ≤ δ / P.f δ s := (div_pos hδ hf).le
  have hsq : s ^ P.q ≤ 1 := Real.rpow_le_one hs.le hs_one P.q_pos.le
  have hsq0 : 0 ≤ s ^ P.q := Real.rpow_nonneg hs.le _
  have hσ_one : σ ≤ 1 := (le_abs_self σ).trans (hσ.trans P.β_le_one)
  have hσterm : σ * (1 + s ^ P.q) ≤ 2 := by
    calc
      _ ≤ 1 * (1 + s ^ P.q) :=
        mul_le_mul_of_nonneg_right hσ_one (by positivity)
      _ ≤ 2 := by linarith
  have hcoef : 0 ≤ (P.p - P.q) * (1 + P.q) / 2 := by
    have := sub_pos.mpr P.q_lt_p
    have := P.q_pos
    positivity
  have hbracket : P.p / 2 + (P.p - P.q) * (1 + P.q) / 2 * s ^ P.q +
      σ * (1 + s ^ P.q) ≤ P.A := by
    have hmul := mul_le_mul_of_nonneg_left hsq hcoef
    unfold A
    linarith
  have hrew : P.drift δ s σ + P.c₁ * P.D δ s =
      δ / P.f δ s * (P.p / 2 + (P.p - P.q) * (1 + P.q) / 2 * s ^ P.q +
        σ * (1 + s ^ P.q) - P.k / 2 * s ^ (P.q - 2)) := by
    unfold drift c₁ D
    ring
  have hbound : P.drift δ s σ + P.c₁ * P.D δ s ≤
      δ / P.f δ s * (P.A - P.k / 2 * s ^ (P.q - 2)) := by
    rw [hrew]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hbracket _) hδf
  have hgoal : P.drift δ s σ + P.c₁ * P.D δ s ≤ P.C₁ * δ := by
    rcases le_total s P.h₀ with hsmall | hlarge
    · have hexp : P.q - 2 ≤ 0 := by linarith [P.q_lt_one]
      have hpow := Real.rpow_le_rpow_of_nonpos hs hsmall hexp
      rw [P.h₀_power] at hpow
      have hcancel : 2 * P.A ≤ s ^ (P.q - 2) * P.k :=
        (div_le_iff₀ P.k_pos).mp hpow
      have hneg : P.A - P.k / 2 * s ^ (P.q - 2) ≤ 0 := by nlinarith
      have hzero := mul_nonpos_of_nonneg_of_nonpos hδf hneg
      have hc : 0 ≤ P.C₁ * δ := by
        unfold C₁
        have := P.A_pos
        have := P.h₀_pos
        positivity
      exact hbound.trans (hzero.trans hc)
    · have hsp : P.h₀ ^ P.p ≤ s ^ P.p :=
        Real.rpow_le_rpow P.h₀_pos.le hlarge P.p_pos.le
      have hflow : P.h₀ ^ P.p ≤ P.f δ s := by
        unfold f
        have hterm : 0 ≤ δ * (1 + s ^ P.q) := by positivity
        linarith
      have hdiv : δ / P.f δ s ≤ δ / P.h₀ ^ P.p :=
        div_le_div_of_nonneg_left hδ.le (Real.rpow_pos_of_pos P.h₀_pos _) hflow
      have hdrop : P.A - P.k / 2 * s ^ (P.q - 2) ≤ P.A := by
        have := P.k_pos
        have := Real.rpow_pos_of_pos hs (P.q - 2)
        nlinarith
      calc
        _ ≤ δ / P.f δ s * (P.A - P.k / 2 * s ^ (P.q - 2)) := hbound
        _ ≤ δ / P.f δ s * P.A := mul_le_mul_of_nonneg_left hdrop hδf
        _ ≤ δ / P.h₀ ^ P.p * P.A := mul_le_mul_of_nonneg_right hdiv P.A_pos.le
        _ = P.C₁ * δ := by
          unfold C₁
          rw [Real.rpow_neg P.h₀_pos.le]
          ring
  linarith

 
lemma η_pos (P : Parameter) : 0 < P.η := by
  unfold η
  exact div_pos (by linarith [P.q_lt_one]) (by linarith [P.q_lt_one])

lemma η_lt_half (P : Parameter) : P.η < 1 / 2 := by
  unfold η
  apply (div_lt_iff₀ (by linarith [P.q_lt_one] : 0 < 2 - P.q)).2
  linarith [P.q_pos]

lemma η_exponent (P : Parameter) : (P.q - 2) * P.η = P.q - 1 := by
  unfold η
  have hq : 2 - P.q ≠ 0 := by linarith [P.q_lt_one]
  field_simp
  ring

lemma M_pos (P : Parameter) : 0 < P.M := by
  unfold M
  exact div_pos (by linarith [P.η_pos]) (by linarith [P.η_lt_half])

lemma M_formula (P : Parameter) : P.M = 3 / P.q - 2 := by
  have hq : P.q ≠ 0 := P.q_pos.ne'
  have hq2 : 2 - P.q ≠ 0 := by linarith [P.q_lt_one]
  have hη : 1 - 2 * P.η ≠ 0 := by linarith [P.η_lt_half]
  unfold M
  apply (div_eq_iff hη).2
  unfold η
  field_simp
  ring

lemma β_pos (P : Parameter) : 0 < P.β := by
  unfold β
  exact lt_min (by norm_num) (div_pos (by linarith [P.a_gt_quarter]) (by
    have := P.M_pos
    positivity))

lemma interaction_exponent_lt (P : Parameter) : 2 * (P.M * P.β) < P.a := by
  have h := min_le_right (1 : ℝ) (P.a / (4 * P.M))
  change P.β ≤ P.a / (4 * P.M) at h
  have hM : 0 < 4 * P.M := by have := P.M_pos; positivity
  have hb := (le_div_iff₀ hM).mp h
  nlinarith [P.a_gt_quarter]

lemma f_ge_δ (P : Parameter) {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s) :
    δ ≤ P.f δ s := by
  unfold f
  have := Real.rpow_nonneg hs P.p
  have := Real.rpow_nonneg hs P.q
  nlinarith

lemma f_le_three (P : Parameter) {δ s : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : P.f δ s ≤ 3 := by
  have hp := Real.rpow_le_one hs hs1 P.p_pos.le
  have hq := Real.rpow_le_one hs hs1 P.q_pos.le
  have hnn := Real.rpow_nonneg hs P.q
  unfold f
  nlinarith

 
def angularDerivative (P : Parameter) (δ s c : ℝ) : ℝ :=
  (P.p * s ^ (P.p - 1) + δ * P.q * s ^ (P.q - 1)) * c

lemma angularDerivative_bound (P : Parameter) {δ s c : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (hc : |c| ≤ 1) :
    |P.angularDerivative δ s c| ≤ (P.p + P.q) * s ^ (P.q - 1) := by
  have hpq : s ^ (P.p - 1) ≤ s ^ (P.q - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith [P.q_lt_p])
  have hp0 := Real.rpow_nonneg hs.le (P.p - 1)
  have hq0 := Real.rpow_nonneg hs.le (P.q - 1)
  have hcoef : 0 ≤ P.p * s ^ (P.p - 1) + δ * P.q * s ^ (P.q - 1) := by
    have := P.p_pos
    have := P.q_pos
    positivity
  unfold angularDerivative
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ (P.p * s ^ (P.p - 1) + δ * P.q * s ^ (P.q - 1)) * 1 :=
      mul_le_mul_of_nonneg_left hc hcoef
    _ ≤ (P.p + P.q) * s ^ (P.q - 1) := by
      have hfirst := mul_le_mul_of_nonneg_left hpq P.p_pos.le
      have hsecond := mul_le_mul_of_nonneg_right hδ1 (mul_nonneg P.q_pos.le hq0)
      nlinarith

 
theorem normalized_angularDerivative_bound (P : Parameter) {δ s c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (hc : |c| ≤ 1) :
    |P.angularDerivative δ s c| / P.f δ s ≤
      (P.p + P.q) * (3 : ℝ) ^ P.η * δ ^ (-1 - P.η) * (P.D δ s) ^ P.η := by
  have hf := P.f_pos hδ hs
  have hfδ := P.f_ge_δ hδ.le hs.le
  have hf3 := P.f_le_three hδ.le hδ1 hs.le hs1
  have hθ := P.angularDerivative_bound hδ.le hδ1 hs hs1 hc
  have hbase : |P.angularDerivative δ s c| / P.f δ s ≤
      (P.p + P.q) / δ * s ^ (P.q - 1) := by
    calc
      _ ≤ ((P.p + P.q) * s ^ (P.q - 1)) / P.f δ s :=
        div_le_div_of_nonneg_right hθ hf.le
      _ ≤ ((P.p + P.q) * s ^ (P.q - 1)) / δ :=
        div_le_div_of_nonneg_left (by have := P.p_pos; have := P.q_pos; positivity)
          hδ hfδ
      _ = (P.p + P.q) / δ * s ^ (P.q - 1) := by ring
  have hD : (P.D δ s) ^ P.η =
      δ ^ P.η / (P.f δ s) ^ P.η * s ^ (P.q - 1) := by
    unfold D
    rw [Real.mul_rpow (div_pos hδ hf).le (Real.rpow_nonneg hs.le _),
      Real.div_rpow hδ.le hf.le, ← Real.rpow_mul hs.le, P.η_exponent]
  have hδpow : δ ^ (-1 - P.η) * δ ^ P.η = δ⁻¹ := by
    rw [← Real.rpow_add hδ]
    convert Real.rpow_neg_one δ using 1
    congr 1
    ring
  have hfη : (P.f δ s) ^ P.η ≤ (3 : ℝ) ^ P.η :=
    Real.rpow_le_rpow hf.le hf3 P.η_pos.le
  have hratio : 1 ≤ (3 : ℝ) ^ P.η / (P.f δ s) ^ P.η :=
    (one_le_div (Real.rpow_pos_of_pos hf _)).2 hfη
  rw [hD]
  have hrew : (P.p + P.q) * (3 : ℝ) ^ P.η * δ ^ (-1 - P.η) *
      (δ ^ P.η / (P.f δ s) ^ P.η * s ^ (P.q - 1)) =
      ((P.p + P.q) / δ * s ^ (P.q - 1)) *
        ((3 : ℝ) ^ P.η / (P.f δ s) ^ P.η) := by
    calc
      _ = (P.p + P.q) * s ^ (P.q - 1) * ((3 : ℝ) ^ P.η /
        (P.f δ s) ^ P.η) * (δ ^ (-1 - P.η) * δ ^ P.η) := by ring
      _ = _ := by rw [hδpow]; ring
  rw [hrew]
  exact hbase.trans (le_mul_of_one_le_right
    (by have := P.p_pos; have := P.q_pos; positivity) hratio)

 
def angleGenerator (P : Parameter) (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv (deriv g) θ / 2 + (1 - 2 * P.a) * (Real.cos θ / Real.sin θ) * deriv g θ

lemma hasDerivAt_sinePower (r θ : ℝ) (hs : 0 < Real.sin θ) :
    HasDerivAt (fun t : ℝ => Real.sin t ^ r)
      (r * Real.cos θ * Real.sin θ ^ (r - 1)) θ := by
  convert! (Real.hasDerivAt_sin θ).rpow_const (Or.inl hs.ne') using 1
  ring

lemma hasDerivAt_sinePower_first (r θ : ℝ) (hs : 0 < Real.sin θ) :
    HasDerivAt (fun t : ℝ => r * Real.cos t * Real.sin t ^ (r - 1))
      (r * (r - 1) * Real.cos θ ^ 2 * Real.sin θ ^ (r - 2) - r * Real.sin θ ^ r) θ := by
  have hp : Real.sin θ ^ (r - 1) * Real.sin θ = Real.sin θ ^ r := by
    convert! (Real.rpow_add_one hs.ne' (r - 1)).symm using 1
    congr 1
    ring
  convert! ((Real.hasDerivAt_cos θ).const_mul r).mul
    ((Real.hasDerivAt_sin θ).rpow_const (p := r - 1) (Or.inl hs.ne')) using 1
  rw [show r - 1 - 1 = r - 2 by ring]
  rw [← hp]
  ring

lemma deriv_sinePower (r θ : ℝ) (hs : 0 < Real.sin θ) :
    deriv (fun t : ℝ => Real.sin t ^ r) θ = r * Real.cos θ * Real.sin θ ^ (r - 1) :=
  (hasDerivAt_sinePower r θ hs).deriv

lemma secondDeriv_sinePower (r θ : ℝ) (hs : 0 < Real.sin θ) :
    deriv (deriv (fun t : ℝ => Real.sin t ^ r)) θ =
      r * (r - 1) * Real.cos θ ^ 2 * Real.sin θ ^ (r - 2) - r * Real.sin θ ^ r := by
  have heq : deriv (fun t : ℝ => Real.sin t ^ r) =ᶠ[nhds θ]
      (fun t : ℝ => r * Real.cos t * Real.sin t ^ (r - 1)) := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds hs)] with t ht
    exact deriv_sinePower r t ht
  exact ((hasDerivAt_sinePower_first r θ hs).congr_of_eventuallyEq heq).deriv

 
theorem sine_generator (P : Parameter) (r θ : ℝ) (hs : 0 < Real.sin θ) :
    P.angleGenerator (fun t : ℝ => Real.sin t ^ r) θ / (Real.sin θ ^ r) =
      -r / 2 + r * (r - P.p) / 2 * (Real.cos θ / Real.sin θ) ^ 2 := by
  have hpow1 : Real.sin θ ^ (r - 1) = Real.sin θ ^ r / Real.sin θ := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  have hpow2 : Real.sin θ ^ (r - 2) = Real.sin θ ^ r / Real.sin θ ^ 2 := by
    rw [Real.rpow_sub hs, Real.rpow_two]
  have hsp : Real.sin θ ^ r ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  unfold angleGenerator
  rw [secondDeriv_sinePower r θ hs, deriv_sinePower r θ hs, hpow1, hpow2]
  unfold p
  field_simp
  ring

lemma hasDerivAt_factor (P : Parameter) {δ θ : ℝ} (hs : 0 < Real.sin θ) :
    HasDerivAt (fun t : ℝ => P.f δ (Real.sin t))
      (P.angularDerivative δ (Real.sin θ) (Real.cos θ)) θ := by
  convert! (hasDerivAt_sinePower P.p θ hs).add
    (((hasDerivAt_sinePower P.q θ hs).const_add 1).const_mul δ) using 1
  unfold angularDerivative
  ring

 
def C₂ (P : Parameter) : ℝ := ((P.p + P.q) * (3 : ℝ) ^ P.η) ^ 2

 
def youngConstant (P : Parameter) (C ε : ℝ) : ℝ :=
  (1 - 2 * P.η) * C ^ (1 / (1 - 2 * P.η)) *
    (P.η / ε) ^ (2 * P.η / (1 - 2 * P.η))

lemma C₂_pos (P : Parameter) : 0 < P.C₂ := by
  unfold C₂
  have := P.p_pos
  have := P.q_pos
  positivity

 

end Parameter
end SLEExactGauge
end
end
end
end
end
end
end
end

end OAI
