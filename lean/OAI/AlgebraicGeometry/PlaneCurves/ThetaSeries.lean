import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import OAI.AlgebraicGeometry.PlaneCurves.ThetaExponents

namespace OAI

noncomputable section

namespace Nagata.W22

/-!
# Theta series, normal convergence, and derivatives
-/

section

/-- The formal frequency factor is the actual iterated complex derivative. -/
theorem iteratedDeriv_scalar_exp (A B x : ℂ) (c : ℕ) :
    iteratedDeriv c (fun y : ℂ => A * Complex.exp (B * y)) x =
      B ^ c * (A * Complex.exp (B * x)) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
  ring

end

section

/-! Analytic bridges used by normalized theta convergence: actual iterated
complex derivatives and their convergence on open sets. -/
open Filter Topology

/-- Iterating holomorphic differentiation stays holomorphic on the open domain. -/
theorem differentiableOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (c : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv c f) U := by
  induction c with
  | zero => simpa using hf
  | succ c ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

/-- All fixed derivatives of holomorphic functions converge locally uniformly
whenever the original functions converge locally uniformly. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv
    {α : Type*} {l : Filter α} {F : α → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ a in l, DifferentiableOn ℂ (F a) U) (hU : IsOpen U) (c : ℕ) :
    TendstoLocallyUniformlyOn (fun a => iteratedDeriv c (F a)) (iteratedDeriv c f) l U := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    have hiF : ∀ᶠ a in l, DifferentiableOn ℂ (iteratedDeriv c (F a)) U :=
      hF.mono fun a ha => differentiableOn_iteratedDeriv ha hU c
    simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hiF hU

/-- The polynomially weighted geometric majorant in the theta estimate is summable. -/
theorem summable_weighted_half (c : ℕ) :
    Summable (fun t : ℕ => ((t + 1 : ℕ) : ℝ) ^ c * (1 / 2 : ℝ) ^ t) := by
  have hs := (summable_nat_add_iff 1).2
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) c (r := 1 / 2)
      (by norm_num))
  convert hs.mul_left 2 using 1
  funext t
  simp only [pow_succ]
  ring

/-- Uniform linear-in-`z` domination, for any nonnegative weight sequence. -/
theorem weighted_term_le {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (t : ℕ) :
    w t * z ^ (t + 1) ≤ z * (w t * (1 / 2 : ℝ) ^ t) := by
  calc
    w t * z ^ (t + 1) = z * (w t * z ^ t) := by ring
    _ ≤ z * (w t * (1 / 2 : ℝ) ^ t) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzhalf t) (hw t)) hz

/-- A summable geometric majorant proves summability of every dominated tail. -/
theorem summable_weighted_tail {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    Summable (fun t => w t * z ^ (t + 1)) := by
  exact (hs.mul_left z).of_nonneg_of_le
    (fun t => mul_nonneg (hw t) (pow_nonneg hz _))
    (weighted_term_le hw hz hzhalf)

/-- The entire tail is bounded by a fixed finite constant times `z`. -/
theorem weighted_tail_le {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    (∑' t, w t * z ^ (t + 1)) ≤
      z * (∑' t, w t * (1 / 2 : ℝ) ^ t) := by
  calc
    _ ≤ ∑' t, z * (w t * (1 / 2 : ℝ) ^ t) :=
      (summable_weighted_tail hw hs hz hzhalf).tsum_le_tsum
        (weighted_term_le hw hz hzhalf) (hs.mul_left z)
    _ = _ := tsum_mul_left

/-- The theta-tail comparison tends to zero for any parameter approaching zero
within the interval `[0,1/2]`. No interchange of an unbounded series is assumed. -/
theorem tendsto_weighted_tail_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    (hz : Tendsto z l (𝓝 0))
    (hzrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2) :
    Tendsto (fun a => ∑' t, w t * z a ^ (t + 1)) l (𝓝 0) := by
  apply squeeze_zero'
    (hzrange.mono fun a ha => tsum_nonneg fun t => mul_nonneg (hw t) (pow_nonneg ha.1 _))
    (hzrange.mono fun a ha => weighted_tail_le hw hs ha.1 ha.2)
  simpa using hz.mul_const (∑' t, w t * (1 / 2 : ℝ) ^ t)

/-- Polynomial weights specialize the preceding estimate to the theta derivative tail. -/
theorem tendsto_polynomial_tail_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    (c : ℕ) (hz : Tendsto z l (𝓝 0))
    (hzrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2) :
    Tendsto (fun a => ∑' t : ℕ, ((t + 1 : ℕ) : ℝ) ^ c * z a ^ (t + 1))
      l (𝓝 0) :=
  tendsto_weighted_tail_zero (fun t => by positivity) (summable_weighted_half c) hz hzrange

/-- The actual affine polynomial weight of the derivative estimate is dominated
by a constant times `(t+1)^c`. -/
theorem affine_weight_le {A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n)
    (c t : ℕ) :
    (A + n * ((t + 1 : ℕ) : ℝ)) ^ c ≤
      (A + n) ^ c * ((t + 1 : ℕ) : ℝ) ^ c := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have ht : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le t)
  nlinarith [mul_nonneg hA (sub_nonneg.mpr ht)]

/-- Summability of the exact derivative majorant displayed in the manuscript. -/
theorem summable_affine_weighted_half {A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n)
    (c : ℕ) :
    Summable (fun t : ℕ => (A + n * ((t + 1 : ℕ) : ℝ)) ^ c * (1 / 2 : ℝ) ^ t) := by
  apply ((summable_weighted_half c).mul_left ((A + n) ^ c)).of_nonneg_of_le
  · intro t
    positivity
  · intro t
    calc
      _ ≤ ((A + n) ^ c * ((t + 1 : ℕ) : ℝ) ^ c) * (1 / 2 : ℝ) ^ t :=
        mul_le_mul_of_nonneg_right (affine_weight_le hA hn c t) (by positivity)
      _ = _ := by ring

/-- Vanishing of the exact polynomially weighted series used to bound every fixed
order derivative of the normalized theta series. -/
theorem tendsto_affine_weighted_tail_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    {A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n) (c : ℕ)
    (hz : Tendsto z l (𝓝 0))
    (hzrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2) :
    Tendsto (fun a => ∑' t : ℕ,
      (A + n * ((t + 1 : ℕ) : ℝ)) ^ c * z a ^ (t + 1)) l (𝓝 0) :=
  tendsto_weighted_tail_zero (fun t => by positivity)
    (summable_affine_weighted_half hA hn c) hz hzrange

/-- A norm bound by a summable weighted geometric sequence gives summability. -/
theorem summable_of_weighted_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {C z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2)
    (hf : ∀ t, ‖f t‖ ≤ C * (w t * z ^ (t + 1))) : Summable f := by
  exact ((summable_weighted_tail hw hs hz hzhalf).mul_left C).of_norm_bounded hf

/-- Uniform scalar majorants also bound the norm of the whole series. -/
theorem norm_tsum_le_weighted_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {C z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2)
    (hf : ∀ t, ‖f t‖ ≤ C * (w t * z ^ (t + 1))) :
    ‖∑' t, f t‖ ≤ C * (∑' t, w t * z ^ (t + 1)) := by
  have hmajor := (summable_weighted_tail hw hs hz hzhalf).mul_left C
  have hnorm : Summable (fun t => ‖f t‖) :=
    hmajor.of_nonneg_of_le (fun t => norm_nonneg _) hf
  calc
    _ ≤ ∑' t, ‖f t‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' t, C * (w t * z ^ (t + 1)) := hnorm.tsum_le_tsum hf hmajor
    _ = _ := tsum_mul_left

/-- A bilateral summable sequence is its central term plus its two positive tails. -/
theorem tsum_int_eq_center_add_tails {E : Type*} [NormedAddCommGroup E]
    {f : ℤ → E}
    (hp : Summable (fun t : ℕ => f (t + 1)))
    (hm : Summable (fun t : ℕ => f (-(t + 1)))) :
    (∑' p : ℤ, f p) = f 0 +
      (∑' t : ℕ, f (t + 1)) + (∑' t : ℕ, f (-(t + 1))) := by
  have hp0 : Summable (fun t : ℕ => f t) := (summable_nat_add_iff 1).1 hp
  rw [tsum_of_nat_of_neg_add_one hp0 hm, ← hp0.sum_add_tsum_nat_add 1]
  simp

/-- Uniform domination by vanishing weighted tails implies uniform convergence to zero. -/
theorem tendstoUniformlyOn_tsum_zero_of_weighted_bound
    {α β E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {l : Filter α} {s : Set β} {f : α → ℕ → β → E} {z : α → ℝ}
    {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    (C : ℝ) (hz : Tendsto z l (𝓝 0))
    (hrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2)
    (hbound : ∀ᶠ a in l, ∀ t x, x ∈ s →
      ‖f a t x‖ ≤ C * (w t * z a ^ (t + 1))) :
    TendstoUniformlyOn (fun a x => ∑' t, f a t x) (fun _ => 0) l s := by
  have hlim : Tendsto (fun a => C * (∑' t, w t * z a ^ (t + 1))) l (𝓝 0) := by
    simpa using (tendsto_weighted_tail_zero hw hs hz hrange).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ a in l, C * (∑' t, w t * z a ^ (t + 1)) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hrange, hbound, hsmall] with a ha hb he x hx
  simpa only [dist_zero_left] using
    (norm_tsum_le_weighted_bound hw hs ha.1 ha.2 (fun t => hb t x hx)).trans_lt he
private theorem norm_tsum_int_sub_center_le_weighted_bound
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℤ → E} {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {C z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2)
    (hp : ∀ t : ℕ, ‖f (t + 1)‖ ≤ C * (w t * z ^ (t + 1)))
    (hm : ∀ t : ℕ, ‖f (-(t + 1))‖ ≤ C * (w t * z ^ (t + 1))) :
    ‖(∑' p, f p) - f 0‖ ≤ 2 * C * (∑' t, w t * z ^ (t + 1)) := by
  have hps := summable_of_weighted_bound hw hs hz hzhalf hp
  have hms := summable_of_weighted_bound hw hs hz hzhalf hm
  rw [tsum_int_eq_center_add_tails hps hms]
  have hid : (f 0 + (∑' t : ℕ, f (t + 1)) + (∑' t : ℕ, f (-(t + 1)))) - f 0 =
      (∑' t : ℕ, f (t + 1)) + (∑' t : ℕ, f (-(t + 1))) := by abel
  rw [hid]
  calc
    _ ≤ ‖∑' t : ℕ, f (t + 1)‖ + ‖∑' t : ℕ, f (-(t + 1))‖ := norm_add_le _ _
    _ ≤ C * (∑' t, w t * z ^ (t + 1)) + C * (∑' t, w t * z ^ (t + 1)) :=
      add_le_add (norm_tsum_le_weighted_bound hw hs hz hzhalf hp)
        (norm_tsum_le_weighted_bound hw hs hz hzhalf hm)
    _ = _ := by ring

/-- A bilateral series with a fixed central term and uniformly vanishing positive
and negative tails converges uniformly to that central term. -/
theorem tendstoUniformlyOn_tsum_int_center_of_weighted_bound
    {α β E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {l : Filter α} {s : Set β} {f : α → ℤ → β → E} {g : β → E} {z : α → ℝ}
    {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    (C : ℝ) (hz : Tendsto z l (𝓝 0))
    (hrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2)
    (hcenter : ∀ a x, f a 0 x = g x)
    (hpos : ∀ᶠ a in l, ∀ t : ℕ, ∀ x ∈ s,
      ‖f a (t + 1) x‖ ≤ C * (w t * z a ^ (t + 1)))
    (hneg : ∀ᶠ a in l, ∀ t : ℕ, ∀ x ∈ s,
      ‖f a (-(t + 1)) x‖ ≤ C * (w t * z a ^ (t + 1))) :
    TendstoUniformlyOn (fun a x => ∑' p : ℤ, f a p x) g l s := by
  have hlim : Tendsto (fun a => 2 * C * (∑' t, w t * z a ^ (t + 1))) l (𝓝 0) := by
    simpa using (tendsto_weighted_tail_zero hw hs hz hrange).const_mul (2 * C)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ a in l, 2 * C * (∑' t, w t * z a ^ (t + 1)) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hrange, hpos, hneg, hsmall] with a ha hp hm he x hx
  have hnorm := norm_tsum_int_sub_center_le_weighted_bound
    (f := fun p => f a p x) (C := C) hw hs ha.1 ha.2
    (fun t => hp t x hx) (fun t => hm t x hx)
  simpa only [dist_eq_norm, norm_sub_rev, hcenter] using hnorm.trans_lt he

end

section
open Nagata.W07

/-- An explicit summable majorant for all integer indices on a fixed disk. -/
def thetaDiskMajorant (n K R z : ℝ) (c : ℕ) (p : ℤ) : ℝ :=
  Real.exp (|K| * R) * (|K| + n * (p.natAbs : ℝ)) ^ c * z ^ p.natAbs
theorem summable_thetaDiskMajorant {n z : ℝ} (hn : 0 ≤ n)
    (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (K R : ℝ) (c : ℕ) :
    Summable (thetaDiskMajorant n K R z c) := by
  have hw : ∀ t : ℕ, 0 ≤ (|K| + n * ((t + 1 : ℕ) : ℝ)) ^ c := fun t => by positivity
  have hs := (summable_weighted_tail hw
    (summable_affine_weighted_half (abs_nonneg K) hn c) hz hzhalf).mul_left
      (Real.exp (|K| * R))
  have hnat (t : ℕ) : ((t : ℤ) + 1).natAbs = t + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Int.natAbs_natCast (t + 1)
  have hp : Summable (fun t : ℕ => thetaDiskMajorant n K R z c (t + 1)) := by
    simpa only [thetaDiskMajorant, hnat, mul_assoc] using hs
  have hm : Summable (fun t : ℕ => thetaDiskMajorant n K R z c (-(t + 1))) := by
    simpa only [thetaDiskMajorant, Int.natAbs_neg, hnat, mul_assoc] using hs
  exact ((summable_nat_add_iff (f := fun t : ℕ => thetaDiskMajorant n K R z c t) 1).1 hp).of_nat_of_neg_add_one hm

end

section

open Filter Topology

open Nagata.W07

/-- Exactly the bilateral exponential series of equation `eq:normalized-theta`. -/
def normalizedThetaSeries (n a K : ℝ) (ε : ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  ∑' p : ℤ, normalizedThetaTerm n a K ε τ p x

/-- Sum of the explicit derivative summands. Identification with the derivative
of `normalizedThetaSeries` is recorded separately. -/
def normalizedThetaDerivativeSeries (n a K : ℝ) (ε : ℂ) (τ : ℝ)
    (c : ℕ) (x : ℂ) : ℂ :=
  ∑' p : ℤ, normalizedThetaDerivativeTerm n a K ε τ c p x

@[simp] theorem normalizedThetaDerivativeSeries_zero (n a K : ℝ) (ε : ℂ)
    (τ : ℝ) (x : ℂ) :
    normalizedThetaDerivativeSeries n a K ε τ 0 x = normalizedThetaSeries n a K ε τ x := by
  simp [normalizedThetaDerivativeSeries, normalizedThetaSeries]

/-- The concrete geometric parameter used in the compact-disk estimate vanishes. -/
theorem theta_geometric_parameter_tendsto_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a R : ℝ}
    (ha : 0 < a) (han : a < n) (hτ : Tendsto τ l (𝓝 0)) :
    Tendsto (fun j => Real.exp (n * R) * τ j ^ thetaMargin n a) l (𝓝 0) := by
  have hδ := thetaMargin_pos ha han
  have hc := (Real.continuousAt_rpow_const 0 (thetaMargin n a) (Or.inr hδ.le)).tendsto.comp hτ
  simpa only [Real.zero_rpow hδ.ne', mul_zero, Function.comp_def] using
    hc.const_mul (Real.exp (n * R))

/-- Every fixed formal derivative series converges uniformly on every disk to the
corresponding exponential derivative. Bounds and summability are discharged. -/
theorem tendstoUniformlyOn_normalizedThetaDerivativeSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (c : ℕ) :
    TendstoUniformlyOn (fun j => normalizedThetaDerivativeSeries n a K ε (τ j) c)
      (fun x => (K : ℂ) ^ c * Complex.exp ((K : ℂ) * x)) l
      {x : ℂ | ‖x‖ ≤ R} := by
  have hn : 0 ≤ n := le_of_lt (lt_trans ha han)
  let z : α → ℝ := fun j => Real.exp (n * R) * τ j ^ thetaMargin n a
  have hz : Tendsto z l (𝓝 0) := theta_geometric_parameter_tendsto_zero ha han hτ
  have hzhalf : ∀ᶠ j in l, z j < 1 / 2 := hz.eventually (gt_mem_nhds (by norm_num))
  have hτone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  have hrange : ∀ᶠ j in l, 0 ≤ z j ∧ z j ≤ 1 / 2 := by
    filter_upwards [hτpos, hzhalf] with j hj hzj
    exact ⟨mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hj.le _), hzj.le⟩
  apply tendstoUniformlyOn_tsum_int_center_of_weighted_bound
    (w := fun t : ℕ => (|K| + n * ((t + 1 : ℕ) : ℝ)) ^ c)
    (fun t => by positivity) (summable_affine_weighted_half (abs_nonneg K) hn c)
    (Real.exp (|K| * R)) hz hrange
  · intro j x
    exact normalizedThetaDerivativeTerm_zero_index n a K ε (τ j) c x
  · filter_upwards [hτpos, hτone] with j ht ht1 t x hx
    have hb := norm_normalizedThetaDerivativeTerm_le (a := a) (K := K)
      hn ht ht1.le hε hR hx c (((t + 1 : ℕ) : ℤ))
    simp only [Int.natAbs_natCast] at hb
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, z] using hb
  · filter_upwards [hτpos, hτone] with j ht ht1 t x hx
    have hb := norm_normalizedThetaDerivativeTerm_le (a := a) (K := K)
      hn ht ht1.le hε hR hx c (-((t + 1 : ℕ) : ℤ))
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hb
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, z] using hb

/-- The normalized theta series itself degenerates uniformly on compact disks. -/
theorem tendstoUniformlyOn_normalizedThetaSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoUniformlyOn (fun j => normalizedThetaSeries n a K ε (τ j))
      (fun x => Complex.exp ((K : ℂ) * x)) l {x : ℂ | ‖x‖ ≤ R} := by
  have h := tendstoUniformlyOn_normalizedThetaDerivativeSeries (K := K) ha han hε hR hτ hτpos 0
  change TendstoUniformlyOn (fun j x => normalizedThetaDerivativeSeries n a K ε (τ j) 0 x)
    (fun x => (K : ℂ) ^ 0 * Complex.exp ((K : ℂ) * x)) l {x : ℂ | ‖x‖ ≤ R} at h
  simpa only [normalizedThetaDerivativeSeries_zero, pow_zero, one_mul] using h

/-- Compact-uniform degeneration on the entire complex logarithmic coordinate plane. -/
theorem tendstoLocallyUniformlyOn_normalizedThetaSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => normalizedThetaSeries n a K ε (τ j))
      (fun x => Complex.exp ((K : ℂ) * x)) l Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro S hS hSc
  obtain ⟨R, hR⟩ := hSc.exists_bound_of_continuousOn (f := fun x : ℂ => x) continuous_id.continuousOn
  apply (tendstoUniformlyOn_normalizedThetaSeries ha han hε
    (le_max_right R 0) hτ hτpos).mono
  intro x hx
  exact (hR x hx).trans (le_max_left R 0)

end

section
open Nagata.W07

/-- The candidate frequency factor is exactly the actual complex derivative. -/
theorem hasDerivAt_normalizedThetaDerivativeTerm
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (c : ℕ) (p : ℤ) (x : ℂ) :
    HasDerivAt (normalizedThetaDerivativeTerm n a K ε τ c p)
      (normalizedThetaDerivativeTerm n a K ε τ (c + 1) p x) x := by
  let B : ℂ := ((K + n * (p : ℝ) : ℝ) : ℂ)
  let A : ℂ := ε ^ (-p) * ((τ ^ thetaExponent n a (p : ℝ) : ℝ) : ℂ)
  have h := ((((hasDerivAt_id x).const_mul B).cexp).const_mul A).const_mul (B ^ c)
  convert h using 1
  · rfl
  · dsimp [normalizedThetaDerivativeTerm, normalizedThetaTerm, A, B]
    ring

/-- Every frequency factor is the genuine iterated derivative of the summand. -/
theorem iteratedDeriv_normalizedThetaTerm
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (c : ℕ) (p : ℤ) (x : ℂ) :
    iteratedDeriv c (normalizedThetaTerm n a K ε τ p) x =
      normalizedThetaDerivativeTerm n a K ε τ c p x := by
  exact iteratedDeriv_scalar_exp
    (ε ^ (-p) * ((τ ^ thetaExponent n a (p : ℝ) : ℝ) : ℂ))
    (((K + n * (p : ℝ) : ℝ) : ℂ)) x c

end

section

/-! Termwise complex differentiation of the actual theta series on a fixed disk.
The geometric disk condition is eventually true in the degeneration, and is
discharged in the final convergence theorem. -/
open Filter Topology

open Nagata.W07

/-- Termwise differentiation is legitimate on a disk where the geometric bound
is at most one half. No differentiation rule is assumed for the series. -/
theorem deriv_normalizedThetaDerivativeSeries
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ < R) (c : ℕ) :
    deriv (normalizedThetaDerivativeSeries n a K ε τ c) x =
      normalizedThetaDerivativeSeries n a K ε τ (c + 1) x := by
  let z := Real.exp (n * R) * τ ^ thetaMargin n a
  have hz : 0 ≤ z := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)
  have hs := summable_thetaDiskMajorant hn hz hzhalf K R c
  have hsum := Complex.hasSum_deriv_of_summable_norm hs
    (F := fun p => normalizedThetaDerivativeTerm n a K ε τ c p)
    (U := {y : ℂ | ‖y‖ < R})
    (fun p y hy => (hasDerivAt_normalizedThetaDerivativeTerm n a K ε τ c p y).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_norm continuous_const)
    (fun p y hy => norm_normalizedThetaDerivativeTerm_le hn hτ hτone hε hR hy.le c p) hx
  have heq : (fun p : ℤ => deriv (normalizedThetaDerivativeTerm n a K ε τ c p) x) =
      (fun p : ℤ => normalizedThetaDerivativeTerm n a K ε τ (c + 1) p x) := by
    funext p
    exact (hasDerivAt_normalizedThetaDerivativeTerm n a K ε τ c p x).deriv
  rw [heq] at hsum
  exact hsum.tsum_eq.symm

/-- The entire derivative series is the iterated derivative of the genuine theta
series throughout the interior of the same disk. -/
theorem iteratedDeriv_normalizedThetaSeries
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ < R) (c : ℕ) :
    iteratedDeriv c (normalizedThetaSeries n a K ε τ) x =
      normalizedThetaDerivativeSeries n a K ε τ c x := by
  induction c generalizing x with
  | zero => simp
  | succ c ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv c (normalizedThetaSeries n a K ε τ) =ᶠ[𝓝 x]
        normalizedThetaDerivativeSeries n a K ε τ c := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq]
    exact deriv_normalizedThetaDerivativeSeries hn hτ hτone hε hR hzhalf hx c

/-- All actual complex derivatives of the normalized theta series converge
uniformly on every fixed compact disk. The auxiliary disk bound is discharged
by choosing the larger radius `R+1` and taking `τ` sufficiently small. -/
theorem tendstoUniformlyOn_iteratedDeriv_normalizedThetaSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (c : ℕ) :
    TendstoUniformlyOn (fun j => iteratedDeriv c (normalizedThetaSeries n a K ε (τ j)))
      (fun x => (K : ℂ) ^ c * Complex.exp ((K : ℂ) * x)) l
      {x : ℂ | ‖x‖ ≤ R} := by
  have hbase := tendstoUniformlyOn_normalizedThetaDerivativeSeries (K := K) ha han hε hR hτ hτpos c
  apply hbase.congr
  have hparam := theta_geometric_parameter_tendsto_zero (R := R + 1) ha han hτ
  have hhalf : ∀ᶠ j in l, Real.exp (n * (R + 1)) * τ j ^ thetaMargin n a < 1 / 2 :=
    hparam.eventually (gt_mem_nhds (by norm_num))
  have hone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hτpos, hhalf, hone] with j hj hh ho x hx
  exact (iteratedDeriv_normalizedThetaSeries (le_of_lt (lt_trans ha han)) hj ho.le hε
    (by linarith) hh.le (by dsimp at hx; linarith) c).symm

/-- The precise limiting x-jet entry needed in the finite matrix. -/
theorem tendsto_iteratedDeriv_normalizedThetaSeries_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (c : ℕ) :
    Tendsto (fun j => iteratedDeriv c (normalizedThetaSeries n a K ε (τ j)) 0)
      l (𝓝 ((K : ℂ) ^ c)) := by
  have h := (tendstoUniformlyOn_iteratedDeriv_normalizedThetaSeries
    (R := 0) (K := K) ha han hε le_rfl hτ hτpos c).tendsto_at (x := (0 : ℂ)) (by simp)
  simpa using h

end

/-! Actual normal convergence on a fixed disk, for the parameter range eventually
used in the theta degeneration. This supports integration on a compact contour. -/
open Filter Topology

section
open Nagata.W07

/-- Pointwise absolute summability with the same concrete disk majorant. -/
theorem summable_normalizedThetaTerm_norm_on_disk
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ ≤ R) :
    Summable (fun p : ℤ => ‖normalizedThetaTerm n a K ε τ p x‖) := by
  have hz : 0 ≤ Real.exp (n * R) * τ ^ thetaMargin n a :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)
  exact (summable_thetaDiskMajorant hn hz hzhalf K R 0).of_nonneg_of_le
    (fun p => norm_nonneg _) (fun p => by
      simpa [thetaDiskMajorant] using norm_normalizedThetaTerm_le hn hτ hτone hε hR hx p)

/-- The actual bilateral series has the stated sum at every point of the disk. -/
theorem hasSum_normalizedThetaTerm_on_disk
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ ≤ R) :
    HasSum (fun p : ℤ => normalizedThetaTerm n a K ε τ p x)
      (normalizedThetaSeries n a K ε τ x) :=
  (summable_normalizedThetaTerm_norm_on_disk hn hτ hτone hε hR hzhalf hx).of_norm.hasSum

/-- Uniform finite-sum convergence of the literal two-sided series on a disk. -/
theorem tendstoUniformlyOn_normalizedThetaSeries_partialSums
    {n a K τ R : ℝ} {ε : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2) :
    TendstoUniformlyOn
      (fun S : Finset ℤ => fun x => ∑ p ∈ S, normalizedThetaTerm n a K ε τ p x)
      (normalizedThetaSeries n a K ε τ) atTop {x : ℂ | ‖x‖ ≤ R} := by
  have hz : 0 ≤ Real.exp (n * R) * τ ^ thetaMargin n a :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)
  apply tendstoUniformlyOn_tsum (summable_thetaDiskMajorant hn hz hzhalf K R 0)
  intro p x hx
  simpa [thetaDiskMajorant] using norm_normalizedThetaTerm_le hn hτ hτone hε hR hx p

/-- On any fixed disk the literal finite-sum convergence applies for all
sufficiently small positive values of the degeneration parameter. -/
theorem eventually_normalizedThetaSeries_partialSums
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    ∀ᶠ j in l, TendstoUniformlyOn
      (fun S : Finset ℤ => fun x => ∑ p ∈ S, normalizedThetaTerm n a K ε (τ j) p x)
      (normalizedThetaSeries n a K ε (τ j)) atTop {x : ℂ | ‖x‖ ≤ R} := by
  have hp := theta_geometric_parameter_tendsto_zero (R := R) ha han hτ
  have hhalf := hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hone := hτ.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hτpos, hhalf, hone] with j hj hh ho
  exact tendstoUniformlyOn_normalizedThetaSeries_partialSums
    (le_of_lt (lt_trans ha han)) hj ho.le hε hR hh.le

end

end Nagata.W22

end

end OAI
