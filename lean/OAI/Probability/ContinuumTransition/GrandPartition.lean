import OAI.Probability.ContinuumTransition.CanonicalIntegral

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def grandPartition (φ : ℝ → ℝ) (t β h L : ℝ) : ℝ :=
  ∑' N : ℕ, Real.exp (t * h * N) * partition φ β L N

theorem summable_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    Summable (fun N : ℕ => Real.exp (t * h * N) * partition φ β L N) := by
  apply Summable.of_nonneg_of_le (fun N => mul_nonneg (Real.exp_pos _).le
    (partition_nonneg φ β L N)) _
    (Real.summable_pow_div_factorial (Real.exp (t * h) * (L ^ 3 * Real.exp (β * B))))
  intro N
  have hb := mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos (t * h * N)).le
  apply hb.trans_eq
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul, mul_pow]
  ring

theorem grandPartition_le_exp {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    grandPartition φ t β h L ≤ Real.exp (L ^ 3 * Real.exp (t * h + β * B)) := by
  let z := L ^ 3 * Real.exp (t * h + β * B)
  have hz : HasSum (fun N : ℕ => z ^ N / (N.factorial : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  unfold grandPartition
  rw [← hz.tsum_eq]
  apply (summable_grandPartition hφ hβ hL hstable t h).tsum_le_tsum _ hz.summable
  intro N
  apply (mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos _).le).trans_eq
  dsimp [z]
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul,
    Real.exp_add, mul_pow, mul_pow]
  ring

theorem tsum_logconvex_bound {f g k : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hk : Summable k)
    (hfS : Summable f) (hgS : Summable g) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hbound : ∀ n, k n ≤ f n ^ a * g n ^ b) :
    (∑' n, k n) ≤ (∑' n, f n) ^ a * (∑' n, g n) ^ b := by
  have heq (x c : ℝ) (hx : 0 ≤ x) (hc : 0 < c) : (x ^ c) ^ (1 / c) = x := by
    rw [← Real.rpow_mul hx, mul_one_div_cancel hc.ne', Real.rpow_one]
  have hu : Summable (fun n => (f n ^ a) ^ (1 / a)) := by
    simpa only [heq _ a (hf _) ha] using hfS
  have hv : Summable (fun n => (g n ^ b) ^ (1 / b)) := by
    simpa only [heq _ b (hg _) hb] using hgS
  obtain ⟨hS, hH⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (fun n => Real.rpow_nonneg (hf n) a) (fun n => Real.rpow_nonneg (hg n) b) hu hv
  simp only [heq _ a (hf _) ha, heq _ b (hg _) hb, one_div_one_div] at hH
  exact (hk.tsum_le_tsum hbound hS).trans hH

theorem convexOn_log_tsum {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (F : ℕ → E → ℝ)
    (hpos : ∀ n x, x ∈ s → 0 < F n x)
    (hconv : ∀ n, ConvexOn ℝ s (fun x => Real.log (F n x)))
    (hS : ∀ x, x ∈ s → Summable (fun n => F n x)) :
    ConvexOn ℝ s (fun x => Real.log (∑' n, F n x)) := by
  have hp (x : E) (hx : x ∈ s) : 0 < ∑' n, F n x :=
    (hpos 0 x hx).trans_le ((hS x hx).le_tsum 0 (fun n _ => (hpos n x hx).le))
  refine convexOn_iff_forall_pos.mpr ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hs hx hy ha.le hb.le hab
  have hbnd (n : ℕ) : F n (a • x + b • y) ≤ F n x ^ a * F n y ^ b := by
    have hc := (hconv n).2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hc
    apply (Real.log_le_log_iff (hpos n _ hz) (mul_pos
      (Real.rpow_pos_of_pos (hpos n x hx) a) (Real.rpow_pos_of_pos (hpos n y hy) b))).mp
    rw [Real.log_mul (Real.rpow_pos_of_pos (hpos n x hx) a).ne'
      (Real.rpow_pos_of_pos (hpos n y hy) b).ne', Real.log_rpow (hpos n x hx),
      Real.log_rpow (hpos n y hy)]
    exact hc
  have hHolder := tsum_logconvex_bound (fun n => (hpos n x hx).le)
    (fun n => (hpos n y hy).le) (hS _ hz) (hS x hx) (hS y hy) ha hb hab hbnd
  calc
    _ ≤ Real.log ((∑' n, F n x) ^ a * (∑' n, F n y) ^ b) :=
      Real.log_le_log (hp _ hz) hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos (hp x hx) a).ne'
      (Real.rpow_pos_of_pos (hp y hy) b).ne',
      Real.log_rpow (hp x hx), Real.log_rpow (hp y hy)]; rfl

theorem convexOn_log_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t : ℝ) :
    ConvexOn ℝ {x : ℝ × ℝ | 0 < x.1}
      (fun x => Real.log (grandPartition φ t x.1 x.2 L)) := by
  have hdomain : Convex ℝ {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x.1 + b * y.1
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by simpa using hab
      simpa [hb'] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
  apply convexOn_log_tsum hdomain
    (fun N x => Real.exp (t * x.2 * N) * partition φ x.1 L N)
  · intro N x hx
    exact mul_pos (Real.exp_pos _) (partition_pos hφ hx.le hL hstable N)
  · intro N
    have hc := convexOn_log_partition hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨hdomain, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz := hdomain hx hy ha.le hb.le hab
    have log_eq (z : ℝ × ℝ) (hz : 0 < z.1) :
        Real.log (Real.exp (t * z.2 * N) * partition φ z.1 L N) =
          t * z.2 * N + Real.log (partition φ z.1 L N) := by
      rw [Real.log_mul (Real.exp_pos _).ne'
        (partition_pos hφ hz.le hL hstable N).ne', Real.log_exp]
    rw [log_eq _ hz, log_eq _ hx, log_eq _ hy]
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have hi := hc.2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    nlinarith only [hi]
  · intro x hx
    exact summable_grandPartition hφ hx.le hL.le hstable t x.2

end ContinuumTemperature
end

end OAI
