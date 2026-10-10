import OAI.NumberTheory.JointDickman.Arithmetic.SparsePrimeReciprocal

namespace OAI

/-! # Passing the sparse prime estimate from integer to real scales -/
namespace JointDickman
open Filter Finset TwoPointCorrelations
open scoped Topology

lemma floor_rpow_eventually_lower {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, x^a ≤ (⌊x^b⌋₊:ℝ) := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1:ℝ),hg] with x hx hg
  have hx0 : 0 < x := by linarith
  have ha1 : 1 ≤ x^a := Real.one_le_rpow hx ha.le
  have he : x^b = x^a*x^(b-a) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hf := Nat.lt_floor_add_one (x^b)
  have hh : 2*x^a ≤ x^b := by rw [he]; nlinarith
  nlinarith

lemma mellin_real_scale_eventually : ∀ᶠ x : ℝ in atTop,
    let q := ⌊x^((1:ℝ)/10)⌋₊
    2 ≤ q ∧ (q:ℝ)^10 ≤ x ∧ x ≤ (q:ℝ)^11 ∧ x^((1:ℝ)/20) ≤ (q:ℝ) := by
  have h11 := floor_rpow_eventually_lower (a := (1:ℝ)/11) (b := 1/10)
    (by norm_num) (by norm_num)
  have h20 := floor_rpow_eventually_lower (a := (1:ℝ)/20) (b := 1/10)
    (by norm_num) (by norm_num)
  have hg := (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10))).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1:ℝ),h11,h20,hg] with x hx h11 h20 hg
  dsimp only
  have hx0 : 0 < x := by linarith
  refine ⟨hg,?_,?_,h20⟩
  · have hf := Nat.floor_le (Real.rpow_nonneg hx0.le ((1:ℝ)/10))
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌊x^((1:ℝ)/10)⌋₊) hf 10
    have he : (x^((1:ℝ)/10))^10=x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rwa [he] at hh
  · have hh := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le ((1:ℝ)/11)) h11 11
    have he : (x^((1:ℝ)/11))^11=x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rwa [he] at hh

/-- Arbitrary sufficiently large real prime lengths are allowed; the
integer auxiliary scale is no longer visible to applications. -/
theorem sparse_prime_reciprocal_real (B : ℝ) (hB : 1 ≤ B) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ᶠ N : ℝ in atTop, ∀ (Q : Finset ℕ) (S : Finset ℝ),
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ N^B) →
      (S.card:ℝ) ≤ N^γ →
      ∀ f : ℕ → ℂ, OneBounded f →
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun n => -Real.log (n:ℝ)) t‖^2) ≤ C/(Real.log N)^2 := by
  obtain ⟨C,κ,hC,hκ,hbound⟩ := sparse_prime_reciprocal_sampling (20*B) (by linarith)
  refine ⟨C,κ/20,hC,by positivity,?_⟩
  have hscale : Tendsto (fun x : ℝ => ⌊x^((1:ℝ)/10)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [mellin_real_scale_eventually,hscale.eventually hbound,
    eventually_ge_atTop (1:ℝ)] with N hscale hbound hN
  let q := ⌊N^((1:ℝ)/10)⌋₊
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hN0 : 0 < N := by linarith
  intro Q S hQ hsep hdiam hcard f hf
  apply hbound N Q S hscale.2.1 hscale.2.2.1 hQ hsep _ _ f hf
  · intro x hx y hy
    apply (hdiam x hx y hy).trans
    calc
      N^B = (N^((1:ℝ)/20))^(20*B) := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ (q:ℝ)^(20*B) := Real.rpow_le_rpow (by positivity) hscale.2.2.2 (by linarith)
  · apply hcard.trans
    calc
      N^(κ/20) = (N^((1:ℝ)/20))^κ := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ (q:ℝ)^κ := Real.rpow_le_rpow (by positivity) hscale.2.2.2 hκ.le

end JointDickman

end OAI
