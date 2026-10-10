import OAI.NumberTheory.CubicMoment.Estimates.MomentExponents

namespace OAI

/-! Numerical consequences of the actual moment exponents. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rewriting the first configuration's sharp moment inequalities in
terms of factor defects yields the manuscript's rigidity conclusion. -/
theorem first_shape_multiplicity_rigidity (a v : ι → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r)
    (hmoment : ∀ k : ι → ℕ,
      1/2 ≤ (∑ i, (k i:ℝ)*a i) → (∑ i, (k i:ℝ)*a i) ≤ 2 →
      r+2*(∑ i, (k i:ℝ)*v i) ≤ 2/3+(5/3)*(∑ i, (k i:ℝ)*a i)) :
    (∀ i, v i = 5*a i/6) ∧ r = 2/3 := by
  let d : ι → ℝ := fun i => v i-5*a i/6
  have hd (k : ι → ℕ) : (∑ i, (k i:ℝ)*d i) =
      (∑ i, (k i:ℝ)*v i)-(5/6)*(∑ i, (k i:ℝ)*a i) := by
    calc
      _ = ∑ i, ((k i:ℝ)*v i-(5/6)*((k i:ℝ)*a i)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [d]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib,Finset.mul_sum]
  have hdone : (∑ i, d i) = (∑ i, v i)-5/6 := by
    simpa only [Nat.cast_one,one_mul,hsum,mul_one] using hd (fun _ => 1)
  have hlarge' : 2/3-2*(∑ i, d i) ≤ r := by rw [hdone]; linarith
  have hm : ∀ k : ι → ℕ,
      1/2 ≤ (∑ i, (k i:ℝ)*a i) → (∑ i, (k i:ℝ)*a i) ≤ 2 →
      r ≤ 2/3-2*(∑ i, (k i:ℝ)*d i) := by
    intro k hk₀ hk₁
    rw [hd]
    linarith [hmoment k hk₀ hk₁]
  obtain ⟨hz,hr⟩ := exceptional_multiplicity_rigidity a d r ha hsum hlarge' hm
  refine ⟨?_,hr⟩
  intro i
  have hi := hz i
  dsimp [d] at hi
  linarith

/-- In the balanced configuration, the second moment lower bound and
all actual fixed-copy ordinary moments contradict every factor having
length exponent strictly below one. -/
theorem balanced_multiplicity_contradiction (a v : ι → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hv : ∀ i, v i ≤ a i)
    (hsum : ∑ i, a i = 1) (hlarge : 7/3-2*(∑ i, v i) ≤ r)
    (hcard : r ≤ 2/3)
    (hmoment : ∀ k : ι → ℕ, r+2*(∑ i, (k i:ℝ)*v i) ≤
      (∑ i, (k i:ℝ)*a i)+max (4/3) (∑ i, (k i:ℝ)*a i)) : False := by
  have hk2 (f : ι → ℝ) : (∑ i, ((2:ℕ):ℝ)*f i) = 2*(∑ i, f i) := by
    rw [Finset.mul_sum]
    norm_num
  have h2 := hmoment (fun _ => 2)
  simp only [hk2,hsum] at h2
  norm_num at h2
  have hfourth : r+4*(∑ i, v i) ≤ 4 := by linarith
  obtain ⟨hr,hvsum⟩ := balanced_moment_saturation hlarge hcard hfourth
  obtain ⟨j,hj,hvj⟩ := exists_balanced_factor a v (fun i => (ha i).1) hv hsum hvsum
  let k : ι → ℕ := fun i => 1+if i=j then 1 else 0
  have hk (f : ι → ℝ) : (∑ i, (k i:ℝ)*f i) = (∑ i, f i)+f j := by
    simp [k,add_mul,Finset.sum_add_distrib]
  have hb := hmoment k
  simp only [hk,hsum,hvsum,hr] at hb
  have hgap := balanced_extra_factor_gap (z := 1+a j) (by linarith) (by linarith [(ha j).2])
  have hbad : 2/3 ≤ max (4/3) (1+a j)-2*(1+a j)/3 := by nlinarith
  exact not_lt_of_ge hbad hgap

end CubicFirstMoment

end

end OAI
