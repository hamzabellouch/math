import OAI.Combinatorics.BalancedRyser.Probability.PatternMoments

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {Ω A Y : Type*} [Fintype Ω] [Fintype A] [Fintype Y]

lemma expectation_add (p f g : Ω → ℝ) :
    expectation p (fun ω => f ω + g ω) = expectation p f + expectation p g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_nonneg (p f : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expectation p f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hp ω) (hf ω)

theorem positive_extension_sum (p f : Ω → ℝ) (I : A → Ω → ℝ) :
    (∑ a, expectation p (fun ω => f ω * (I a ω + expectation p (I a)))) =
      expectation p (fun ω => f ω * count I ω) +
        expectation p f * expectation p (count I) := by
  classical
  rw [← expectation_sum]
  have hpoint : (fun ω => ∑ a, f ω * (I a ω + expectation p (I a))) =
      (fun ω => f ω * count I ω + f ω * expectation p (count I)) := by
    funext ω
    rw [show expectation p (count I) = ∑ a, expectation p (I a) from
      expectation_sum p I]
    simp only [count, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hpoint, expectation_add, expectation_mul_const]

theorem centered_weight_extension_bound [DecidableEq Y]
    (p f : Ω → ℝ) (I : A → Ω → ℝ) (expose : Ω → Y) (M : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hf : ∀ ω, 0 ≤ f ω)
    (hconst : ∀ ω ω', expose ω = expose ω' → f ω = f ω')
    (hconditional : ∀ y,
      (∑ ω : {ω // expose ω = y}, p ω * count I ω) ≤
        M * ∑ ω : {ω // expose ω = y}, p ω) :
    (∑ a, expectation p (fun ω => f ω * (I a ω + expectation p (I a)))) ≤
      (2 * M) * expectation p f := by
  have hweighted := weighted_fiber_bound p (count I) f expose M hf hconst hconditional
  have hmean := weighted_fiber_bound p (count I) (fun _ => 1) expose M
    (fun _ => by norm_num) (fun _ _ _ => rfl) hconditional
  simp only [one_mul, expectation, mul_one, hp1] at hmean
  have hEf := expectation_nonneg p f hp hf
  have hmeanmul := mul_le_mul_of_nonneg_left hmean hEf
  change expectation p f * expectation p (count I) ≤ expectation p f * M at hmeanmul
  rw [positive_extension_sum]
  nlinarith

def positiveWeight (p : Ω → ℝ) (I : A → Ω → ℝ) (pre : List A) : ℝ :=
  expectation p (fun ω => (pre.map (fun a => I a ω + expectation p (I a))).prod)

omit [Fintype A] in
lemma positiveWeight_nil (p : Ω → ℝ) (I : A → Ω → ℝ)
    (hp1 : ∑ ω, p ω = 1) : positiveWeight p I [] = 1 := by
  simp [positiveWeight, expectation, hp1]

omit [Fintype A] in
lemma positiveWeight_nonneg (p : Ω → ℝ) (I : A → Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hI : ∀ a ω, 0 ≤ I a ω) (pre : List A) :
    0 ≤ positiveWeight p I pre := by
  apply expectation_nonneg p _ hp
  intro ω
  apply List.prod_nonneg
  intro y hy
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
  exact add_nonneg (hI a ω) (expectation_nonneg p (I a) hp (hI a))

omit [Fintype A] in
lemma positiveWeight_perm (p : Ω → ℝ) (I : A → Ω → ℝ)
    {pre post : List A} (h : pre.Perm post) :
    positiveWeight p I pre = positiveWeight p I post := by
  unfold positiveWeight
  congr 1
  funext ω
  exact (h.map _).prod_eq

theorem positiveWeight_extension [DecidableEq Y]
    (p : Ω → ℝ) (I : A → Ω → ℝ) (pre : List A) (expose : Ω → Y) (M : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hI : ∀ a ω, 0 ≤ I a ω)
    (hconst : ∀ ω ω', expose ω = expose ω' →
      (pre.map (fun a => I a ω + expectation p (I a))).prod =
        (pre.map (fun a => I a ω' + expectation p (I a))).prod)
    (hconditional : ∀ y,
      (∑ ω : {ω // expose ω = y}, p ω * count I ω) ≤
        M * ∑ ω : {ω // expose ω = y}, p ω) :
    (∑ a, positiveWeight p I (a :: pre)) ≤ (2 * M) * positiveWeight p I pre := by
  have hf (ω : Ω) : 0 ≤ (pre.map (fun a => I a ω + expectation p (I a))).prod := by
    apply List.prod_nonneg
    intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    exact add_nonneg (hI a ω) (expectation_nonneg p (I a) hp (hI a))
  have h := centered_weight_extension_bound p _ I expose M hp hp1 hf hconst hconditional
  simpa only [positiveWeight, List.map_cons, List.prod_cons, mul_comm] using h

theorem centered_weight_extension_bound_finset [DecidableEq Y]
    (p f : Ω → ℝ) (I : A → Ω → ℝ) (S : Finset A) (expose : Ω → Y) (M : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hf : ∀ ω, 0 ≤ f ω)
    (hconst : ∀ ω ω', expose ω = expose ω' → f ω = f ω')
    (hconditional : ∀ y,
      (∑ ω : {ω // expose ω = y}, p ω * (∑ a ∈ S, I a ω)) ≤
        M * ∑ ω : {ω // expose ω = y}, p ω) :
    (∑ a ∈ S, expectation p (fun ω => f ω * (I a ω + expectation p (I a)))) ≤
      (2 * M) * expectation p f := by
  classical
  let J : A → Ω → ℝ := fun a ω => if a ∈ S then I a ω else 0
  have hcount (ω : Ω) : count J ω = ∑ a ∈ S, I a ω := by
    simp [count, J]
  have hjmean (a : A) : expectation p (J a) =
      if a ∈ S then expectation p (I a) else 0 := by
    by_cases ha : a ∈ S <;> simp [J, ha, expectation]
  have h := centered_weight_extension_bound p f J expose M hp hp1 hf hconst
    (by intro y; simpa only [hcount] using hconditional y)
  have hsum : (∑ a, expectation p (fun ω => f ω * (J a ω + expectation p (J a)))) =
      ∑ a ∈ S, expectation p (fun ω => f ω * (I a ω + expectation p (I a))) := by
    calc
      (∑ a, expectation p (fun ω => f ω * (J a ω + expectation p (J a)))) =
          ∑ a, if a ∈ S then
            expectation p (fun ω => f ω * (I a ω + expectation p (I a))) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ∈ S <;> simp [J, ha, expectation]
      _ = _ := by simp
  rw [hsum] at h
  exact h

end Balanced.PatternMoments

end OAI
