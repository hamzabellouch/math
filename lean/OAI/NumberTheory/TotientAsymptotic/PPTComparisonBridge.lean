import OAI.NumberTheory.TotientAsymptotic.CollisionInput
import OAI.NumberTheory.TotientFibers.FiniteFiber

namespace OAI

/-!
Fixed-common-factor and fixed-left-tail arithmetic for Ford's comparison estimate.
Fixing the left tail `a` includes its totient in `D = d * φ(a)`, and the common
prime product `c` supplies the divisor `r = φ(c)`.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_totient_primeProduct {b : ℕ} (p : Fin b → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (∏ i, p i).totient = shiftedProduct p := by
  classical
  have hprime : ∀ q ∈ Finset.univ.image p, q.Prime := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp i
  have hh := TotientFibers.totient_prime_prod hprime
  rw [Finset.prod_image (fun i _ j _ he => hinj he),
    Finset.prod_image (fun i _ j _ he => hinj he)] at hh
  exact hh

/-- The three factors are genuinely coprime; high primes are distinct. -/
lemma ppt_common_tail_totient {b c a : ℕ} (p : Fin b → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hca : c.Coprime a) (hcp : c.Coprime (∏ i, p i))
    (hap : a.Coprime (∏ i, p i)) :
    (c*a*∏ i, p i).totient = c.totient*a.totient*shiftedProduct p := by
  rw [Nat.totient_mul (hcp.mul_left hap), Nat.totient_mul hca,
    ppt_totient_primeProduct p hp hinj]

/-- Canceling the totient of the actual common factor gives exactly the
equation required by the `l = 0` comparison theorem. -/
theorem ppt_fixed_comparison_equation {b d c a e : ℕ}
    (p q : Fin b → ℕ) (hc : 0 < c)
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hpinj : Function.Injective p) (hqinj : Function.Injective q)
    (hca : c.Coprime a) (hcp : c.Coprime (∏ i, p i))
    (hap : a.Coprime (∏ i, p i))
    (hce : c.Coprime e) (hcq : c.Coprime (∏ i, q i))
    (heq : e.Coprime (∏ i, q i))
    (hvalue : (c*e*∏ i, q i).totient = d*(c*a*∏ i, p i).totient) :
    (d*a.totient)*shiftedProduct p = e.totient*shiftedProduct q := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hc)
  calc
    c.totient*((d*a.totient)*shiftedProduct p) =
        d*(c.totient*a.totient*shiftedProduct p) := by ring
    _ = d*(c*a*∏ i, p i).totient := by
      rw [ppt_common_tail_totient p hp hpinj hca hcp hap]
    _ = (c*e*∏ i, q i).totient := hvalue.symm
    _ = c.totient*(e.totient*shiftedProduct q) := by
      rw [ppt_common_tail_totient q hq hqinj hce hcq heq]
      ring

/-- The scale controls the seed-multiplied totient.  A bound on `φ(n)`
alone is insufficient when the seed multiplier exceeds one. -/
theorem ppt_fixed_comparison_size {b d c a : ℕ} {z : ℝ}
    (p : Fin b → ℕ) (hc : 0 < c)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hca : c.Coprime a) (hcp : c.Coprime (∏ i, p i))
    (hap : a.Coprime (∏ i, p i))
    (hsize : ((d*(c*a*∏ i, p i).totient : ℕ) : ℝ) ≤ z) :
    (((d*a.totient)*shiftedProduct p : ℕ) : ℝ) ≤ z/c.totient := by
  apply (le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hc)).mpr
  rw [ppt_common_tail_totient p hp hpinj hca hcp hap] at hsize
  push_cast at hsize ⊢
  nlinarith

def pptFixedComparisonPair {b : ℕ} (p q : Fin b → ℕ) (e : ℕ) : ShiftedPair b :=
  ⟨p, q, e.totient⟩

lemma pptFixedComparisonPair_equation {b d c a e : ℕ}
    (p q : Fin b → ℕ) (hc : 0 < c)
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hpinj : Function.Injective p) (hqinj : Function.Injective q)
    (hca : c.Coprime a) (hcp : c.Coprime (∏ i, p i))
    (hap : a.Coprime (∏ i, p i))
    (hce : c.Coprime e) (hcq : c.Coprime (∏ i, q i))
    (heq : e.Coprime (∏ i, q i))
    (hvalue : (c*e*∏ i, q i).totient = d*(c*a*∏ i, p i).totient) :
    (d*a.totient)*shiftedProduct (pptFixedComparisonPair p q e).left =
      (pptFixedComparisonPair p q e).remainder*
        shiftedProduct (pptFixedComparisonPair p q e).right :=
  ppt_fixed_comparison_equation p q hc hp hq hpinj hqinj hca hcp hap hce hcq heq hvalue

/-- At fixed `c,a`, the actual candidate integer is recovered from the
left high-prime list.  No injectivity of the totient is used. -/
lemma ppt_fixed_comparison_injective {b c a : ℕ} (S : Finset ℕ)
    (p q : ℕ → Fin b → ℕ) (e : ℕ → ℕ)
    (hreal : ∀ n ∈ S, n = c*a*∏ i, p n i) :
    Set.InjOn (fun n => pptFixedComparisonPair (p n) (q n) (e n)) (S : Set ℕ) := by
  intro n hn m hm he
  have hp : p n = p m := congrArg ShiftedPair.left he
  rw [hreal n hn, hreal m hm, hp]

/-- Direct unconditional use of the proved Ford comparison estimate on a
fixed `(c,a)` block.  All remaining hypotheses are the literal published
comparison predicates. -/
theorem ppt_fixed_comparison_count :
    ∃ C z₀ : ℝ, 0 < C ∧ 1 < z₀ ∧
    ∀ (b d c a : ℕ) (z W : ℝ) (Y U : ℕ → ℝ),
      z₀ ≤ z → FordComparisonParameters b z W (d*a.totient) c.totient Y U →
      ∀ (S : Finset ℕ) (p q : ℕ → Fin b → ℕ) (e : ℕ → ℕ),
        (∀ n ∈ S, n = c*a*∏ i, p n i) →
        (∀ n ∈ S, FordComparisonConditions b z W (d*a.totient) c.totient Y U
          (pptFixedComparisonPair (p n) (q n) (e n))) →
        (S.card : ℝ) ≤ fordComparisonBound C b z W (d*a.totient) c.totient Y U := by
  classical
  obtain ⟨C, z₀, hC, hz₀, hford⟩ := fordLemma51Input
  refine ⟨C, z₀, hC, hz₀, ?_⟩
  intro b d c a z W Y U hz hparams S p q e hreal hconditions
  let F : ℕ → ShiftedPair b := fun n => pptFixedComparisonPair (p n) (q n) (e n)
  have hinj : Set.InjOn F (S : Set ℕ) := ppt_fixed_comparison_injective S p q e hreal
  have hcount := hford b z W (d*a.totient) c.totient Y U hz hparams (S.image F) (by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    exact hconditions n hn)
  rwa [Finset.card_image_of_injOn hinj] at hcount

end TotientAsymptotic

end

end OAI
