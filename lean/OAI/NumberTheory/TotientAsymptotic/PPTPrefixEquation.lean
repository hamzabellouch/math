import OAI.NumberTheory.TotientAsymptotic.PPTTailAlignment
import OAI.NumberTheory.TotientAsymptotic.PPTComparisonBridge

namespace OAI

/-!
Truncate the two actual prime lists to the same high-prefix length.  The
left residual multiplier is exactly the seed times the totient of the
removed prime tail; the right multiplier is the smooth factor already
estimated in `PPTTailAlignment`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def pptPrimePrefix {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k) : Fin J → ℕ :=
  fun i => p (i.castLE hJ)

def pptPrimeTailProduct {k : ℕ} (p : Fin k → ℕ) (J : ℕ) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), p i

lemma ppt_prefix_product {k J : ℕ} (f : Fin k → ℕ) (hJ : J ≤ k) :
    (∏ i : Fin J, f (i.castLE hJ)) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => i.val < J), f i := by
  apply Finset.prod_bij (fun i _ => i.castLE hJ)
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i _ j _ he
    exact Fin.ext (congrArg (fun v : Fin k => v.val) he)
  · intro j hj
    have hjJ := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.val, hjJ⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

lemma ppt_prime_prefix_tail_split {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k) :
    pptPrimeTailProduct p J * (∏ i, pptPrimePrefix p hJ i) = ∏ i, p i := by
  rw [show (∏ i, pptPrimePrefix p hJ i) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => i.val < J), p i from
    ppt_prefix_product p hJ]
  have he := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin k => i.val < J) p
  simp only [not_lt] at he
  simpa only [pptPrimeTailProduct, mul_comm] using he

lemma ppt_shifted_prefix_tail_split {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), (p i-1)) *
      shiftedProduct (pptPrimePrefix p hJ) = shiftedProduct p := by
  have he := ppt_prime_prefix_tail_split (fun i => p i-1) hJ
  exact he

lemma ppt_prime_tail_totient {k J : ℕ} (p : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (pptPrimeTailProduct p J).totient =
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), (p i-1) := by
  let I := Finset.univ.filter (fun i : Fin k => J ≤ i.val)
  have hprime : ∀ r ∈ I.image p, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hh := TotientFibers.totient_prime_prod hprime
  rw [Finset.prod_image (fun i _ j _ he => hinj he),
    Finset.prod_image (fun i _ j _ he => hinj he)] at hh
  exact hh

/-- The fixed left tail enters the scalar `D`, exactly as required by
the available `l=0` specialization of Ford's comparison lemma. -/
theorem ppt_equal_prefix_equation {k l J d E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (heq : d*shiftedProduct p = E*shiftedProduct q) :
    (d*(pptPrimeTailProduct p J).totient)*shiftedProduct (pptPrimePrefix p hJp) =
      pptRightLowFactor q E J*shiftedProduct (pptPrimePrefix q hJq) := by
  rw [ppt_prime_tail_totient p hp hinj]
  calc
    _ = d*((∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), (p i-1))*
      shiftedProduct (pptPrimePrefix p hJp)) := by ring
    _ = d*shiftedProduct p := by rw [ppt_shifted_prefix_tail_split p hJp]
    _ = E*shiftedProduct q := heq
    _ = E*((∏ i ∈ Finset.univ.filter (fun i : Fin l => J ≤ i.val), (q i-1))*
      shiftedProduct (pptPrimePrefix q hJq)) := by rw [ppt_shifted_prefix_tail_split q hJq]
    _ = _ := by unfold pptRightLowFactor; ring

lemma ppt_prime_prefix_strictAnti {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k)
    (hp : StrictAnti p) : StrictAnti (pptPrimePrefix p hJ) := by
  intro i j hij
  exact hp (show i.castLE hJ < j.castLE hJ from hij)

lemma ppt_prime_prefix_first {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k) (hpos : 0 < J) :
    pptPrimePrefix p hJ ⟨0, hpos⟩ = p ⟨0, hpos.trans_le hJ⟩ := rfl

end TotientAsymptotic

end

end OAI
