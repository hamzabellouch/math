import OAI.NumberTheory.TwoPoint.Bounds.FiniteLawMapping
import OAI.NumberTheory.TwoPoint.Bounds.PrimeResidueLift
import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages

namespace OAI

/-! The common padded carrier law pushes forward to the genuine uniform
product of prime residue fields. Padding points contribute zero mass. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem uniformResidue_product_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (F : (∀ i, ZMod (p i)) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => F (fun i => (x i).val)) = uniformAverage F := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  rw [μ.average_fibers (fun x i => ((x i).val : ZMod (p i))) F]
  have hprob (y : ∀ i, ZMod (p i)) :
      μ.probability (fun x => (fun i => ((x i).val : ZMod (p i))) = y) =
        ∏ i, (p i : ℝ)⁻¹ := by
    have he : (fun x : ι → Fin B => (fun i => ((x i).val : ZMod (p i))) = y) =
        (fun x => ∀ i, ((x i).val : ZMod (p i)) = y i) := by
      funext x
      exact propext funext_iff
    rw [he]
    dsimp only [μ]
    rw [FiniteLaw.independent_probability_all
      (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
      (fun i (x : Fin B) => (x.val : ZMod (p i)) = y i)]
    apply prod_congr rfl
    intro i _
    exact uniformResidueLaw_mod_eq B (p i) (hp i) (hpB i) (y i)
  simp only [hprob, uniformAverage, Fintype.card_pi, ZMod.card, Nat.cast_prod,
    div_eq_mul_inv, ← prod_inv_distrib, ← mul_sum]
  ring

local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩

theorem ProhibitedPrimeFamily.residue_average_uniform {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (F : (∀ p : ↥(data.P ∪ data.Q), ZMod p.val) → ℝ) :
    (data.residueLaw B hB).average (fun x => F (fun p => (x p).val)) = uniformAverage F := by
  exact uniformResidue_product_average B (fun p : ↥(data.P ∪ data.Q) => p.val)
    (fun p => (data.prime p).pos) (fun p => hB _ p.property) F

end TwoPointCorrelations

end OAI
