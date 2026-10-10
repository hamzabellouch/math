import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace OAI

/-! The finite-chain infimum used in the compatible barrier construction.
Costs may be infinite. In particular, truncation remains valid on components
unreachable by finite-cost chains. -/

open Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} (R : X → X → ℝ≥0∞ → Prop)

inductive PaidChain : X → X → ℝ≥0∞ → Prop where
  | refl (x : X) : PaidChain x x 0
  | cons {x y z : X} {a b : ℝ≥0∞} :
      R x y a → PaidChain y z b → PaidChain x z (a + b)

namespace PaidChain

variable {R}

theorem single {x y : X} {a : ℝ≥0∞} (h : R x y a) : PaidChain R x y a := by
  simpa using cons h (refl y)

theorem append {x y z : X} {a b : ℝ≥0∞}
    (h : PaidChain R x y a) (k : PaidChain R y z b) : PaidChain R x z (a + b) := by
  induction h with
  | refl => simpa using k
  | cons h _ ih => simpa only [add_assoc] using cons h (ih k)

theorem reverse (hR : ∀ x y a, R x y a → R y x a)
    {x y : X} {a : ℝ≥0∞} (h : PaidChain R x y a) : PaidChain R y x a := by
  induction h with
  | refl x => exact refl x
  | @cons x y z a b h _ ih =>
      simpa only [add_comm] using ih.append (single (hR x y a h))

end PaidChain

def chainDistance (E : Set X) (y : X) : ℝ≥0∞ :=
  ⨅ (x : X) (_ : x ∈ E) (a : ℝ≥0∞) (_ : PaidChain R x y a), a

theorem chainDistance_le {E : Set X} {x y : X} {a : ℝ≥0∞}
    (hx : x ∈ E) (h : PaidChain R x y a) : chainDistance R E y ≤ a :=
  iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le a (iInf_le_of_le h le_rfl)))

theorem chainDistance_anchor {E : Set X} {x : X} (hx : x ∈ E) :
    chainDistance R E x = 0 :=
  bot_unique (chainDistance_le R hx (PaidChain.refl x))

theorem le_chainDistance {E : Set X} {y : X} {b : ℝ≥0∞}
    (h : ∀ x ∈ E, ∀ a, PaidChain R x y a → b ≤ a) : b ≤ chainDistance R E y :=
  le_iInf fun x => le_iInf fun hx => le_iInf fun a => le_iInf fun ha => h x hx a ha

theorem chainDistance_extend {E : Set X} {x y : X} {a : ℝ≥0∞}
    (h : R x y a) : chainDistance R E y ≤ chainDistance R E x + a := by
  change chainDistance R E y ≤
    (⨅ (z : X) (_ : z ∈ E) (b : ℝ≥0∞) (_ : PaidChain R z x b), b) + a
  simp only [ENNReal.iInf_add]
  refine le_iInf fun z => le_iInf fun hz => le_iInf fun b => le_iInf fun hb => ?_
  exact chainDistance_le R hz (hb.append (PaidChain.single h))

def chainPotential (E : Set X) (x : X) : ℝ≥0∞ := min 1 (4 * chainDistance R E x)

theorem chainPotential_le_one (E : Set X) (x : X) : chainPotential R E x ≤ 1 := min_le_left _ _

theorem chainPotential_anchor {E : Set X} {x : X} (hx : x ∈ E) :
    chainPotential R E x = 0 := by simp [chainPotential, chainDistance_anchor R hx]

theorem chainPotential_separated {E : Set X} {y : X}
    (h : ∀ x ∈ E, ∀ a, PaidChain R x y a → (1 / 4 : ℝ≥0∞) ≤ a) :
    chainPotential R E y = 1 := by
  apply min_eq_left
  have hd := mul_le_mul' (show (4 : ℝ≥0∞) ≤ 4 from le_rfl) (le_chainDistance R h)
  rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)] at hd
  exact hd

private theorem min_one_add_le (a b : ℝ≥0∞) : min 1 (a + b) ≤ min 1 a + b := by
  by_cases ha : 1 ≤ a
  · rw [min_eq_left ha]
    exact (min_le_left _ _).trans le_self_add
  · rw [min_eq_right (le_of_not_ge ha)]
    exact min_le_right _ _

theorem chainPotential_extend {E : Set X} {x y : X} {a : ℝ≥0∞}
    (h : R x y a) : chainPotential R E y ≤ chainPotential R E x + 4 * a := by
  have hd := mul_le_mul' (show (4 : ℝ≥0∞) ≤ 4 from le_rfl) (chainDistance_extend R (E := E) h)
  rw [mul_add] at hd
  exact (min_le_min_left 1 hd).trans (min_one_add_le _ _)

theorem chainPotential_two_sided (hR : ∀ x y a, R x y a → R y x a)
    {E : Set X} {x y : X} {a : ℝ≥0∞} (h : R x y a) :
    chainPotential R E y ≤ chainPotential R E x + 4 * a ∧
      chainPotential R E x ≤ chainPotential R E y + 4 * a :=
  ⟨chainPotential_extend R h, chainPotential_extend R (hR x y a h)⟩

end CircleDomainRigidity

end

end OAI
