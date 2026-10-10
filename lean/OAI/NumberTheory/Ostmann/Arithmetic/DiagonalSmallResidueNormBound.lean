import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNorm

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open Construction
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem transformFactor_le {p : ℕ} [Fact p.Prime] (g : ZMod p → ℂ)
    (hgnorm : ∑ x : ZMod p, ‖g x‖^2 = (p : ℝ))
    (a y : (ZMod p)ˣ) (x : ZMod p) : transformFactor g a y x ≤ p := by
  rw [←hgnorm]
  exact Finset.single_le_sum (f := fun x : ZMod p => ‖g x‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ _)

theorem localFactor_le {p : ℕ} [Fact p.Prime] (retained : Bool)
    (g : ZMod p → ℂ) (hgnorm : ∑ x : ZMod p, ‖g x‖^2 = (p : ℝ))
    (a : (ZMod p)ˣ) (z : ZMod p × (ZMod p)ˣ) : localFactor retained g a z ≤ p := by
  cases retained
  · have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    change (if IsUnit z.1 then (1:ℝ) else 0) ≤ p
    split_ifs
    · exact hp
    · positivity
  · exact transformFactor_le g hgnorm a z.2 z.1

omit [DecidableEq ι] in
theorem productTest_le_modulus (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (retained : ι → Bool) (g : ∀ i, ZMod (p i) → ℂ)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, (ZMod (p i))ˣ) (z : LocalPair p) :
    productTest p retained g a z ≤ (∏ i, p i : ℕ) := by
  rw [Nat.cast_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    simp only [localFactor,transformFactor,unitFactor]
    split_ifs <;> positivity
  · intro i _
    exact localFactor_le (retained i) (g i) (hgnorm i) (a i) (z i)

omit [DecidableEq ι] in
theorem actual_crtTest_bounds (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (d : Decomposition) (retained : ι → Bool) (a : ∀ i, (ZMod (p i))ˣ)
    (z : ZMod (∏ i,p i) × (ZMod (∏ i,p i))ˣ) :
    0 ≤ crtTest p hc retained (fun i => residueTransform d (p i)) a z ∧
      crtTest p hc retained (fun i => residueTransform d (p i)) a z ≤ (∏ i,p i : ℕ) :=
  ⟨productTest_nonneg p retained _ a _,
    productTest_le_modulus p retained _
      (fun i => residueTransform_sq_sum d (p i) (Fact.out : (p i).Prime)) a _⟩

theorem actual_small_pointwise_bounds (d : Decomposition) (D P q : ℕ)
    (outerU xs : List SmallSlot) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    (h : SmallUnitData D P q outerU xs v)
    (z : ZMod (∏ i,smallPrime xs outerU i) × (ZMod (∏ i,smallPrime xs outerU i))ˣ) :
    0 ≤ crtTest (smallPrime xs outerU) h.coprime (smallRetained xs outerU)
        (fun i => residueTransform d (smallPrime xs outerU i))
        (smallCoefficients D outerU xs v h.frequency h.denominator) z ∧
      crtTest (smallPrime xs outerU) h.coprime (smallRetained xs outerU)
        (fun i => residueTransform d (smallPrime xs outerU i))
        (smallCoefficients D outerU xs v h.frequency h.denominator) z ≤
          (smallProduct xs * smallProduct outerU : ℕ) := by
  simpa only [smallPrime_product] using actual_crtTest_bounds (smallPrime xs outerU)
    h.coprime d (smallRetained xs outerU)
    (smallCoefficients D outerU xs v h.frequency h.denominator) z

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
