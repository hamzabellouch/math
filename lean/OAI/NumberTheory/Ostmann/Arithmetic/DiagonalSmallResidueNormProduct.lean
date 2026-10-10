import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open scoped BigOperators
open Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev LocalPair (p : ι → ℕ) := ∀ i, ZMod (p i) × (ZMod (p i))ˣ

def localFactor {p : ℕ} [Fact p.Prime] (retained : Bool)
    (g : ZMod p → ℂ) (a : (ZMod p)ˣ) (z : ZMod p × (ZMod p)ˣ) : ℝ :=
  if retained then transformFactor g a z.2 z.1 else unitFactor z.1

def localDensity (p : ℕ) (retained : Bool) : ℝ :=
  if retained then 1 else ((p-1 : ℕ) : ℝ)/p

theorem localFactor_average {p : ℕ} [Fact p.Prime] (retained : Bool)
    (g : ZMod p → ℂ) (hg0 : g 0 = 0)
    (hgnorm : ∑ x : ZMod p, ‖g x‖^2 = (p : ℝ)) (a : (ZMod p)ˣ) :
    (∑ z : ZMod p × (ZMod p)ˣ, localFactor retained g a z) /
        Fintype.card (ZMod p × (ZMod p)ˣ) = localDensity p retained := by
  cases retained
  · exact unitFactor_average
  · exact transformFactor_average g hg0 hgnorm a

def productTest (p : ι → ℕ) [∀ i, Fact (p i).Prime] (retained : ι → Bool)
    (g : ∀ i, ZMod (p i) → ℂ) (a : ∀ i, (ZMod (p i))ˣ) (z : LocalPair p) : ℝ :=
  ∏ i, localFactor (retained i) (g i) (a i) (z i)

omit [DecidableEq ι] in
theorem productTest_nonneg (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (retained : ι → Bool) (g : ∀ i, ZMod (p i) → ℂ)
    (a : ∀ i, (ZMod (p i))ˣ) (z : LocalPair p) :
    0 ≤ productTest p retained g a z := by
  apply Finset.prod_nonneg
  intro i hi
  simp only [localFactor, transformFactor, unitFactor]
  split_ifs <;> positivity

theorem productTest_average (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (retained : ι → Bool) (g : ∀ i, ZMod (p i) → ℂ)
    (hg0 : ∀ i, g i 0 = 0)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, (ZMod (p i))ˣ) :
    (∑ z : LocalPair p, productTest p retained g a z) / Fintype.card (LocalPair p) =
      ∏ i, localDensity (p i) (retained i) := by
  unfold productTest
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun i _ => localFactor_average (retained i) (g i)
    (hg0 i) (hgnorm i) (a i))

theorem localDensity_bounds (p : ℕ) (hp : 0 < p) (retained : Bool) :
    0 ≤ localDensity p retained ∧ localDensity p retained ≤ 1 := by
  cases retained
  · have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    refine ⟨by exact div_nonneg (Nat.cast_nonneg _) hp'.le, ?_⟩
    change ((p-1 : ℕ) : ℝ)/p ≤ 1
    apply (div_le_one hp').2
    exact_mod_cast Nat.sub_le p 1
  · simp [localDensity]

theorem productTest_average_le_one (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (retained : ι → Bool) (g : ∀ i, ZMod (p i) → ℂ)
    (hg0 : ∀ i, g i 0 = 0)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, (ZMod (p i))ˣ) :
    (∑ z : LocalPair p, productTest p retained g a z) / Fintype.card (LocalPair p) ≤ 1 := by
  rw [productTest_average p retained g hg0 hgnorm a]
  apply Finset.prod_le_one₀
  · intro i hi
    exact (localDensity_bounds (p i) (Fact.out : (p i).Prime).pos (retained i)).1
  · intro i hi
    exact (localDensity_bounds (p i) (Fact.out : (p i).Prime).pos (retained i)).2

theorem actual_productTest_average (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (d : Decomposition) (retained : ι → Bool) (a : ∀ i, (ZMod (p i))ˣ) :
    (∑ z : LocalPair p, productTest p retained (fun i => residueTransform d (p i)) a z) /
      Fintype.card (LocalPair p) = ∏ i, localDensity (p i) (retained i) :=
  productTest_average p retained _
    (fun _ => by simp [residueTransform_eq, Supply.additiveTransform_zero])
    (fun i => residueTransform_sq_sum d (p i) (Fact.out : (p i).Prime)) a

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
