import Mathlib.Data.Fintype.BigOperators
import OAI.NumberTheory.Ostmann.Construction.SpectatorNorm

namespace OAI

/-! # The full spectator cost under its independent residue law -/

namespace Ostmann

open scoped BigOperators Classical

theorem product_uniform_mean {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] (F : ∀ i, A i → ℝ) :
    (Fintype.card (∀ i, A i) : ℝ)⁻¹ * (∑ x : ∀ i, A i, ∏ i, F i (x i)) =
      ∏ i, (Fintype.card (A i) : ℝ)⁻¹ * ∑ a, F i a := by
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

theorem product_uniform_mean_le {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] (F : ∀ i, A i → ℝ) (hF : ∀ i a, 0 ≤ F i a)
    (B : I → ℝ) (hB : ∀ i, (Fintype.card (A i) : ℝ)⁻¹ * ∑ a, F i a ≤ B i) :
    (Fintype.card (∀ i, A i) : ℝ)⁻¹ * (∑ x : ∀ i, A i, ∏ i, F i (x i)) ≤ ∏ i, B i := by
  rw [product_uniform_mean]
  exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun a _ => hF i a)) (fun i _ => hB i)

/-- The data of one actual diagram at a spectator prime. -/
structure SpectatorDiagram (p n : ℕ) [Fact p.Prime] where
  D : (ZMod p)ˣ
  C : (ZMod p)ˣ
  tree : RationalTreeData (ZMod p)ˣ n C
  XL : (ZMod p)ˣ
  XR : (ZMod p)ˣ
  conjugations : TreeLeafTuple Bool n

noncomputable def SpectatorDiagram.value {p n : ℕ} [Fact p.Prime]
    (d : SpectatorDiagram p n) (g : ZMod p → ℂ) (x : TreeLeafTuple (ZMod p)ˣ n) : ℂ :=
  rationalTreeAmplitude g d.D d.tree d.XL d.XR d.conjugations x

theorem spectator_product_absolute_le {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (n : ℕ)
    (hp : ∀ i, 3 ≤ p i) (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) ≤ (p i : ℝ))
    (d e : ∀ i, SpectatorDiagram (p i) n) :
    (Fintype.card (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) : ℝ)⁻¹ *
      (∑ x : ∀ i, TreeLeafTuple (ZMod (p i))ˣ n,
        ∏ i, ‖(d i).value (g i) (x i) * star ((e i).value (g i) (x i))‖) ≤
      (3 : ℝ) ^ (2 ^ n * Fintype.card I) := by
  have h := product_uniform_mean_le
    (fun i x => ‖(d i).value (g i) x * star ((e i).value (g i) x)‖)
    (fun _ _ => norm_nonneg _) (fun _ => (3 : ℝ) ^ (2 ^ n)) (fun i => by
      simpa only [SpectatorDiagram.value, div_eq_mul_inv, mul_comm] using
        rationalTree_absolute_pair_le (hp i) (g i) (hg i) (henergy i)
          (d i).D (e i).D (d i).tree (e i).tree (d i).XL (d i).XR (e i).XL (e i).XR
          (d i).conjugations (e i).conjugations)
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul] using h

end Ostmann

end OAI
