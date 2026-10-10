import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkComparison
import OAI.NumberTheory.Ostmann.Tree.UniformGroupReduction

namespace OAI

/-! # Absolute bounds under the original independent bulk-slot law -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

def bulkBlockProductHom {L G : Type*} [Fintype L] [CommGroup G] (m : ℕ) :
    (L × Fin m → G) →* (L → G) where
  toFun := bulkBlockProduct
  map_one' := by ext; simp [bulkBlockProduct]
  map_mul' x y := by ext; simp [bulkBlockProduct, Finset.prod_mul_distrib]

theorem bulkBlockProductHom_surjective {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) : Function.Surjective (bulkBlockProductHom (L := L) (G := G) m) := by
  intro y
  let j₀ : Fin m := ⟨0, hm⟩
  refine ⟨fun s => if s.2 = j₀ then y s.1 else 1, ?_⟩
  ext l
  simp [bulkBlockProductHom, bulkBlockProduct]

/-- A nonempty set of independent slots gives a uniform product in each
leaf. This is the marginal used before exposing any frequency conditions. -/
theorem bulkBlockProduct_average {L G : Type*} [Fintype L] [CommGroup G] [Fintype G]
    {m : ℕ} (hm : 0 < m) (F : (L → G) → ℝ) :
    (Fintype.card (L × Fin m → G) : ℝ)⁻¹ * ∑ x : L × Fin m → G, F (bulkBlockProduct x) =
      (Fintype.card (L → G) : ℝ)⁻¹ * ∑ y, F y :=
  surjective_group_average (bulkBlockProductHom m) (bulkBlockProductHom_surjective hm) F

theorem SpectatorDiagram.bulk_l2_bound {p n m : ℕ} [Fact p.Prime]
    (d : SpectatorDiagram p n) (hp : 3 ≤ p) (hm : 0 < m)
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : ∑ x : ZMod p, ‖g x‖ ^ 2 ≤ (p : ℝ)) :
    (∑ x : TreeLeafIndex n × Fin m → (ZMod p)ˣ, ‖d.bulkValue g x‖ ^ 2) /
      (Fintype.card (TreeLeafIndex n × Fin m → (ZMod p)ˣ) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  change (∑ x, ‖indexedRationalAmplitude g d.D d.tree d.XL d.XR d.conjugations
    (bulkBlockProduct x)‖ ^ 2) / _ ≤ _
  have h := bulkBlockProduct_average (L := TreeLeafIndex n) (G := (ZMod p)ˣ) (m := m) hm
    (fun x => ‖indexedRationalAmplitude g d.D d.tree d.XL d.XR d.conjugations x‖ ^ 2)
  have hb := indexedRationalAmplitude_l2_bound hp g hg henergy d.D d.tree d.XL d.XR d.conjugations
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h hb ⊢
  rw [div_eq_mul_inv, mul_comm]
  calc
    _ = _ := h
    _ ≤ _ := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact hb

theorem spectator_bulk_absolute_le {p n m : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (hm : 0 < m) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : ∑ x : ZMod p, ‖g x‖ ^ 2 ≤ (p : ℝ))
    (d₁ d₂ : SpectatorDiagram p n) (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod p)ˣ) : ℝ)⁻¹ *
      ∑ x, ‖d₁.bulkValue g x * conj (d₂.bulkValue g (x ∘ e.symm))‖ ≤ (3 : ℝ) ^ (2 ^ n) := by
  let E : (TreeLeafIndex n × Fin m → (ZMod p)ˣ) ≃
      (TreeLeafIndex n × Fin m → (ZMod p)ˣ) :=
    { toFun := fun x => x ∘ e.symm
      invFun := fun x => x ∘ e
      left_inv := by intro x; ext j; simp
      right_inv := by intro x; ext j; simp }
  have hsum := E.sum_comp (fun x => ‖d₂.bulkValue g x‖ ^ 2)
  have h₂ := d₂.bulk_l2_bound hp hm g hg henergy
  rw [← hsum] at h₂
  have h := uniform_absolute_pair_le
    (fun x => d₁.bulkValue g x) (fun x => d₂.bulkValue g (x ∘ e.symm))
    ((3 : ℝ) ^ (2 ^ n)) (d₁.bulk_l2_bound hp hm g hg henergy) h₂
  simpa only [div_eq_mul_inv, mul_comm, starRingEnd_apply] using h

/-- All spectators retain the paper's `3^(r m)` bound under the bulk-slot
law, even for an arbitrary matching of the two assignments. -/
theorem spectator_bulk_product_absolute_le {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (n m : ℕ) (hm : 0 < m)
    (hp : ∀ i, 3 ≤ p i) (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (d₁ d₂ : ∀ i, SpectatorDiagram (p i) n)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
    (Fintype.card (∀ i, TreeLeafIndex n × Fin m → (ZMod (p i))ˣ) : ℝ)⁻¹ *
      (∑ x : ∀ i, TreeLeafIndex n × Fin m → (ZMod (p i))ˣ, ∏ i, ‖(d₁ i).bulkValue (g i) (x i) *
        conj ((d₂ i).bulkValue (g i) (x i ∘ e.symm))‖) ≤
      (3 : ℝ) ^ (2 ^ n * Fintype.card I) := by
  have h := product_uniform_mean_le
    (fun i x => ‖(d₁ i).bulkValue (g i) x * conj ((d₂ i).bulkValue (g i) (x ∘ e.symm))‖)
    (fun _ _ => norm_nonneg _) (fun _ => (3 : ℝ) ^ (2 ^ n))
    (fun i => spectator_bulk_absolute_le (hp i) hm (g i) (hg i) (henergy i) (d₁ i) (d₂ i) e)
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul] using h

end Ostmann

end OAI
