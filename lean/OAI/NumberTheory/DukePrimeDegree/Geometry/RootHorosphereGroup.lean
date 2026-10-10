import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingHorosphere

namespace OAI

/-!
# The two-step horospherical group used in the low-entropy argument

The shearing shape is a closed subgroup of the special linear group.
Its displacement matrices have products supported only at the selected
root entry. These elementary facts provide the group on which the
remaining conditional-support argument is carried out.
-/

noncomputable section
open Set Matrix
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma sparse_root_product_entry_zero
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (M N : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ r s, (r ≠ i ∧ s ≠ j) ∨ r = s → M r s = 0)
    (hN : ∀ r s, (r ≠ i ∧ s ≠ j) ∨ r = s → N r s = 0)
    (r s : Fin n) (hrs : r ≠ i ∨ s ≠ j) : (M * N) r s = 0 := by
  change (∑ k, M r k * N k s) = 0
  apply Finset.sum_eq_zero
  intro k _
  rcases hrs with hr | hs
  · by_cases hkj : k = j
    · subst k
      have hn : N j s = 0 := by
        by_cases hsj : s = j
        · subst s; exact hN j j (Or.inr rfl)
        · exact hN j s (Or.inl ⟨hij.symm, hsj⟩)
      rw [hn, mul_zero]
    · rw [hM r k (Or.inl ⟨hr, hkj⟩), zero_mul]
  · by_cases hki : k = i
    · subst k
      have hm : M r i = 0 := by
        by_cases hri : r = i
        · subst r; exact hM i i (Or.inr rfl)
        · exact hM r i (Or.inl ⟨hri, hij⟩)
      rw [hm, zero_mul]
    · rw [hN k s (Or.inl ⟨hki, hs⟩), mul_zero]

lemma rootHorosphere_displacement_shape {n : ℕ} {i j : Fin n}
    (g : G n) (hg : RootHorosphereShape i j g) :
    ∀ r s, (r ≠ i ∧ s ≠ j) ∨ r = s → (g.val - 1) r s = 0 := by
  intro r s hrs
  exact sub_eq_zero.mpr (hg r s hrs)

theorem rootHorosphere_product_displacement_zero
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g h : G n) (hg : RootHorosphereShape i j g) (hh : RootHorosphereShape i j h)
    (r s : Fin n) (hrs : r ≠ i ∨ s ≠ j) :
    ((g.val - 1) * (h.val - 1)) r s = 0 :=
  sparse_root_product_entry_zero hij _ _
    (rootHorosphere_displacement_shape g hg) (rootHorosphere_displacement_shape h hh) r s hrs

theorem rootHorosphereShape_mul {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {g h : G n} (hg : RootHorosphereShape i j g) (hh : RootHorosphereShape i j h) :
    RootHorosphereShape i j (g * h) := by
  let M := g.val - 1
  let N := h.val - 1
  have hmul : (g * h).val = 1 + M + N + M * N := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, M, N]
    noncomm_ring
  intro r s hrs
  have hoff : r ≠ i ∨ s ≠ j := by
    rcases hrs with h | rfl
    · exact Or.inl h.1
    · by_cases hri : r = i
      · exact Or.inr (hri ▸ hij)
      · exact Or.inl hri
  have hM := rootHorosphere_displacement_shape g hg r s hrs
  have hN := rootHorosphere_displacement_shape h hh r s hrs
  have hMN := rootHorosphere_product_displacement_zero hij g h hg hh r s hoff
  rw [hmul]
  change (1 : Matrix (Fin n) (Fin n) ℝ) r s + M r s + N r s + (M * N) r s = _
  dsimp only [M, N]
  rw [hM, hN, hMN, add_zero, add_zero, add_zero]

theorem rootHorosphere_inverse_matrix {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : RootHorosphereShape i j g) :
    (g⁻¹).val = 1 - (g.val - 1) + (g.val - 1) ^ 2 := by
  let M := g.val - 1
  have hnil : M ^ 3 = 0 := rootHorosphereShape_nilpotent hij g hg
  have hprod : g.val * (1 - M + M ^ 2) = 1 := by
    have hpoly : g.val * (1 - M + M ^ 2) = 1 + M ^ 3 := by
      dsimp only [M]
      noncomm_ring
    rw [hpoly, hnil, add_zero]
  calc
    (g⁻¹).val = (g⁻¹).val * (g.val * (1 - M + M ^ 2)) := by rw [hprod, mul_one]
    _ = 1 - M + M ^ 2 := by
      rw [← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      exact one_mul _

theorem rootHorosphereShape_inv {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {g : G n} (hg : RootHorosphereShape i j g) : RootHorosphereShape i j g⁻¹ := by
  intro r s hrs
  have hoff : r ≠ i ∨ s ≠ j := by
    rcases hrs with h | rfl
    · exact Or.inl h.1
    · by_cases hri : r = i
      · exact Or.inr (hri ▸ hij)
      · exact Or.inl hri
  have hM := rootHorosphere_displacement_shape g hg r s hrs
  have hMM := rootHorosphere_product_displacement_zero hij g g hg hg r s hoff
  rw [rootHorosphere_inverse_matrix hij g hg, pow_two]
  change (1 : Matrix (Fin n) (Fin n) ℝ) r s - (g.val - 1) r s +
    ((g.val - 1) * (g.val - 1)) r s = _
  rw [hM, hMM, sub_zero, add_zero]

def rootHorosphereGroup {n : ℕ} {i j : Fin n} (hij : i ≠ j) : Subgroup (G n) where
  carrier := {g | RootHorosphereShape i j g}
  one_mem' := by intro r s _; rfl
  mul_mem' := fun hg hh => rootHorosphereShape_mul hij hg hh
  inv_mem' := fun hg => rootHorosphereShape_inv hij hg

theorem isClosed_rootHorosphereGroup {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    IsClosed (rootHorosphereGroup hij : Set (G n)) := by
  change IsClosed {g : G n | ∀ r s,
    (r ≠ i ∧ s ≠ j) ∨ r = s → g.val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro r
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro _
  exact isClosed_eq (by fun_prop) continuous_const

end DukePrimeDegree

end

end OAI
