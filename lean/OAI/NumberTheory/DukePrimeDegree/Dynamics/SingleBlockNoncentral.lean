import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockTransverse
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI

/-!
# A fixed root detects a transverse sequence

Every matrix outside the two-block preserving group fails to commute
with a root in the selected nontrivial block. There are only finitely
many such roots, so one root detects an entire subsequence. This chooses
the shearing direction from the actual return matrices.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_noncentral_singleBlock_root {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (g : G n) (hg : g ∉ blockMatrixGroup (blockComplementSetoid S)) :
    ∃ (i j : Fin n) (hij : i ≠ j), i ∈ S ∧ j ∈ S ∧
      ¬∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
        Matrix.SpecialLinearGroup.transvection hij t * g := by
  by_contra hn
  have hcomm (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∈ S) (hij : i ≠ j) :
      g * Matrix.SpecialLinearGroup.transvection hij 1 =
        Matrix.SpecialLinearGroup.transvection hij 1 * g := by
    by_contra hh
    exact hn ⟨i, j, hij, hi, hj, fun hall => hh (hall 1)⟩
  have hpartner (i : Fin n) (hi : i ∈ S) : ∃ j, j ∈ S ∧ i ≠ j := by
    by_cases hik : i = k
    · subst i
      exact ⟨l, hl, hkl⟩
    · exact ⟨k, hk, hik⟩
  apply hg
  apply mem_blockMatrixGroup_of_cross_zero
  intro i j hij
  change ¬(i ∈ S ↔ j ∈ S) at hij
  by_cases hi : i ∈ S
  · have hj : j ∉ S := fun hj => hij ⟨fun _ => hj, fun _ => hi⟩
    obtain ⟨p, hp, hip⟩ := hpartner i hi
    have he := ((commutes_root_one_iff hip.symm g).mp (hcomm p hp i hi hip.symm)).2.1
    exact he j (fun hji => hj (hji.symm ▸ hi))
  · have hj : j ∈ S := by
      by_contra hj
      exact hij ⟨fun h => (hi h).elim, fun h => (hj h).elim⟩
    obtain ⟨p, hp, hjp⟩ := hpartner j hj
    have he := ((commutes_root_one_iff hjp g).mp (hcomm j hj p hp hjp)).1
    exact he i (fun hij => hi (hij.symm ▸ hj))

lemma exists_constant_subsequence_of_finite {A : Type*} [Finite A] (f : ℕ → A) :
    ∃ a : A, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m, f (φ m) = a := by
  have hf : ∃ a : A, ∃ᶠ m in atTop, f m = a := by
    by_contra hn
    have hnone (a : A) : ∀ᶠ m in atTop, f m ≠ a :=
      not_frequently.mp (fun ha => hn ⟨a, ha⟩)
    obtain ⟨m, hm⟩ := (Filter.eventually_all.mpr hnone).exists
    exact hm (f m) rfl
  obtain ⟨a, ha⟩ := hf
  obtain ⟨φ, hφ, hfφ⟩ := extraction_of_frequently_atTop ha
  exact ⟨a, φ, hφ, hfφ⟩

theorem exists_fixed_noncentral_root_subsequence {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (g : ℕ → G n)
    (hg : ∀ m, g m ∉ blockMatrixGroup (blockComplementSetoid S)) :
    ∃ (i j : Fin n) (hij : i ≠ j), i ∈ S ∧ j ∈ S ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m,
        ¬∀ t : ℝ, g (φ m) * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * g (φ m) := by
  let A := {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2}
  have hex (m : ℕ) : ∃ p : A,
      ¬∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection p.property.2.2 t =
        Matrix.SpecialLinearGroup.transvection p.property.2.2 t * g m := by
    obtain ⟨i, j, hij, hi, hj, hnot⟩ :=
      exists_noncentral_singleBlock_root S k l hkl hk hl (g m) (hg m)
    exact ⟨⟨(i, j), hi, hj, hij⟩, hnot⟩
  choose p hp using hex
  obtain ⟨a, φ, hφ, ha⟩ := exists_constant_subsequence_of_finite p
  refine ⟨a.val.1, a.val.2, a.property.2.2, a.property.1, a.property.2.1, φ, hφ, ?_⟩
  intro m
  simpa only [ha m] using hp (φ m)

end DukePrimeDegree

end

end OAI
