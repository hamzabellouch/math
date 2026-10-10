import Mathlib
import OAI.Probability.UnimodularPercolation.Main

namespace OAI

/-! Cayley graphs, translation symmetries and root transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v

noncomputable def AmenableGroup (Λ : Type u) [Group Λ] : Prop := by
  classical
  exact ∀ K : Finset Λ, ∀ ε : ℝ, 0 < ε → ∃ A : Finset Λ, A.Nonempty ∧
    ∀ g ∈ K, (((A.image (fun x => x * g)) \ A).card : ℝ) < ε * A.card

def CayleyEdge {Λ : Type u} [Group Λ] (S : Finset Λ) :=
  {e : Sym2 Λ // ∃ x : Λ, ∃ s ∈ S, e = s(x, x * s)}

def cayleyGraph {Λ : Type u} [Group Λ] (S : Finset Λ) :
    BondGraph Λ (CayleyEdge S) := Subtype.val

section GroupGeometry
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.propDecidable Classical.decEq

lemma amenableGroup_of_finite [Finite Λ] : AmenableGroup Λ := by
  classical
  let := Fintype.ofFinite Λ
  intro K ε hε
  refine ⟨Finset.univ, Finset.univ_nonempty, ?_⟩
  intro g hg
  have he : (Finset.univ.image (fun x : Λ => x * g)) \ Finset.univ = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
  rw [he, Finset.card_empty, Nat.cast_zero, Finset.card_univ]
  exact mul_pos hε (Nat.cast_pos.mpr (Fintype.card_pos))

lemma infinite_of_nonamenable (h : ¬ AmenableGroup Λ) : Infinite Λ := by
  by_contra hi
  let : Finite Λ := not_infinite_iff_finite.mp hi
  exact h amenableGroup_of_finite

lemma cayleyGraph_injective (S : Finset Λ) : Function.Injective (cayleyGraph S) :=
  Subtype.val_injective

lemma cayley_adj_of_mem (S : Finset Λ) (x s : Λ) (hs : s ∈ S) :
    Adj (cayleyGraph S) x (x * s) :=
  ⟨⟨s(x, x * s), x, s, hs, rfl⟩, rfl⟩

lemma cayley_adj_iff (S : Finset Λ) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (x y : Λ) :
    Adj (cayleyGraph S) x y ↔ ∃ s ∈ S, x * s = y := by
  constructor
  · rintro ⟨⟨e, z, s, hs, rfl⟩, he⟩
    change s(z, z * s) = s(x, y) at he
    rcases Sym2.eq_iff.mp he with ⟨hz, hy⟩ | ⟨hz, hx⟩
    ·
      exact ⟨s, hs, hz ▸ hy⟩
    · refine ⟨s⁻¹, hS s hs, ?_⟩
      rw [← hx, mul_inv_cancel_right, hz]
  · rintro ⟨s, hs, rfl⟩
    exact cayley_adj_of_mem S x s hs

lemma cayley_loopless (S : Finset Λ) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (h1 : 1 ∉ S)
    (x : Λ) : ¬ Adj (cayleyGraph S) x x := by
  rintro hx
  obtain ⟨s, hs, he⟩ := (cayley_adj_iff S hS x x).mp hx
  have : s = 1 := mul_left_cancel (by simpa using he : x * s = x * 1)
  exact h1 (this ▸ hs)

lemma cayley_locallyFinite (S : Finset Λ) : LocallyFinite (cayleyGraph S) := by
  intro x
  let F : Set (Sym2 Λ) :=
    ((fun s => s(x, x * s)) '' (S : Set Λ)) ∪
    ((fun s => s(x * s⁻¹, x)) '' (S : Set Λ))
  have hF : F.Finite :=
    (S.finite_toSet.image _).union (S.finite_toSet.image _)
  apply (hF.preimage (cayleyGraph_injective S).injOn).subset
  rintro ⟨e, z, s, hs, rfl⟩ hx
  change x ∈ s(z, z * s) at hx
  rcases Sym2.mem_iff.mp hx with hx | hx
  · left
    exact ⟨s, hs, by simp [hx, cayleyGraph]⟩
  · right
    refine ⟨s, hs, ?_⟩
    simp [hx, cayleyGraph]

noncomputable def cayleyEdgeTranslation (S : Finset Λ) (a : Λ) : CayleyEdge S ≃ CayleyEdge S where
  toFun e := ⟨e.val.map (fun x => a * x), by
    obtain ⟨e, x, s, hs, rfl⟩ := e
    exact ⟨a * x, s, hs, by simp [mul_assoc]⟩⟩
  invFun e := ⟨e.val.map (fun x => a⁻¹ * x), by
    obtain ⟨e, x, s, hs, rfl⟩ := e
    exact ⟨a⁻¹ * x, s, hs, by simp [mul_assoc]⟩⟩
  left_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]

lemma cayley_translation_isAut (S : Finset Λ) (a : Λ) :
    IsAut (cayleyGraph S) (Equiv.mulLeft a) (cayleyEdgeTranslation S a) := by
  intro e
  rfl

lemma cayley_translation_mem (S : Finset Λ) (a : Λ) :
    Equiv.mulLeft a ∈ vertexAut (cayleyGraph S) :=
  ⟨cayleyEdgeTranslation S a, cayley_translation_isAut S a⟩

lemma cayley_quasiTransitive (S : Finset Λ) : QuasiTransitive (cayleyGraph S) := by
  refine ⟨{1}, ?_⟩
  intro x
  exact ⟨1, Finset.mem_singleton_self _, Equiv.mulLeft x, cayleyEdgeTranslation S x,
    cayley_translation_isAut S x, mul_one x⟩

lemma cayley_connected (S : Finset Λ) (hgen : Subgroup.closure (S : Set Λ) = ⊤) :
    Connected (cayleyGraph S) := by
  have paths (g : Λ) : ∀ x : Λ,
      Relation.ReflTransGen (Adj (cayleyGraph S)) x (x * g) := by
    have hg : g ∈ Subgroup.closure (S : Set Λ) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact fun x => .single (cayley_adj_of_mem S x g hg)
    | one => intro x; simpa using (Relation.ReflTransGen.refl (a := x))
    | mul a b ha hb ia ib =>
      intro x
      simpa [mul_assoc] using (ia x).trans (ib (x * a))
    | inv a ha ia =>
      intro x
      have h := ia (x * a⁻¹)
      rw [inv_mul_cancel_right] at h
      let : Std.Symm (Adj (cayleyGraph S)) := ⟨fun _ _ => adj_symm (cayleyGraph S)⟩
      exact symm h
  intro x y
  simpa using paths (x⁻¹ * y) x

lemma cayley_rootTransport (S : Finset Λ) :
    RootTransport (fun _ : Unit => (1 : Λ)) (fun _ => (1 : ℝ))
      (vertexAut (cayleyGraph S)) := by
  intro m hm hr hc
  simp only [Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one, one_mul]
  calc
    (∑' y, m 1 y) = ∑' y, m y⁻¹ 1 := by
      apply tsum_congr
      intro y
      simpa using (hm (Equiv.mulLeft y⁻¹) (cayley_translation_mem S y⁻¹) 1 y).symm
    _ = ∑' x, m x 1 := (Equiv.inv Λ).tsum_eq (fun x => m x 1)

end GroupGeometry
end Percolation

end OAI
