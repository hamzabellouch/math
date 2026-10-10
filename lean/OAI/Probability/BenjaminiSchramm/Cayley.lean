import OAI.Probability.BenjaminiSchramm.FullConclusion
import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

abbrev CayleyEdge (S : Finset Λ) := (SimpleGraph.mulCayley (S : Set Λ)).edgeSet

def cayleyBond (S : Finset Λ) : BondGraph Λ (CayleyEdge S) := Subtype.val

theorem cayleyBond_adj (S : Finset Λ) (x y : Λ) :
    Adj (cayleyBond S) x y ↔ (SimpleGraph.mulCayley (S : Set Λ)).Adj x y :=
  (SimpleGraph.adj_iff_exists_edge_coe).symm

def cayleyLeftIso (S : Finset Λ) (a : Λ) :
    SimpleGraph.mulCayley (S : Set Λ) ≃g SimpleGraph.mulCayley (S : Set Λ) where
  toEquiv := Equiv.mulLeft a
  map_rel_iff' := SimpleGraph.mulCayley_adj_mul_iff_right

theorem cayleyLeft_isAut (S : Finset Λ) (a : Λ) :
    IsAut (cayleyBond S) (Equiv.mulLeft a) (cayleyLeftIso S a).mapEdgeSet := by
  intro e
  rfl

theorem cayleyBond_quasiTransitive (S : Finset Λ) : QuasiTransitive (cayleyBond S) := by
  classical
  refine ⟨{1}, ?_⟩
  intro x
  exact ⟨1, by simp, Equiv.mulLeft x, (cayleyLeftIso S x).mapEdgeSet,
    cayleyLeft_isAut S x, mul_one x⟩

theorem cayleyBond_locallyFinite (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) : LocallyFinite (cayleyBond S) := by
  classical
  let H := SimpleGraph.mulCayley (S : Set Λ)
  intro x
  have hn : (H.neighborSet x).Finite := by
    apply (S.finite_toSet.image (fun s => x * s)).subset
    intro y hy
    obtain ⟨_, s, hs, h | h⟩ := (SimpleGraph.mulCayley_adj' (S : Set Λ) x y).mp hy
    · exact ⟨s, hs, h⟩
    · exact ⟨s⁻¹, hsym s hs, by simp only [h, mul_inv_cancel_right]⟩
  have hi : (H.incidenceSet x).Finite := by
    apply (hn.image (fun y => s(x, y))).subset
    intro e he
    exact ⟨H.otherVertexOfIncident he, H.incidence_other_prop he,
      Sym2.other_spec' he.2⟩
  apply Set.Finite.of_finite_image (f := fun e : CayleyEdge S => e.val)
  · apply hi.subset
    rintro e ⟨f, hf, rfl⟩
    exact ⟨f.property, hf⟩
  · exact Subtype.val_injective.injOn

theorem cayleyBond_connected (S : Finset Λ)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) : Connected (cayleyBond S) := by
  have htranslate (a : Λ) {x y : Λ}
      (h : Relation.ReflTransGen (Adj (cayleyBond S)) x y) :
      Relation.ReflTransGen (Adj (cayleyBond S)) (a * x) (a * y) := by
    induction h with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (adj_aut _ (cayleyLeft_isAut S a) h)
  have hreverse {x y : Λ} (h : Relation.ReflTransGen (Adj (cayleyBond S)) x y) :
      Relation.ReflTransGen (Adj (cayleyBond S)) y x := by
    induction h with
    | refl => exact .refl
    | tail _ h ih => exact (Relation.ReflTransGen.single (adj_symm _ h)).trans ih
  have hroot (y : Λ) : Relation.ReflTransGen (Adj (cayleyBond S)) 1 y := by
    have hy : y ∈ Subgroup.closure (S : Set Λ) := by rw [hgen]; trivial
    induction hy using Subgroup.closure_induction with
    | mem s hs =>
      by_cases h : (1 : Λ) = s
      · simpa only [← h] using (Relation.ReflTransGen.refl (a := (1 : Λ)))
      · exact .single ((cayleyBond_adj S 1 s).mpr
          ((SimpleGraph.mulCayley_adj' (S : Set Λ) 1 s).mpr
            ⟨h, s, hs, Or.inl (one_mul s)⟩))
    | one => exact .refl
    | mul a b _ _ ha hb => exact ha.trans (by simpa using htranslate a hb)
    | inv a _ ha => simpa using htranslate a⁻¹ (hreverse ha)
  intro x y
  simpa using htranslate x (hroot (x⁻¹ * y))

def FolnerAmenable (Λ : Type u) [Group Λ] : Prop :=
  ∀ K : Finset Λ, ∀ ε : ℝ, 0 < ε → ∃ A : Finset Λ, A.Nonempty ∧
    ∀ k ∈ K, (((A.image (fun x => x * k)) \ A).card : ℝ) < ε * A.card

theorem folnerAmenable_of_finite [Finite Λ] : FolnerAmenable Λ := by
  classical
  let : Fintype Λ := Fintype.ofFinite Λ
  intro K ε hε
  refine ⟨Finset.univ, Finset.univ_nonempty, ?_⟩
  intro k _hk
  simpa using
    mul_pos hε (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card Λ))

theorem infinite_of_not_folnerAmenable (hna : ¬ FolnerAmenable Λ) : Infinite Λ := by
  by_contra h
  let : Finite Λ := not_infinite_iff_finite.mp h
  exact hna folnerAmenable_of_finite

def CayleyFolnerInput (Λ : Type u) [Group Λ] : Prop :=
  ¬ FolnerAmenable Λ → ∀ S : Finset Λ, (∀ s ∈ S, s⁻¹ ∈ S) →
    Subgroup.closure (S : Set Λ) = ⊤ → 0 < hV (cayleyBond S)

def PublishedPhaseInput {V E : Type*} (G : BondGraph V E) : Prop :=
  ∀ p : unitInterval, pc G < p → p < pu G →
    ∀ᵐ ω ∂law p, (infiniteClusters G ω).Infinite

theorem cayley_conditional
    (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ)
    (hfolner : CayleyFolnerInput Λ)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision (cayleyBond S))
        (subdivision_injective (cayleyBond S))
        (subdivision_connected (cayleyBond S) (cayleyBond_connected S hgen))
        (subdivision_locallyFinite (cayleyBond S) (cayleyBond_locallyFinite S hsym)) →
      pc (subdivision (cayleyBond S)) < ptwo (subdivision (cayleyBond S)))
    (hphase : PublishedPhaseInput (cayleyBond S)) :
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) ∧
      MainConclusion (cayleyBond S) ∧
      ∀ p : unitInterval, pc (cayleyBond S) < p → p < pu (cayleyBond S) →
        ∀ᵐ ω ∂law p, (infiniteClusters (cayleyBond S) ω).Infinite := by
  let : Infinite Λ := infinite_of_not_folnerAmenable hna
  have hm := main_conditional (cayleyBond S) (cayleyBond_connected S hgen)
    (cayleyBond_locallyFinite S hsym) (cayleyBond_quasiTransitive S)
    (hfolner hna S hsym hgen) hutchcroft2019
  exact ⟨(operatorNorm_lt_top_iff _ _).mp hm.2.1, hm, hphase⟩

end Percolation.BenjaminiSchramm

end OAI
