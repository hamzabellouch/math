import OAI.MeasureTheory.Falconer.Geometry.IntegerFourPaths
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

namespace OAI

/-! Counting four-edge paths with a common difference. This proves the
small-difference-set conclusion needed by the additive-energy argument. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem four_path_difference_bound (A B C G : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hG : G ⊆ B) (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C)
    {k : ℝ} (hpaths : ∀ b ∈ G, ∀ c ∈ G, k ≤ (integerFourPaths A B e b c).card) :
    ((G-G).card : ℝ)*k ≤ (C.card : ℝ)^4 := by
  have hex (z : ℤ) : ∃ b c : ℤ, z ∈ G-G → b ∈ G ∧ c ∈ G ∧ b-c = z := by
    by_cases hz : z ∈ G-G
    · obtain ⟨b,hb,c,hc,he⟩ := Finset.mem_sub.mp hz
      exact ⟨b,c,fun _ => ⟨hb,hc,he⟩⟩
    · exact ⟨0,0,fun h => False.elim (hz h)⟩
  choose b c hbc using hex
  let W := (G-G).sigma fun z => integerFourPaths A B e (b z) (c z)
  let code : (Σ _z : ℤ, IntegerPath) → (ℤ × ℤ) × (ℤ × ℤ) :=
    fun p => integerPathSums (b p.1) (c p.1) p.2
  let V : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := (C ×ˢ C) ×ˢ (C ×ˢ C)
  have hlower : ((G-G).card : ℝ)*k ≤ (W.card : ℝ) := by
    have hw : (W.card : ℝ) =
        ∑ z ∈ G-G, ((integerFourPaths A B e (b z) (c z)).card : ℝ) := by
      simp only [W,Finset.card_sigma,Nat.cast_sum]
    rw [hw]
    calc
      _ = ∑ _z ∈ G-G, k := by simp
      _ ≤ _ := Finset.sum_le_sum fun z hz => hpaths _ (hbc z hz).1 _ (hbc z hz).2.1
  have hmap : Set.MapsTo code (W : Set (Σ _z : ℤ, IntegerPath))
      (V : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
    intro p hp
    obtain ⟨hz,hp⟩ := Finset.mem_sigma.mp hp
    exact integerPathSums_mem A B C e hlabels (hG (hbc p.1 hz).1) (hG (hbc p.1 hz).2.1) hp
  have hinj : Set.InjOn code (W : Set (Σ _z : ℤ, IntegerPath)) := by
    rintro ⟨z,p⟩ hp ⟨w,q⟩ hq he
    have hz := (Finset.mem_sigma.mp hp).1
    have hw := (Finset.mem_sigma.mp hq).1
    have hd := congrArg (fun t : (ℤ × ℤ) × (ℤ × ℤ) => t.1.1-t.1.2+t.2.1-t.2.2) he
    change (integerPathSums (b z) (c z) p).1.1-(integerPathSums (b z) (c z) p).1.2+
      (integerPathSums (b z) (c z) p).2.1-(integerPathSums (b z) (c z) p).2.2 =
      (integerPathSums (b w) (c w) q).1.1-(integerPathSums (b w) (c w) q).1.2+
      (integerPathSums (b w) (c w) q).2.1-(integerPathSums (b w) (c w) q).2.2 at hd
    rw [integerPathSums_alternating,integerPathSums_alternating,
      (hbc z hz).2.2,(hbc w hw).2.2] at hd
    subst w
    have hpq : p = q := integerPathSums_injective (b z) (c z) he
    subst q
    rfl
  have hc := Finset.card_le_card_of_injOn code hmap hinj
  dsimp [V] at hc
  simp only [Finset.card_product] at hc
  have hu : (W.card : ℝ) ≤ (C.card : ℝ)^4 := by
    have hc' : (W.card : ℝ) ≤ ((C.card : ℝ)*(C.card : ℝ))*((C.card : ℝ)*(C.card : ℝ)) := by
      exact_mod_cast hc
    exact hc'.trans_eq (by ring)
  exact hlower.trans hu

theorem integer_dense_small_difference (A B C : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hsmall : L ≤ ρ^2*(A.card : ℝ)/32)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C) :
    ∃ G ⊆ B, ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ((G-G).card : ℝ)*((ρ*(B.card : ℝ)/4)*L^2) ≤ (C.card : ℝ)^4 := by
  obtain ⟨a,_,G,hGN,hGcard,hpartners⟩ := integer_dense_good_partners A B e hA hB hρ hL hsmall hdense
  have hNB : integerNeighbors B e a ⊆ B := Finset.filter_subset _ _
  refine ⟨G,hGN.trans hNB,hGcard,?_⟩
  apply four_path_difference_bound A B C G e (hGN.trans hNB) hlabels
  intro b hb c hc
  let V := (integerNeighbors B e a).filter fun v =>
    L ≤ (integerCommonNeighbors A e b v).card ∧ L ≤ (integerCommonNeighbors A e c v).card
  have hvB : V ⊆ B := (Finset.filter_subset _ _).trans hNB
  have hp := integerFourPaths_lower A B V e b c hvB hL (fun v hv => (Finset.mem_filter.mp hv).2)
  exact (mul_le_mul_of_nonneg_right (hpartners b hb c hc) (sq_nonneg L)).trans hp

end Falconer

end OAI
