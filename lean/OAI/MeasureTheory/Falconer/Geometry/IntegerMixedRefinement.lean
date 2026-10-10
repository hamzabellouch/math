import OAI.MeasureTheory.Falconer.Geometry.IntegerFivePaths

namespace OAI

/-! Two-sided dense-graph refinement. Both vertex sets stay large and
their full sumset is bounded by the original restricted sum labels. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem integer_mixed_refinement_with_degrees (A B C : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C) :
    ∃ X ⊆ A, ∃ G ⊆ B,
      ρ^2*(A.card : ℝ)/64 ≤ (X.card : ℝ) ∧
      ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ((X+G).card : ℝ)*(ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2) ≤
        1048576*(C.card : ℝ)^5 ∧
      ∀ x ∈ X, ρ^2*(G.card:ℝ)/64 ≤ ((G.filter fun b => e x b).card:ℝ) := by
  have hAc : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hBc : 0 < (B.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  let L : ℝ := ρ^2*(A.card : ℝ)/32
  let u : ℝ := ρ*(B.card : ℝ)/4
  have hL : 0 < L := div_pos (mul_pos (sq_pos_of_pos hρ) hAc) (by norm_num)
  have hu : 0 < u := div_pos (mul_pos hρ hBc) (by norm_num)
  obtain ⟨a,_,G,hGN,hGsize,hpartners⟩ := integer_dense_good_partners A B e hA hB hρ
    hL.le (le_refl L) hdense
  have hGB : G ⊆ B := hGN.trans (Finset.filter_subset _ _)
  have hGc : 0 < (G.card : ℝ) := hu.trans_le hGsize
  have hfour (b : ℤ) (hb : b ∈ G) (c : ℤ) (hc : c ∈ G) :
      u*L^2 ≤ (integerFourPaths A B e b c).card := by
    let V := (integerNeighbors B e a).filter fun v =>
      L ≤ (integerCommonNeighbors A e b v).card ∧ L ≤ (integerCommonNeighbors A e c v).card
    have hVB : V ⊆ B := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hV : u ≤ (V.card : ℝ) := hpartners b hb c hc
    have hlower := integerFourPaths_lower A B V e b c hVB hL.le
      (fun v hv => (Finset.mem_filter.mp hv).2)
    exact (mul_le_mul_of_nonneg_right hV (sq_nonneg L)).trans hlower
  have hcolumn (b : ℤ) (hb : b ∈ G) : L ≤ ((A.filter fun x => e x b).card : ℝ) := by
    let V := (integerNeighbors B e a).filter fun v =>
      L ≤ (integerCommonNeighbors A e b v).card ∧ L ≤ (integerCommonNeighbors A e b v).card
    have hV : 0 < (V.card : ℝ) := hu.trans_le (hpartners b hb b hb)
    have hVnat : 0 < V.card := by exact_mod_cast hV
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hVnat
    have hl := (Finset.mem_filter.mp hv).2.1
    have hsub : integerCommonNeighbors A e b v ⊆ A.filter (fun x => e x b) := by
      intro x hx
      obtain ⟨hx,hxb,_⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx,hxb⟩
    exact hl.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  let w : ℤ → ℝ := fun x => ((G.filter fun b => e x b).card : ℝ)
  have htotal : L*(G.card : ℝ) ≤ ∑ x ∈ A, w x := by
    have hsum : (∑ x ∈ A, w x) = ∑ b ∈ G, ((A.filter fun x => e x b).card : ℝ) := by
      have hn := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := A) (t := G) e
      dsimp only [Finset.bipartiteAbove,Finset.bipartiteBelow] at hn
      dsimp only [w]
      exact_mod_cast hn
    rw [hsum]
    calc
      _ = ∑ _b ∈ G, L := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcolumn
  let θ : ℝ := L*(G.card : ℝ)/(2*(A.card : ℝ))
  have hθ : 0 ≤ θ := div_nonneg (mul_nonneg hL.le hGc.le) (by positivity)
  have hsmall : θ*(A.card : ℝ) ≤ L*(G.card : ℝ)/2 := by
    dsimp [θ]
    field_simp
    rfl
  have hupper (x : ℤ) (_hx : x ∈ A) : w x ≤ (G.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have hp := finite_popular_mass A w hθ htotal hsmall hupper
  let X := A.filter fun x => θ ≤ w x
  have hXsize : L/2 ≤ (X.card : ℝ) := by
    have hb : L*(G.card : ℝ)/2 ≤ (G.card : ℝ)*(X.card : ℝ) := hp.2
    nlinarith
  have hpaths (x : ℤ) (hx : x ∈ X) (c : ℤ) (hc : c ∈ G) :
      θ*(u*L^2) ≤ (integerFivePaths A B G e x c).card :=
    integerFivePaths_lower A B G e (mul_nonneg hu.le (sq_nonneg L))
      (Finset.mem_filter.mp hx).2 (fun b hb => hfour b hb c hc)
  have hbound := five_path_sum_bound A B C X G e (Finset.filter_subset _ _) hGB hlabels hpaths
  have hθlower : L*u/(2*(A.card : ℝ)) ≤ θ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGsize hL.le) (by positivity)
  have hcoeff : (ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2)/1048576 ≤ θ*(u*L^2) := by
    have he : (L*u/(2*(A.card : ℝ)))*(u*L^2) =
        (ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2)/1048576 := by
      dsimp [L,u]
      field_simp
      ring
    rw [← he]
    exact mul_le_mul_of_nonneg_right hθlower (mul_nonneg hu.le (sq_nonneg L))
  have hfinal := (mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg (X+G).card)).trans hbound
  refine ⟨X,Finset.filter_subset _ _,G,hGB,?_,hGsize,?_,?_⟩
  · have he : ρ^2*(A.card : ℝ)/64 = L/2 := by dsimp [L]; ring
    rwa [he]
  · nlinarith

  · intro x hx
    have hh : θ ≤ w x := (Finset.mem_filter.mp hx).2
    have he : θ = ρ^2*(G.card:ℝ)/64 := by
      dsimp [θ,L]
      field_simp
      ring
    rw [he] at hh
    exact hh

theorem integer_mixed_refinement (A B C : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C) :
    ∃ X ⊆ A, ∃ G ⊆ B,
      ρ^2*(A.card : ℝ)/64 ≤ (X.card : ℝ) ∧
      ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ((X+G).card : ℝ)*(ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2) ≤
        1048576*(C.card : ℝ)^5 := by
  obtain ⟨X,hXA,G,hGB,hX,hG,hbound,_⟩ :=
    integer_mixed_refinement_with_degrees A B C e hA hB hρ hdense hlabels
  exact ⟨X,hXA,G,hGB,hX,hG,hbound⟩

end Falconer

end OAI
