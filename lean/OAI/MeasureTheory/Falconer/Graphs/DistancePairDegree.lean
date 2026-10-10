import OAI.MeasureTheory.Falconer.Graphs.GraphFiberPacking

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def distancePairCells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath) :
    Fin 4 → DyadicSquare :=
  ![Q₁.descendant row.1,Q₂.descendant col.1,Q₂.descendant row.2,Q₁.descendant col.2]

theorem distance_pair_fiber_card (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (P : CellPath) :
    ((C.filter (fun c => c.1 = P)).card : ℝ) ≤ 144*((2:ℝ)^N)^(60*sig) := by
  classical
  let F := C.filter (fun c => c.1 = P)
  by_cases hn : F.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hn
    have hproj : (F.image Prod.snd).card = F.card := by
      apply Finset.card_image_iff.mpr
      intro c hc b hb he
      exact Prod.ext ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hb).2.symm) he
    rw [← show F.card = (C.filter (fun c => c.1 = P)).card from rfl,← hproj]
    apply graph_unit_center_fiber_card Q₁ hQ₁ N p hsig (F.image Prod.snd)
      (by
        intro b hb
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
        exact hlen c (Finset.mem_filter.mp hc).1)
      (Q₁.descendant c₀.2).center
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have h0 := (hedge c₀ (Finset.mem_filter.mp hc₀).1).1
    have h1 := (hedge c (Finset.mem_filter.mp hc).1).1
    have he : c.1 = c₀.1 := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm
    simp only [distancePairCells,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1
    rw [he] at h1
    have hh := graphB_two_edges_close _ _ _ _ _ _ (graphSourceSign_cases true plus) h1 h0
    simpa only [dist_sub_left] using hh
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (F.card : ℝ) ≤ _
    rw [hz,Finset.card_empty,Nat.cast_zero]
    positivity

theorem distance_pair_card_of_projection (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (b : ℝ) (hproj : ((C.image Prod.fst).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ b*(144*((2:ℝ)^N)^(60*sig)) := by
  classical
  have he := Finset.card_eq_sum_card_image Prod.fst C
  calc
    _ = ∑ P ∈ C.image Prod.fst, ((C.filter (fun c => c.1 = P)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _P ∈ C.image Prod.fst, 144*((2:ℝ)^N)^(60*sig) :=
      Finset.sum_le_sum (fun P _ => distance_pair_fiber_card Q₁ Q₂ hQ₁ N p hsig plus q row C hlen hedge P)
    _ = ((C.image Prod.fst).card : ℝ)*(144*((2:ℝ)^N)^(60*sig)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hproj (by positivity)

theorem distance_pair_first_fiber_card (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.1 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (P : CellPath) :
    ((C.filter (fun c => c.2 = P)).card : ℝ) ≤ 144*((2:ℝ)^N)^(60*sig) := by
  classical
  let F := C.filter (fun c => c.2 = P)
  by_cases hn : F.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hn
    have hproj : (F.image Prod.fst).card = F.card := by
      apply Finset.card_image_iff.mpr
      intro c hc b hb he
      exact Prod.ext he ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hb).2.symm)
    rw [← show F.card = (C.filter (fun c => c.2 = P)).card from rfl,← hproj]
    apply graph_unit_center_fiber_card Q₂ hQ₂ N p hsig (F.image Prod.fst)
      (by
        intro b hb
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
        exact hlen c (Finset.mem_filter.mp hc).1)
      (Q₂.descendant c₀.1).center
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have h0 := (hedge c₀ (Finset.mem_filter.mp hc₀).1).1
    have h1 := (hedge c (Finset.mem_filter.mp hc).1).1
    have he : c.2 = c₀.2 := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm
    simp only [distancePairCells,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1
    rw [he] at h1
    have hh := graphA_two_edges_close _ _ _ _ _ _ h1 h0
    simpa only [dist_sub_left] using hh
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (F.card : ℝ) ≤ _
    rw [hz,Finset.card_empty,Nat.cast_zero]
    positivity

theorem distance_pair_card_of_second_projection (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.1 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (b : ℝ) (hproj : ((C.image Prod.snd).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ b*(144*((2:ℝ)^N)^(60*sig)) := by
  classical
  have he := Finset.card_eq_sum_card_image Prod.snd C
  calc
    _ = ∑ P ∈ C.image Prod.snd, ((C.filter (fun c => c.2 = P)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _P ∈ C.image Prod.snd, 144*((2:ℝ)^N)^(60*sig) :=
      Finset.sum_le_sum (fun P _ => distance_pair_first_fiber_card Q₁ Q₂ hQ₂ N p hsig plus q row C hlen hedge P)
    _ = ((C.image Prod.snd).card : ℝ)*(144*((2:ℝ)^N)^(60*sig)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hproj (by positivity)

theorem distance_pair_card_min (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen₁ : ∀ c ∈ C, c.1 ∈ dyadicPaths p) (hlen₂ : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (b₁ b₂ : ℝ) (hproj₁ : ((C.image Prod.fst).card : ℝ) ≤ b₁)
    (hproj₂ : ((C.image Prod.snd).card : ℝ) ≤ b₂) :
    (C.card : ℝ) ≤ min b₁ b₂*(144*((2:ℝ)^N)^(60*sig)) := by
  have h₁ := distance_pair_card_of_projection Q₁ Q₂ hQ₁ N p hsig plus q row C hlen₂ hedge b₁ hproj₁
  have h₂ := distance_pair_card_of_second_projection Q₁ Q₂ hQ₂ N p hsig plus q row C hlen₁ hedge b₂ hproj₂
  rcases le_total b₁ b₂ with hb | hb
  · simpa only [min_eq_left hb] using h₁
  · simpa only [min_eq_right hb] using h₂

end PlanarFalconer

end OAI
