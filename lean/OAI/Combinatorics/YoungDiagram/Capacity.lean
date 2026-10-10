import OAI.Combinatorics.YoungDiagram.Prefixes

namespace OAI

/-! A sharp bound on a nonempty Young diagram from opposite row and column prefixes. -/

namespace ArithmeticTensorSquares.Capacity

theorem rectangle_corner_arithmetic (n C R x y i j : Nat)
    (hx : j ≤ x) (hy : i ≤ y) (hC : i*x ≤ C) (hR : j*y ≤ R)
    (hn : n + i*j ≤ C + R + (x-j)*(y-i)) : i*j*n ≤ C*R := by
  have hx' : x - j + j = x := by omega
  have hy' : y - i + i = y := by omega
  have hCi : i*j ≤ C := le_trans (Nat.mul_le_mul_left i hx) hC
  have hRj : i*j ≤ R := by
    have h := le_trans (Nat.mul_le_mul_left j hy) hR
    simpa only [Nat.mul_comm] using h
  have hC' : C - i*j + i*j = C := by omega
  have hR' : R - i*j + i*j = R := by omega
  have ha : i*(x-j) ≤ C-i*j := by
    rw [← hx', Nat.mul_add] at hC
    omega
  have hb : j*(y-i) ≤ R-i*j := by
    rw [← hy', Nat.mul_add] at hR
    have hji : j*i = i*j := Nat.mul_comm j i
    rw [hji] at hR
    omega
  have hp := Nat.mul_le_mul ha hb
  have hn' := Nat.mul_le_mul_left (i*j) hn
  rw [← hC', ← hR'] at hn' ⊢
  nlinarith only [hp, hn']

theorem native_rectangle_sharp (μ : YoungDiagram) (i j : Nat)
    (hμ : 0 < μ.card) (hi : 0 < i) (hj : 0 < j) :
    μ.card ≤ colPrefix μ i + rowPrefix μ j - 1 ∨
    i*j*μ.card ≤ colPrefix μ i * rowPrefix μ j := by
  let R := firstRows μ j
  let C := firstCols μ i
  have hsub : R ∪ C ⊆ μ.cells := by
    intro p hp
    simp only [R, C, firstRows, firstCols, Finset.mem_union, Finset.mem_filter] at hp
    rcases hp with hp | hp
    · exact hp.1
    · exact hp.1
  have hRcard : R.card = rowPrefix μ j := firstRows_card μ j
  have hCcard : C.card = colPrefix μ i := firstCols_card μ i
  by_cases hcornerPresent : (j-1,i-1) ∈ μ
  · right
    let x := μ.colLen (i-1)
    let y := μ.rowLen (j-1)
    have hx : j ≤ x := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hcornerPresent
      dsimp [x]
      omega
    have hy : i ≤ y := by
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcornerPresent
      dsimp [y]
      omega
    have hCX : Finset.range x ×ˢ Finset.range i ⊆ C := by
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      have ha : (a,i-1) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hp.1
      change (a,b) ∈ μ.cells.filter (fun p => p.2 < i)
      exact Finset.mem_filter.mpr ⟨μ.up_left_mem le_rfl (by omega) ha, hp.2⟩
    have hRY : Finset.range j ×ˢ Finset.range y ⊆ R := by
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      have hb : (j-1,b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hp.2
      change (a,b) ∈ μ.cells.filter (fun p => p.1 < j)
      exact Finset.mem_filter.mpr ⟨μ.up_left_mem (by omega) le_rfl hb, hp.1⟩
    have hCx : i*x ≤ colPrefix μ i := by
      have hh := Finset.card_le_card hCX
      simpa [hCcard, Nat.mul_comm] using hh
    have hRy : j*y ≤ rowPrefix μ j := by
      have hh := Finset.card_le_card hRY
      simpa [hRcard] using hh
    have hinter : R ∩ C = Finset.range j ×ˢ Finset.range i := by
      ext p
      rcases p with ⟨a,b⟩
      simp only [R, C, firstRows, firstCols, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range]
      constructor
      · intro hh
        exact ⟨hh.1.2,hh.2.2⟩
      · intro hh
        have hm : (a,b) ∈ μ := μ.up_left_mem (by omega) (by omega) hcornerPresent
        exact ⟨⟨hm,hh.1⟩,⟨hm,hh.2⟩⟩
    have hcorner : μ.cells \ (R ∪ C) ⊆ Finset.Ico j x ×ˢ Finset.Ico i y := by
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_sdiff, Finset.mem_union, R, C, firstRows, firstCols,
        Finset.mem_filter] at hp
      have hna : ¬ a < j := fun ha => hp.2 (Or.inl ⟨hp.1,ha⟩)
      have hnb : ¬ b < i := fun hb => hp.2 (Or.inr ⟨hp.1,hb⟩)
      have hja : j ≤ a := by omega
      have hib : i ≤ b := by omega
      have hax : a < x := YoungDiagram.mem_iff_lt_colLen.mp
        (μ.up_left_mem le_rfl (by omega) hp.1)
      have hby : b < y := YoungDiagram.mem_iff_lt_rowLen.mp
        (μ.up_left_mem (by omega) le_rfl hp.1)
      simp only [Finset.mem_product, Finset.mem_Ico]
      exact ⟨⟨hja,hax⟩,⟨hib,hby⟩⟩
    have hcornerCard : (μ.cells \ (R ∪ C)).card ≤ (x-j)*(y-i) := by
      simpa using Finset.card_le_card hcorner
    have hcover := Finset.card_sdiff_add_card_eq_card hsub
    have hunion := Finset.card_union_add_card_inter R C
    have hinterCard : (R ∩ C).card = i*j := by
      rw [hinter]
      simp [Nat.mul_comm]
    have harea : μ.card + i*j ≤ colPrefix μ i + rowPrefix μ j + (x-j)*(y-i) := by
      change μ.cells.card + i*j ≤ _
      omega
    exact rectangle_corner_arithmetic _ _ _ _ _ _ _ hx hy hCx hRy harea
  · left
    have hcover : μ.cells ⊆ R ∪ C := by
      rintro ⟨a,b⟩ hp
      have hh : a < j ∨ b < i := by
        by_contra hn
        apply hcornerPresent
        apply μ.up_left_mem (show j-1 ≤ a by omega) (show i-1 ≤ b by omega) hp
      simp only [R, C, firstRows, firstCols, Finset.mem_union, Finset.mem_filter]
      rcases hh with ha | hb
      · exact Or.inl ⟨hp,ha⟩
      · exact Or.inr ⟨hp,hb⟩
    have h₁ := Finset.card_le_card hcover
    have hnonempty : μ.cells.Nonempty := Finset.card_pos.mp hμ
    obtain ⟨⟨a,b⟩, hab⟩ := hnonempty
    have hzero : (0,0) ∈ μ :=
      μ.up_left_mem (Nat.zero_le a) (Nat.zero_le b) hab
    have hzeroInter : (0,0) ∈ R ∩ C := by
      simp only [R, C, firstRows, firstCols, Finset.mem_inter, Finset.mem_filter]
      exact ⟨⟨hzero,hj⟩,⟨hzero,hi⟩⟩
    have hinterPos : 0 < (R ∩ C).card := Finset.card_pos.mpr ⟨(0,0), hzeroInter⟩
    have hunion := Finset.card_union_add_card_inter R C
    change μ.cells.card ≤ _
    omega

theorem capacity_rectangle (μ : YoungDiagram) (i j U V : Nat)
    (hμ : 0 < μ.card) (hi : 0 < i) (hj : 0 < j)
    (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V) :
    μ.card ≤ max (U + V - 1) (U * V / (i * j)) := by
  rcases native_rectangle_sharp μ i j hμ hi hj with hsum | hprod
  · have hbound : μ.card ≤ U + V - 1 :=
      le_trans hsum (Nat.sub_le_sub_right (Nat.add_le_add hU hV) 1)
    exact le_trans hbound (le_max_left _ _)
  · have hmul : i * j * μ.card ≤ U * V :=
      le_trans hprod (Nat.mul_le_mul hU hV)
    have hbound : μ.card ≤ U * V / (i * j) :=
      (Nat.le_div_iff_mul_le (Nat.mul_pos hi hj)).mpr (by
        simpa only [Nat.mul_comm] using hmul)
    exact le_trans hbound (le_max_right _ _)

end ArithmeticTensorSquares.Capacity

end OAI
