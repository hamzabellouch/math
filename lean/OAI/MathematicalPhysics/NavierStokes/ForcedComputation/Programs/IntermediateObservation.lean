import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Trajectories

namespace OAI

/-! The finite shear program cannot produce an observation between safe endpoints. -/

noncomputable section
open Set

namespace ShearFlows

theorem RationalBox.coordinate_le_center_add_halfWidth {R : RationalBox 2} {X : Plane}
    (hX : X ∈ R.carrier) (j : Fin 2) : X j ≤ R.center j + R.halfWidth j := by
  have hj := (hX j).2
  dsimp [RationalBox.center, RationalBox.halfWidth]
  linarith

theorem RationalBox.center_sub_halfWidth_le_coordinate {R : RationalBox 2} {X : Plane}
    (hX : X ∈ R.carrier) (j : Fin 2) : R.center j - R.halfWidth j ≤ X j := by
  have hj := (hX j).1
  dsimp [RationalBox.center, RationalBox.halfWidth]
  linarith

theorem branchNodes_first_le {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) {X : Plane} (hX : X ∈ (d.sources i).carrier)
    {a : ℝ} (hs : d.instructions[i].source.center 0 ≤ a)
    (ht : d.instructions[i].target.center 0 ≤ a) (k : Fin 8) :
    branchNodes d i X 0 k 0 ≤ a + 2 * (d.h : ℝ) := by
  have hh : (0 : ℝ) < d.h := by exact_mod_cast hd.h_pos
  have hXs : X ∈ d.instructions[i].source.carrier := hX
  have hys : d.instructions[i].affine X ∈ d.instructions[i].target.carrier := by
    rw [← hd.image_eq d.instructions[i] (List.getElem_mem i.isLt)]
    exact mem_image_of_mem _ hXs
  have hx₀ := RationalBox.coordinate_le_center_add_halfWidth hXs 0
  have hy₀ := RationalBox.coordinate_le_center_add_halfWidth hys 0
  have hx : X 0 ≤ a + 2 * (d.h : ℝ) := by
    have hw := (hd.halfWidths d.instructions[i] (List.getElem_mem i.isLt) 0).1
    linarith
  have hy : d.instructions[i].affine X 0 ≤ a + 2 * (d.h : ℝ) := by
    have hw := (hd.halfWidths d.instructions[i] (List.getElem_mem i.isLt) 0).2
    linarith
  have hscale (j : Fin 5) : scalingPoint d.instructions[i] X j 0 ≤ a + 2 * (d.h : ℝ) := by
    have hb := scalingPoint_bound hd (b := d.instructions[i]) (List.getElem_mem i.isLt) hXs j
    have hb' := (abs_le.mp ((norm_le_pi_norm _ 0).trans hb)).2
    change scalingPoint d.instructions[i] X j 0 - d.instructions[i].source.center 0 ≤ _ at hb'
    linarith
  fin_cases k
  · exact hx
  · exact hx
  · exact hscale 1
  · exact hscale 2
  · exact hscale 3
  · exact hscale 4
  · exact hy
  · exact hy

theorem branchNodes_first_ge {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) {X : Plane} (hX : X ∈ (d.sources i).carrier)
    {a : ℝ} (hs : a ≤ d.instructions[i].source.center 0)
    (ht : a ≤ d.instructions[i].target.center 0) (k : Fin 8) :
    a - 2 * (d.h : ℝ) ≤ branchNodes d i X 0 k 0 := by
  have hh : (0 : ℝ) < d.h := by exact_mod_cast hd.h_pos
  have hXs : X ∈ d.instructions[i].source.carrier := hX
  have hys : d.instructions[i].affine X ∈ d.instructions[i].target.carrier := by
    rw [← hd.image_eq d.instructions[i] (List.getElem_mem i.isLt)]
    exact mem_image_of_mem _ hXs
  have hx₀ := RationalBox.center_sub_halfWidth_le_coordinate hXs 0
  have hy₀ := RationalBox.center_sub_halfWidth_le_coordinate hys 0
  have hx : a - 2 * (d.h : ℝ) ≤ X 0 := by
    have hw := (hd.halfWidths d.instructions[i] (List.getElem_mem i.isLt) 0).1
    linarith
  have hy : a - 2 * (d.h : ℝ) ≤ d.instructions[i].affine X 0 := by
    have hw := (hd.halfWidths d.instructions[i] (List.getElem_mem i.isLt) 0).2
    linarith
  have hscale (j : Fin 5) : a - 2 * (d.h : ℝ) ≤ scalingPoint d.instructions[i] X j 0 := by
    have hb := scalingPoint_bound hd (b := d.instructions[i]) (List.getElem_mem i.isLt) hXs j
    have hb' := (abs_le.mp ((norm_le_pi_norm _ 0).trans hb)).1
    change _ ≤ scalingPoint d.instructions[i] X j 0 - d.instructions[i].source.center 0 at hb'
    linarith
  fin_cases k
  · exact hx
  · exact hx
  · exact hscale 1
  · exact hscale 2
  · exact hscale 3
  · exact hscale 4
  · exact hy
  · exact hy

theorem exists_block_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (7 / 8)) :
    ∃ j : Fin 7, t ∈ Icc (blockStart j) (blockFinish j) := by
  by_cases h₀ : t ≤ 1 / 8
  · exact ⟨0, by norm_num [blockStart, blockFinish]; exact ⟨ht.1, h₀⟩⟩
  by_cases h₁ : t ≤ 2 / 8
  · exact ⟨1, by norm_num [blockStart, blockFinish]; constructor <;> linarith⟩
  by_cases h₂ : t ≤ 3 / 8
  · exact ⟨2, by norm_num [blockStart, blockFinish]; constructor <;> linarith⟩
  by_cases h₃ : t ≤ 4 / 8
  · exact ⟨3, by norm_num [blockStart, blockFinish]; constructor <;> linarith⟩
  by_cases h₄ : t ≤ 5 / 8
  · exact ⟨4, by norm_num [blockStart, blockFinish]; constructor <;> linarith⟩
  by_cases h₅ : t ≤ 6 / 8
  · exact ⟨5, by norm_num [blockStart, blockFinish]; constructor <;> linarith⟩
  exact ⟨6, by norm_num [blockStart, blockFinish]; constructor <;> linarith [ht.2]⟩

theorem materialFlow_first_le {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    (i : Fin d.instructions.length) {X : Plane} (hX : X ∈ (d.sources i).carrier)
    {a : ℝ} (hs : d.instructions[i].source.center 0 ≤ a)
    (ht : d.instructions[i].target.center 0 ≤ a) {t : ℝ} (htime : t ∈ Icc (0 : ℝ) 1) :
    Φ t (atHeight X d.codingHeight) 0 ≤ a + 2 * (d.h : ℝ) := by
  have hδ : (0 : ℝ) < d.tubeRadius := by exact_mod_cast tubeRadius_pos hd
  have hblock {s : ℝ} (hs' : s ∈ Icc (0 : ℝ) (7 / 8)) :
      Φ s (atHeight X d.codingHeight) 0 ≤ a + 2 * (d.h : ℝ) := by
    obtain ⟨j, hj⟩ := exists_block_of_mem hs'
    have he := materialFlow_branch_segment hd hΦ i hX
      (X := X) (by simpa using hδ) (ζ := 0) (by simpa using hδ) j hj
    simp only [add_zero] at he
    rw [he]
    have ha := branchNodes_first_le hd i hX hs ht j.castSucc
    have hb := branchNodes_first_le hd i hX hs ht j.succ
    have hp := standardSchedule.range j s
    change (1 - standardSchedule.progress j s) * _ + standardSchedule.progress j s * _ ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr ha),
      mul_nonneg hp.1 (sub_nonneg.mpr hb)]
  by_cases he : t ≤ 7 / 8
  · exact hblock ⟨htime.1, he⟩
  · rw [materialFlow_period_tail hd hΦ _ ⟨(lt_of_not_ge he).le, htime.2⟩]
    exact hblock (by norm_num)

theorem materialFlow_first_ge {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    (i : Fin d.instructions.length) {X : Plane} (hX : X ∈ (d.sources i).carrier)
    {a : ℝ} (hs : a ≤ d.instructions[i].source.center 0)
    (ht : a ≤ d.instructions[i].target.center 0) {t : ℝ} (htime : t ∈ Icc (0 : ℝ) 1) :
    a - 2 * (d.h : ℝ) ≤ Φ t (atHeight X d.codingHeight) 0 := by
  have hδ : (0 : ℝ) < d.tubeRadius := by exact_mod_cast tubeRadius_pos hd
  have hblock {s : ℝ} (hs' : s ∈ Icc (0 : ℝ) (7 / 8)) :
      a - 2 * (d.h : ℝ) ≤ Φ s (atHeight X d.codingHeight) 0 := by
    obtain ⟨j, hj⟩ := exists_block_of_mem hs'
    have he := materialFlow_branch_segment hd hΦ i hX
      (X := X) (by simpa using hδ) (ζ := 0) (by simpa using hδ) j hj
    simp only [add_zero] at he
    rw [he]
    have ha := branchNodes_first_ge hd i hX hs ht j.castSucc
    have hb := branchNodes_first_ge hd i hX hs ht j.succ
    have hp := standardSchedule.range j s
    change _ ≤ (1 - standardSchedule.progress j s) * _ + standardSchedule.progress j s * _
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr ha),
      mul_nonneg hp.1 (sub_nonneg.mpr hb)]
  by_cases he : t ≤ 7 / 8
  · exact hblock ⟨htime.1, he⟩
  · rw [materialFlow_period_tail hd hΦ _ ⟨(lt_of_not_ge he).le, htime.2⟩]
    exact hblock (by norm_num)

end ShearFlows

end

end OAI
