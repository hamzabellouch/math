import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EndpointFlow

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem norm_centered_segment_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : E} {R θ : ℝ} (ha : ‖a-p‖ ≤ R) (hb : ‖b-p‖ ≤ R)
    (hθ : θ ∈ Icc (0 : ℝ) 1) : ‖(1-θ) • a + θ • b - p‖ ≤ R := by
  have he : (1-θ) • a + θ • b - p = (1-θ) • (a-p) + θ • (b-p) := by module
  rw [he]
  exact norm_segment_le ha hb hθ

theorem scaling_time_in_block {t : ℝ} (ht : t ∈ Icc (stageStart 1 : ℝ) (stageFinish 4 : ℝ)) :
    ∃ k : Fin 4, t ∈ Icc (blockStart (scalingIndex k)) (blockFinish (scalingIndex k)) := by
  norm_num [stageStart, stageFinish] at ht
  by_cases h₁ : t ≤ 2/8
  · exact ⟨0, by norm_num [blockStart,blockFinish,scalingIndex]; constructor <;> linarith [ht.1]⟩
  by_cases h₂ : t ≤ 3/8
  · exact ⟨1, by norm_num [blockStart,blockFinish,scalingIndex]; constructor <;> linarith⟩
  by_cases h₃ : t ≤ 4/8
  · exact ⟨2, by norm_num [blockStart,blockFinish,scalingIndex]; constructor <;> linarith⟩
  exact ⟨3, by norm_num [blockStart,blockFinish,scalingIndex]; constructor <;> linarith [ht.2]⟩

theorem realizingVelocity_stages {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ) :
    StageMotion d Φ standardSchedule := by
  have hδ : (0 : ℝ) < d.tubeRadius := by exact_mod_cast tubeRadius_pos hd
  have hseg (i : Fin d.instructions.length) {X : Plane} (hX : X ∈ (d.sources i).carrier)
      (j : Fin 7) {t : ℝ} (ht : t ∈ Icc (blockStart j) (blockFinish j)) :
      Φ t (atHeight X d.codingHeight) =
        (1-standardSchedule.progress j t) • branchNodes d i X 0 j.castSucc +
          standardSchedule.progress j t • branchNodes d i X 0 j.succ := by
    simpa only [add_zero] using materialFlow_branch_segment hd hΦ i hX
      (X := X) (by simpa using hδ) (ζ := 0) (by simpa using hδ) j ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb X hX t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hb
    have ht' : t ∈ Icc (blockStart 0) (blockFinish 0) := by
      norm_num [standardSchedule,stageFinish,blockStart,blockFinish] at ht ⊢; exact ht
    rw [hseg ⟨i,hi⟩ hX 0 ht']
    simp only [horizontal_add, horizontal_smul]
    simp only [branchNodes, Matrix.cons_val_zero, Fin.succ_zero_eq_one, Matrix.cons_val_one,
      Fin.castSucc_zero, atHeight_horizontal]
    module
  · intro b hb X hX t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hb
    let idx : Fin d.instructions.length := ⟨i,hi⟩
    obtain ⟨k,hk⟩ := scaling_time_in_block ht
    rw [hseg idx hX (scalingIndex k) hk,
      (branchNodes_scaling d idx X 0 k).1, (branchNodes_scaling d idx X 0 k).2]
    simp only [horizontal_add, horizontal_smul, atHeight_horizontal]
    exact norm_centered_segment_le
      (scalingPoint_bound hd (b := d.instructions[i]) (List.getElem_mem _) hX k.castSucc)
      (scalingPoint_bound hd (b := d.instructions[i]) (List.getElem_mem _) hX k.succ)
      (standardSchedule.range _ _)
  · intro b hb X hX
    exact scaledOffset_bound hd hb hX
  · intro b hb X hX t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hb
    have ht' : t ∈ Icc (blockStart 5) (blockFinish 5) :=
      ⟨(block_bounds 5).2.1.le.trans ht.1, ht.2.trans (block_bounds 5).2.2.1.le⟩
    rw [hseg ⟨i,hi⟩ hX 5 ht']
    change horizontal ((1-standardSchedule.progress 5 t) •
        atHeight (scalingPoint d.instructions[i] X 4) (d.privateHeight ⟨i,hi⟩+0) +
        standardSchedule.progress 5 t • atHeight (d.instructions[i].affine X) (d.privateHeight ⟨i,hi⟩+0)) = _
    simp only [horizontal_add, horizontal_smul, atHeight_horizontal, scalingPoint_final,
      affine_eq_target_add_scaledOffset]
    module
  · intro b hb X hX t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hb
    by_cases htt : t ≤ (7/8 : ℝ)
    · have ht' : t ∈ Icc (blockStart 6) (blockFinish 6) :=
        ⟨(block_bounds 6).2.1.le.trans ht.1, by norm_num [blockFinish]; exact htt⟩
      rw [hseg ⟨i,hi⟩ hX 6 ht']
      change horizontal ((1-standardSchedule.progress 6 t) •
        atHeight (d.instructions[i].affine X) (d.privateHeight ⟨i,hi⟩+0) +
        standardSchedule.progress 6 t • atHeight (d.instructions[i].affine X) (d.codingHeight+0)) = _
      simp only [horizontal_add, horizontal_smul, atHeight_horizontal]
      module
    · rw [materialFlow_period_tail hd hΦ _ ⟨le_of_not_ge htt,ht.2⟩]
      have he := materialFlow_branchNodes hd hΦ (⟨i,hi⟩ : Fin d.instructions.length)
        hX (X := X) (by simpa using hδ) (ζ := 0) (by simpa using hδ) 7
      have he' : Φ (7/8) (atHeight X d.codingHeight) =
          atHeight (d.instructions[i].affine X) d.codingHeight := by simpa [branchNodes] using he
      rw [he',atHeight_horizontal]

end ShearFlows

end

end OAI
