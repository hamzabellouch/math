import OAI.Geometry.HeilbronnTriangle.AnisotropicGeometry
import OAI.Geometry.HeilbronnTriangle.AnisotropicPlaneData

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix PrimitiveNormal

theorem normal_group_card_le_of_data
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    {U Y : ℝ} (hU : 1 ≤ U) (hY : 0 ≤ Y) (S : Finset IntVector)
    (hS : ∀ y ∈ S, IsPrimitive y ∧ length y ≤ 2 * Y ∧
      (∀ w : IntVector, w ⬝ᵥ y = 0 → w ≠ 0 → U ≤ length w) ∧
      ∃ w : IntVector, w ⬝ᵥ y = 0 ∧ w ≠ 0 ∧ length w ≤ 2 * U) :
    (S.card : ℝ) ≤ 18000 * Real.pi * U ^ 2 * Y ^ 2 := by
  classical
  let P : IntVector → Prop := fun z => IsPrimitive z ∧ length z ≤ 2 * Y
  have hcover : ∀ y ∈ S, ∃ z : IntVector,
      P z ∧ U ≤ length z ∧ length z ≤ 2 * U ∧ z ⬝ᵥ y = 0 := by
    intro y hy
    obtain ⟨hyp, hyl, hlow, w, hwy, hw0, hwU⟩ := hS y hy
    let d := Classical.choice (hplanes y hyp)
    obtain ⟨z, hzp, hzy, hzlen⟩ := d.shortest
    have hzY : length z ≤ 2 * Y := by
      rw [hzlen]
      exact d.first_le_second.trans (d.second_le_length.trans hyl)
    have hzU : length z ≤ 2 * U := by
      rw [hzlen]
      exact (d.first_le w hwy hw0).trans hwU
    exact ⟨z, ⟨hzp, hzY⟩, hlow z hzy hzp.ne_zero, hzU, hzy⟩
  have hplane : ∀ z, P z → U ≤ length z → length z ≤ 2 * U →
      ((S.filter (fun y => z ⬝ᵥ y = 0)).card : ℝ) ≤
        (9 * Real.pi) * (4 * Y) ^ 2 / length z := by
    intro z hz _ _
    let d := Classical.choice (hplanes z hz.1)
    apply d.large_count _ (4 * Y)
    · exact d.second_le_length.trans (hz.2.trans (by linarith))
    · intro y hy
      obtain ⟨hyS, hzy⟩ := Finset.mem_filter.mp hy
      exact ⟨by simpa only [dotProduct_comm] using hzy,
        (hS y hyS).2.1.trans (by linarith)⟩
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have h := LatticeBox.normal_group_card_le (Z := Y / U) hU
    (show 0 ≤ 144 * Real.pi by positivity) P S hcover (by
      intro z hz hzU hz2U
      calc
        ((S.filter (fun y => z ⬝ᵥ y = 0)).card : ℝ) ≤
            (9 * Real.pi) * (4 * Y) ^ 2 / length z := hplane z hz hzU hz2U
        _ ≤ (9 * Real.pi) * (4 * Y) ^ 2 / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 hzU
        _ = (144 * Real.pi) * U * (Y / U) ^ 2 := by field_simp; ring)
  have heq : 125 * (144 * Real.pi) * U ^ 4 * (Y / U) ^ 2 =
      18000 * Real.pi * U ^ 2 * Y ^ 2 := by field_simp; ring
  simpa only [heq] using h

theorem normal_shell_card_le
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    {U Y : ℝ} (hU : 1 ≤ U) (hY : 0 ≤ Y) (S : Finset IntVector)
    (hS : ∀ y ∈ S, IsPrimitive y ∧ length y ≤ 2 * Y ∧
      ∃ d : PlaneData y, U ≤ d.first ∧ d.first ≤ 2 * U) :
    (S.card : ℝ) ≤ 18000 * Real.pi * U ^ 2 * Y ^ 2 := by
  apply normal_group_card_le_of_data hplanes hU hY S
  intro y hy
  obtain ⟨hyp, hyl, d, hUd, hdU⟩ := hS y hy
  refine ⟨hyp, hyl, fun w hw hw0 => hUd.trans (d.first_le w hw hw0), ?_⟩
  obtain ⟨z, hzp, hzy, hzlen⟩ := d.shortest
  exact ⟨z, hzy, hzp.ne_zero, hzlen.le.trans hdU⟩

theorem normal_group_card_le_unconditional
    {U Y : ℝ} (hU : 1 ≤ U) (hY : 0 ≤ Y) (S : Finset IntVector)
    (hS : ∀ y ∈ S, IsPrimitive y ∧ length y ≤ 2 * Y ∧
      (∀ w : IntVector, w ⬝ᵥ y = 0 → w ≠ 0 → U ≤ length w) ∧
      ∃ w : IntVector, w ⬝ᵥ y = 0 ∧ w ≠ 0 ∧ length w ≤ 2 * U) :
    (S.card : ℝ) ≤ 18000 * Real.pi * U ^ 2 * Y ^ 2 :=
  normal_group_card_le_of_data exists_planeData hU hY S hS

theorem normal_shell_card_le_unconditional
    {U Y : ℝ} (hU : 1 ≤ U) (hY : 0 ≤ Y) (S : Finset IntVector)
    (hS : ∀ y ∈ S, IsPrimitive y ∧ length y ≤ 2 * Y ∧
      ∃ d : PlaneData y, U ≤ d.first ∧ d.first ≤ 2 * U) :
    (S.card : ℝ) ≤ 18000 * Real.pi * U ^ 2 * Y ^ 2 :=
  normal_shell_card_le exists_planeData hU hY S hS

end Problem355.Anisotropic

end

end OAI
