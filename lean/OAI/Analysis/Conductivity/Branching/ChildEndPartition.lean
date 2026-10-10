import Mathlib
import OAI.Analysis.Conductivity.Branching.ParentEndPartition

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem child_end_partition_exists :
    ∃ χ η : (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ x,|χ x|≤1) ∧ tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0 ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) η ∧ HasCompactSupport η ∧
      (∀ x,|η x|≤1) ∧ tsupport η⊆sourceClosedCollarBand
        (-3*centralThickness/4) (centralThickness/2) ∧
      (∀ x∈sourceClosedCollarBand (-centralThickness) 0,
        (fun y => χ y+η y)=ᶠ[𝓝 x] (fun _ => 1)) := by
  obtain ⟨χ,hχ,hχc,hχb,hχs,hχ1⟩ := exists_nonneg_band_cutoff
    (l₀ := -7*centralThickness/4) (l := -3*centralThickness/2)
    (r := -centralThickness/2) (r₀ := -centralThickness/4)
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
  obtain ⟨ψ,hψ,hψc,hψb,hψs,hψ1⟩ := exists_nonneg_band_cutoff
    (l₀ := -3*centralThickness/4) (l := -centralThickness/2)
    (r:=centralThickness/4) (r₀:=centralThickness/2)
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
  let η := fun x => (1-χ x)*ψ x
  have hη : ContDiff ℝ (↑(⊤:ℕ∞)) η := (contDiff_const.sub hχ).mul hψ
  have hηc : HasCompactSupport η := hψc.mul_left
  refine ⟨χ,η,hχ,hχc,?_,?_,hη,hηc,?_,?_,?_⟩
  · intro x
    rw [abs_of_nonneg (hχb x).1]
    exact (hχb x).2
  · intro x hx
    have hb := hχs hx
    constructor <;> dsimp [centralThickness] at * <;> linarith [hb.1,hb.2]
  · intro x
    have h₀ := (hχb x).1
    have h₁ := (hχb x).2
    have h₂ := (hψb x).1
    have h₃ := (hψb x).2
    dsimp only [η]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h₁) h₂)]
    nlinarith [mul_nonneg h₀ h₂]
  · exact tsupport_mul_subset_right.trans hψs
  · intro x hx
    by_cases ht : -centralThickness/2 ≤ sourceCollarTime x
    · have hm : x∈sourceClosedCollarBand (-centralThickness/2) (centralThickness/4) :=
        ⟨ht,(by dsimp [centralThickness]; linarith [hx.2])⟩
      filter_upwards [hψ1 x hm] with y hy
      simp only [η,hy,mul_one]
      ring
    · have hm : x∈sourceClosedCollarBand (-3*centralThickness/2) (-centralThickness/2) :=
        ⟨(by dsimp [centralThickness] at *; linarith [hx.1]),(lt_of_not_ge ht).le⟩
      filter_upwards [hχ1 x hm] with y hy
      simp [η,hy]

end ScalarConductivity

end

end OAI
