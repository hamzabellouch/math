import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalEndLocalLipschitz
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarBand

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma exists_nonneg_band_cutoff {l₀ l r r₀ : ℝ} (hl : l₀<l) (hr : r<r₀)
    (hl₀ : -(1:ℝ)/100≤l₀) (hr₀ : r₀≤1/100) :
    ∃ χ : (Fin 3 → ℝ) → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ x,χ x∈Icc 0 1) ∧ tsupport χ⊆sourceClosedCollarBand l₀ r₀ ∧
      (∀ x∈sourceClosedCollarBand l r,χ=ᶠ[𝓝 x] (fun _ => 1)) := by
  have hbig := isCompact_sourceClosedCollarBand hl₀ hr₀
  have hsmall := isCompact_sourceClosedCollarBand (hl₀.trans hl.le) (hr.le.trans hr₀)
  have hi : sourceClosedCollarBand l r⊆interior (sourceClosedCollarBand l₀ r₀) := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have hm := locallyLipschitz_sourceCollarTime.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (show sourceCollarTime x∈Ioo l₀ r₀ from
        ⟨hl.trans_le hx.1,hx.2.trans_lt hr⟩))
    exact mem_of_superset hm (fun y hy => ⟨hy.1.le,hy.2.le⟩)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hsmall.isClosed hi (n:=↑(⊤:ℕ∞))
  refine ⟨χ,χ.contMDiff.contDiff,HasCompactSupport.intro hbig hχ0,hχb,?_,?_⟩
  · apply closure_minimal _ hbig.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  · intro x hx
    exact hχ1.filter_mono (nhds_le_nhdsSet hx)

theorem parent_end_partition_exists :
    ∃ χ η : (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ x,|χ x|≤1) ∧ tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) η ∧ HasCompactSupport η ∧
      (∀ x,|η x|≤1) ∧ tsupport η⊆sourceClosedCollarBand
        (-centralThickness/2) (3*centralThickness/4) ∧
      (∀ x∈sourceClosedCollarBand 0 centralThickness,
        (fun y => χ y+η y)=ᶠ[𝓝 x] (fun _ => 1)) := by
  obtain ⟨χ,hχ,hχc,hχb,hχs,hχ1⟩ := exists_nonneg_band_cutoff
    (l₀:=centralThickness/4) (l:=centralThickness/2)
    (r:=3*centralThickness/2) (r₀:=7*centralThickness/4)
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
  obtain ⟨ψ,hψ,hψc,hψb,hψs,hψ1⟩ := exists_nonneg_band_cutoff
    (l₀ := -centralThickness/2) (l := -centralThickness/4)
    (r:=centralThickness/2) (r₀:=3*centralThickness/4)
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
    by_cases ht : sourceCollarTime x≤centralThickness/2
    · have hm : x∈sourceClosedCollarBand (-centralThickness/4) (centralThickness/2) :=
        ⟨(by dsimp [centralThickness]; linarith [hx.1]),ht⟩
      filter_upwards [hψ1 x hm] with y hy
      simp only [η,hy,mul_one]
      ring
    · have hm : x∈sourceClosedCollarBand (centralThickness/2) (3*centralThickness/2) :=
        ⟨(lt_of_not_ge ht).le,(by dsimp [centralThickness] at *; linarith [hx.2])⟩
      filter_upwards [hχ1 x hm] with y hy
      simp [η,hy]

end ScalarConductivity

end

end OAI
