import OAI.MeasureTheory.Falconer.Radial.PlateZoom
import OAI.MeasureTheory.Falconer.Estimates.ProjectedCompactPieces

namespace OAI

/-! # Positive dilations of the chosen auxiliary projections -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem map_smul_linear (μ : Measure (Space d)) (P : Space d →L[ℝ] Space m)
    {a : ℝ} (ha : 0 < a) :
    μ.map (a • P) = (μ.map P).map (radialZoom a ha.ne' (0 : Space m)) := by
  rw [Measure.map_map (radialZoom a ha.ne' (0 : Space m)).measurable P.continuous.measurable]
  congr 1
  funext x
  simp only [Function.comp_apply,radialZoom_apply,sub_zero,smul_apply]

theorem dilated_projected_frostman (μ : Measure (Space d))
    (P : Space d →L[ℝ] Space m) {a s C : ℝ} (ha : 0 < a)
    (hfrost : FrostmanBallBound (μ.map P) s C) :
    FrostmanBallBound (μ.map (a • P)) s (C*a^(-s)) := by
  rw [map_smul_linear μ P ha]
  exact radialZoom_full_frostman (μ.map P) ha 0 hfrost

theorem exists_contractive_dilation (P : Space d →L[ℝ] Space m) :
    ∃ a : ℝ, 0 < a ∧ ‖a • P‖ ≤ 1 := by
  refine ⟨(‖P‖+1)⁻¹,by positivity,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (‖P‖+1)⁻¹)]
  rw [inv_mul_le_iff₀ (by positivity : 0 < ‖P‖+1)]
  linarith only [norm_nonneg P]

theorem compact_projected_support (μ : Measure (Space d))
    (hK : IsCompact μ.support) (P : Space d →L[ℝ] Space m) :
    (μ.map P).support ⊆ P '' μ.support ∧ IsCompact (μ.map P).support := by
  have himage := hK.image P.continuous
  have hsub : (μ.map P).support ⊆ P '' μ.support := by
    apply Measure.support_subset_of_isClosed himage.isClosed
    change μ.map P (P '' μ.support)ᶜ = 0
    rw [Measure.map_apply P.continuous.measurable himage.isClosed.measurableSet.compl]
    apply measure_mono_null _ μ.measure_compl_support
    intro x hx hxS
    exact hx ⟨x,hxS,rfl⟩
  exact ⟨hsub,himage.of_isClosed_subset Measure.isClosed_support hsub⟩

theorem projected_supports_disjoint (μ ν : Measure (Space d))
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    (P : Space d →L[ℝ] Space m)
    (hneq : ∀ x ∈ μ.support, ∀ y ∈ ν.support, P x ≠ P y) :
    Disjoint (μ.map P).support (ν.map P).support := by
  apply Set.disjoint_left.mpr
  intro z hzμ hzν
  obtain ⟨x,hx,rfl⟩ := (compact_projected_support μ hμ P).1 hzμ
  obtain ⟨y,hy,hxy⟩ := (compact_projected_support ν hν P).1 hzν
  exact hneq x hx y hy hxy.symm

end Falconer

end OAI
