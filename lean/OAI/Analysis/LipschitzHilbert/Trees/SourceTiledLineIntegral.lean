import OAI.Analysis.LipschitzHilbert.Estimates.PartitionIntegral
import OAI.Analysis.LipschitzHilbert.Trees.FiniteLineGrid
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeBoxMask
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! Sum the source root-window estimates over the actual half-open tiling
of a line. Local integrability comes from the marked-window theorem; it
is not inferred from a vacuous Bochner-integral inequality. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

def sourceLineTile (H : ℝ) (k : ℤ) : Set ℝ := Ico (H*k) (H*((k:ℝ)+1))

theorem sourceLineTile_measurable (H : ℝ) (k : ℤ) : MeasurableSet (sourceLineTile H k) :=
  measurableSet_Ico

theorem sourceLineTile_mem (H : ℝ) (hH : 0 < H) (x : ℝ) :
    x ∈ sourceLineTile H ⌊x/H⌋ := by
  have hl := mul_le_mul_of_nonneg_left (Int.floor_le (x/H)) hH.le
  have hr := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x/H)) hH
  have heq : H*(x/H) = x := by field_simp
  rw [heq] at hl hr
  exact ⟨hl,hr⟩

theorem sourceLineTile_pairwise (H : ℝ) (hH : 0 < H) :
    Pairwise (fun k j : ℤ => Disjoint (sourceLineTile H k) (sourceLineTile H j)) := by
  intro k j hkj
  apply Set.disjoint_left.mpr
  intro x hk hj
  rcases lt_or_gt_of_ne hkj with h | h
  · have hij : (k:ℝ)+1 ≤ j := by exact_mod_cast (show k+1 ≤ j by omega)
    have hmul := mul_le_mul_of_nonneg_left hij hH.le
    exact (not_lt_of_ge (hmul.trans hj.1)) hk.2
  · have hji : (j:ℝ)+1 ≤ k := by exact_mod_cast (show j+1 ≤ k by omega)
    have hmul := mul_le_mul_of_nonneg_left hji hH.le
    exact (not_lt_of_ge (hmul.trans hk.1)) hj.2

theorem sourceLineTile_cover (H : ℝ) (hH : 0 < H) :
    (⋃ k : ℤ, sourceLineTile H k) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x/H⌋,sourceLineTile_mem H hH x⟩

theorem sourceLineTile_length (H : ℝ) (hH : 0 < H) (k : ℤ) :
    volume.real (sourceLineTile H k) = H := by
  rw [sourceLineTile,Real.volume_real_Ico_of_le]
  · ring
  · nlinarith

theorem finiteLineGrid_root_tile (g : FiniteLineGrid) (k : ℤ)
    (ho : g.origin = g.width*k) : g.root = sourceLineTile g.width k := by
  rw [FiniteLineGrid.root,ho,sourceLineTile]
  congr 1
  ring

/-- Summable control of the local integrals gives global integrability
and the same constant, with no dependence on the number of root windows. -/
theorem source_tiled_line_integral (H : ℝ) (hH : 0 < H) (f weight : ℝ → ℝ) (C : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hw : Integrable weight volume)
    (hlocal : ∀ k : ℤ, IntegrableOn f (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f x) ≤ C*∫ x in sourceLineTile H k, weight x) :
    Integrable f volume ∧ (∫ x, f x) ≤ C*∫ x, weight x :=
  integral_le_of_partition volume (sourceLineTile H) (sourceLineTile_measurable H)
    (sourceLineTile_pairwise H hH) (sourceLineTile_cover H hH) f weight hf hw
    (fun k => (hlocal k).1) (fun k => (hlocal k).2)

namespace SlopeBox

/-- Every actual top-weight slice is integrable, including along a slope
different from the top's own slope. Horizontal decay alone suffices. -/
theorem weight_line_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 1 < D)
    (s y : ℝ) : Integrable (fun x => T.weight K D (x,y+s*x)) volume := by
  have hbase : Integrable (fun x : ℝ => (1+‖x‖)^(-D)) volume :=
    integrable_one_add_norm (by simpa using hD)
  have hscale := (hbase.comp_div (mul_pos hK T.length_pos).ne').comp_sub_right T.x
  have hint := hscale.const_mul ((2:ℝ)^D)
  apply hint.mono' ((T.weight_continuous K D hK).comp
    (show Continuous (fun x : ℝ => (x,y+s*x)) by fun_prop)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simp only [Function.comp_apply,Real.norm_eq_abs]
  rw [abs_of_pos (T.weight_pos hK D _)]
  change (2:ℝ)^D*(1+T.radius (x,y+s*x)/K)^(-D) ≤
    (2:ℝ)^D*(1+‖(x-T.x)/(K*T.length)‖)^(-D)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  have hnorm : ‖(x-T.x)/(K*T.length)‖ = |T.horizontal (x,y+s*x)|/K := by
    simp only [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hK,
      abs_of_pos T.length_pos,horizontal]
    ring
  rw [hnorm]
  apply add_le_add (le_refl (1:ℝ))
  apply div_le_div_of_nonneg_right _ hK.le
  exact le_add_of_nonneg_right (abs_nonneg (T.transverse (x,y+s*x)))

end SlopeBox

/-- Specialization to the original top weight removes the last auxiliary
integrability premise in the source's whole-line gluing step. -/
theorem source_top_tiled_line_integral (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 1 < D) (s y H C : ℝ) (hH : 0 < H)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hlocal : ∀ k : ℤ, IntegrableOn f (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f x) ≤
        C*∫ x in sourceLineTile H k, T.weight K D (x,y+s*x)) :
    Integrable f volume ∧ (∫ x, f x) ≤ C*∫ x, T.weight K D (x,y+s*x) :=
  source_tiled_line_integral H hH f (fun x => T.weight K D (x,y+s*x)) C hf
    (T.weight_line_integrable hK hD s y) hlocal

end LipschitzHilbert

end

end OAI
