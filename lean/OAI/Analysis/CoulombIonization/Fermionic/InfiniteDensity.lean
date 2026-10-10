import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.DyadicPowerSq

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT
open CoulombAtom Metric
variable {ι : Type*}

def infiniteDensity (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) : ℝ≥0∞ :=
  ∑' j, ENNReal.ofReal (‖f j x‖^2)

def fourierMoment (f : Lp ℂ 2 (volume : Measure Space)) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2 * ‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2)

lemma finite_fourierMoment [Fintype ι] (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2*familyDensity (fun j => 𝓕 (f j)) ξ)) =
    ∑ j, fourierMoment (f j) := by
  have he (ξ : Space) :
      ENNReal.ofReal (‖ξ‖^2*familyDensity (fun j => 𝓕 (f j)) ξ) =
      ∑ j, ENNReal.ofReal (‖ξ‖^2*‖(𝓕 (f j) : Lp ℂ 2 volume) ξ‖^2) := by
    rw [familyDensity, Finset.mul_sum]
    exact ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  simp_rw [he]
  apply lintegral_finsetSum'
  intro j _
  exact ((continuous_norm.pow 2).aestronglyMeasurable.mul
    ((Lp.memLp (𝓕 (f j))).aestronglyMeasurable.norm.pow 2)).aemeasurable.ennreal_ofReal

lemma infiniteDensity_rpow (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) :
    infiniteDensity f x ^ (5/3:ℝ) =
      ⨆ s : Finset ι, ENNReal.ofReal ((∑ j ∈ s, ‖f j x‖^2)^(5/3:ℝ)) := by
  rw [infiniteDensity, ENNReal.tsum_eq_iSup_sum]
  change (ENNReal.orderIsoRpow (5/3:ℝ) (by norm_num)) _ = _
  rw [OrderIso.map_iSup]
  congr 1
  funext s
  change (∑ j ∈ s, ENNReal.ofReal (‖f j x‖^2)) ^ (5/3:ℝ) = _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  exact ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (by norm_num)

theorem countable_lieb_thirring_lintegral [Countable ι]
    {f : ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : ∀ s : Finset ι, BesselFamily (fun j : s => f j)) :
    (∫⁻ x, infiniteDensity f x ^ (5/3:ℝ)) ≤
      16*(∑' j, ENNReal.ofReal (‖f j‖^2)) +
        ENNReal.ofReal (1024/3:ℝ)*(∑' j, fourierMoment (f j)) := by
  classical
  have hm (s : Finset ι) : AEMeasurable
      (fun x => ENNReal.ofReal ((∑ j ∈ s, ‖f j x‖^2)^(5/3:ℝ))) volume := by
    have hi : Integrable (fun x => ∑ j ∈ s, ‖f j x‖^2) volume :=
      integrable_finsetSum s (fun j _ =>
        (memLp_two_iff_integrable_sq_norm (Lp.memLp (f j)).aestronglyMeasurable).mp (Lp.memLp (f j)))
    have h := hi.aestronglyMeasurable
    exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤5/3)).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal
  have hmono (s t : Finset ι) (h : s ⊆ t) (x : Space) :
      ENNReal.ofReal ((∑ j ∈ s, ‖f j x‖^2)^(5/3:ℝ)) ≤
      ENNReal.ofReal ((∑ j ∈ t, ‖f j x‖^2)^(5/3:ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) _ (by norm_num)
    exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)
  simp_rw [infiniteDensity_rpow]
  rw [lintegral_iSup_directed hm (fun s t =>
    ⟨s ∪ t, hmono s (s ∪ t) Finset.subset_union_left,
      hmono t (s ∪ t) Finset.subset_union_right⟩)]
  apply iSup_le
  intro s
  have hb := finite_lieb_thirring_lintegral (hf s)
  rw [finite_fourierMoment, ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)] at hb
  have he (x : Space) : familyDensity (fun j : s => f j) x = ∑ j ∈ s, ‖f j x‖^2 := by
    exact Finset.sum_coe_sort s (fun j => ‖f j x‖^2)
  simp_rw [he] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
    rw [Finset.sum_coe_sort s (fun j => ENNReal.ofReal (‖f j‖^2))]
    exact ENNReal.sum_le_tsum s
  · gcongr
    rw [Finset.sum_coe_sort s (fun j => fourierMoment (f j))]
    exact ENNReal.sum_le_tsum s
end CoulombLT

end

end OAI
