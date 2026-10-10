import OAI.Dynamics.StandardMap.BandFlux

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma lengthBand_disjoint : Pairwise (fun i j : ℤ => Disjoint (lengthBand i) (lengthBand j)) := by
  intro i j hij
  rw [disjoint_left]
  intro d hi hj
  have hpow : StrictMono (fun n:ℤ => (2:ℝ)^n) := zpow_right_strictMono₀ (by norm_num)
  rcases lt_or_gt_of_ne hij with h|h
  · have hh := hpow.monotone (by omega : i + 1 ≤ j)
    exact (not_le_of_gt hi.2.2.2) (hh.trans hj.2.2.1)
  · have hh := hpow.monotone (by omega : j + 1 ≤ i)
    exact (not_le_of_gt hj.2.2.2) (hh.trans hi.2.2.1)
lemma mem_union_lengthBand {d:NonAffineArray} (hu:UnitArray d.val) (hd:d.val∈twoRayClass) (hl:0<coreLength d.val) : d∈⋃j:ℤ,lengthBand (-j) := by
  obtain ⟨j,hj⟩ := exists_mem_Ico_zpow hl (by norm_num : (1:ℝ)<2)
  exact mem_iUnion.mpr ⟨-j,by simpa only [neg_neg,lengthBand,mem_Ico,mem_ofPred_eq] using And.intro hu (And.intro hd hj)⟩
lemma restrict_lengthBand (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (hS:μ.map nonaffineDilate=μ) (j:ℤ) :
    μ.restrict (lengthBand (-j))=(bandLaw μ).map (scaleZ j) := by
  have hh := Measure.restrict_map (μ:=μ) (measurable_scaleZ j) (measurableSet_lengthBand (-j))
  rw [map_scaleZ μ hu hS j,lengthBand_scaleZ,add_neg_cancel] at hh
  exact hh
lemma bandSeries_law (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (hS:μ.map nonaffineDilate=μ) :
    μ.restrict (⋃j:ℤ,lengthBand (-j))=Measure.sum (fun j:ℤ => (bandLaw μ).map (scaleZ j)) := by
  rw [Measure.restrict_iUnion (fun i j hij => lengthBand_disjoint (by omega : -i ≠ -j)) (fun j => measurableSet_lengthBand (-j))]
  congr 1; funext j; exact restrict_lengthBand μ hu hS j
lemma band_integral_series (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (hS:μ.map nonaffineDilate=μ)
    (g:NonAffineArray→ℝ) (hg:Integrable g μ) :
    HasSum (fun j:ℤ => ∫d,g (scaleZ j d) ∂bandLaw μ) (∫d in ⋃j:ℤ,lengthBand (-j),g d ∂μ) := by
  have hh : Integrable g (Measure.sum (fun j:ℤ => (bandLaw μ).map (scaleZ j))) := by rw [←bandSeries_law μ hu hS]; exact hg.restrict
  have hm (j:ℤ) : Integrable g ((bandLaw μ).map (scaleZ j)) := hh.mono_measure (Measure.le_sum (fun index : ℤ => (bandLaw μ).map (scaleZ index)) j)
  have he (j:ℤ) : (∫d,g d ∂(bandLaw μ).map (scaleZ j))=∫d,g (scaleZ j d) ∂bandLaw μ :=
    integral_map (measurable_scaleZ j).aemeasurable (hm j).aestronglyMeasurable
  have hh' := hasSum_integral_measure hh
  simp_rw [he] at hh'
  rwa [←bandSeries_law μ hu hS] at hh'
lemma bilateral_coboundary_nonpos (F:ℤ→ℝ) (A:ℝ) (h:HasSum (fun j:ℤ => F (j+1)-F j) A)
    (hf:∀ᶠn:ℕ in atTop,F (n:ℤ)≤F (-(n:ℤ))) : A≤0 := by
  have ht : Tendsto (fun n:ℕ => ∑j∈Finset.Ico (-(n:ℤ)) (n:ℤ),(F (j+1)-F j)) atTop (𝓝 A) :=
    h.comp Finset.tendsto_Ico_neg
  have he (n:ℕ) : (∑j∈Finset.Ico (-(n:ℤ)) (n:ℤ),(F (j+1)-F j))=F (n:ℤ)-F (-(n:ℤ)) := by
    have hh := Finset.sum_Ico_int_sub n (fun j => -F j)
    simpa only [neg_sub_neg] using hh
  simp_rw [he] at ht
  exact le_of_tendsto ht (hf.mono (fun n hn => sub_nonpos.mpr hn))
end StandardMapEntropy

end OAI
