import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FermionicNear

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma fineKernel_near_coulomb_le {b : ℝ} (hb : 0<b) (y w : Space)
    (hw : w≠y) (r : ℝ) :
    (∫ z in Metric.ball y r,coulombKernel (y-z)*fineKernel b (z-w))≤nearWeight y (r+2*b) w := by
  by_cases hn : w∈Metric.ball y (r+2*b)
  · rw [nearWeight,indicator_of_mem hn]
    calc
      _≤∫ z,coulombKernel (y-z)*fineKernel b (z-w) :=
        setIntegral_le_integral (fineKernel_shift_coulomb_integrable hb y w)
          (Eventually.of_forall (fun z => mul_nonneg (coulombKernel_nonneg _) (fineKernel_nonneg ..)))
      _≤_ := by
        rw [fineKernel_shift_coulomb_integral]
        exact fineKernel_coulomb_le hb (sub_ne_zero.mpr hw.symm)
  · rw [nearWeight,indicator_of_notMem hn]
    have hdist : r+2*b≤‖w-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
    have he : (∫ z in Metric.ball y r,coulombKernel (y-z)*fineKernel b (z-w))=0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      exact Eventually.of_forall (fun z hz => by
      have hz' : ‖z-y‖<r := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
      have htri := norm_sub_le_norm_sub_add_norm_sub w z y
      rw [norm_sub_rev w z] at htri
      rw [fineKernel_eq_zero_of_two_mul_lt hb _ (by linarith),mul_zero])
    exact he.le

theorem retainedFine_near_le {n : ℕ} {b : ℝ} (hb : 0<b) (y : Space) (r : ℝ)
    (I : Finset (Fin n)) (x : Configuration n) (hxy : ∀ i,position x i≠y) :
    (∫ z in Metric.ball y r,coulombKernel (y-z)*retainedFineDensity b I (position x) z)≤
      nearPotential y (r+2*b) x := by
  simp only [retainedFineDensity,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => (fineKernel_shift_coulomb_integrable hb y (position x i)).integrableOn)]
  exact (Finset.sum_le_sum (fun i _ => fineKernel_near_coulomb_le hb y (position x i) (hxy i) r)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => nearWeight_nonneg y _ _))

lemma fineKernel_raw_deficit {b : ℝ} (hb : 0<b) (y w : Space) (hw : w≠y) :
    0≤coulombKernel (y-w)-(∫ z,coulombKernel (y-z)*fineKernel b (z-w)) ∧
    coulombKernel (y-w)-(∫ z,coulombKernel (y-z)*fineKernel b (z-w))≤nearWeight y (2*b) w := by
  have hnewton : (∫ z,coulombKernel (y-z)*fineKernel b (z-w))≤coulombKernel (y-w) := by
    rw [fineKernel_shift_coulomb_integral]
    exact fineKernel_coulomb_le hb (sub_ne_zero.mpr hw.symm)
  refine ⟨sub_nonneg.mpr hnewton,?_⟩
  by_cases hn : w∈Metric.ball y (2*b)
  · rw [nearWeight,indicator_of_mem hn]
    exact sub_le_self _ (integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _) (fineKernel_nonneg ..)))
  · rw [nearWeight,indicator_of_notMem hn]
    have hsep : Real.sqrt 3*b≤‖y-w‖ := by
      have hd : 2*b≤‖w-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
      have hs : Real.sqrt 3≤2 := by apply (Real.sqrt_le_iff).mpr; norm_num
      rw [norm_sub_rev]
      exact (mul_le_mul_of_nonneg_right hs hb.le).trans hd
    rw [fineKernel_shift_coulomb_eq hb y w hsep,sub_self]

theorem patchFine_raw_deficit {n : ℕ} {b t a : ℝ} (hb : 0<b) (ha : 0<a)
    (hat : a≤t-7*b) (y : Space) (x : Configuration n) (hxy : ∀ i,position x i≠y) :
    0≤nuclearPotential (unitNucleus y) x-
      NeutralAtom.potentialOf (retainedFineDensity b (patchRetained y t b x) (position x)) y ∧
    nuclearPotential (unitNucleus y) x-
      NeutralAtom.potentialOf (retainedFineDensity b (patchRetained y t b x) (position x)) y≤
      nearPotential y (2*b) x+((deletedLabels (patchRetained y t b) x).card:ℝ)/a := by
  let I := patchRetained y t b x
  let D := deletedLabels (patchRetained y t b) x
  have hpot : NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y=
      ∑ i∈I,∫ z,coulombKernel (y-z)*fineKernel b (z-position x i) := by
    unfold NeutralAtom.potentialOf
    simp only [retainedFineDensity,Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => fineKernel_shift_coulomb_integrable hb y _)
  have hraw : nuclearPotential (unitNucleus y) x=∑ i,coulombKernel (y-position x i) := by
    simp [nuclearPotential,attraction,unitNucleus,coulombKernel,norm_sub_rev]
  have hdel : (∑ i∈D,coulombKernel (y-position x i))≤(D.card:ℝ)/a := by
    calc
      _≤∑ _i∈D,a⁻¹ := by
        apply Finset.sum_le_sum
        intro i hi
        have hni : i∉I := by simpa only [D,deletedLabels,Finset.mem_sdiff,Finset.mem_univ,true_and] using hi
        have hn : t-7*b≤‖position x i-y‖ := by simpa only [I,patchRetained_mem,not_lt] using hni
        unfold coulombKernel
        rw [norm_sub_rev]
        exact inv_anti₀ ha (hat.trans hn)
      _=_ := by simp [div_eq_mul_inv]
  have he : nuclearPotential (unitNucleus y) x-NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y=
      (∑ i∈I,(coulombKernel (y-position x i)-(∫ z,coulombKernel (y-z)*fineKernel b (z-position x i))))+
        ∑ i∈D,coulombKernel (y-position x i) := by
    rw [hraw,hpot,←retained_deleted_sum (patchRetained y t b) x (fun i => coulombKernel (y-position x i)),Finset.sum_sub_distrib]
    ring
  change 0≤nuclearPotential (unitNucleus y) x-NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y ∧ _
  rw [he]
  constructor
  · exact add_nonneg (Finset.sum_nonneg (fun i _ => (fineKernel_raw_deficit hb y _ (hxy i)).1))
      (Finset.sum_nonneg (fun i _ => coulombKernel_nonneg _))
  · have hh := (Finset.sum_le_sum (fun i (_ : i∈I) => (fineKernel_raw_deficit hb y _ (hxy i)).2)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => nearWeight_nonneg y (2*b) _))
    exact add_le_add hh hdel
end Coulomb
end

end
end

end OAI
