import Mathlib
import OAI.Analysis.CoulombRadii.Screening.OutCap
import OAI.Analysis.CoulombRadii.Screening.CountMoments

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma sliceCount_weight_integrable {m k : ℕ} (u : H1Vector (m+k))
    {A : Set Space} (hA : MeasurableSet A) (s : Spins m) (q : ℕ) :
    Integrable (fun x => mass (u.coreSlice s x)*(localCount A x)^q) := by
  apply ((mass_coreSlice_integrable u s).mul_const ((m:ℝ)^q)).mono'
    ((mass_coreSlice_integrable u s).aestronglyMeasurable.mul
      ((localCount_measurable hA).pow_const q).aestronglyMeasurable)
  filter_upwards [] with x
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (mass_nonneg _) (pow_nonneg (localCount_nonneg _ _) _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) q) (mass_nonneg _)

lemma sliceCount_cap_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {A : Set Space} (hA : MeasurableSet A)
    (s : Spins m) {a : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    Integrable (fun x => mass (u.coreSlice s x)*localCount A x*localFarCap S (u.coreSlice s x).normalized x y a) := by
  have hc : Integrable (fun x => mass (u.coreSlice s x)*localFarCap S (u.coreSlice s x).normalized x y a) := by
    simpa only [pow_one] using localFarCap_weight_integrable S u s ha y hnuc 1
  apply (hc.mul_const (m:ℝ)).mono'
    (((mass_coreSlice_integrable u s).aestronglyMeasurable.mul (localCount_measurable hA).aestronglyMeasurable).mul
      (localFarCap_normalized_slice_aestronglyMeasurable S u s y a))
  filter_upwards [] with x
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mass_nonneg _) (localCount_nonneg _ _)) (localFarCap_nonneg _ _ _ _ _))]
  calc
    _ = mass (u.coreSlice s x)*localFarCap S (u.coreSlice s x).normalized x y a*localCount A x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (localCount_le _ _) (mul_nonneg (mass_nonneg _) (localFarCap_nonneg _ _ _ _ _))

lemma coreScreenedField_sum_le_cover {C : Type*} [Fintype C] {J m k : ℕ}
    (S : Nuclei J) (u : H1Vector k) (x : Configuration m)
    (y : C → Space) (a : C → ℝ) (ha : ∀ c, 0<a c)
    (hnuc : ∀ c j, 4*a c ≤ ‖S.position j-y c‖)
    (hcover : ∀ i, ∃ c, ‖position x i-y c‖ ≤ a c) :
    (∑ i : Fin m, coreScreenedField S u (position x i)) ≤
      ∑ c, localCount (Metric.closedBall (y c) (a c)) x*
        (localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c)) := by
  have H (i : Fin m) : coreScreenedField S u (position x i) ≤
      ∑ c, if position x i ∈ Metric.closedBall (y c) (a c) then
        localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) else 0 := by
    obtain ⟨c,hc⟩ := hcover i
    have hm : position x i ∈ Metric.closedBall (y c) (a c) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hc
    calc
      _ ≤ localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) :=
        coreField_le_local_far_cap S u x (ha c) (y c) (position x i) hc (hnuc c)
      _ = (if position x i ∈ Metric.closedBall (y c) (a c) then
          localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) else 0) := (ite_eq_left hm).symm
      _ ≤ _ := Finset.single_le_sum (f := fun d : C => if position x i ∈ Metric.closedBall (y d) (a d) then
          localFarCap S u x (y d) (a d)+(m:ℝ)/(3*a d) else 0) (fun d _ => by
        split_ifs
        · exact add_nonneg (localFarCap_nonneg _ _ _ _ _) (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (ha d).le))
        · exact le_refl _) (Finset.mem_univ c)
  calc
    _ ≤ ∑ i : Fin m, ∑ c, if position x i ∈ Metric.closedBall (y c) (a c) then
        localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) else 0 := Finset.sum_le_sum (fun i _ => H i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      simp only [localCount,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : position x i ∈ Metric.closedBall (y c) (a c) <;> simp only [Set.indicator,h,ite_true,ite_false,one_mul,zero_mul]

theorem conditionalOutCost_lower_cover {C : Type*} [Fintype C] {J m k : ℕ}
    (S : Nuclei J) (u : H1Vector (m+k))
    (y : C → Space) (a : C → ℝ) (ha : ∀ c, 0<a c)
    (hnuc : ∀ c j, 4*a c ≤ ‖S.position j-y c‖)
    (hsupp : ∀ s, ∀ᵐ x, mass (u.coreSlice s x) ≠0 → ∀ i, ∃ c, ‖position x i-y c‖ ≤ a c) :
    -(∑ c, sliceExpectation u (fun s x => localCount (Metric.closedBall (y c) (a c)) x*
      (localFarCap S (u.coreSlice s x).normalized x (y c) (a c)+(m:ℝ)/(3*a c)))) ≤ conditionalOutCost S u := by
  let F := fun c (s : Spins m) (x : Configuration m) => localCount (Metric.closedBall (y c) (a c)) x*
      (localFarCap S (u.coreSlice s x).normalized x (y c) (a c)+(m:ℝ)/(3*a c))
  have hi (c : C) (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*F c s x) := by
    have hc := sliceCount_cap_weight_integrable S u (show MeasurableSet (Metric.closedBall (y c) (a c)) from measurableSet_closedBall) s (ha c) (y c) (hnuc c)
    have hn : Integrable (fun x => mass (u.coreSlice s x)*localCount (Metric.closedBall (y c) (a c)) x) := by
      simpa only [pow_one] using sliceCount_weight_integrable u (show MeasurableSet (Metric.closedBall (y c) (a c)) from measurableSet_closedBall) s 1
    exact (hc.add (hn.mul_const ((m:ℝ)/(3*a c)))).congr (Eventually.of_forall (fun x => by dsimp [F]; ring))
  have H (s : Spins m) :
      -(∑ c, ∫ x, mass (u.coreSlice s x)*F c s x) ≤
      ∫ x, mass (u.coreSlice s x)*(pairPotential x-∑ i : Fin m, coreScreenedField S (u.coreSlice s x).normalized (position x i)) := by
    rw [←integral_finsetSum _ (fun c _ => hi c s),←integral_neg]
    apply integral_mono_ae ((integrable_finsetSum _ (fun c _ => hi c s)).neg)
      (conditionalOutCost_weight_integrable S u s)
    filter_upwards [hsupp s] with x hx
    by_cases hm : mass (u.coreSlice s x)=0
    · simp [hm]
    · have h := coreScreenedField_sum_le_cover S (u.coreSlice s x).normalized x y a ha hnuc (hx hm)
      have hp := pairPotential_nonneg_pointwise x
      have h' := mul_le_mul_of_nonneg_left (show -(∑ c, F c s x) ≤ pairPotential x-∑ i : Fin m, coreScreenedField S (u.coreSlice s x).normalized (position x i) by dsimp [F]; linarith) (mass_nonneg (u.coreSlice s x))
      simpa only [Finset.mul_sum,mul_neg,Pi.neg_apply] using h'
  have H' := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => H s)
  rw [Finset.sum_neg_distrib,Finset.sum_comm] at H'
  change -(∑ c, sliceExpectation u (F c)) ≤ sliceExpectation u _ at H'
  exact H'.trans (le_add_of_nonneg_left (outerKinetic_nonneg u))

end Coulomb
end

end
end

end OAI
