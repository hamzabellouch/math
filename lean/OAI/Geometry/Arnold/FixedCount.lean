import OAI.Geometry.Arnold.CriticalLifts

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma zeroLift_fixed : mainEquiv (project zeroLift) = project zeroLift := by
  apply vertical_core_fixed zeroLift (by rfl) 0 (by norm_num)
  simp only [zero_smul]
  change core zeroVector = 0
  exact core_zeroVector

lemma otherLift_fixed (r : ℝ) (hr : r^2 = 3) :
    mainEquiv (project ⟨otherVector r,otherVector_unit r hr⟩) =
      project ⟨otherVector r,otherVector_unit r hr⟩ := by
  apply vertical_core_fixed _ (by rfl) (-(3*r/2))
  · have hb : |r| ≤ 2 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    rw [abs_neg, abs_div, abs_mul]
    norm_num
    linarith
  · exact core_otherVector r hr

lemma plusLift_fixed : mainEquiv (project plusLift) = project plusLift :=
  otherLift_fixed _ (Real.sq_sqrt (by norm_num))
lemma minusLift_fixed : mainEquiv (project minusLift) = project minusLift :=
  otherLift_fixed _ (by rw [neg_sq]; exact Real.sq_sqrt (by norm_num))

lemma factors_respects (z w : UnitQuadric) (h : project z = project w) :
    sphereFactors z = sphereFactors w := by
  obtain ⟨c,hc,he⟩ := (project_eq_iff_phase z w).mp h
  rw [← he]
  simp only [sphereFactors, left_scale, right_scale, hc, one_smul]

lemma zeroLift_ne_plusLift : project zeroLift ≠ project plusLift := by
  intro h
  have he := factors_respects _ _ h
  rw [plusLift_factors, show sphereFactors zeroLift = qzero from zeroVector_factors] at he
  exact qzero_ne_qplus he
lemma zeroLift_ne_minusLift : project zeroLift ≠ project minusLift := by
  intro h
  have he := factors_respects _ _ h
  rw [minusLift_factors, show sphereFactors zeroLift = qzero from zeroVector_factors] at he
  exact qzero_ne_qminus he
lemma plusLift_ne_minusLift : project plusLift ≠ project minusLift := by
  intro h
  have he := factors_respects _ _ h
  rw [plusLift_factors, minusLift_factors] at he
  exact qplus_ne_qminus he

lemma main_fixed_iff (q : Q3) : mainEquiv q = q ↔
    q = project zeroLift ∨ q = project plusLift ∨ q = project minusLift := by
  constructor
  · obtain ⟨z,rfl⟩ := project_surjective q
    intro hz
    have hz0 := fixed_zero_coordinate z hz
    have hc := multiplierCritical_iff (sphereFactors z) |>.mp (fixed_factor_critical z hz)
    rcases hc with hc | hc | hc
    · exact Or.inl (sphereFactors_project_injective z zeroLift hz0 (by rfl) (hc.trans zeroVector_factors.symm))
    · exact Or.inr (Or.inl (sphereFactors_project_injective z plusLift hz0 (by rfl) (hc.trans plusLift_factors.symm)))
    · exact Or.inr (Or.inr (sphereFactors_project_injective z minusLift hz0 (by rfl) (hc.trans minusLift_factors.symm)))
  · rintro (rfl | rfl | rfl)
    · exact zeroLift_fixed
    · exact plusLift_fixed
    · exact minusLift_fixed

lemma main_fixed_set : fixedSet mainEquiv = {project zeroLift, project plusLift, project minusLift} := by
  ext q
  simp only [fixedSet, mem_ofPred_eq, main_fixed_iff, mem_insert_iff, mem_singleton_iff]

lemma main_fixed_encard : (fixedSet mainEquiv).encard = 3 := by
  rw [main_fixed_set, Set.encard_insert_of_notMem]
  · rw [Set.encard_pair plusLift_ne_minusLift]
    norm_num
  · simp [zeroLift_ne_plusLift, zeroLift_ne_minusLift]

end ArnoldCounterexample.Construction

end

end OAI
