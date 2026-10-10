import OAI.MeasureTheory.Falconer.Estimates.OuterMaskFailure
import OAI.MeasureTheory.Falconer.Estimates.ActualClassFamilies

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem ae_actualClassMeasure_imp (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) (P : Plane → Prop)
    (hP : ∀ᵐ x ∂actualClassMeasure Q μ N B T, P x) :
    ∀ᵐ x ∂μ, x ∈ actualClassDomain Q μ N B T → P x := by
  apply (ae_restrict_iff' (measurableSet_actualClassDomain Q μ N B T)).mp
  simp only [actualClassMeasure,normalizedClass,classMeasure,Measure.restrict_apply_univ] at hP
  change ∀ᵐ x ∂(μ (actualClassDomain Q μ N B T))⁻¹ • μ.restrict (actualClassDomain Q μ N B T), P x at hP
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top μ _))).mp hP

noncomputable def retainedAngularFailure (Q : DyadicSquare) (μ : Measure Plane)
    (m : List ℕ → ℝ → ℝ) (N B : ℕ) (lam sig kap : ℝ) (x : Plane) : Set UnitCircle :=
  ⋃ T ∈ retainedClassLabels Q μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
    {dir | x ∈ actualClassDomain Q μ N B T ∧
      dir ∈ outerAllEntryFailure Q (actualClassMeasure Q μ N B T) (m T) N lam sig kap x}

theorem measurableSet_retainedAngularFailure (Q : DyadicSquare) (μ : Measure Plane)
    (m : List ℕ → ℝ → ℝ) (N B : ℕ) (lam sig kap : ℝ) :
    MeasurableSet {z : Plane × UnitCircle | z.2 ∈ retainedAngularFailure Q μ m N B lam sig kap z.1} := by
  have he : {z : Plane × UnitCircle | z.2 ∈ retainedAngularFailure Q μ m N B lam sig kap z.1} =
      ⋃ T ∈ retainedClassLabels Q μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
        {z : Plane × UnitCircle | z.1 ∈ actualClassDomain Q μ N B T ∧
          z.2 ∈ outerAllEntryFailure Q (actualClassMeasure Q μ N B T) (m T) N lam sig kap z.1} := by
    ext z
    simp only [retainedAngularFailure,mem_ofPred_eq,mem_iUnion]
  rw [he]
  apply Finset.measurableSet_biUnion
  intro T _
  exact ((measurableSet_actualClassDomain Q μ N B T).preimage measurable_fst).inter
    (measurableSet_outerAllEntryFailure _ _ _ _ _ _ _)

theorem ae_retainedAngularFailure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane)
    [IsProbabilityMeasure μ] (m : List ℕ → ℝ → ℝ) {N H : ℕ} (hN : 0 < N)
    (δ lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (hf : ActualClassFamily Q μ N H δ lam sig m) :
    ∀ᵐ x ∂μ, sourceArcLength (retainedAngularFailure Q μ m N (N/H) lam sig kap x) ≤
      (((4*N+1)^(2*H+1):ℕ):ENNReal)*((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*
        ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  classical
  let S := retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let w := ((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))
  have hx : ∀ᵐ x ∂μ, ∀ T : List ℕ, T ∈ S → x ∈ actualClassDomain Q μ N (N/H) T →
      sourceArcLength (outerAllEntryFailure Q (actualClassMeasure Q μ N (N/H) T) (m T) N lam sig kap x) ≤ w := by
    apply ae_all_iff.mpr
    intro T
    by_cases hT : T ∈ S
    · filter_upwards [ae_actualClassMeasure_imp Q μ N (N/H) T _
        (ae_outerAllEntryFailure_bound Q hQ _ (actualClassMeasure_carry Q hQ μ N (N/H) T) (m T)
          hN lam sig hkap (hf.profiles T hT).2)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hT h))
  filter_upwards [hx] with x hx
  have hb : sourceArcLength (retainedAngularFailure Q μ m N (N/H) lam sig kap x) ≤ (S.card:ENNReal)*w := by
    apply (measure_biUnion_finset_le _ _).trans
    calc
      _ ≤ ∑ _T ∈ S, w := by
        apply Finset.sum_le_sum
        intro T hT
        by_cases hdom : x ∈ actualClassDomain Q μ N (N/H) T
        · apply (measure_mono (fun _ h => h.2)).trans
          exact hx T hT hdom
        · have he : {dir | x ∈ actualClassDomain Q μ N (N/H) T ∧
              dir ∈ outerAllEntryFailure Q (actualClassMeasure Q μ N (N/H) T) (m T) N lam sig kap x} = ∅ := by
            ext dir; simp [hdom]
          rw [he,measure_empty]
          exact zero_le
      _ = _ := by simp
  apply hb.trans
  simpa only [w,mul_assoc] using
    mul_le_mul_left (show (S.card:ENNReal) ≤ (((4*N+1)^(2*H+1):ℕ):ENNReal) from by dsimp only [S]; exact_mod_cast hf.count) w

end PlanarFalconer

end OAI
