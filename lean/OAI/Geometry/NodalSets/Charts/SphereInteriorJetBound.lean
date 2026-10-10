import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas
import OAI.Geometry.NodalSets.Spectral.SphereEigenForcingDerivativeBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_interior_jet_bound (d : SphereEnergyData) (p : Base)
    (C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    ∃ A > 0, ∀ (f : SphereWeightedL2 d)
      (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
      (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4)))),
      (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      let Q := Yau.realCenteredCube 4 (1/4)
      let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
      (MemLp (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) 2 (volume.restrict Q) ∧
        (∫ x in Q, ((sphereL2Resolvent d f) (sphereChartCoordMap p x))^2) ≤ A*E) ∧
      (∀ a, MemLp (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) 2 (volume.restrict Q) ∧
        (∫ x in Q, ((sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x)^2) ≤ A*E) ∧
      (∀ a k, MemLp (H a k) 2 (volume.restrict Q) ∧ (∫ x in Q, (H a k x)^2) ≤ A*E) ∧
      (∀ a k i, MemLp (J a k i) 2 (volume.restrict Q) ∧ (∫ x in Q, (J a k i x)^2) ≤ A*E) := by
  let Q := Yau.realCenteredCube 4 (1/4)
  obtain ⟨W,hW,hwb⟩ := sphereWeightedL2_compact_chart_bound d p (Yau.realCenteredCube_isCompact 4 (1/4))
  obtain ⟨D,hD,hdb⟩ := sphereChartDerivativeMap_bound d p
  let A := W+D^2+C2+C3+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,fun f H J hH hJ ↦ ?_⟩
  dsimp only
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hWle : W ≤ A := by dsimp [A]; nlinarith [sq_nonneg D]
  have hDle : D^2 ≤ A := by dsimp [A]; linarith
  have h2le : C2 ≤ A := by dsimp [A]; nlinarith [sq_nonneg D]
  have h3le : C3 ≤ A := by dsimp [A]; nlinarith [sq_nonneg D]
  have hfE : ‖f‖^2 ≤ E := by dsimp [E]; nlinarith [sq_nonneg ‖sphereWeakSolution d f‖]
  have hzE : ‖sphereWeakSolution d f‖^2 ≤ E := by dsimp [E]; nlinarith [sq_nonneg ‖f‖]
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hsub2 : Q ⊆ Yau.realCenteredCube 4 (1/2) := Yau.realCenteredCube_mono (by norm_num)
  refine ⟨⟨(hwb (sphereL2Resolvent d f)).1,?_⟩,?_,?_,?_⟩
  · have hn : ‖sphereL2Resolvent d f‖ ≤ ‖f‖ :=
      ((sphereL2Resolvent d).le_opNorm f).trans (by
        simpa using mul_le_mul_of_nonneg_right (sphereL2Resolvent_norm_le d) (norm_nonneg f))
    have hn2 := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hfE
    exact (hwb (sphereL2Resolvent d f)).2.trans
      ((mul_le_mul_of_nonneg_left hn2 hW.le).trans (mul_le_mul_of_nonneg_right hWle hE))
  · intro a
    have ht := Yau.real_Lp_restricted_square_le (Measure.restrict_mono hsub (le_refl volume))
      (sphereChartDerivativeMap d p a (sphereWeakSolution d f))
    refine ⟨ht.1,ht.2.trans ?_⟩
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hdb a (sphereWeakSolution d f)) 2
    rw [mul_pow] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hzE (sq_nonneg D)).trans
      (mul_le_mul_of_nonneg_right hDle hE))
  · intro a k
    have ht := Yau.real_Lp_restricted_square_le (Measure.restrict_mono hsub2 (le_refl volume)) (H a k)
    refine ⟨ht.1,ht.2.trans ?_⟩
    have hone : ‖H a k‖^2 ≤ ∑ b, ∑ c, ‖H b c‖^2 :=
      (Finset.single_le_sum (f := fun c ↦ ‖H a c‖^2) (fun c _ ↦ sq_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun b ↦ ∑ c, ‖H b c‖^2)
        (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ sq_nonneg _)) (Finset.mem_univ a))
    exact (hone.trans hH).trans (mul_le_mul_of_nonneg_right h2le hE)
  · intro a k i
    have ht := Yau.real_Lp_restricted_square_le (le_refl (volume.restrict Q)) (J a k i)
    refine ⟨ht.1,ht.2.trans ?_⟩
    have hone : ‖J a k i‖^2 ≤ ∑ b, ∑ c, ∑ e, ‖J b c e‖^2 :=
      (Finset.single_le_sum (f := fun e ↦ ‖J a k e‖^2) (fun e _ ↦ sq_nonneg _) (Finset.mem_univ i)).trans
      ((Finset.single_le_sum (f := fun c ↦ ∑ e, ‖J a c e‖^2)
        (fun c _ ↦ Finset.sum_nonneg (fun e _ ↦ sq_nonneg _)) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun b ↦ ∑ c, ∑ e, ‖J b c e‖^2)
        (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ Finset.sum_nonneg (fun e _ ↦ sq_nonneg _))) (Finset.mem_univ a)))
    exact (hone.trans hJ).trans (mul_le_mul_of_nonneg_right h3le hE)

end
end Yau.Target

end OAI
