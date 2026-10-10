import OAI.Analysis.Laughlin.FourBody.Formula
import OAI.Analysis.Laughlin.FourBody.GlobalFock
import OAI.Analysis.Laughlin.Operators.NormalCertificate

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_rotation_integrable {I : Type*} [Fintype I]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (M : Matrix I I ℂ) (x : Space Q) :
    Integrable (fun g : SourceSU2 => contractionForm Q L M (exteriorRotation Q g⁻¹ x)) sourceHaar := by
  unfold contractionForm
  exact integrable_finsetSum _ (fun i hi => integrable_finsetSum _
    (fun j hj => (linearMap_rotation_inner_integrable Q (L i) (L j) x).const_mul _))

noncomputable def sourceKForm (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) : ℝ :=
  ((2*Q-2+1 : ℕ) : ℝ) * ∫ g, (Certificate.rows.map (fun row =>
    occupationNormSq Q (sourceRowSquareVector Q hQ row (exteriorRotation Q g⁻¹ x)))).sum ∂sourceHaar

noncomputable def sourceA3Form (Q : ℕ) (x : Space Q) : ℝ :=
  ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceThreeEnd Q)
    ((physicalThreeBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re

theorem sourceKForm_nonneg (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) : 0 ≤ sourceKForm Q hQ x := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro g
  apply List.sum_nonneg
  intro a ha
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp ha
  exact occupationNormSq_nonneg Q _

theorem sourceKForm_decomposition (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceKForm Q (by omega) x = (93527408868499/10^14 : ℝ)*sourceFockEnergy Q x +
      sourceA3Form Q x + sourceA4Form Q x := by
  let L2 := fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val
  let M2 := physicalTwoBodyMatrix Q
  let M3 := (physicalThreeBodyMatrix Q).map Complex.ofReal
  let M4 := (physicalFourBodyMatrix Q).map Complex.ofReal
  have hp (y : Space Q) :
      (Certificate.rows.map (fun row => occupationNormSq Q (sourceRowSquareVector Q (by omega) row y))).sum =
      (contractionForm Q L2 M2 y + contractionForm Q (sourceThreeEnd Q) M3 y +
        contractionForm Q (sourceFourFamilyEnd Q) M4 y).re := by
    have h := congrArg Complex.re (source_seven_squares_normal_form Q hQ y)
    have hs (l : List (ℕ × ℤ × List (ℕ × ℕ × ℤ))) :
        (l.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q (by omega) row y) : ℂ))).sum.re =
          (l.map (fun row => occupationNormSq Q (sourceRowSquareVector Q (by omega) row y))).sum := by
      induction l with
      | nil => simp
      | cons row l ih => simp only [List.map_cons,List.sum_cons,Complex.add_re,Complex.ofReal_re,ih]
    rw [hs] at h
    exact h
  have hi2 := contractionForm_rotation_integrable Q L2 M2 x
  have hi3 := contractionForm_rotation_integrable Q (sourceThreeEnd Q) M3 x
  have hi4 := contractionForm_rotation_integrable Q (sourceFourFamilyEnd Q) M4 x
  have h2 := congrArg Complex.re (physical_twoBody_certificate_haar Q (by omega) x)
  norm_num [Complex.mul_re] at h2
  rw [sourceKForm]
  simp_rw [hp]
  have hre := integral_re ((hi2.add hi3).add hi4)
  change (∫ g, (contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceFourFamilyEnd Q) M4 (exteriorRotation Q g⁻¹ x)).re ∂sourceHaar) =
    (∫ g, contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceFourFamilyEnd Q) M4 (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re at hre
  have hi23 : Integrable (fun g : SourceSU2 =>
      contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x)) sourceHaar := hi2.add hi3
  rw [hre,integral_add hi23 hi4,
    integral_add hi2 hi3,Complex.add_re,Complex.add_re]
  change _ = _ + ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceThreeEnd Q) M3
    (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re +
    ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceFourFamilyEnd Q) M4
    (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re
  rw [mul_add,mul_add]
  congr 2
  norm_num [L2,M2]
  exact h2

end Laughlin.Fock

end OAI
