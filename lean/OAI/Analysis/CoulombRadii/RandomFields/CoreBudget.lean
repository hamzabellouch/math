import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.BinaryDeletion
import OAI.Analysis.CoulombRadii.Localization.ExteriorCut

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb
namespace RecordedEnsemble

theorem atomic_zero_offset_core_deletion : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j,S.position j=0) →
    ∀ ψ : H1Vector n, Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {t : ℝ}, 0<t → ∃ T : RecordedEnsemble n,
      T.Conserves ψ ∧ T.CoreFermionic ∧ T.CoreSupported {y | ‖y‖<2*t} ∧
      T.OutSupported {y | t≤‖y‖} ∧ T.totalMass=1 ∧
      T.totalCoreForm S ≤ E+C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
  obtain ⟨Ci,hCi,Hi⟩ := exists_atomic_exterior_IMS_bound
  obtain ⟨Ca,hCa,Ha⟩ := atomic_weighted_exterior_deletion
  refine ⟨Ci+Ca,add_nonneg hCi hCa,?_⟩
  intro J n S hatom ψ hψ hm E hE he t ht
  have hinner y (hy : ‖y‖<t) : exteriorCut t 0 y=0 := exteriorCut_out_zero ht hy.le
  have hcore y (hy : y∉{y | ‖y‖<2*t}) : exteriorCut t 1 y=0 :=
    exteriorCut_core_zero ht (le_of_not_gt hy)
  obtain ⟨T,hT,hF,hS,hO,hM,hform,hcoreform⟩ := binary_localization_deletion S hatom ψ hψ
    (exteriorCut t) (exteriorCut_smooth t) (exteriorCut_partition t)
    (radialCutCoefficient/t) (div_nonneg radialCutCoefficient_pos.le ht.le)
    (exteriorCut_derivative_bound ht) ht (by linarith : t/4≤t/2)
    hinner {y | ‖y‖<2*t} hcore
  refine ⟨T,hT,hF,hS,hO,by simpa only [hm] using hM,?_⟩
  have hweight y : exteriorCut t 0 y^2≤1 := by
    have H := exteriorCut_partition t y
    simp only [Fin.sum_univ_two] at H
    nlinarith [sq_nonneg (exteriorCut t 1 y)]
  have ha := Ha S hatom ψ hψ hm hE he ht (fun y => exteriorCut t 0 y^2)
    ((exteriorCut_smooth t 0).continuous.measurable.pow_const 2) (fun y => sq_nonneg _) hweight
    (fun y hy => by simp only [hinner y hy,zero_pow (by decide : 2≠0)])
  have hi := Hi S hatom ψ hψ hm hE he ht
  rw [←hform] at hi
  have h1 : 0≤(screenMass 0 (t/4))^2/t := div_nonneg (sq_nonneg _) ht.le
  have h2 : 0 ≤ screenMass 0 t/t^2 := div_nonneg (screenMass_pos _ _).le (sq_nonneg _)
  calc
    T.totalCoreForm S ≤ T.totalForm S+potentialForm (weightedInnerField S (t/4) (fun y => exteriorCut t 0 y^2)) ψ := hcoreform
    _ ≤ (form S ψ+Ci*screenMass 0 t/t^2)+Ca*(screenMass 0 (t/4))^2/t := add_le_add hi ha
    _ ≤ E+(Ci+Ca)*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
      simp only [mul_div_assoc] at *
      nlinarith [mul_nonneg hCi h1,mul_nonneg hCa h2]

end RecordedEnsemble
end Coulomb
end

end

end OAI
