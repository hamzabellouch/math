import Mathlib
import OAI.Analysis.VlasovMaxwell.Model

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_velocity_integral_bound_from_caps {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {H : Vec × Vec → W} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ))
    (A P : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ f : Phase → ℝ,
      (∀ z, |f z|≤A) → (∀ x v, P<‖v‖ → f (x,v)=0) →
      ∀ y n : Vec, ‖n‖=1 → ‖∫ v : Vec, f (y,v) • H (n,v)‖≤C := by
  let K := closedBall (0:Vec) P
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := ((isCompact_sphere (0:Vec) 1).prod hK).exists_bound_of_continuousOn
    (hH.mono (by intro p hp; exact ⟨hp.1,mem_univ _⟩))
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨A*D*(volume K).toReal,by positivity,?_⟩
  intro f hf hp y n hn
  have hn' : n∈sphere (0:Vec) 1 := mem_sphere_zero_iff_norm.mpr hn
  have he : (∫ v in K, f (y,v) • H (n,v))=(∫ v, f (y,v) • H (n,v)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hp y v (by simpa only [K,mem_closedBall,dist_zero_right,not_le] using hv),zero_smul]
  rw [←he]
  have hb : ∀ v∈K, ‖f (y,v) • H (n,v)‖≤A*D := by
    intro v hv
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hf (y,v)) ((hB (n,v) ⟨hn',hv⟩).trans (le_max_left _ _)) (norm_nonneg _) hA
  exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb

lemma uniform_velocity_integral_lipschitz_from_caps {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {H : Vec × Vec → W} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ))
    (A P : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ f : Phase → ℝ, Continuous f →
      (∀ x y v, |f (y,v)-f (x,v)|≤A*‖y-x‖) → (∀ x v, P<‖v‖ → f (x,v)=0) →
      ∀ x y n : Vec, ‖n‖=1 →
      ‖(∫ v, f (y,v) • H (n,v))-(∫ v, f (x,v) • H (n,v))‖≤C*‖y-x‖ := by
  let K := closedBall (0:Vec) P
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := ((isCompact_sphere (0:Vec) 1).prod hK).exists_bound_of_continuousOn
    (hH.mono (by intro p hp; exact ⟨hp.1,mem_univ _⟩))
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨A*D*(volume K).toReal,by positivity,?_⟩
  intro f hf hfl hp x y n hn
  have hz (z v : Vec) (hv : v∉K) : f (z,v)=0 :=
    hp z v (by simpa only [K,mem_closedBall,dist_zero_right,not_le] using hv)
  have hn' : n∈sphere (0:Vec) 1 := mem_sphere_zero_iff_norm.mpr hn
  have hint (z : Vec) : Integrable (fun v => f (z,v) • H (n,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.comp (continuous_const.prodMk continuous_id)).smul
        (hH.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hn',mem_univ v⟩))
    · exact HasCompactSupport.intro hK (fun v hv => by rw [hz z v hv,zero_smul])
  rw [← integral_sub (hint y) (hint x)]
  have he : (∫ v in K, f (y,v) • H (n,v)-f (x,v) • H (n,v))=
      ∫ v, f (y,v) • H (n,v)-f (x,v) • H (n,v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    simp only [hz _ v hv,zero_smul,sub_self]
  rw [← he]
  have hb : ∀ v∈K, ‖f (y,v) • H (n,v)-f (x,v) • H (n,v)‖≤ A*‖y-x‖*D := by
    intro v hv
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hfl x y v) ((hB (n,v) ⟨hn',hv⟩).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  exact (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb).trans_eq (by simp only [Measure.real]; ring)

end RVM
end

end OAI
