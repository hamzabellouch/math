import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ShellSummable
import OAI.Analysis.CoulombRadii.Localization.AnnularCut

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

def exteriorCut (t : ℝ) (l : Fin 2) : Space → ℝ :=
  if l=0 then radialCut 0 t 1 else radialCut 0 t 0

lemma exteriorCut_smooth (t : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (exteriorCut t l) := by
  unfold exteriorCut
  split_ifs <;> exact radialCut_smooth 0 t _

lemma exteriorCut_partition (t : ℝ) (x : Space) : ∑ l : Fin 2, exteriorCut t l x^2=1 := by
  simpa only [Fin.sum_univ_two,exteriorCut,ite_true,show (1:Fin 2)≠0 by decide,ite_false,add_comm]
    using radialCut_partition 0 t x

lemma exteriorCut_derivative_bound {t : ℝ} (ht : 0<t) (l : Fin 2) (b : Fin 3) (x : Space) :
    |fderiv ℝ (exteriorCut t l) x (EuclideanSpace.single b 1)|≤radialCutCoefficient/t := by
  unfold exteriorCut
  split_ifs <;> exact radialCut_derivative_bound 0 ht _ b x

lemma exteriorCut_out_zero {t : ℝ} (ht : 0<t) {x : Space} (hx : ‖x‖≤t) : exteriorCut t 0 x=0 := by
  have H := cutAngle_inner 0 ht (x:=x) (by simpa only [sub_zero] using hx)
  simp [exteriorCut,radialCut,H]

lemma exteriorCut_core_zero {t : ℝ} (ht : 0<t) {x : Space} (hx : 2*t≤‖x‖) : exteriorCut t 1 x=0 := by
  have H := cutAngle_outer 0 ht (x:=x) (by simpa only [sub_zero] using hx)
  simp [exteriorCut,radialCut,H]

lemma exteriorCut_gradient_sum (t : ℝ) (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (exteriorCut t l) x (EuclideanSpace.single b 1))^2)=
      ∑ l : Fin 2, (fderiv ℝ (radialCut 0 t l) x (EuclideanSpace.single b 1))^2 := by
  simp only [Fin.sum_univ_two,exteriorCut,ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  exact add_comm ..

lemma form_exterior_labelCut_shell {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) {t : ℝ} (ht : 0<t) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (exteriorCut t) (exteriorCut_smooth t)
      (exteriorCut_partition t) (radialCutCoefficient/t) (div_nonneg radialCutCoefficient_pos.le ht.le)
        (exteriorCut_derivative_bound ht) p))≤
      form S ψ+3*(radialCutCoefficient/t)^2*expectedPopulation ψ (imsShell 0 t) := by
  have H := form_radial_labelCut_shell S ψ 0 ht
  rw [form_labelCut] at H ⊢
  simpa only [exteriorCut_gradient_sum] using H

theorem exists_atomic_exterior_IMS_bound : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j,S.position j=0) →
    ∀ ψ : H1Vector n, Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {t : ℝ} (ht : 0<t),
      (∑ p : Fin n → Fin 2, form S (ψ.labelCut (exteriorCut t) (exteriorCut_smooth t)
        (exteriorCut_partition t) (radialCutCoefficient/t) (div_nonneg radialCutCoefficient_pos.le ht.le)
          (exteriorCut_derivative_bound ht) p)) ≤
      form S ψ+C*(screenMass 0 t)/t^2 := by
  obtain ⟨C,hC,H⟩ := exists_atomic_imsShell_population_bound
  refine ⟨3*radialCutCoefficient^2*C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E hE he t ht
  have hc := H S hatom ψ hψ hm hE (by simpa using he) (le_refl 0) ht
  calc
    _ ≤ form S ψ+3*(radialCutCoefficient/t)^2*expectedPopulation ψ (imsShell 0 t) :=
      form_exterior_labelCut_shell S ψ ht
    _ ≤ form S ψ+3*(radialCutCoefficient/t)^2*(C*screenMass 0 t) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show 0≤3*(radialCutCoefficient/t)^2 by positivity))
    _ = _ := by ring

end Coulomb
end

end

end OAI
