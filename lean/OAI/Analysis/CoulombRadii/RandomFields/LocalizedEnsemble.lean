import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalPositiveField
import OAI.Analysis.CoulombRadii.FormDomain.SortedCut
import OAI.Analysis.CoulombRadii.Localization.RadialCut

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def conditionalOutCost {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k)) : ℝ :=
  outerKinetic ψ+sliceExpectation ψ (fun s x => pairPotential x-
    ∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i))

lemma conditionalOutCost_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*(pairPotential x-
      ∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i))) := by
  apply ((conditionalEnergy_weight_integrable S ψ s).sub
    (normalized_coreForm_weight_integrable S ψ s)).congr
  exact Eventually.of_forall (fun x => by
    simp only [Pi.sub_apply,conditionalEnergy_eq_screened]
    ring)

lemma form_eq_conditionalOutCost {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k)) :
    form S ψ = sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)+conditionalOutCost S ψ := by
  rw [conditional_energy_identity]
  change outerKinetic ψ+sliceExpectation ψ (conditionalEnergy S ψ)=_
  have H : sliceExpectation ψ (conditionalEnergy S ψ) =
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)+
      sliceExpectation ψ (fun s x => pairPotential x-
        ∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) := by
    rw [← sliceExpectation_add ψ _ _ (normalized_coreForm_weight_integrable S ψ)
      (conditionalOutCost_weight_integrable S ψ)]
    congr 1
    funext s x
    rw [conditionalEnergy_eq_screened]
    ring
  rw [H]
  unfold conditionalOutCost
  ring

theorem radial_conditional_gain_ensemble {J n : ℕ} (S : Nuclei J)
    (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hmass : mass ψ=1)
    {a E δ : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖)
    (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ) :
    ∃ (m k : (Fin n → Fin 2) → ℕ) (u : (p : Fin n → Fin 2) → H1Vector (m p+k p)),
      (∀ p, m p+k p=n) ∧ (∑ p, mass (u p))=1 ∧
      (∀ p s, ∀ᵐ x, Antisymmetric ((u p).coreSlice s x)) ∧
      (∀ p s, ∀ᵐ x, SpatiallySupported ((u p).coreSlice s x).normalized {z | 3*a ≤ ‖z-y‖}) ∧
      a/(16*ballTrialCoefficient)*(∑ p, sliceExpectation (u p) (fun s x =>
        (max (coreScreenedField S ((u p).coreSlice s x).normalized y) 0)^2)) ≤
      δ+3*(radialCutCoefficient/(3*a))^2*expectedPopulation ψ (Metric.closedBall y (6*a))+
        4*ballTrialCoefficient*(screenBaseMass a)^2/a-∑ p, conditionalOutCost S (u p) := by
  have hr : 0 < 3*a := by positivity
  let χ := radialCut y (3*a)
  have hc : ∀ z ∉ {z | 3*a ≤ ‖z-y‖}, χ 1 z=0 := by
    intro z hz
    apply radialCut_core_zero y hr z
    exact (lt_of_not_ge hz).le
  have H (p : Fin n → Fin 2) := binary_cut_core_outcome S ψ hψ χ (radialCut_smooth y (3*a))
    (radialCut_partition y (3*a)) (radialCutCoefficient/(3*a))
    (div_nonneg radialCutCoefficient_pos.le hr.le) (radialCut_derivative_bound y hr) p _ hc
  choose m k u hn hm hf hanti hs using H
  have hsum : (∑ p, mass (u p))=1 := by
    simp_rw [hm]
    rw [mass_labelCut,hmass]
  have hsupport (p) (s : Spins (m p)) :
      ∀ᵐ x, SpatiallySupported ((u p).coreSlice s x).normalized {z | 3*a ≤ ‖z-y‖} := by
    filter_upwards [hs p s] with x hx
    exact hx.normalized
  have hclosed : IsClosed {z : Space | 3*a ≤ ‖z-y‖} := isClosed_le continuous_const (by fun_prop)
  have HG (p : Fin n → Fin 2) :
      a/(16*ballTrialCoefficient)*sliceExpectation (u p) (fun s x =>
        (max (coreScreenedField S ((u p).coreSlice s x).normalized y) 0)^2) ≤
      form S (u p)-conditionalOutCost S (u p)-E*mass (u p)+
        (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass (u p) := by
    have H := conditional_positive_field_gain S (u p) (hanti p) ha y _ hclosed
      (hsupport p) (fun _ h => h) hnuc hE
    rw [form_eq_conditionalOutCost S (u p)]
    linarith
  have HI : (∑ p, form S (u p)) ≤ E+δ+
      3*(radialCutCoefficient/(3*a))^2*expectedPopulation ψ (Metric.closedBall y (6*a)) := by
    simp_rw [hf]
    have H := form_radial_labelCut S ψ y hr
    dsimp [χ]
    have he : 2*(3*a)=6*a := by ring
    rw [he] at H
    exact H.trans (add_le_add hstate le_rfl)
  have HH := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => HG p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hsum,mul_one] at HH
  refine ⟨m,k,u,hn,hsum,hanti,hsupport,?_⟩
  linarith

end Coulomb
end

end
end

end OAI
