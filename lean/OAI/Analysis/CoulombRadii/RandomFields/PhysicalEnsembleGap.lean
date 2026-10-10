import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.PhysicalEnsemble

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

theorem physical_ensemble_gap {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (T : RecordedEnsemble n) (_ : T.Conserves ψ) (hc : T.CoreFermionic) (ho : T.OutFermionic)
    (hm : T.totalMass=1) {E B : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (henergy : T.totalForm S≤E+B)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hos : T.OutSupported (Metric.closedBall y (t+b)))
    (F : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ)
    (hFm : ∀ p s, AEStronglyMeasurable (F p s) volume)
    (hF0 : ∀ p s, ∀ᵐ x, 0≤F p s x)
    (hFi : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x)^2))
    (hcap : ∀ p s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x) :
    let Q := ∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2)
    let N := ∑ p, (T.out p:ℝ)^2*mass (T.vector p)
    let ρ := fun p s x => localTFDensity measurableSet_ball
      (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn))
    (∑ p, sliceExpectation (T.vector p) (fun s x =>
      rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized)
        (retainedFineDensity b (patchRetained y t b x) (position x))-
      rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized) (ρ p s x))) ≤
    B+12*a*unitWindowKinetic/b^2*Real.sqrt Q+Real.sqrt (Q*T.deletedSquare y t b)+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*N^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt N := by
  dsimp only
  let ρ := fun p s x => localTFDensity measurableSet_ball
    (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn))
  let G := fun p s x => rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized)
    (retainedFineDensity b (patchRetained y t b x) (position x))-
    rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized) (ρ p s x)
  have hcs' (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} := by
    filter_upwards [(hcs p).coreSlice s] with x hx
    exact hx.normalized
  have hcap' (p : T.index) (s) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x := by
    filter_upwards [hcap p s] with x hx
    exact fun w hw => hx w (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw)
  have hgap (p : T.index) := physical_patch_comparison S (T.vector p) (ho p).outer_symmetry
    (fun s => (hc p).coreSlice s) ha hb hsmall ht y hn (hcs' p) (fun s => (hos p).recorded_positions s)
    (F p) (hFm p) (hF0 p) (hFi p) (hcap p) hE
  have hpacket (p : T.index) := patch_packet_expected_bound S (T.vector p) ha hb ht.2 y hn
    (F p) (hFm p) (hF0 p) (hFi p) (hcap' p)
  have hmean := slice_ensemble_mean_le_sqrt T.out T.core T.vector F hFm hF0 hFi hm
  have hdel := slice_ensemble_mul_le_sqrt T.out T.core T.vector F
    (fun _ _ x => localCount {z | t-7*b≤‖z-y‖} x) hFi
    (fun p s => sliceCount_weight_integrable (T.vector p) (isClosed_le continuous_const (by fun_prop)).measurableSet s 2)
    (fun p s => weighted_cap_count_integrable (mass_coreSlice_integrable (T.vector p) s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm p s) (hF0 p s) (hFi p s)
      (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
      (Nat.cast_nonneg (T.out p)) (Eventually.of_forall (fun x => ⟨localCount_nonneg _ x,localCount_le _ x⟩)))
  have hfine := ensemble_fineLocalizationError T.out (fun p => mass (T.vector p)) (fun p => mass_nonneg _) hm hb
  have hsumgap := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hgap p)
  have hsumpacket := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hpacket p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hsumgap hsumpacket
  change (∑ p, sliceExpectation (T.vector p) (G p))≤_ at hsumgap
  have hGapBound : (∑ p, sliceExpectation (T.vector p) (G p))≤B+
      12*a*unitWindowKinetic/b^2*Real.sqrt (∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))+
      Real.sqrt ((∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))*T.deletedSquare y t b)+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (∑ p, (T.out p:ℝ)^2*mass (T.vector p)) := by
    have hp := mul_le_mul_of_nonneg_left hmean (show 0≤12*a*unitWindowKinetic/b^2 by exact div_nonneg (mul_nonneg (by positivity) unitWindowKinetic_nonneg) (sq_nonneg _))
    change (∑ p, mass (T.vector p))=1 at hm
    rw [hm,mul_one] at hsumgap
    change (∑ p, form S (T.vector p))≤E+B at henergy
    unfold RecordedEnsemble.deletedSquare
    linarith
  exact hGapBound
end Coulomb
end

end
end

end OAI
