import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CorePointMeasurable
import OAI.Analysis.CoulombRadii.Variational.WeightedNegative

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

theorem exists_patch_negative_mean_bound :
    ∃ C : ℝ, 0<C ∧ ∀ {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 0≤r → r≤a → C*(r/a)≤1/2 →
    ∀ (χ : Space → ℝ) (K M : ℝ), 0≤K → 0<M → Measurable χ →
    (∀ z, 0≤χ z ∧ χ z≤K) → (∀ z, χ z≠0 → ‖z-y‖≤r) →
    (∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      M≤∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*χ z) →
    (∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*
      max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0)) ∧
    (∑ p, sliceExpectation (T.vector p) (fun s x =>
      max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))≤
      (2*K/M)*(∑ p, sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      (2*(C*(r/a))*(a^4)⁻¹)*T.totalMass := by
  obtain ⟨C,hC,H⟩ := exists_patch_negative_center_bound
  refine ⟨C,hC,?_⟩
  intro J n S T a b t r ha hb hsmall ht y hn hcs hr hra hθ χ K M hK hM hχm hχ hs hmass
  let Y := fun p s x => max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0
  let G := fun p s x => patchSliceTFGap S (T.vector p) ha hb ht.2 y hn s x
  let A := 2*K/M
  let d := 2*(C*(r/a))*(a^4)⁻¹
  have hcs' (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun _ hx => hx.normalized)
  have hGi (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x)*G p s x) :=
    patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hcs' p s)
  have hYm (p : T.index) (s : Spins (T.out p)) : AEStronglyMeasurable (Y p s) volume :=
    (patchTFScreenedField_slice_aestronglyMeasurable S (T.vector p) s ha hb ht.2 y hn y).neg.sup aestronglyMeasurable_const
  have hY0 (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x, 0≤Y p s x :=
    Eventually.of_forall (fun _ => le_max_right _ _)
  have hbound (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      mass ((T.vector p).coreSlice s x)≠0 → Y p s x≤A*G p s x+d := by
    filter_upwards [hcs' p s,hmass p s] with x hx hm
    intro hw
    apply H S ((T.vector p).coreSlice s x).normalized ha hb hsmall ht y hx hn hr hra hθ x χ K M hK hM
      (Eventually.of_forall hχ) _ hs (hm hw)
    exact (retainedFineDensity_integrable hb _ _).mul_bdd hχm.aestronglyMeasurable
      (Eventually.of_forall (fun z => by rw [Real.norm_of_nonneg (hχ z).1]; exact (hχ z).2))
  have hYi (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x)*Y p s x) :=
    NeutralAtom.weighted_nonneg_integrable_of_le (mass_coreSlice_integrable (T.vector p) s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hYm p s) (hY0 p s) (hGi p s) (hbound p s)
  refine ⟨hYi,?_⟩
  have hmean (p : T.index) : sliceExpectation (T.vector p) (Y p)≤
      A*sliceExpectation (T.vector p) (G p)+d*mass (T.vector p) := by
    have HH := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
      NeutralAtom.weighted_integral_le (mass_coreSlice_integrable (T.vector p) s)
        (Eventually.of_forall (fun _ => mass_nonneg _)) (hYm p s) (hY0 p s) (hGi p s) (hbound p s))
    simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_mass_coreSlice,sliceExpectation] using HH
  have HH := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hmean p)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,RecordedEnsemble.totalMass,Y,G,A,d] using HH

end Coulomb
end

end
end

end OAI
