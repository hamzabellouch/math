import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FreshFieldTransfer
import OAI.Analysis.CoulombRadii.FieldAnalysis.FreshMeanBounds

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma patch_TF_center_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j,20*a≤‖S.position j-y‖) :
    patchTFScreenedField S u ha hb ht.2 y hn y≤tfInteriorConstant thomasFermiKineticConstant/a^4 := by
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)), W x≤totalCharge S/a := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    rw [hx]
    apply (sub_le_self _ (coreCoulombPotential_nonneg u x)).trans
    exact attraction_le_totalCharge_div S ha x (fun j => patch_nucleus_separation S ha hb ht.2 y hn j x hy)
  exact tfScreened_three_quarters measurableSet_ball thomasFermiKineticConstant_pos
    (div_nonneg (totalCharge_nonneg S) ha.le) W hW
    (localTFMinimizer_nonneg measurableSet_ball W) (fun f hf => localTFMinimizer_minimizes measurableSet_ball W hf)
    (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) ha (patch_inner_ball ha hb hsmall ht.1 y)
    (by simpa using (Metric.mem_closedBall_self (x:=y) (show 0≤3*a by positivity)))

theorem patch_field_mean_lower {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    {a b t q L : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space) (hn : ∀ j,20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hq : 0<q) (hL : 0≤L)
    (hneg : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*
      max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))
    (hgood : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      patchSliceTFGap S (T.vector p) ha hb ht.2 y hn s x≤q →
      L≤patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) :
    L*T.totalMass-(L/q)*(∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))-
      (∑ p,sliceExpectation (T.vector p) (fun s x =>
        max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))≤
      ∑ p,sliceExpectation (T.vector p) (fun s x =>
        patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) := by
  have hs (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun _ hx => hx.normalized)
  have H (p : T.index) (s : Spins (T.out p)) := NeutralAtom.weighted_field_mean_lower
    (mass_coreSlice_integrable (T.vector p) s) (Eventually.of_forall (fun _ => mass_nonneg _))
    (patchTFScreenedField_weight_integrable S (T.vector p) ha hb hsmall ht y hn ha le_rfl
      (by norm_num : (0:ℝ)<1) (hs p) s)
    (patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hs p s)) (hneg p s) hq hL
    (Eventually.of_forall (fun x => patchSliceTFGap_nonneg S (T.vector p) ha hb ht.2 y hn s x)) (hgood p s)
  have HP (p : T.index) := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => H p s)
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,integral_mass_coreSlice] at HP
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => HP p)
  simpa only [Finset.sum_sub_distrib,←Finset.mul_sum,RecordedEnsemble.totalMass,sliceExpectation] using HH

theorem patch_field_mean_upper {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    {a b t q U : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space) (hn : ∀ j,20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hq : 0<q) (hU : 0≤U)
    (hgood : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      patchSliceTFGap S (T.vector p) ha hb ht.2 y hn s x≤q →
      patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y≤U) :
    (∑ p,sliceExpectation (T.vector p) (fun s x =>
      patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y))≤
    U*T.totalMass+((tfInteriorConstant thomasFermiKineticConstant/a^4)/q)*
      (∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)) := by
  have hs (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun _ hx => hx.normalized)
  have H (p : T.index) (s : Spins (T.out p)) := NeutralAtom.weighted_field_mean_upper
    (mass_coreSlice_integrable (T.vector p) s) (Eventually.of_forall (fun _ => mass_nonneg _))
    (patchTFScreenedField_weight_integrable S (T.vector p) ha hb hsmall ht y hn ha le_rfl
      (by norm_num : (0:ℝ)<1) (hs p) s)
    (patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hs p s)) hq hU
    (div_nonneg (tfInteriorConstant_nonneg _) (pow_nonneg ha.le _))
    (Eventually.of_forall (fun x => patchSliceTFGap_nonneg S (T.vector p) ha hb ht.2 y hn s x))
    ((hs p s).mono (fun x hx _ => patch_TF_center_bound S _ ha hb hsmall ht y hx hn)) (hgood p s)
  have HP (p : T.index) := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => H p s)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,integral_mass_coreSlice] at HP
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => HP p)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,RecordedEnsemble.totalMass,sliceExpectation] using HH
end Coulomb
end

end

end OAI
