import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.EnsembleCauchy
import OAI.Analysis.CoulombRadii.Screening.PatchComparison

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
namespace Coulomb

def unitWindowKinetic : ℝ := ∑ j : Fin 3, ∫ z : Space, (fderiv ℝ unitWindow z (EuclideanSpace.single j 1))^2
lemma unitWindowKinetic_nonneg : 0≤unitWindowKinetic := unitWindow_kinetic_nonneg

lemma patch_packet_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t F : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hF : 0≤F)
    (hcap : ∀ w∈Metric.ball y (t-4*b), coreScreenedField S u w≤F) :
    packetKineticError (scaledWindow unitWindow b hb.ne')
      (localTFDensity measurableSet_ball (coreTFField S u measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn))) ≤ 12*a*unitWindowKinetic/b^2*F := by
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)),
      coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn) x≤F := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    exact hx ▸ hcap x hy
  have HM := (localTFMass_bound measurableSet_ball (show 0<12*a by positivity) hF (patch_diameter ha hb ht y)
    (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)) hW).2
  unfold packetKineticError
  rw [scaledWindow_kinetic unitWindow hb]
  have H := mul_le_mul_of_nonneg_right HM (show 0≤(1/2:ℝ)*(unitWindowKinetic/b^2) by positivity [unitWindowKinetic_nonneg])
  change (1/2:ℝ)*_*(unitWindowKinetic/b^2) ≤ _
  calc
    _ = _*(1/2*(unitWindowKinetic/b^2)) := by ring
    _ ≤ _ := H
    _ = _ := by ring

lemma weighted_cap_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w F : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hF : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ x ∂μ, 0≤F x)
    (hFi : Integrable (fun x => w x*(F x)^2) μ) : Integrable (fun x => w x*F x) μ := by
  simpa only [mul_one] using weighted_cap_count_integrable hw hw0 hF hF0 hFi
    (aestronglyMeasurable_const (b := (1:ℝ))) zero_le_one (Eventually.of_forall (fun _ => ⟨zero_le_one,le_rfl⟩))

lemma slice_ensemble_mean_le_sqrt {P : Type*} [Fintype P] (m k : P → ℕ)
    (u : (p : P) → H1Vector (m p+k p))
    (F : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hFm : ∀ p s, AEStronglyMeasurable (F p s) volume)
    (hF0 : ∀ p s, ∀ᵐ x, 0≤F p s x)
    (hFi : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2))
    (hm : (∑ p, mass (u p))=1) :
    (∑ p, sliceExpectation (u p) (F p))≤Real.sqrt
      (∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)) := by
  have H := slice_ensemble_mul_le_sqrt m k u F (fun _ _ _ => 1) hFi
    (fun p s => by simpa only [one_pow,mul_one] using mass_coreSlice_integrable (u p) s)
    (fun p s => by
      simpa only [mul_one] using (weighted_cap_integrable (mass_coreSlice_integrable (u p) s)
        (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm p s) (hF0 p s) (hFi p s)))
  simpa only [mul_one,one_pow,sliceExpectation_number,one_mul,hm] using H

lemma ensemble_number_rpow {P : Type*} [Fintype P] (n : P → ℕ) (w : P → ℝ)
    (hw : ∀ p, 0≤w p) (hm : ∑ p, w p=1) :
    (∑ p, (n p:ℝ)^(4/3:ℝ)*w p) ≤ (∑ p, (n p:ℝ)^2*w p)^(2/3:ℝ) := by
  have H := (Real.concaveOn_rpow (by norm_num : (0:ℝ)≤2/3) (by norm_num : (2/3:ℝ)≤1)).le_map_sum
    (t := Finset.univ) (w := w) (p := fun p => (n p:ℝ)^2)
    (fun p _ => hw p) hm (fun p _ => by change 0 ≤ (n p:ℝ)^2; positivity)
  simp only [smul_eq_mul] at H
  have he (p : P) : ((n p:ℝ)^2)^(2/3:ℝ)=(n p:ℝ)^(4/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp only [he] at H
  simpa only [mul_comm] using H

lemma ensemble_number_mean {P : Type*} [Fintype P] (n : P → ℕ) (w : P → ℝ)
    (hw : ∀ p, 0≤w p) (hm : ∑ p, w p=1) :
    (∑ p, (n p:ℝ)*w p) ≤ Real.sqrt (∑ p, (n p:ℝ)^2*w p) := by
  apply Real.le_sqrt_of_sq_le
  have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p => (n p:ℝ)*Real.sqrt (w p)) (fun p => Real.sqrt (w p))
  simp only [mul_pow,Real.sq_sqrt (hw _)] at H
  have he : ∑ p, ↑(n p)*Real.sqrt (w p)*Real.sqrt (w p)=∑ p, ↑(n p)*w p :=
    Finset.sum_congr rfl (fun p _ => by rw [mul_assoc,←sq,Real.sq_sqrt (hw p)])
  rw [he,hm,mul_one] at H
  exact H

end Coulomb
end

end
end

end OAI
