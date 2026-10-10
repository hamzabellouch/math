import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CoveredOutCost
import OAI.Analysis.CoulombRadii.Screening.PatchComparison

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma tfInteriorCountConstant_nonneg : 0≤tfInteriorCountConstant := by
  unfold tfInteriorCountConstant
  positivity [tfInteriorConstant_nonneg thomasFermiKineticConstant,thomasFermiKineticConstant_pos,Real.pi_pos]

lemma patch_retained_nucleus_separated {J n : ℕ} (S : Nuclei J) {a b t : ℝ}
    (_ : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (x : Configuration n) :
    ∀ j i, i∈patchRetained y t b x → Real.sqrt 3*b≤‖S.position j-position x i‖ := by
  intro j i hi
  have hret := (patchRetained_mem ..).mp hi
  have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) (position x i) y
  have hs : Real.sqrt 3≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  nlinarith [hn j]

lemma patchFineTF_weight_integrable {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t≤6*a)
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (ψ.coreSlice s x)*rawThomasFermiEnergy
      (coreScreenedField S (ψ.coreSlice s x).normalized)
      (retainedFineDensity b (patchRetained y t b x) (position x))) := by
  apply (discreteFineTF_weight_integrable S ψ hb (patchRetained y t b) (patchRetained_measurable y t b) s).congr
  filter_upwards [hcs] with x hx
  congr 1
  exact discreteFineTF_eq_raw S ψ hb (patchRetained y t b) s x hx
    (patch_retained_nucleus_separated S ha hb hsmall ht y hn x)
    (patch_retained_separated ha hb y x)

lemma physical_patch_count_gap {J n k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t F : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hu : SpatiallySupported u {z | t≤‖z-y‖})
    (hF : 0≤F) (hcap : ∀ w∈Metric.ball y (t-4*b), coreScreenedField S u w≤F)
    (x : Configuration n) :
    let ρ := localTFDensity measurableSet_ball
      (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (localCount (Metric.closedBall y a) x)^2 ≤
      2*(tfInteriorCountConstant/a^3)^2+6*a*(max countTestEnergy 0)*
      (rawThomasFermiEnergy (coreScreenedField S u) (retainedFineDensity b (patchRetained y t b x) (position x))-
        rawThomasFermiEnergy (coreScreenedField S u) ρ) := by
  dsimp only
  have Hcount := localCount_le_fine_test (t := t) ha hb (by linarith) (by linarith [ht.1]) y x
  have Hgap := rawTF_count_test measurableSet_ball (coreScreenedField S u)
    (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (retainedFineDensity_memLp hb (patchRetained y t b x) (position x))
    (Eventually.of_forall (retainedFineDensity_nonneg b (patchRetained y t b x) (position x)))
    (retainedFineDensity_patch_support hb y t x) y (show 0<3*a/2 by positivity)
    (show Metric.closedBall y (2*(3*a/2))⊆Metric.ball y (t-4*b) from
      (Metric.closedBall_subset_closedBall (by linarith)).trans (patch_inner_ball ha hb hsmall ht.1 y))
  have HT := patch_TF_test_bound S u ha hb hsmall ht y hu hn hF hcap
  have hp : 0≤∫ z, localTFDensity measurableSet_ball
      (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)) z*countTest y (3*a/2) z :=
    integral_nonneg (fun z => mul_nonneg (tfDensity_nonneg _ z) (countTest_nonneg ..))
  have Ht2 := pow_le_pow_left₀ hp HT 2
  have Hc2 := pow_le_pow_left₀ (localCount_nonneg _ _) Hcount 2
  nlinarith only [Hgap,Ht2,Hc2]

lemma sliceExpectation_le_affine {m k : ℕ} (ψ : H1Vector (m+k))
    (H G : Spins m → Configuration m → ℝ) (A B : ℝ)
    (hH : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*H s x))
    (hG : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*G s x))
    (hbound : ∀ s, ∀ᵐ x, H s x≤A+B*G s x) :
    sliceExpectation ψ H≤A*mass ψ+B*sliceExpectation ψ G := by
  rw [←sliceExpectation_number ψ A]
  unfold sliceExpectation
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul,←integral_add ((mass_coreSlice_integrable ψ s).mul_const A) ((hG s).const_mul B)]
  apply integral_mono_ae (hH s) (((mass_coreSlice_integrable ψ s).mul_const A).add ((hG s).const_mul B))
  filter_upwards [hbound s] with x hx
  convert mul_le_mul_of_nonneg_left hx (mass_nonneg (ψ.coreSlice s x)) using 1
  dsimp only [Pi.add_apply]
  ring

section Averaged
variable {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized {z | t≤‖z-y‖})
    (F : Spins m → Configuration m → ℝ)
    (hF0 : ∀ s, ∀ᵐ x, 0≤F s x)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x)^2))
    (hcap : ∀ s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x)

include hsmall hcs F hF0 hFi hcap in
lemma physical_patch_averaged_count :
    let ρ := fun s x => localTFDensity measurableSet_ball
      (coreTFField S (ψ.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn))
    sliceExpectation ψ (fun _ x => (localCount (Metric.closedBall y a) x)^2)≤
      2*(tfInteriorCountConstant/a^3)^2*mass ψ+6*a*(max countTestEnergy 0)*
      sliceExpectation ψ (fun s x =>
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
          (retainedFineDensity b (patchRetained y t b x) (position x))-
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) := by
  dsimp only
  have hcap' (s : Spins m) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x := by
    filter_upwards [hcap s] with x hx
    exact fun w hw => hx w (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw)
  apply sliceExpectation_le_affine
  · exact fun s => sliceCount_weight_integrable ψ measurableSet_closedBall s 2
  · intro s
    have hTF := coreTF_conditional_integrable measurableSet_ball S ψ s ha
      (patch_nucleus_separation S ha hb ht.2 y hn) (show 0<12*a by positivity)
      (patch_diameter ha hb ht.2 y) (F s) (hF0 s) (hFi s) (hcap' s)
    apply ((patchFineTF_weight_integrable S ψ ha hb hsmall ht.2 y hn s (hcs s)).sub hTF.2).congr
    exact Eventually.of_forall (fun x => (mul_sub ..).symm)
  · intro s
    filter_upwards [hcs s,hF0 s,hcap' s] with x hc hf hcap
    exact physical_patch_count_gap S _ ha hb hsmall ht y hn hc hf hcap x

end Averaged

end Coulomb
end

end
end

end OAI
