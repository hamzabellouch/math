import Mathlib
import OAI.Analysis.SymmetricDomains.OneParameterOneGenerator
import OAI.Analysis.SymmetricDomains.OneParameterGeneratorAdd

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

@[simp] theorem infinitesimalGenerator_of_not_mem (a : ℝ → Biholomorph U U)
    {x : Affine n} (hx : x∉U) : infinitesimalGenerator a x=0 := by
  simp [infinitesimalGenerator,ambientAut,ambientExtend,hx]

@[simp] theorem infinitesimalGenerator_one :
    infinitesimalGenerator (fun _ : ℝ => (1 : Biholomorph U U))=0 := by
  funext x
  exact deriv_const (0:ℝ) ((1 : Biholomorph U U).ambientAut x)

theorem infinitesimalGenerator_hasDerivAt (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (x : Affine n) :
    HasDerivAt (fun t => (a t).ambientAut x) (infinitesimalGenerator a x) 0 := by
  by_cases hx : x∈U
  · simpa only [ambientAut_apply (p := ⟨x,hx⟩)] using
      oneParameter_hasDerivAt_zero hU a ha hbd ha0 ham ⟨x,hx⟩
  · simpa only [infinitesimalGenerator_of_not_mem a hx,ambientAut,ambientExtend,dite_eq_right hx]
      using hasDerivAt_const (0:ℝ) (0 : Affine n)

theorem infinitesimalGenerator_time_smul (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (c : ℝ) :
    infinitesimalGenerator (fun t => a (c*t))=c • infinitesimalGenerator a := by
  funext x
  have hd := infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham x
  have htime : HasDerivAt (fun t : ℝ => c*t) c 0 := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (0:ℝ)).const_mul c
  have hd' : HasDerivAt (fun t => (a t).ambientAut x) (infinitesimalGenerator a x) (c*0) := by
    simpa only [mul_zero] using hd
  exact (hd'.scomp 0 htime).deriv

def IsCompleteGenerator (U : Set (Affine n)) (X : Affine n → Affine n) : Prop :=
  ∃ a : ℝ → Biholomorph U U, Continuous a ∧ a 0=1 ∧
    (∀ s t, a (s+t)=a s*a t) ∧ infinitesimalGenerator a=X

lemma IsCompleteGenerator.analyticOnNhd (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) {X : Affine n → Affine n} (hX : IsCompleteGenerator U X) :
    AnalyticOnNhd ℂ X U := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  exact infinitesimalGenerator_analytic hU a ha hbd ha0 ham

lemma IsCompleteGenerator.eq_zero_of_not_mem {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) {x : Affine n} (hx : x∉U) : X x=0 := by
  obtain ⟨a,_,_,_,rfl⟩ := hX
  exact infinitesimalGenerator_of_not_mem a hx

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def completeGeneratorSpace : Submodule ℝ (Affine n → Affine n) where
  carrier := {X | IsCompleteGenerator U X}
  zero_mem' := ⟨fun _ => 1,continuous_const,rfl,(by intro s t; simp),infinitesimalGenerator_one⟩
  add_mem' := by
    rintro X Y ⟨a,ha,ha0,ham,rfl⟩ ⟨b,hb,hb0,hbm,rfl⟩
    obtain ⟨H,hH0,hHc,hHm,hHX⟩ := exists_oneParameter_generator_add hU hc hbd Γ hhol a b ha hb ha0 ham hb0 hbm
    refine ⟨H,hHc,hH0,hHm,funext fun x => ?_⟩
    by_cases hx : x∈U
    · exact hHX x hx
    · simp only [Pi.add_apply,infinitesimalGenerator_of_not_mem _ hx,add_zero]
  smul_mem' := by
    rintro c X ⟨a,ha,ha0,ham,rfl⟩
    refine ⟨fun t => a (c*t),ha.comp (continuous_const.mul continuous_id),by simpa using ha0,?_,
      infinitesimalGenerator_time_smul hU hbd a ha ha0 ham c⟩
    intro s t
    dsimp only
    rw [mul_add,ham]

def completeGeneratorFirstJet (p : U) : completeGeneratorSpace hU hc hbd Γ hhol →ₗ[ℝ]
    Affine n × (Affine n →L[ℂ] Affine n) where
  toFun X := (X.val p.val,fderiv ℂ X.val p.val)
  map_add' X Y := by
    change (X.val p.val+Y.val p.val,fderiv ℂ (X.val+Y.val) p.val)=
      (X.val p.val+Y.val p.val,fderiv ℂ X.val p.val+fderiv ℂ Y.val p.val)
    rw [fderiv_add ((X.property.analyticOnNhd hU hbd) p.val p.property).differentiableAt
      ((Y.property.analyticOnNhd hU hbd) p.val p.property).differentiableAt]
  map_smul' c X := by
    change (c • X.val p.val,fderiv ℂ (c • X.val) p.val)=
      (c • X.val p.val,c • fderiv ℂ X.val p.val)
    rw [fderiv_const_smul ((X.property.analyticOnNhd hU hbd) p.val p.property).differentiableAt]

theorem completeGeneratorFirstJet_injective (p : U) :
    Function.Injective (completeGeneratorFirstJet hU hc hbd Γ hhol p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  obtain ⟨a,ha,ha0,ham,heq⟩ := X.property
  have hvalue : infinitesimalGenerator a p.val=0 := by
    have h := congrArg Prod.fst hX
    change X.val p.val=0 at h
    rwa [heq]
  have hderiv : fderiv ℂ (infinitesimalGenerator a) p.val=0 := by
    have h := congrArg Prod.snd hX
    change fderiv ℂ X.val p.val=0 at h
    rwa [heq]
  have haone : a=(fun _ => 1) := funext fun t => oneParameter_eq_one_of_generator_zero_jet
    hU a ha hc.isPreconnected hbd ha0 ham p hvalue hderiv t
  apply Subtype.ext
  change X.val=0
  rw [← heq,haone,infinitesimalGenerator_one]

theorem finiteDimensional_completeGeneratorSpace :
    FiniteDimensional ℝ (completeGeneratorSpace hU hc hbd Γ hhol) := by
  obtain ⟨p,hp⟩ := hc.nonempty
  exact FiniteDimensional.of_injective (completeGeneratorFirstJet hU hc hbd Γ hhol ⟨p,hp⟩)
    (completeGeneratorFirstJet_injective hU hc hbd Γ hhol ⟨p,hp⟩)

end Biholomorph
end Release061

end

end OAI
