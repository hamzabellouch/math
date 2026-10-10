import Mathlib
import OAI.Analysis.SymmetricDomains.AdNilpotentPositiveDilations
import OAI.Analysis.SymmetricDomains.CoordinateFieldApply

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
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

section
open scoped Classical
variable {n : ℕ} {D : Set (Affine n)}

 theorem infinitesimalGenerator_translationAut (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v∈D ↔ x∈D) :
    infinitesimalGenerator (translationAut v hD)=D.indicator (fun _ => v) := by
  funext x
  by_cases hx : x∈D
  · have hh : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x using 1 <;> first | rfl | exact (one_smul ℝ v).symm
    change deriv (fun t => (translationAut v hD t).ambientAut x) 0=_
    have he : (fun t => (translationAut v hD t).ambientAut x)=fun t => x+t • v := by
      funext t
      rw [ambientAut_apply _ ⟨x,hx⟩,translationAut_apply]
    rw [he,hh.deriv,Set.indicator_of_mem hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,Set.indicator_of_notMem hx]

 theorem transported_translation_generator_in_model {m : ℕ} {U : Set (Affine m)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hbd : Bornology.IsBounded U)
    [LocallyCompactSpace D] (e : Biholomorph D U)
    (v : Affine n) (hD : ∀ t : ℝ, ∀ x, x+t • v∈D ↔ x∈D) :
    coordinateField e.symm
      (infinitesimalGenerator (fun t => autTransport e (translationAut v hD t)))=
      D.indicator (fun _ => v) := by
  let b : ℝ → Biholomorph U U := fun t => autTransport e (translationAut v hD t)
  have hb : Continuous b := (continuous_autTransport e).comp (continuous_translationAut v hD)
  have hb0 : b 0=1 := by simp [b]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t; simp only [b,translationAut_add,autTransport_mul]
  rw [←infinitesimalGenerator_autTransport hU hbd e.symm b hb hb0 hbm]
  have he : (fun t => autTransport e.symm (b t))=translationAut v hD := by
    funext t
    exact autTransport_symm_cancel e (translationAut v hD t)
  rw [he,infinitesimalGenerator_translationAut]

theorem lieBracket_indicator_const (hD : IsOpen D) (v : Affine n)
    (Y : Affine n → Affine n) {x : Affine n} (hx : x∈D) :
    VectorField.lieBracket ℂ (D.indicator (fun _ => v)) Y x=(fderiv ℂ Y x) v := by
  have he : D.indicator (fun _ : Affine n => v) =ᶠ[𝓝 x] fun _ => v := by
    filter_upwards [hD.mem_nhds hx] with z hz
    exact Set.indicator_of_mem hz _
  rw [VectorField.lieBracket,he.fderiv_eq,Set.indicator_of_mem hx]
  rw [fderiv_const_apply,zero_apply,sub_zero]

end

open scoped Classical
variable {n m : ℕ} {D : Set (Affine n)} {U : Set (Affine m)}

 theorem infinitesimalGenerator_eq_indicator_of_hasDerivAt
    (a : ℝ → Biholomorph D D) (V : Affine n → Affine n)
    (hd : ∀ x : D, HasDerivAt (fun t => (a t).toHomeomorph x |>.val) (V x.val) 0) :
    infinitesimalGenerator a=D.indicator V := by
  funext x
  by_cases hx : x∈D
  · change deriv (fun t => (a t).ambientAut x) 0=_
    have he : (fun t => (a t).ambientAut x)=fun t => ((a t).toHomeomorph ⟨x,hx⟩).val := by
      funext t; exact ambientAut_apply _ ⟨x,hx⟩
    rw [he,(hd ⟨x,hx⟩).deriv,Set.indicator_of_mem hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,Set.indicator_of_notMem hx]

 theorem exists_complete_generator_in_model
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace D] (e : Biholomorph D U)
    (a : ℝ → Biholomorph D D) (ha : Continuous a) (ha0 : a 0=1)
    (ham : ∀ s t, a (s+t)=a s*a t) (V : Affine n → Affine n)
    (hd : ∀ x : D, HasDerivAt (fun t => ((a t).toHomeomorph x).val) (V x.val) 0) :
    ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm X.val=D.indicator V := by
  let b : ℝ → Biholomorph U U := fun t => autTransport e (a t)
  have hb : Continuous b := (continuous_autTransport e).comp ha
  have hb0 : b 0=1 := by simp [b,ha0]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t; simp only [b,ham,autTransport_mul]
  refine ⟨⟨infinitesimalGenerator b,⟨b,hb,hb0,hbm,rfl⟩⟩,?_⟩
  rw [←infinitesimalGenerator_autTransport hU hbd e.symm b hb hb0 hbm]
  have he : (fun t => autTransport e.symm (b t))=a := by
    funext t; exact autTransport_symm_cancel e (a t)
  rw [he]
  exact infinitesimalGenerator_eq_indicator_of_hasDerivAt a V hd

 theorem exists_complete_linear_generator_in_model
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace D] (e : Biholomorph D U)
    (L : ℝ → Affine n ≃L[ℂ] Affine n)
    (hL : ∀ t x, L t x∈D ↔ x∈D)
    (h0 : ∀ x, L 0 x=x) (hm : ∀ s t x, L (s+t) x=L s (L t x))
    (hcont : Continuous (fun p : ℝ × Affine n => L p.1 p.2))
    (A : Affine n →L[ℂ] Affine n)
    (hd : ∀ x, HasDerivAt (fun t => L t x) (A x) 0) :
    ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm X.val=D.indicator A := by
  let a : ℝ → Biholomorph D D := fun t => linearAut (L t) (hL t)
  have ha : Continuous a := by
    apply continuous_of_joint_evaluation
    · apply Continuous.subtype_mk
      exact hcont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    · have hi : ∀ t x, (L t).symm x=L (-t) x := by
        intro t x
        apply (L t).injective
        rw [(L t).apply_symm_apply,←hm,add_neg_cancel,h0]
      apply Continuous.subtype_mk
      change Continuous (fun p : ℝ × D => (L p.1).symm p.2.val)
      simp_rw [hi]
      exact hcont.comp (continuous_fst.neg.prodMk (continuous_subtype_val.comp continuous_snd))
  apply exists_complete_generator_in_model hU hc hbd Γ hhol e a ha
  · apply Biholomorph.ext
    intro x
    apply Subtype.ext
    exact h0 x.val
  · intro s t
    apply Biholomorph.ext
    intro x
    apply Subtype.ext
    exact hm s t x.val
  · intro x
    exact hd x.val

end Biholomorph
end Release061

end

end OAI
