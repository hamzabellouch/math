import Mathlib
import OAI.Analysis.SymmetricDomains.ContinuousAutTransport

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
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {D : Set (Affine n)}

def translationAut (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (t : ℝ) : Biholomorph D D :=
  biholomorphOfAmbientInverse D D (fun x => x+t • v) (fun x => x+(-t) • v)
    (fun x _ => analyticAt_id.add analyticAt_const)
    (fun x _ => analyticAt_id.add analyticAt_const)
    (fun _ hx => (hD t _).mpr hx) (fun _ hx => (hD (-t) _).mpr hx)
    (by intro x _; simp [add_assoc]) (by intro x _; simp [add_assoc])

@[simp] theorem translationAut_apply (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (t : ℝ) (x : D) :
    ((translationAut v hD t).toHomeomorph x).val=x.val+t • v := rfl

@[simp] theorem translationAut_inv_apply (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (t : ℝ) (x : D) :
    ((translationAut v hD t).toHomeomorph.symm x).val=x.val+(-t) • v := rfl

@[simp] theorem translationAut_zero (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) : translationAut v hD 0=1 := by
  apply Biholomorph.ext
  intro x
  apply Subtype.ext
  simp only [translationAut_apply,zero_smul,add_zero,one_apply]

 theorem translationAut_add (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (s t : ℝ) :
    translationAut v hD (s+t)=translationAut v hD s*translationAut v hD t := by
  apply Biholomorph.ext
  intro x
  apply Subtype.ext
  simp only [translationAut_apply,mul_apply,add_smul]
  abel

 theorem continuous_translationAut (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) : Continuous (translationAut v hD) := by
  apply continuous_of_joint_evaluation
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).add (continuous_fst.smul continuous_const)
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).add
      (continuous_fst.neg.smul continuous_const)

def linearAut (L : Affine n ≃L[ℂ] Affine n) (hL : ∀ x, L x∈D ↔ x∈D) :
    Biholomorph D D :=
  biholomorphOfAmbientInverse D D L L.symm
    (fun x _ => L.toContinuousLinearMap.analyticAt x)
    (fun x _ => L.symm.toContinuousLinearMap.analyticAt x)
    (fun _ hx => (hL _).mpr hx)
    (fun _ hx => (hL _).mp (by simpa only [L.apply_symm_apply] using hx))
    (fun x _ => L.symm_apply_apply x) (fun x _ => L.apply_symm_apply x)

@[simp] theorem linearAut_apply (L : Affine n ≃L[ℂ] Affine n)
    (hL : ∀ x, L x∈D ↔ x∈D) (x : D) :
    ((linearAut L hL).toHomeomorph x).val=L x.val := rfl

@[simp] theorem linearAut_inv_apply (L : Affine n ≃L[ℂ] Affine n)
    (hL : ∀ x, L x∈D ↔ x∈D) (x : D) :
    ((linearAut L hL).toHomeomorph.symm x).val=L.symm x.val := rfl

 theorem linearAut_translation_conjugate (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D)
    (L : Affine n ≃L[ℂ] Affine n) (hL : ∀ x, L x∈D ↔ x∈D)
    (r : ℝ) (hv : L v=r • v) (t : ℝ) :
    linearAut L hL*translationAut v hD t*(linearAut L hL)⁻¹=
      translationAut v hD (r*t) := by
  apply Biholomorph.ext
  intro x
  apply Subtype.ext
  change L (L.symm x.val+t • v)=x.val+(r*t) • v
  have hs : L (t • v)=t • L v := (L.restrictScalars ℝ).map_smul t v
  rw [map_add,hs,L.apply_symm_apply,hv,smul_smul,mul_comm t r]

end Biholomorph
end Release061

open Filter Topology

theorem LinearMap.isNilpotent_of_positive_smul_conjugate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E)
    (hA : ∀ r : ℝ, 0 < r → ∃ e : E ≃ₗ[ℝ] E, e.conj A = r • A) :
    IsNilpotent A := by
  apply (LinearMap.isNilpotent_iff_charpoly A).2
  apply Polynomial.funext
  intro t
  let F : ℝ → ℝ := fun r =>
    (t • ContinuousLinearMap.id ℝ E-r • A.toContinuousLinearMap).det
  have hF : Continuous F := ContinuousLinearMap.continuous_det.comp
    (continuous_const.sub (continuous_id.smul continuous_const))
  have hpos (r : ℝ) (hr : 0<r) : F r=A.charpoly.eval t := by
    obtain ⟨e,he⟩ := hA r hr
    have hh := congrArg (Polynomial.eval t) (e.charpoly_conj A)
    rw [he,LinearMap.eval_charpoly] at hh
    exact hh
  have hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
    hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hconst : F =ᶠ[𝓝[>] (0 : ℝ)] fun _ => A.charpoly.eval t := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hpos r hr
  have hEq : F 0=A.charpoly.eval t := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' hconst.symm)
  rw [←hEq]
  simp [F,ContinuousLinearMap.det,LinearMap.det_smul]

theorem LinearMap.isNilpotent_of_positive_smul_conjugate_algebraic
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E)
    (hA : ∀ r : ℝ, 0 < r → ∃ e : E ≃ₗ[ℝ] E, e.conj A = r • A) :
    IsNilpotent A := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  let e := b.equivFun
  have h := LinearMap.isNilpotent_of_positive_smul_conjugate (e.conj A) (by
    intro r hr
    obtain ⟨g,hg⟩ := hA r hr
    refine ⟨(e.symm.trans g).trans e,?_⟩
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun T : E →ₗ[ℝ] E => e (T (e.symm x))) hg
    simpa [LinearEquiv.conj_apply,LinearEquiv.trans_apply] using hh)
  obtain ⟨N,hN⟩ := h
  have heq : e.conjRingEquiv A=e.conj A := by
    apply LinearMap.ext
    intro x
    rfl
  exact ⟨N,e.conjRingEquiv.injective (by simpa only [map_pow,map_zero,heq] using hN)⟩

theorem LieAlgebra.ad_isNilpotent_of_positive_dilations
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (X : L) (hX : ∀ r : ℝ, 0<r → ∃ e : L ≃ₗ⁅ℝ⁆ L, e X=r • X) :
    IsNilpotent (LieAlgebra.ad ℝ L X) := by
  apply LinearMap.isNilpotent_of_positive_smul_conjugate_algebraic
  intro r hr
  obtain ⟨e,he⟩ := hX r hr
  refine ⟨e.toLinearEquiv,?_⟩
  apply LinearMap.ext
  intro Y
  change e ⁅X,e.symm Y⁆ = r • ⁅X,Y⁆
  rw [e.map_lie,he,e.apply_symm_apply,smul_lie]

end

end OAI
