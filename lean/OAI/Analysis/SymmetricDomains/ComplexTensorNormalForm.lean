import Mathlib
import OAI.Analysis.SymmetricDomains.CommutingGeneratorsValueZero
import OAI.Analysis.SymmetricDomains.IsotropyCompleteGeneratorsTotally

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
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
open Set Filter Topology
open scoped Classical
variable {n : ℕ}

theorem bracket_zero_firstJet_of_zero_secondJet
    {Z W : Affine n → Affine n} {p : Affine n}
    (hZ : AnalyticAt ℂ Z p) (hW : AnalyticAt ℂ W p)
    (hz0 : Z p=0) (hz1 : fderiv ℂ Z p=0)
    (hz2 : fderiv ℂ (fderiv ℂ Z) p=0) :
    VectorField.lieBracket ℂ Z W p=0 ∧ fderiv ℂ (VectorField.lieBracket ℂ Z W) p=0 := by
  refine ⟨?_,?_⟩
  · simp only [VectorField.lieBracket,hz0,hz1,map_zero,zero_apply,sub_zero]
  · have hA := hW.fderiv.differentiableAt.hasFDerivAt.clm_apply hZ.differentiableAt.hasFDerivAt
    have hB := hZ.fderiv.differentiableAt.hasFDerivAt.clm_apply hW.differentiableAt.hasFDerivAt
    have hder := hA.sub hB
    change fderiv ℂ ((fun y => (fderiv ℂ W y) (Z y)) - fun y => (fderiv ℂ Z y) (W y)) p=0
    rw [hder.fderiv]
    simp [hz0,hz1,hz2]

 theorem eq_I_smul_of_add_I_smul_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    {x y : E} (h : x+Complex.I • y=0) : y=Complex.I • x := by
  have hh := congrArg (fun v => Complex.I • v) h
  simp only [smul_add,smul_smul,Complex.I_mul_I,neg_one_smul,smul_zero] at hh
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)).symm

namespace Biholomorph
variable {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem complex_complete_generators_secondJet_zero
    {X Y : Affine n → Affine n} (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y)
    (p : U) (hz0 : (X+Complex.I • Y) p.val=0)
    (hz1 : fderiv ℂ (X+Complex.I • Y) p.val=0)
    (hz2 : fderiv ℂ (fderiv ℂ (X+Complex.I • Y)) p.val=0) : X=0 ∧ Y=0 := by
  have haX := hX.analyticOnNhd hU hbd
  have haY := hY.analyticOnNhd hU hbd
  have haZ : AnalyticOnNhd ℂ (X+Complex.I • Y) U := fun x hx =>
    (haX x hx).add ((haY x hx).const_smul)
  have hbe : VectorField.lieBracket ℂ (X+Complex.I • Y) Y =ᶠ[𝓝 p.val]
      VectorField.lieBracket ℂ X Y := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    rw [VectorField.lieBracket_add_left (haX x hx).differentiableAt
      ((haY x hx).differentiableAt.const_smul Complex.I),
      VectorField.lieBracket_const_smul_left (haY x hx).differentiableAt,
      VectorField.lieBracket_self,Pi.zero_apply,smul_zero,add_zero]
  obtain ⟨hbrp0,hbrp1⟩ := bracket_zero_firstJet_of_zero_secondJet (haZ p.val p.property)
    (haY p.val p.property) hz0 hz1 hz2
  rw [hbe.eq_of_nhds] at hbrp0
  rw [hbe.fderiv_eq] at hbrp1
  have hbr : VectorField.lieBracket ℂ X Y=0 :=
    (hX.lieBracket hU hc hbd Γ hhol hY).eq_zero_of_zero_jet hU hc hbd p hbrp0 hbrp1
  have hvalrel : Y p.val=Complex.I • X p.val := eq_I_smul_of_add_I_smul_eq_zero hz0
  have hderrel : fderiv ℂ Y p.val=Complex.I • fderiv ℂ X p.val := by
    rw [fderiv_add (haX p.val p.property).differentiableAt
      ((haY p.val p.property).differentiableAt.const_smul Complex.I),
      fderiv_const_smul (haY p.val p.property).differentiableAt] at hz1
    exact eq_I_smul_of_add_I_smul_eq_zero hz1
  have hXp : X p.val=0 := by
    obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
    obtain ⟨b,hb,hb0,hbm,rfl⟩ := hY
    apply commuting_generators_value_zero hU hbd a b ha hb ha0 ham hb0 hbm _ p hvalrel
    funext x
    rw [VectorField.lieBracket_swap,hbr,Pi.zero_apply,neg_zero]
  have hYp : Y p.val=0 := by rw [hvalrel,hXp,smul_zero]
  have hx := isotropy_complete_generators_totally_real hU hc hbd Γ hhol hX hY p hXp hYp hderrel
  refine ⟨hx,hY.eq_zero_of_zero_jet hU hc hbd p hYp ?_⟩
  rw [hderrel,hx,fderiv_zero]
  change Complex.I • (0 : Affine n →L[ℂ] Affine n)=0
  exact smul_zero (A := Affine n →L[ℂ] Affine n) Complex.I
end Biholomorph
end Release061

open scoped TensorProduct
open Set Filter Topology

theorem complex_tensor_normalForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Z : ℂ ⊗[ℝ] V) : ∃ X Y : V, Z=1 ⊗ₜ[ℝ] X+Complex.I ⊗ₜ[ℝ] Y := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    refine ⟨z.re • X,z.im • X,?_⟩
    rw [TensorProduct.tmul_smul,TensorProduct.tmul_smul,TensorProduct.smul_tmul',TensorProduct.smul_tmul',←TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp [Complex.real_smul]
  | add Z W hZ hW =>
    obtain ⟨X,Y,rfl⟩ := hZ
    obtain ⟨X',Y',rfl⟩ := hW
    exact ⟨X+X',Y+Y',by simp only [TensorProduct.tmul_add]; abel⟩

end

end OAI
