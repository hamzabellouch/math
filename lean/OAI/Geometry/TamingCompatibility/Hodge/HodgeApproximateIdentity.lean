import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.FirstJetGauge
import OAI.Geometry.TamingCompatibility.HeatFlow.FlatHeat
import OAI.Geometry.TamingCompatibility.Elliptic.OperatorCalculus

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open MeasureTheory Set Filter Bornology
open scoped Topology

lemma heat_decay : Tendsto (fun z : V => ‖z‖^4 * heat 1 z) (cobounded V) (𝓝 0) := by
  have hsq : Tendsto (fun z : V => ‖z‖^2) (cobounded V) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1/4) (by norm_num)).comp hsq
  have h' := h.const_mul ((4*Real.pi)⁻¹^2)
  simp only [mul_zero] at h'
  convert h' using 1
  funext z
  simp only [Function.comp_apply,Real.rpow_ofNat,heat,mul_one]
  rw [show -(1/4 : ℝ)*‖z‖^2 = -‖z‖^2/4 by ring]
  ring

lemma heat_scale_inverse_sqrt {t : ℝ} (ht : 0 < t) (z : V) :
    (Real.sqrt t)⁻¹^4 * heat 1 ((Real.sqrt t)⁻¹ • z) = heat t z := by
  have hr := Real.sqrt_pos.2 ht
  have he := heat_scale hr 1 ((Real.sqrt t)⁻¹ • z)
  simpa only [Real.sq_sqrt ht.le,mul_one,smul_smul,mul_inv_cancel₀ (ne_of_gt hr),one_smul] using he.symm

lemma heat_approximate_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : V → E) (hf : Integrable f) (hfc : ContinuousAt f 0) :
    Tendsto (fun t : ℝ => ∫ z : V, heat t z • f z) (𝓝[>] 0) (𝓝 (f 0)) := by
  have hd : Tendsto (fun z : V => ‖z‖^(Module.finrank ℝ V) * heat 1 z)
      (cobounded V) (𝓝 0) := by simpa using heat_decay
  have h := tendsto_integral_comp_smul_smul_of_integrable
    (fun z => heat_nonneg 1 z) (heat_integral zero_lt_one) hd hf hfc
  have hc : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) (𝓝[>] 0) atTop := by
    simpa only [Function.comp_def,Real.sqrt_inv] using Real.tendsto_sqrt_atTop.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  have h' := h.comp hc
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  dsimp only [Function.comp_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  simpa using heat_scale_inverse_sqrt ht z

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff Topology
open Filter
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]

omit [Fintype ι] in
lemma adjoint_product_commutes (S : W →L[ℝ] W) (T : Q →L[ℝ] Q)
    (hS : S.adjoint = S) (hT : T.adjoint = T) (A B : W →L[ℝ] Q)
    (hA : A ∘L S = T ∘L A) (hB : B ∘L S = T ∘L B) :
    Commute (A.adjoint ∘L B) S := by
  have hAs := congrArg (fun L : W →L[ℝ] Q => L.adjoint) hA
  simp only [ContinuousLinearMap.adjoint_comp,hS,hT] at hAs
  change (A.adjoint ∘L B) ∘L S = S ∘L (A.adjoint ∘L B)
  rw [ContinuousLinearMap.comp_assoc,hB,←ContinuousLinearMap.comp_assoc,←hAs,
    ContinuousLinearMap.comp_assoc]

omit [Fintype ι] [CompleteSpace Q] [CompleteSpace W] in
lemma fderiv_commutes (S : W →L[ℝ] W) (F : V → W →L[ℝ] W) {x : V}
    (hF : DifferentiableAt ℝ F x) (hcomm : ∀ᶠ y in 𝓝 x, Commute (F y) S) (v : V) :
    Commute (fderiv ℝ F x v) S := by
  have he : (fun y => F y ∘L S) =ᶠ[𝓝 x] (fun y => S ∘L F y) := hcomm
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hleft := (hF.hasFDerivAt.clm_comp (hasFDerivAt_const (c := S) x)).fderiv
  have hright := ((hasFDerivAt_const (c := S) x).clm_comp hF.hasFDerivAt).fderiv
  rw [hleft,hright] at hd
  have hv := congrArg (fun L : V →L[ℝ] (W →L[ℝ] W) => L v) hd
  change (fderiv ℝ F x v) ∘L S = S ∘L (fderiv ℝ F x v)
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,zero_apply,ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero,add_zero,zero_add] using hv

lemma firstMatrix_commutes (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (S : W →L[ℝ] W) (T : Q →L[ℝ] Q)
    (hS : S.adjoint = S) (hT : T.adjoint = T) {x : V}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x)
    (hea : ∀ i, ∀ᶠ y in 𝓝 x, a i y ∘L S = T ∘L a i y)
    (heb : b x ∘L S = T ∘L b x) (j : ι) : Commute (firstMatrix e a b ρ j x) S := by
  have hp (i : ι) : DifferentiableAt ℝ (principalMatrix a ρ i j) x :=
    ((ContinuousLinearMap.adjoint.toContinuousLinearEquiv.differentiableAt.comp x
      (hρ.smul (ha i))).clm_comp (ha j))
  have hc (i : ι) : ∀ᶠ y in 𝓝 x, Commute (principalMatrix a ρ i j y) S := by
    filter_upwards [hea i,hea j] with y hi hj
    apply adjoint_product_commutes S T hS hT (ρ y • a i y) (a j y) _ hj
    simpa only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul] using congrArg (ρ y • ·) hi
  have hder (i : ι) := fderiv_commutes S (principalMatrix a ρ i j) (hp i) (hc i) (e i)
  have hax := (hea j).self_of_nhds
  unfold firstMatrix
  exact (((Commute.sum_left _ _ _ fun i _ => hder i).smul_left _).add_left
    (adjoint_product_commutes S T hS hT (b x) (a j x) heb hax)).sub_left
      (adjoint_product_commutes S T hS hT (a j x) (b x) hax heb)

lemma zeroMatrix_commutes (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (S : W →L[ℝ] W) (T : Q →L[ℝ] Q)
    (hS : S.adjoint = S) (hT : T.adjoint = T) {x : V}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hb : DifferentiableAt ℝ b x)
    (hρ : DifferentiableAt ℝ ρ x)
    (hea : ∀ i, ∀ᶠ y in 𝓝 x, a i y ∘L S = T ∘L a i y)
    (heb : ∀ᶠ y in 𝓝 x, b y ∘L S = T ∘L b y) : Commute (zeroMatrix e a b ρ x) S := by
  have hp (i : ι) : DifferentiableAt ℝ (lowerMatrix a b ρ i) x :=
    ((ContinuousLinearMap.adjoint.toContinuousLinearEquiv.differentiableAt.comp x
      (hρ.smul (ha i))).clm_comp hb)
  have hc (i : ι) : ∀ᶠ y in 𝓝 x, Commute (lowerMatrix a b ρ i y) S := by
    filter_upwards [hea i,heb] with y hi hj
    apply adjoint_product_commutes S T hS hT (ρ y • a i y) (b y) _ hj
    simpa only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul] using congrArg (ρ y • ·) hi
  have hder (i : ι) := fderiv_commutes S (lowerMatrix a b ρ i) (hp i) (hc i) (e i)
  have hbx := heb.self_of_nhds
  unfold zeroMatrix
  exact ((Commute.sum_left _ _ _ fun i _ => hder i).smul_left _).add_left
    (adjoint_product_commutes S T hS hT (b x) (b x) hbx hbx)

omit [CompleteSpace W] in
lemma gauge_commutes (q : ι → V →L[ℝ] ℝ) (b : ι → W →L[ℝ] W)
    (S : W →L[ℝ] W) (hb : ∀ i, Commute (b i) S) (z : V) :
    Commute (OrthogonalJets.gauge (FirstJetGauge.halfJet q b) z) S := by
  apply Commute.exp_left
  simp only [FirstJetGauge.halfJet,sum_apply,ContinuousLinearMap.smulRight_apply]
  exact Commute.sum_left _ _ _ fun i _ => ((hb i).smul_left (1/2 : ℝ)).smul_left _
end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
