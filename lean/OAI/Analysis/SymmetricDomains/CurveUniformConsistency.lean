import Mathlib
import OAI.Analysis.SymmetricDomains.CurvePowerDisplacement

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
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped NNReal
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem productCurve_powers_uniform_compact (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    ∃ δ > (0:ℝ), ∃ K : Set (Biholomorph U U), IsCompact K ∧
      ∀ t : ℝ, |t| ≤ δ → ∀ N : ℕ, ∀ j ≤ N+1,
        (a (t/(N+1))*b (t/(N+1)))^j ∈ K := by
  let c : ℝ → Biholomorph U U := fun t => a t*b t
  obtain ⟨r,hr,L,hRU,hstep⟩ := curve_uniform_displacement hU c (by simp [c,ha0,hb0]) p
    (productCurve_joint_hasStrictFDerivAt hU a b ha hb hbd ha0 ham hb0 hbm p)
  let δ : ℝ := min r (r/(L+1))
  have hL1 : 0 < (L:ℝ)+1 := by positivity
  have hδ : 0<δ := lt_min hr (div_pos hr hL1)
  let V : Set U := Subtype.val ⁻¹' closedBall p.val r
  have hV : IsCompact V := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa only [V,image_preimage_eq_inter_range,Subtype.range_coe_subtype,ofPred_mem_eq,
      inter_eq_left.mpr hRU] using isCompact_closedBall p.val r
  let K : Set (Biholomorph U U) := (fun e : Biholomorph U U => e.toHomeomorph p) ⁻¹' V
  refine ⟨δ,hδ,K,(bounded_divisible_automorphism_evaluation_proper hU hc hbd Γ hhol p).isCompact_preimage hV,?_⟩
  intro t ht N j hj
  have htr : |t|≤r := ht.trans (min_le_left _ _)
  have hLt : (L:ℝ)*|t|≤r := by
    have hh : |t| *((L:ℝ)+1)≤r := (le_div_iff₀ hL1).mp (ht.trans (min_le_right _ _))
    nlinarith [abs_nonneg t]
  have hi := curve_power_displacement c p hstep (Nat.succ_ne_zero N) htr hLt j hj
  have hNr : (0:ℝ)<(N+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  have hbound : (j:ℝ)*(L*|t|/((N+1:ℕ):ℝ))≤r := by
    calc
      _ ≤ ((N+1:ℕ):ℝ)*(L*|t|/((N+1:ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj)
          (div_nonneg (mul_nonneg L.coe_nonneg (abs_nonneg t)) hNr.le)
      _ = L*|t| := mul_div_cancel₀ _ (ne_of_gt hNr)
      _ ≤ r := hLt
  change dist (((a (t/(N+1))*b (t/(N+1)))^j).toHomeomorph p).val p.val ≤ r
  simpa only [c,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hi.trans hbound

end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
include hU

theorem curve_uniform_consistency (c : ℝ → Biholomorph U U) (hc0 : c 0=1)
    (X : Affine n → Affine n) (hX : ContinuousOn X U)
    (hd : ∀ p : U, HasStrictFDerivAt (fun z : ℝ × Affine n => (c z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (X p.val)).coprod 1) (0,p.val))
    (K : Set (Affine n)) (hK : IsCompact K) (hKU : K⊆U)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ y ∈ K, ‖(c t).ambientAut y-y-t • X y‖ ≤ ε*|t| := by
  apply hK.eventually_forall_of_forall_eventually
  intro p hp
  have hpu := hKU hp
  have hdiff := (hd ⟨p,hpu⟩).isLittleO.bound (half_pos hε)
  have hm : ContinuousAt (fun z : ℝ × Affine n => (z,((0:ℝ),z.2))) (0,p) := by fun_prop
  have he : ∀ᶠ z : ℝ × Affine n in 𝓝 (0,p),
      ‖(c z.1).ambientAut z.2-(c 0).ambientAut z.2-z.1 • X p‖ ≤ (ε/2)*|z.1| := by
    have hv := hm.tendsto.eventually hdiff
    filter_upwards [hv] with z hz
    simpa [ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,
      Prod.norm_def] using hz
  have hXc : ContinuousAt X p := (hX p hpu).continuousAt (hU.mem_nhds hpu)
  have hx : ∀ᶠ z : ℝ × Affine n in 𝓝 (0,p), ‖X p-X z.2‖ ≤ ε/2 := by
    have hv := (hXc.comp (x := ((0:ℝ),p)) continuous_snd.continuousAt)
      (ball_mem_nhds (X p) (half_pos hε))
    filter_upwards [hv] with z hz
    have hz' : dist (X z.2) (X p) < ε/2 := hz
    simpa only [dist_eq_norm,norm_sub_rev] using hz'.le
  have hu : ∀ᶠ z : ℝ × Affine n in 𝓝 (0,p), z.2 ∈ U :=
    continuous_snd.continuousAt (hU.mem_nhds hpu)
  filter_upwards [he,hx,hu] with z hz hzx hzu
  have h0 : (c 0).ambientAut z.2=z.2 := by rw [hc0,ambientAut_apply 1 ⟨z.2,hzu⟩,one_apply]
  rw [h0] at hz
  have heq : (c z.1).ambientAut z.2-z.2-z.1 • X z.2 =
      ((c z.1).ambientAut z.2-z.2-z.1 • X p)+z.1 • (X p-X z.2) := by
    rw [smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖(c z.1).ambientAut z.2-z.2-z.1 • X p‖+‖z.1 • (X p-X z.2)‖ := norm_add_le _ _
    _ ≤ (ε/2)*|z.1|+|z.1| *(ε/2) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add hz (mul_le_mul_of_nonneg_left hzx (abs_nonneg _))
    _ = ε*|z.1| := by ring

end Biholomorph
end Release061

end

end OAI
