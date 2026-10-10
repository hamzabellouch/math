import Mathlib
import OAI.Analysis.SymmetricDomains.VariableEulerAutomorphismFamily
import OAI.Analysis.SymmetricDomains.OneParameterPositiveLocal

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
open scoped NNReal
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem normalized_automorphism_limit_complete (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0))
    (p : U) (X : Affine n → Affine n) (hX : AnalyticOnNhd ℂ X U)
    (hq : TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)) X l U) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ EqOn (infinitesimalGenerator H) X U := by
  have hf : ContDiffAt ℝ 1 X p.val := (hX p.val p.property).contDiffAt.restrict_scalars ℝ
  obtain ⟨L,S,hS,hL⟩ := hf.exists_lipschitzOnWith
  obtain ⟨R,hR,hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hS (hU.mem_nhds p.property))
  let K : Set (Affine n) := closedBall p.val R
  have hKU : K⊆U := fun x hx => (hRsub hx).2
  have hLK : LipschitzOnWith L X K := hL.mono (fun x hx => (hRsub hx).1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hconv : TendstoUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)) X l K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hq.mono hKU)
  have hcons (ε : ℝ) (hε : 0<ε) : ∀ᶠ i in l, ∀ y∈K,
      ‖(q i).ambientAut y-y-h i • X y‖≤ε*h i := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with i hi
    intro y hy
    have he : (q i).ambientAut y-y-h i • X y=
        h i • ((h i)⁻¹ • ((q i).ambientAut y-y)-X y) := by
      rw [smul_sub,smul_smul,mul_inv_cancel₀ (ne_of_gt (hp i)),one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (hp i)]
    have hb : ‖(h i)⁻¹ • ((q i).ambientAut y-y)-X y‖≤ε := by
      exact le_of_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hi y hy)
    calc
      _ ≤ h i*ε := mul_le_mul_of_nonneg_left hb (hp i).le
      _ = ε*h i := mul_comm _ _
  obtain ⟨C,hC,hCb⟩ := (hK.image_of_continuousOn (hX.continuousOn.mono hKU)).isBounded.exists_pos_norm_le
  let M : ℝ := C+1
  have hM : 0<M := by dsimp [M]; linarith
  have hstep : ∀ᶠ i in l, ∀ y∈K, ‖(q i).ambientAut y-y‖≤M*h i := by
    filter_upwards [hcons 1 zero_lt_one] with i hi
    intro y hy
    have hb := hCb (X y) (mem_image_of_mem X hy)
    have he : (q i).ambientAut y-y=((q i).ambientAut y-y-h i • X y)+h i • X y := by abel
    rw [he]
    calc
      _ ≤ ‖(q i).ambientAut y-y-h i • X y‖+‖h i • X y‖ := norm_add_le _ _
      _ ≤ 1*h i+h i*C := add_le_add (hi y hy) (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hp i)]
        exact mul_le_mul_of_nonneg_left hb (hp i).le)
      _ = M*h i := by dsimp [M]; ring
  obtain ⟨r₀,hr₀,δ₀,hδ₀,α,hα0,hα,hαc⟩ := exists_local_integralCurves_in_nhds X p.val K
    (closedBall_mem_nhds p.val hR) (fun y hy => (hX y (hKU hy)).continuousAt) hf
  let r : ℝ := min r₀ (R/2)
  let T : ℝ := min δ₀ (R/(2*M))
  have hr : 0<r := lt_min hr₀ (half_pos hR)
  have hT : 0<T := lt_min hδ₀ (div_pos hR (by positivity))
  have hrr : r≤r₀ := min_le_left _ _
  have hrR : r≤R/2 := min_le_right _ _
  have hTδ : T≤δ₀ := min_le_left _ _
  have hTM : T≤R/(2*M) := min_le_right _ _
  have hsize : r+M*T≤R := by
    have hv := (le_div_iff₀ (show 0<2*M by positivity)).mp hTM
    nlinarith
  have hbU : closedBall p.val r⊆U :=
    (closedBall_subset_closedBall (hrR.trans (half_le_self hR.le))).trans hKU
  have htδ {t : ℝ} (ht : t∈Icc 0 T) : t∈Icc (-δ₀) δ₀ := by
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨g,_,hgc,_,hgeq⟩ := variable_Euler_automorphism_family hU hc hbd Γ hhol l q h hp hh p X
    hr hM.le hT hsize hKU hLK hstep hcons α
    (fun x hx => hα0 x (closedBall_subset_closedBall hrr hx))
    (fun x hx t ht => hα x (closedBall_subset_closedBall hrr hx) t (htδ ht))
    (hαc.mono (fun z hz => ⟨closedBall_subset_closedBall hrr hz.1,htδ hz.2⟩))
  apply exists_oneParameter_of_positive_local_ODE hU hc hbd p X hX g hr hT hbU hgc
  intro x hx t ht
  have heq : α x=ᶠ[𝓝 t] (fun s => (g s).ambientAut x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (hgeq x hx s ⟨hs.1.le,hs.2.le⟩).symm
  have hd := (hα x (closedBall_subset_closedBall hrr hx) t (htδ ⟨ht.1.le,ht.2.le⟩)).2.1
  have hder := hd.congr_of_eventuallyEq heq
  simpa only [hgeq x hx t ⟨ht.1.le,ht.2.le⟩] using hder
end Biholomorph
end Release061

end

end OAI
