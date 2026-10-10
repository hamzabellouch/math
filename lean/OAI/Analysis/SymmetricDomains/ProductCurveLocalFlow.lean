import Mathlib
import OAI.Analysis.SymmetricDomains.ConsistentIteratesTendsto

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
open Set Filter Topology Metric
open scoped NNReal

theorem exists_local_integralCurves_in_nhds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (X : E → E) (p : E) (K : Set E)
    (hK : K∈𝓝 p) (hX : ∀ x∈K, ContinuousAt X x) (hf : ContDiffAt ℝ 1 X p) :
    ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∃ α : E → ℝ → E,
      (∀ x∈closedBall p r, α x 0=x) ∧
      (∀ x∈closedBall p r, ∀ t∈Icc (-δ) δ, α x t∈K ∧
        HasStrictDerivAt (α x) (X (α x t)) t ∧ ContinuousAt (fun s => X (α x s)) t) ∧
      ContinuousOn (fun z : E × ℝ => α z.1 z.2) (closedBall p r ×ˢ Icc (-δ) δ) := by
  obtain ⟨e,he,a,r₀,L,M,hr₀,hPL⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨β,hβ,hβc⟩ := (hPL 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hr₀' : (0:ℝ)<r₀ := hr₀
  have hB : closedBall p (r₀:ℝ) ×ˢ Icc (0-e) (0+e)∈𝓝 (p,(0:ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds p hr₀') (Icc_mem_nhds (by linarith) (by linarith))
  have hpc : ContinuousAt β (p,0) := (hβc (p,0) (mem_of_mem_nhds hB)).continuousAt hB
  have hp0 : β (p,0)=p := (hβ p (mem_closedBall_self hr₀'.le)).1
  have hpre : β ⁻¹' K∈𝓝 (p,(0:ℝ)) := by
    apply hpc
    simpa only [hp0] using hK
  obtain ⟨s,hs,hsp⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hpre
  let r : ℝ := min s (r₀:ℝ)/2
  let δ : ℝ := min s e/2
  have hr : 0<r := half_pos (lt_min hs hr₀')
  have hδ : 0<δ := half_pos (lt_min hs he)
  have hrs : r≤ s := (half_le_self (le_of_lt (lt_min hs hr₀'))).trans (min_le_left _ _)
  have hrr : r≤(r₀:ℝ) := (half_le_self (le_of_lt (lt_min hs hr₀'))).trans (min_le_right _ _)
  have hδs : δ≤ s := (half_le_self (le_of_lt (lt_min hs he))).trans (min_le_left _ _)
  have hδe : δ<e := (half_lt_self (lt_min hs he)).trans_le (min_le_right _ _)
  have hdom : closedBall p r ×ˢ Icc (-δ) δ ⊆ closedBall p (r₀:ℝ) ×ˢ Icc (0-e) (0+e) := by
    intro z hz
    exact ⟨closedBall_subset_closedBall hrr hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  refine ⟨r,hr,δ,hδ,(fun x t => β (x,t)),?_,?_,hβc.mono hdom⟩
  · intro x hx
    exact (hβ x (closedBall_subset_closedBall hrr hx)).1
  · intro x hx t ht
    have hxt : β (x,t)∈K := hsp (by
      simpa only [mem_closedBall,Prod.dist_eq,Real.dist_eq,sub_zero,max_le_iff] using
        And.intro ((mem_closedBall.mp hx).trans hrs) ((abs_le.mpr ht).trans hδs))
    have hdx (s : ℝ) (hs' : s∈Ioo (-e) e) : HasDerivAt (fun u => β (x,u)) (X (β (x,s))) s := by
      have hd := (hβ x (closedBall_subset_closedBall hrr hx)).2 s (by
        constructor <;> linarith [hs'.1,hs'.2])
      exact hd.hasDerivAt (Icc_mem_nhds (by linarith [hs'.1]) (by linarith [hs'.2]))
    have hte : t∈Ioo (-e) e := by constructor <;> linarith [ht.1,ht.2]
    have hvc : ContinuousAt (fun s => X (β (x,s))) t :=
      (hX _ hxt).comp (x := t) (f := fun s : ℝ => β (x,s)) (hdx t hte).continuousAt
    refine ⟨hxt,?_,hvc⟩
    exact hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (Filter.mem_of_superset (Ioo_mem_nhds hte.1 hte.2) hdx) hvc

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

@[simp] theorem ambientAut_iterate (a : Biholomorph U U) (p : U) (j : ℕ) :
    (a.ambientAut^[j]) p.val=((a^j).toHomeomorph p).val := by
  induction j with
  | zero => simp [one_apply]
  | succ j ih => rw [Function.iterate_succ_apply',ih,ambientAut_apply,pow_succ',mul_apply]

theorem productCurve_local_flow_limit (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∃ α : Affine n → ℝ → Affine n,
      closedBall p.val r ⊆ U ∧
      (∀ x∈closedBall p.val r, α x 0=x) ∧
      (∀ x∈closedBall p.val r, ∀ t∈Icc (-δ) δ,
        α x t∈U ∧ HasStrictDerivAt (α x)
          (infinitesimalGenerator a (α x t)+infinitesimalGenerator b (α x t)) t ∧
        Tendsto (fun N : ℕ => ((a (t/(N+1))*b (t/(N+1)))^(N+1)).ambientAut x)
          atTop (𝓝 (α x t))) ∧
      ContinuousOn (fun z : Affine n × ℝ => α z.1 z.2)
        (closedBall p.val r ×ˢ Icc (-δ) δ) := by
  let X : Affine n → Affine n := fun y => infinitesimalGenerator a y+infinitesimalGenerator b y
  let c : ℝ → Biholomorph U U := fun t => a t*b t
  have hX : AnalyticOnNhd ℂ X U := fun y hy =>
    (infinitesimalGenerator_analytic hU a ha hbd ha0 ham y hy).add
      (infinitesimalGenerator_analytic hU b hb hbd hb0 hbm y hy)
  have hf : ContDiffAt ℝ 1 X p.val := (hX p.val p.property).contDiffAt.restrict_scalars ℝ
  obtain ⟨R₀,hR₀,M,hR₀U,hstep⟩ := curve_uniform_displacement hU c (by simp [c,ha0,hb0]) p
    (productCurve_joint_hasStrictFDerivAt hU a b ha hb hbd ha0 ham hb0 hbm p)
  obtain ⟨L,S,hS,hL⟩ := hf.exists_lipschitzOnWith
  obtain ⟨R₁,hR₁,hR₁S⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hS
  let R : ℝ := min R₀ R₁
  have hR : 0<R := lt_min hR₀ hR₁
  let K : Set (Affine n) := closedBall p.val R
  have hKU : K⊆U := (closedBall_subset_closedBall (min_le_left _ _)).trans hR₀U
  have hLK : LipschitzOnWith L X K := hL.mono ((closedBall_subset_closedBall (min_le_right _ _)).trans hR₁S)
  obtain ⟨r₀,hr₀,δ₀,hδ₀,α,hα0,hα,hαc⟩ := exists_local_integralCurves_in_nhds X p.val K
    (closedBall_mem_nhds p.val hR) (fun y hy => (hX y (hKU hy)).continuousAt) hf
  let r : ℝ := min r₀ (R/2)
  let δ : ℝ := min δ₀ (min (R/2) (R/(2*((M:ℝ)+1))))
  have hr : 0<r := lt_min hr₀ (half_pos hR)
  have hM1 : 0<(M:ℝ)+1 := by positivity
  have hδ : 0<δ := lt_min hδ₀ (lt_min (half_pos hR) (div_pos hR (by positivity)))
  have hrr : r≤r₀ := min_le_left _ _
  have hrR : r≤R/2 := min_le_right _ _
  have hδδ : δ≤δ₀ := min_le_left _ _
  have hδR : δ≤R/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδM : δ≤R/(2*((M:ℝ)+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hballU : closedBall p.val r ⊆ U :=
    (closedBall_subset_closedBall (hrR.trans (half_le_self hR.le))).trans hKU
  have hdom : closedBall p.val r ×ˢ Icc (-δ) δ ⊆ closedBall p.val r₀ ×ˢ Icc (-δ₀) δ₀ := by
    intro z hz
    exact ⟨closedBall_subset_closedBall hrr hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  refine ⟨r,hr,δ,hδ,α,hballU,(fun x hx => hα0 x (closedBall_subset_closedBall hrr hx)),?_,hαc.mono hdom⟩
  intro x hx t ht
  have hxx : x∈closedBall p.val r₀ := closedBall_subset_closedBall hrr hx
  have htt : t∈Icc (-δ₀) δ₀ := by constructor <;> linarith [ht.1,ht.2]
  refine ⟨hKU (hα x hxx t htt).1,(hα x hxx t htt).2.1,?_⟩
  have hta : |t|≤δ := abs_le.mpr ht
  have hsδ {s : ℝ} (hs : s∈Icc (-|t|) |t|) : s∈Icc (-δ₀) δ₀ := by
    constructor <;> linarith [hs.1,hs.2]
  have hlocalstep : ∀ u : ℝ, |u|≤R/2 → ∀ y∈closedBall x (R/2),
      ‖(c u).ambientAut y-y‖≤M*|u| := by
    intro u hu y hy
    apply hstep u (hu.trans ((half_le_self hR.le).trans (min_le_left _ _))) y
    have hd := dist_triangle y x p.val
    have hxp : dist x p.val≤R/2 := (mem_closedBall.mp hx).trans hrR
    exact hd.trans (by linarith [mem_closedBall.mp hy,min_le_left R₀ R₁])
  have hit : ∀ N : ℕ, ∀ j≤N+1, (((fun y => (c (t/(N+1))).ambientAut y))^[j]) x∈K := by
    intro N j hj
    have hMt : (M:ℝ)*|t|≤R/2 := by
      have hh : |t| *(2*((M:ℝ)+1))≤R := (le_div_iff₀ (by positivity)).mp (hta.trans hδM)
      nlinarith [abs_nonneg t]
    have hv := curve_power_displacement c ⟨x,hballU hx⟩ hlocalstep (Nat.succ_ne_zero N)
      (hta.trans hδR) hMt j hj
    have hNr : (0:ℝ)<(N+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
    have hbound : (j:ℝ)*(M*|t|/((N+1:ℕ):ℝ))≤R/2 := by
      calc
        _ ≤ ((N+1:ℕ):ℝ)*(M*|t|/((N+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj)
          (div_nonneg (mul_nonneg M.coe_nonneg (abs_nonneg t)) hNr.le)
        _ = M*|t| := mul_div_cancel₀ _ (ne_of_gt hNr)
        _ ≤ R/2 := hMt
    have hx' : (c (t/(N+1))).ambientAut^[j] x =
        (((c (t/(N+1)))^j).toHomeomorph ⟨x,hballU hx⟩).val := ambientAut_iterate _ ⟨x,hballU hx⟩ j
    rw [hx']
    have hd := dist_triangle (((c (t/(N+1)))^j).toHomeomorph ⟨x,hballU hx⟩).val x p.val
    have hv' := hv.trans hbound
    simp only [Nat.cast_succ] at hv'
    exact hd.trans (by linarith [hv',(mem_closedBall.mp hx).trans hrR])
  have hv := consistent_iterates_tendsto (fun t y => (c t).ambientAut y) X K hLK
    (fun ε hε => productCurve_uniform_consistency hU hbd a b ha hb ha0 ham hb0 hbm K
      (isCompact_closedBall _ _) hKU hε) x (α x) t (hα0 x hxx)
    (fun s hs => (hα x hxx s (hsδ hs)).1)
    (fun s hs => (hα x hxx s (hsδ hs)).2.1)
    (fun s hs => (hα x hxx s (hsδ hs)).2.2) hit
  simpa only [ambientAut_iterate (p := ⟨x,hballU hx⟩),ambientAut_apply (p := ⟨x,hballU hx⟩),c] using hv

end Biholomorph
end Release061

end

end OAI
