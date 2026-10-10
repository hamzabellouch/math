import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.SplitTrial

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma shifted_injectivityDomain_of_injectivityDomain {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ injectivityDomain x)
    {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  obtain ⟨a,ha,hmin⟩ := hp
  have hden : 0<1-t := sub_pos.mpr ht1
  let b := (a-t)/(1-t)
  have hb : 1<b := (lt_div_iff₀ hden).mpr (by linarith)
  have hbt : b*(1-t)=a-t := div_mul_cancel₀ _ hden.ne'
  refine ⟨b,hb,?_⟩
  rw [smul_smul,hbt,riemannianExp_eq_sprayFlow]
  change dist (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    (sprayFlow 1 (tangentScale (a-t) (sprayFlow t ⟨x,p⟩))).1 = _
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel]
  have hm : dist x (sprayFlow a (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=a*‖p‖ := by
    rw [←riemannianExp_smul]
    exact hmin
  change dist (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    (sprayFlow a (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 = _
  rw [sprayFlow_minimizing_subinterval _ ht (ht1.trans ha).le hm]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hden,sprayFlow_speed,←mul_assoc,hbt]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma splitTrialValue_source (x : M) (p xi : TangentSpace 𝓘(ℝ,Model n) x) (t : ℝ) :
    splitTrialValue x t xi 0 p=hessianValue x (t • p) xi/t := by
  simp only [splitTrialValue,splitNormalAction,smul_zero,add_zero]
  simp only [add_comm]
  rw [iteratedDeriv_const_add (by norm_num : 0<(2:ℕ)),iteratedDeriv_div_const]
  rfl

lemma hessianValue_strict_radial_decrease {x : M} {p xi : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) {t : ℝ} (ht : 0<t) (ht1 : t<1) (hxi : xi≠0) :
    hessianValue x p xi<hessianValue x (t • p) xi/t := by
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hpair : inner ℝ xi xi≠0 := inner_self_ne_zero.mpr hxi
  obtain ⟨hpos,hSchur⟩ := splitTrialValue_schur ht ht1 hp hleft hright hpair
  rw [splitTrialValue_source] at hSchur
  exact lt_of_le_of_lt hSchur (sub_lt_self _ (div_pos (sq_pos_of_ne_zero hpair) hpos))

lemma divided_hessian_strict_decrease {x : M} {p xi : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {t s : ℝ} (ht : 0<t) (hts : t<s) (hs : s<1)
    (hxi : xi≠0) : hessianValue x (s • p) xi/s<hessianValue x (t • p) xi/t := by
  have hs0 := ht.trans hts
  have hsp := contracted_minimizer_mem_injectivityDomain hp hs0 hs
  have hts0 : 0<t/s := div_pos ht hs0
  have hts1 : t/s<1 := (div_lt_one hs0).mpr hts
  have H := hessianValue_strict_radial_decrease hsp hts0 hts1 hxi
  rw [smul_smul,div_mul_cancel₀ _ hs0.ne'] at H
  have H' := div_lt_div_of_pos_right H hs0
  simpa only [div_div,div_mul_cancel₀ _ hs0.ne'] using H'
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.contracted_transverse_concaveOn_set (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {xi : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    {C : Set (TangentSpace 𝓘(ℝ,Model n) x)} (hC : Convex ℝ C)
    (hID : ∀ p ∈ C, t • p ∈ injectivityDomain x)
    (hortho : ∀ p ∈ C, ∀ q ∈ C, inner ℝ xi (q-p)=0) :
    ConcaveOn ℝ C (fun p => hessianValue x (t • p) xi) := by
  refine ⟨hC,?_⟩
  intro p hp q hq a b ha hb hab
  have hline : ∀ s ∈ Icc (0:ℝ) 1, t • p+s • (t • (q-p)) ∈ injectivityDomain x := by
    intro s hs
    have heq : t • p+s • (t • (q-p))=t • ((1-s) • p+s • q) := by module
    rw [heq]
    exact hID _ (hC hp hq (sub_nonneg.mpr hs.2) hs.1 (by ring))
  have H := hmtw.transverse_concaveOn_injectivityDomain x (t • p) xi (t • (q-p))
    (convex_Icc 0 1) hline (by simp only [real_inner_smul_right,hortho p hp q hq,mul_zero])
  have hh := H.2 (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) ha hb hab
  have heq : t • p+b • (t • (q-p))=t • (a • p+b • q) := by
    rw [show a=1-b by linarith]
    module
  have heq1 : t • p+t • (q-p)=t • q := by module
  simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,add_zero,one_smul,heq1,heq] using hh

lemma WeakMTW.finite_transverse_slack_strict (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0<t) (hts : t<s) (hs : s<1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {xi : TangentSpace 𝓘(ℝ,Model n) x} (hxi : xi≠0)
    (hortho : ∀ i, inner ℝ xi (p i-∑ j, w j • p j)=0) :
    (∑ i, w i*(hessianValue x (s • p i) xi/s)) <
      hessianValue x (t • (∑ i, w i • p i)) xi/t := by
  let r := ∑ i, w i • p i
  have hhyper : Convex ℝ {q : TangentSpace 𝓘(ℝ,Model n) x | inner ℝ xi q=inner ℝ xi r} := by
    intro u hu v hv a b ha hb hab
    simp only [mem_ofPred_eq,inner_add_right,real_inner_smul_right] at hu hv ⊢
    rw [hu,hv,←add_mul,hab,one_mul]
  have hsub : convexHull ℝ (range p) ⊆ {q | inner ℝ xi q=inner ℝ xi r} := by
    apply convexHull_min _ hhyper
    rintro q ⟨i,rfl⟩
    have hh := hortho i
    rw [inner_sub_right] at hh
    exact sub_eq_zero.mp hh
  have hc := hmtw.contracted_transverse_concaveOn_set (convex_convexHull ℝ (range p)) hID
    (fun u hu v hv => by rw [inner_sub_right,hsub hu,hsub hv,sub_self])
  have hj := hc.le_map_sum (t := Finset.univ) (w := w) (p := p)
    (fun i _ => (hw i).le) hsum (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  simp only [smul_eq_mul] at hj
  have hj' := div_le_div_of_nonneg_right hj ht.le
  rw [Finset.sum_div] at hj'
  have hlt : (∑ i, w i*(hessianValue x (s • p i) xi/s)) <
      ∑ i, w i*hessianValue x (t • p i) xi/t := by
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_div_assoc]
      exact (mul_lt_mul_of_pos_left (divided_hessian_strict_decrease (hmin i) ht hts hs hxi) (hw i)).le
    · obtain ⟨i⟩ := ‹Nonempty ι›
      refine ⟨i,Finset.mem_univ i,?_⟩
      rw [mul_div_assoc]
      exact mul_lt_mul_of_pos_left (divided_hessian_strict_decrease (hmin i) ht hts hs hxi) (hw i)
  exact hlt.trans_le hj'

end WeakMTWTransport

end

end OAI
