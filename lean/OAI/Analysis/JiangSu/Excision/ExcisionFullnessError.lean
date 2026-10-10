import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormCentralFunctionalCalculus

namespace OAI

noncomputable section


namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_two_sided_contractions (y x z : A) (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖y*x*z‖ ≤ ‖x‖ := by
  calc
    _ ≤ (‖y‖*‖x‖)*‖z‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖x‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hy (norm_nonneg _)) hz (norm_nonneg _)
      (by positivity)
    _=‖x‖ := by ring

lemma norm_sqrt_upperCut_le {δ : ℝ} (hδ : 0<δ) (f : A) (hfn : ‖f‖ ≤ 1) :
    ‖CFC.sqrt (upperCut δ f)‖ ≤ 1 := by
  have h : ‖star (CFC.sqrt (upperCut δ f))*CFC.sqrt (upperCut δ f)‖=
      ‖CFC.sqrt (upperCut δ f)‖*‖CFC.sqrt (upperCut δ f)‖ := CStarRing.norm_star_mul_self
  rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self _ (upperCut_nonneg hδ.le f)] at h
  nlinarith [upperCut_norm_le hδ f hfn,norm_nonneg (CFC.sqrt (upperCut δ f))]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_star_commutator (t x : A) (ht : IsSelfAdjoint t) :
    ‖t*star x-star x*t‖=‖x*t-t*x‖ := by
  rw [←norm_star (t*star x-star x*t),star_sub,star_mul,star_mul,star_star,ht.star_eq]

omit [PartialOrder A] [StarOrderedRing A] in
lemma fullness_error_le {I : Type*} [Fintype I] (c t : A) (hc : ‖c‖ ≤ 1)
    (ht : ‖t‖ ≤ 1) (hsa : IsSelfAdjoint t) (x : I → A) :
    (∑ i,(‖t*star (x i)-star (x i)*t‖*‖(c*c)*x i*t‖+
      ‖star (x i)*t*(c*c)‖*‖x i*t-t*x i‖)) ≤
      ∑ i,2*‖x i‖*‖t*x i-x i*t‖ := by
  have hc2 : ‖c*c‖ ≤ 1 := (norm_mul_le _ _).trans
    (by nlinarith [norm_nonneg c])
  apply Finset.sum_le_sum
  intro i _
  have h1 := norm_two_sided_contractions (c*c) (x i) t hc2 ht
  have h2 : ‖star (x i)*t*(c*c)‖ ≤ ‖x i‖ := by
    calc
      _ ≤ ‖star (x i)‖*(‖t‖*‖c*c‖) := by
        rw [mul_assoc]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖x i‖ := by
        rw [norm_star]
        have hp : ‖t‖*‖c*c‖ ≤ 1 := by
          nlinarith [norm_nonneg t,norm_nonneg (c*c),
            mul_nonneg (sub_nonneg.mpr ht) (norm_nonneg (c*c))]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg (x i))
  rw [norm_star_commutator t (x i) hsa,norm_sub_rev (x i*t) (t*x i)]
  nlinarith [norm_nonneg (t*x i-x i*t),
    mul_le_mul_of_nonneg_left h1 (norm_nonneg (t*x i-x i*t)),
    mul_le_mul_of_nonneg_right h2 (norm_nonneg (t*x i-x i*t))]

lemma hereditaryUpperCut_trace_lower_simple {I : Type*} [Fintype I]
    (τ : TracialState A) {δ : ℝ} (hδ : 0<δ) (f c : A)
    (hf : 0 ≤ f) (hfn : ‖f‖ ≤ 1) (hc : IsSelfAdjoint c) (hcn : ‖c‖ ≤ 1) (x : I → A)
    (hframe : ∑ i,star (x i)*(c*c)*x i=1) :
    (τ.functional f).re-(τ.functional (f-f*f)).re/δ ≤
      (∑ i,‖x i‖^2)*(τ.functional (hereditaryUpperCut δ f c)).re+
        ∑ i,2*‖x i‖*‖CFC.sqrt (upperCut δ f)*x i-x i*CFC.sqrt (upperCut δ f)‖ := by
  exact (hereditaryUpperCut_trace_lower τ hδ f c hf hfn hc x hframe).trans
    (add_le_add le_rfl (fullness_error_le c _ hcn (norm_sqrt_upperCut_le hδ f hfn)
      (CFC.sqrt_nonneg _).isSelfAdjoint x))

 theorem central_fullness_error_tendsto {I : Type*} [Fintype I]
    (U : Ultrafilter ℕ) (f : lp (fun _ : ℕ => A) ∞) (hf : ∀ n,0 ≤ f n)
    (hcentral : ∀ a : A,Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    {δ : ℝ} (hδ : 0<δ) (hδ1 : δ ≤ 1) (x : I → A) :
    Tendsto (fun n => ∑ i,2*‖x i‖*‖CFC.sqrt (upperCut δ (f n))*x i-x i*CFC.sqrt (upperCut δ (f n))‖)
      (U : Filter ℕ) (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    (tendsto_const_nhds (x := 2*‖x i‖)).mul (norm_central_upperCut_sqrt U f hf (x i) (hcentral _) hδ hδ1))
  simpa only [mul_zero,Finset.sum_const_zero] using h


theorem eventual_hereditary_upperCut_trace_lower
    (hsimple : TopologicallySimple A) (U : Ultrafilter ℕ)
    (f : lp (fun _ : ℕ => A) ∞) (hf : ∀ n,0 ≤ f n) (hfn : ∀ n,‖f n‖ ≤ 1)
    (hcentral : ∀ a : A,Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    {t : ℝ} (ht : 0<t)
    (hlarge : ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,t ≤ (τ.functional (f n)).re)
    (hdefect : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (f n-f n*f n)).re<η)
    (c : A) (hc : 0 ≤ c) (hcn : ‖c‖ ≤ 1) (hc0 : c≠0) :
    ∃ β : ℝ,0<β ∧ ∀ δ : ℝ,0<δ → δ ≤ 1 →
      ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
        2*β ≤ (τ.functional (hereditaryUpperCut δ (f n) c)).re := by
  have hc2 : 0 ≤ c*c := by simpa only [hc.isSelfAdjoint.star_eq] using star_mul_self_nonneg c
  have hc20 : c*c≠0 := by
    intro hz
    apply hc0
    apply norm_eq_zero.mp
    have hn : ‖c‖*‖c‖=0 := by
      rw [←CStarRing.norm_star_mul_self,hc.isSelfAdjoint.star_eq,hz,norm_zero]
    nlinarith [norm_nonneg c]
  obtain ⟨l,hl⟩ := exists_positive_fullness_frame hc2
    (closure_span_singleton_eq_univ hsimple (c*c) hc20)
  let x : Fin l.length → A := l.get
  have hframe : ∑ i,star (x i)*(c*c)*x i=1 := by
    rw [←List.sum_ofFn]
    have hlist : List.ofFn (fun i => star (x i)*(c*c)*x i)=l.map (fun v => star v*(c*c)*v) := by
      change List.ofFn ((fun v : A => star v*(c*c)*v) ∘ l.get)=_
      rw [←List.map_ofFn,List.ofFn_get]
    rw [hlist,hl]
  let M : ℝ := (∑ i,‖x i‖^2)+1
  have hM : 0<M := by dsimp [M]; positivity
  let β := t/(8*M)
  refine ⟨β,by dsimp [β]; positivity,?_⟩
  intro δ hδ hδ1
  have herr := central_fullness_error_tendsto U f hf hcentral hδ hδ1 x
  have hevent := (tendsto_order.1 herr).2 (t/4) (by positivity)
  have hdevent := hdefect (δ*(t/4)) (by positivity)
  filter_upwards [hlarge,hevent,hdevent] with n hn he hd
  intro τ
  have hw := hereditaryUpperCut_nonneg hδ.le (f n) c hc.isSelfAdjoint
  have hwp : 0 ≤ (τ.functional (hereditaryUpperCut δ (f n) c)).re :=
    (τ.functional.map_nonneg hw).1
  have hq := hereditaryUpperCut_trace_lower_simple τ hδ (f n) c (hf n) (hfn n)
    hc.isSelfAdjoint hcn x hframe
  have hdiv : (τ.functional (f n-f n*f n)).re/δ<t/4 :=
    (div_lt_iff₀ hδ).mpr (by nlinarith [hd τ])
  have hlow : t/2 ≤ M*(τ.functional (hereditaryUpperCut δ (f n) c)).re := by
    dsimp [M]
    nlinarith [hn τ]
  have hβ : 2*β ≤ t/(2*M) := by
    dsimp [β]
    field_simp
    nlinarith
  exact hβ.trans ((div_le_iff₀ (by positivity : 0<2*M)).mpr (by nlinarith))

end DirectComparison

end

end OAI
