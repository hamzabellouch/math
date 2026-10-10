import Mathlib
import OAI.Analysis.WeakInfiniteness.SeparatedSpectralWindows

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma residual_eq_unital (e h : A) : residual e h=(1-e)*h*(1-e) := by
  unfold residual
  noncomm_ring

lemma exists_windows_of_single_nonzero_spectral_value
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₐ[ℂ] B) {U p q : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    (hp : IsSelfAdjoint p) (hpD : p ∈ D) (hpq : p*q=0) (hc : π (p*U*q) ≠ 0)
    {t : ℝ} (ht : t ∈ spectrum ℝ (π U)) (ht0 : t ≠ 0)
    (honly : ∀ s ∈ spectrum ℝ (π U),s=0 ∨ s=t) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧ ContinuouslySupported U u S ∧
        ContinuouslySupported U v T ∧ (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  let r := |t|/4
  have hr : 0 < r := by dsimp [r]; exact div_pos (abs_pos.mpr ht0) (by norm_num)
  let f : C(ℝ,ℝ) := ⟨spectralTent t (r/2),spectralTent_continuous t (r/2)⟩
  let E : C(ℝ,ℝ) := ⟨spectralPlateau t r,spectralPlateau_continuous t r⟩
  have hf0 : f 0=0 := spectralTent_zero (by positivity) (by dsimp [r]; simp; linarith [abs_nonneg t])
  have hE0 : E 0=0 := spectralPlateau_zero hr (by dsimp [r]; simp; linarith [abs_nonneg t])
  have hEt : E t=1 := spectralPlateau_one hr (by simp; exact hr.le)
  let e := cfc E U
  have heSA : IsSelfAdjoint e := cfc_predicate E U
  let u := cfc f U
  let v := residual e (p*p)
  have heD : e ∈ D := cfc_mem_of_zero D hUD E hE0
  have hp2 : p*p ∈ D := D.mul_mem hpD hpD
  have hvD : v ∈ D := D.add_mem (D.sub_mem (D.sub_mem hp2 (D.mul_mem heD hp2))
    (D.mul_mem hp2 heD)) (D.mul_mem (D.mul_mem heD hp2) heD)
  have hUe : π U=t • π e := by
    dsimp only [e]
    rw [π.map_cfc E U E.continuous.continuousOn (by fun_prop) hU (hU.map π),
      ← cfc_const_mul t E (π U) E.continuous.continuousOn]
    calc
      π U=cfc (fun s : ℝ => s) (π U) := (cfc_id' ℝ _ (hU.map π)).symm
      _ = cfc (fun s => t*E s) (π U) := by
        apply cfc_congr
        intro s hs
        change s=t*E s
        rcases honly s hs with rfl | rfl
        · rw [hE0,mul_zero]
        · rw [hEt,mul_one]
  have hvn : π v ≠ 0 := by
    intro hz
    have he : π ((1-e)*p)=0 := by
      apply (CStarRing.mul_star_self_eq_zero_iff _).mp
      have hv : ((1-e)*p)*star ((1-e)*p)=v := by
        dsimp only [v]
        rw [residual_eq_unital]
        simp only [star_mul,hp.star_eq,star_sub,star_one,heSA.star_eq]
        noncomm_ring
      rw [← map_star,← map_mul,hv,hz]
    have hep : π e*π p=π p := by
      rw [map_mul,map_sub,map_one,sub_mul,one_mul] at he
      exact (sub_eq_zero.mp he).symm
    have hpe : π p*π e=π p := by
      have hh := congrArg star hep
      simpa only [star_mul,← map_star,hp.star_eq,heSA.star_eq] using hh
    apply hc
    rw [map_mul,map_mul,hUe,mul_smul_comm,smul_mul_assoc,hpe,← map_mul,hpq,map_zero,smul_zero]
  have hfE : u*(1-e)=0 ∧ (1-e)*u=0 := by
    have hf : ContinuouslySupported U u (Metric.closedBall t (r/2)) :=
      continuouslySupported_cfc U f _ (tent_support_subset t (r/2) (by positivity))
    let g : C(ℝ,ℝ) := 1-E
    have hgf : ∀ x ∈ Metric.closedBall t (r/2),g x=0 := by
      intro x hx
      change 1-spectralPlateau t r x=0
      rw [spectralPlateau_one hr (by
        have hx' : |x-t| ≤ r/2 := by simpa only [Metric.mem_closedBall,Real.dist_eq] using hx
        linarith),sub_self]
    have hh := hf g hgf
    have hg : cfc g U=1-e := by
      change cfc (fun x => 1-E x) U=1-e
      rw [cfc_sub (fun _ : ℝ => 1) E U continuousOn_const E.continuous.continuousOn,
        cfc_const_one ℝ U hU]
    rwa [hg] at hh
  have huv : u*v=0 := by
    dsimp only [v]
    rw [residual_eq_unital,← mul_assoc,← mul_assoc,hfE.1,zero_mul,zero_mul]
  have hvS : ContinuouslySupported U v {s : ℝ | r ≤ dist s t} := by
    intro g hg
    have hEg : (1-e)*cfc g U=0 ∧ cfc g U*(1-e)=0 := by
      have hzero : (fun s : ℝ => (1-E s)*g s)=(0 : ℝ → ℝ) := by
        funext s
        change (1-E s)*g s=0
        by_cases hs : r ≤ dist s t
        · rw [hg s hs,mul_zero]
        · have hs' : |s-t| ≤ r := by simpa only [Real.dist_eq] using (le_of_lt (lt_of_not_ge hs))
          change (1-spectralPlateau t r s)*g s=0
          rw [spectralPlateau_one hr hs',sub_self,zero_mul]
      have hmap : cfc (fun s : ℝ => 1-E s) U=1-e := by
        rw [cfc_sub (fun _ : ℝ => 1) E U continuousOn_const E.continuous.continuousOn,
          cfc_const_one ℝ U hU]
      constructor
      · rw [← hmap,← cfc_mul (fun s : ℝ => 1-E s) g U
          (by fun_prop) g.continuous.continuousOn,hzero,cfc_zero ℝ U]
      · rw [← hmap,← cfc_mul g (fun s : ℝ => 1-E s) U
          g.continuous.continuousOn (by fun_prop)]
        have heq : (fun s : ℝ => g s*(1-E s))=(0 : ℝ → ℝ) := by
          simpa only [mul_comm] using hzero
        rw [heq,cfc_zero ℝ U]
    constructor
    · dsimp only [v]
      rw [residual_eq_unital,mul_assoc,hEg.1,mul_zero]
    · dsimp only [v]
      rw [residual_eq_unital,← mul_assoc,← mul_assoc,hEg.2,zero_mul,zero_mul]
  refine ⟨u,cfc_mem_of_zero D hUD f hf0,v,hvD,
    cfc_nonneg (fun x _ => spectralTent_nonneg t (r/2) x),
    residual_nonneg e (p*p) (cfc_predicate E U) (by simpa only [hp.star_eq] using star_mul_self_nonneg p),
    huv,cfc_nonzero_of_spectral_value π hU f ht ?_,hvn,
    Metric.closedBall t (r/2),{s : ℝ | r ≤ dist s t},r/2,by positivity,
    continuouslySupported_cfc U f _ (tent_support_subset t (r/2) (by positivity)),hvS,?_⟩
  · change spectralTent t (r/2) t ≠ 0
    rw [spectralTent_center]; exact one_ne_zero
  · intro x hx y hy
    have hx' : dist x t ≤ r/2 := hx
    have hy' : r ≤ dist y t := hy
    have hh := dist_triangle y x t
    rw [dist_comm y x] at hh
    linarith

end

end WeakPureInfiniteness
end

end OAI
