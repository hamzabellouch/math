import Mathlib
import OAI.Analysis.Conductivity.Geometry.SmoothCollarTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma gradient_of_pi_function (q : (Fin 3 → ℝ) → ℝ) (x : R3) (i : Fin 3)
    (hq : DifferentiableAt ℝ q (WithLp.ofLp x)) :
    gradient (fun x : R3 => q (WithLp.ofLp x)) x i =
      fderiv ℝ q (WithLp.ofLp x) (Pi.single i 1) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have he := (hq.hasFDerivAt.comp x E.hasFDerivAt).fderiv
  have hi := congrArg (fun F : R3 →L[ℝ] ℝ => F (EuclideanSpace.single i 1)) he
  rw [←toDual_gradient,InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_single_right] at hi
  have hEi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,hEi,mul_one,one_mul,starRingEnd_apply,star_trivial] using hi

lemma compact_smooth_pi_H1 {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hc : HasCompactSupport q)
    {R : ℝ} (hR : R<3) (hs : ∀ x∈tsupport q,‖WithLp.toLp 2 x‖≤R) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=q (WithLp.ofLp x) ∧ ∀ i,
      weakGradient w x i=fderiv ℝ q (WithLp.ofLp x) (Pi.single i 1)) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hd : ContDiff ℝ (↑(⊤:ℕ∞)) (q ∘ E) := hq.comp E.contDiff
  refine ⟨smoothH1 (q ∘ E) hd,smoothH1_mem_H10 _ hd ?_ ?_,?_⟩
  · exact hc.comp_homeomorph E.toHomeomorph
  · intro x hx
    have hh : tsupport (q ∘ E)⊆E ⁻¹' tsupport q :=
      closure_minimal (fun y hy => subset_tsupport q hy) ((isClosed_tsupport q).preimage E.continuous)
    have hx' : E x∈tsupport q := hh hx
    have hnorm := (hs (E x) hx').trans_lt hR
    have he : WithLp.toLp 2 (E x)=x := rfl
    rw [he] at hnorm
    simpa only [ball,Metric.mem_ball,dist_zero_right] using hnorm
  · filter_upwards [smoothH1_value (q ∘ E) hd,smoothH1_gradient (q ∘ E) hd] with x hx hg
    refine ⟨hx,fun i => ?_⟩
    rw [hg]
    exact gradient_of_pi_function q x i ((hq.differentiable (by simp)) _)

def localJoinedValue (τ χ q p : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  χ x*(if 0<τ x then p x else q x)

def localJoinedGradient (τ χ q p : (Fin 3 → ℝ) → ℝ)
    (i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ χ x (Pi.single i 1)*(if 0<τ x then p x else q x)+
    χ x*(if 0<τ x then fderiv ℝ p x (Pi.single i 1) else fderiv ℝ q x (Pi.single i 1))

theorem smoothCollarTrace_localJoined_H1 {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand (b-η) (b+η)) :
    let p := fun y => (attachedEndPoissonField s (smoothCollarTrace s b hq) a b 0 y).re
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=localJoinedValue (fun y => a*(sourceCollarTime y-b)) χ q p (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=localJoinedGradient (fun y => a*(sourceCollarTime y-b)) χ q p i (WithLp.ofLp x)) := by
  obtain ⟨w,hw,hwe⟩ := smoothCollarTrace_matched_H1 hs hq hχ hc hχb ha hη hl hr hχs
  obtain ⟨z,hz,hze⟩ := compact_smooth_pi_H1 (hχ.mul hq) (hc.mul_right (f':=q))
    (by norm_num : (5:ℝ)/2<3) (fun x hx => sourceBand_euclidean_bound
      (show x∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) from
        ⟨hl.trans (hχs (tsupport_mul_subset_left hx)).1,
          (hχs (tsupport_mul_subset_left hx)).2.trans hr⟩))
  refine ⟨w+z,H10.add_mem hw hz,?_⟩
  filter_upwards [hwe,hze,weakValue_add w z,weakGradient_add w z] with x hx hz hv hg
  refine ⟨?_,fun i => ?_⟩
  · rw [hv]
    change weakValue w x+weakValue z x=_
    rw [hx.1,hz.1]
    dsimp only [Pi.add_apply,localJoinedValue,cutMatchedValue]
    split_ifs <;> ring
  · rw [hg]
    change weakGradient w x i+weakGradient z x i=_
    rw [hx.2 i,hz.2 i]
    change _+fderiv ℝ (χ*q) (WithLp.ofLp x) (Pi.single i 1)=_
    rw [fderiv_mul ((hχ.differentiable (by simp)) _) ((hq.differentiable (by simp)) _)]
    simp only [cutMatchedGradient,localJoinedGradient,sub_apply,
      add_apply,smul_apply,smul_eq_mul]
    split_ifs <;> ring

end ScalarConductivity

end

end OAI
