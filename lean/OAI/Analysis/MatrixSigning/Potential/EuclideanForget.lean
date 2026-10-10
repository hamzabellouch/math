import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ChooseCoordinate
import OAI.Analysis.MatrixSigning.Potential.StencilScalarBounds
import OAI.Analysis.MatrixSigning.Optimization.ShiftedHessian

namespace OAI

open Matrix

namespace CurrentKS.Difference
open scoped ContDiff

theorem symmetric_bilinear_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hsymm : ∀ u v,B u v=B v u) (hquad : ∀ u,|B u u| ≤ M*‖u‖^2) : ‖B‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro v hv
  have hp := hquad (u+v)
  have hm := hquad (u-v)
  have hid : B (u+v) (u+v)-B (u-v) (u-v)=4*B u v := by
    simp only [map_add,map_sub,_root_.add_apply,_root_.sub_apply,hsymm v u]
    ring
  have hineq := (abs_sub (B (u+v) (u+v)) (B (u-v) (u-v))).trans (add_le_add hp hm)
  rw [hid,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at hineq
  have hpara := parallelogram_law_with_norm ℝ u v
  rw [hu,hv] at hpara
  rw [Real.norm_eq_abs]
  nlinarith

variable {N : ℕ}

noncomputable def euclideanForget : EuclideanSpace ℝ (Fin N) →L[ℝ] (Fin N → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).toContinuousLinearMap

lemma euclideanForget_apply (u : EuclideanSpace ℝ (Fin N)) : euclideanForget u=WithLp.ofLp u := rfl

lemma euclideanForget_bound (u : EuclideanSpace ℝ (Fin N)) : ‖euclideanForget u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le u i

noncomputable def euclideanBilinear
    (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  (B.flip.comp euclideanForget).flip.comp euclideanForget

lemma euclideanBilinear_apply (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ)
    (u v : EuclideanSpace ℝ (Fin N)) : euclideanBilinear B u v = B u v := rfl

theorem actual_hessian_norm (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ContDiffAt ℝ 2 f x)
    (hder : ∀ u,‖u‖ ≤ 1 → |iteratedDeriv 2 (fun t : ℝ => f (x+t • u)) 0| ≤ M) :
    ‖euclideanBilinear (fderiv ℝ (fderiv ℝ f) x)‖ ≤ M := by
  apply symmetric_bilinear_norm_le _ hM
  · intro u v
    exact hf.isSymmSndFDerivAt (by norm_num) u v
  · intro u
    by_cases hu : u=0
    · subst u
      simp only [map_zero,abs_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hh := bounded_directional_derivative 2 f x (euclideanForget u) hn (euclideanForget_bound u) hder
      have hfx : ContDiffAt ℝ 2 f (x+(0:ℝ) • euclideanForget u) := by simpa using hf
      have hid := second_deriv_line (x:=x) (h:=euclideanForget u) (t:=0) hfx
      rw [iteratedDeriv_succ,iteratedDeriv_one] at hh
      rw [hid,zero_smul,add_zero] at hh
      exact hh

open CurrentKS.RationalRoot Matrix Set

def interiorCandidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) : List (Fin N → ℚ) :=
  let g := stencilGradient query x h
  let H := stencilHessian query x h
  (x+s • rationalGradientDirection g) ::
    match computedCurvature H a M s ρ with
    | none => []
    | some q => [x+q,x-q]

lemma gradient_mem_candidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) :
    x+s • rationalGradientDirection (stencilGradient query x h) ∈ interiorCandidates query x h a M s ρ := by
  exact List.mem_cons_self

lemma curvature_mem_candidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x q : Fin N → ℚ)
    (h a M s ρ : ℚ) (hq : computedCurvature (stencilHessian query x h) a M s ρ=some q) :
    x+q ∈ interiorCandidates query x h a M s ρ ∧ x-q ∈ interiorCandidates query x h a M s ρ := by
  simp [interiorCandidates,hq]

lemma rationalVector_forget (q : Fin N → ℚ) : euclideanForget (realVector q)=pointCast q := rfl

lemma pointCast_gradient [NeZero N] (x g : Fin N → ℚ) (s : ℚ) :
    pointCast (x+s • rationalGradientDirection g)=pointCast x+(s:ℝ) • gradientDirection g := by
  rw [pointCast_step]
  have hh : pointCast (rationalGradientDirection g)=gradientDirection g := rationalGradientDirection_cast g
  rw [hh]

theorem interiorCandidates_progress [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) (ha : 0 < a) (ha1 : a ≤ 1) (hM1 : 1 ≤ M)
    (hs : 0 < s) (hs1 : s ≤ 1/4) (hstep : M*s ≤ a/4) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhsmall : h ≤ a/(64*M*N)) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8)
    (hf : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hders : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 2 (fun t : ℝ => f (y+t • u)) 0| ≤ (M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ (M:ℝ))
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) →
      |(query y:ℝ)-f (pointCast y)| ≤ (a:ℝ)*(h:ℝ)^2/(128*N))
    (hprogress : (∃ i,(a:ℝ) ≤ |fderiv ℝ f (pointCast x) (realBasis i)|) ∨
      ¬ ∀ u,0 ≤ realQuadratic (stencilHessian query x h) u+7*(a:ℝ)*‖u‖^2) :
    ∃ y∈interiorCandidates query x h a M s ρ,
      f (pointCast y) ≤ f (pointCast x)-2*(a:ℝ)*(s:ℝ)^2 := by
  have har : (0:ℝ) < a := by exact_mod_cast ha
  have hsr : (0:ℝ) < s := by exact_mod_cast hs
  have hhr : (0:ℝ) < h := by exact_mod_cast hh
  have hMr : (0:ℝ) ≤ M := by exact_mod_cast (le_trans (by norm_num : (0:ℚ) ≤ 1) hM1)
  have hacc := computed_stencil_accuracy query f x har (by exact_mod_cast hM1)
    hh (by exact_mod_cast hh1) (by exact_mod_cast hhsmall)
    (fun y hy => hf y (by linarith))
    (fun y hy u hu => (hders y (by linarith) u hu).2) hquery
  have hcenter : ‖pointCast x-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) := by
    simp only [sub_self,norm_zero];positivity
  rcases hprogress with hlarge|hnegative
  · let g := stencilGradient query x h
    have hs1r : (s:ℝ) ≤ (1:ℝ)/4 := by
      have ht : (s:ℝ) ≤ ((1/4:ℚ):ℝ) := Rat.cast_le.mpr hs1
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using ht
    have he := gradient_candidate_decrease f (pointCast x) g (M:=(M:ℝ)) har hsr
      hs1r (by exact_mod_cast hstep) hacc.1 hlarge
      (fun t ht => (hf _ (by
        have hb := segment_in_ball (x:=pointCast x) hsr.le zero_le_one (gradientDirection_bound g) ht
        linarith)).of_le (by norm_num))
      (fun t ht => (hders _ (by
        have hb := segment_in_ball (x:=pointCast x) hsr.le zero_le_one (gradientDirection_bound g) ⟨ht.1.le,ht.2.le⟩
        linarith) _ (gradientDirection_bound g)).1)
    refine ⟨x+s • rationalGradientDirection g,gradient_mem_candidates query x h a M s ρ,?_⟩
    rw [pointCast_gradient]
    nlinarith [sq_nonneg (s:ℝ)]
  · let H := stencilHessian query x h
    let B := euclideanBilinear (fderiv ℝ (fderiv ℝ f) (pointCast x))
    have hBn : ‖B‖ ≤ (M:ℝ) := actual_hessian_norm f _ hMr
      ((hf _ hcenter).of_le (by norm_num)) (fun u hu => (hders _ hcenter u hu).1)
    have hBe : ∀ u,|realQuadratic H u-B u u| ≤ (a:ℝ)/16*‖u‖^2 := by
      intro u
      exact stencil_quadratic_accuracy H _ har.le hacc.2 u
    have hc := computedCurvature_spec H (stencilHessian_symm query x h) B a M s ρ
      ha ha1 hM1 hs.le hρ hmesh hBn hBe
    cases he : computedCurvature H a M s ρ with
    | none =>
      simp only [he] at hc
      exact False.elim (hnegative hc)
    | some q =>
      simp only [he] at hc
      have hqnorm : ‖pointCast q‖ ≤ (s:ℝ) :=
        (euclideanForget_bound (realVector q)).trans hc.1
      have hqnorm' : ∀ v∈({pointCast q,-pointCast q}:Set (Fin N → ℝ)),‖v‖ ≤ (s:ℝ) := by
        intro v hv
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
        rcases hv with rfl|rfl
        · exact hqnorm
        · simpa only [norm_neg] using hqnorm
      have hseg (v : Fin N → ℝ) (hv : v∈({pointCast q,-pointCast q}:Set (Fin N → ℝ)))
          (t : ℝ) (ht : t∈Icc 0 1) : ‖pointCast x+t • v-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) := by
        have hb := segment_in_ball (by norm_num : (0:ℝ) ≤ 1) hsr.le (hqnorm' v hv) ht (x:=pointCast x)
        linarith
      have hdec := opposite_candidates_decrease f (pointCast x) (pointCast q) har hsr
        (by exact_mod_cast hstep) hc.2
        (fun v hv t ht => hf _ (hseg v hv t ht))
        (fun v hv t ht => bounded_directional_derivative 3 f _ v hsr (hqnorm' v hv)
          (fun u hu => (hders _ (hseg v hv t ⟨ht.1.le,ht.2.le⟩) u hu).2))
      have hm := curvature_mem_candidates query x q h a M s ρ he
      rcases hdec with hd|hd
      · exact ⟨x+q,hm.1,by simpa only [pointCast_add] using hd⟩
      · exact ⟨x-q,hm.2,by simpa only [pointCast_sub] using hd⟩

end CurrentKS.Difference

end OAI
