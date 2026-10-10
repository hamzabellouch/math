import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.NormSmulRightId

namespace OAI

open Matrix

namespace CurrentKS.Implicit
noncomputable section
open Filter
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_multilinear_two (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G)
    (u v : E) : ‖B ![u,v]‖ ≤ ‖B‖*‖u‖*‖v‖ := by
  simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,mul_assoc] using B.le_opNorm ![u,v]
lemma norm_multilinear_three (B : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) G)
    (u : E) : ‖B (fun _ => u)‖ ≤ ‖B‖*‖u‖^3 := by
  simpa using B.le_opNorm (fun _ => u)

lemma norm_implicit_inverse (J : F ≃L[ℝ] G) {A : ℝ} (hA : ‖J.symm.toContinuousLinearMap‖ ≤ A)
    (z : F) : ‖z‖ ≤ A*‖J z‖ := by
  calc
    ‖z‖ = ‖J.symm (J z)‖ := by rw [J.symm_apply_apply]
    _ ≤ ‖J.symm.toContinuousLinearMap‖*‖J z‖ := J.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)

theorem curve_bounds (funct : E → G) (c : ℝ → E) (a : ℝ)
    (hf : ContDiffAt ℝ 3 funct (c a)) (hc : ContDiffAt ℝ 3 c a)
    (heq : funct ∘ c =ᶠ[𝓝 a] fun _ => 0)
    (V : F →L[ℝ] E) (J : F ≃L[ℝ] G)
    (hJ : ∀ u, fderiv ℝ funct (c a) (V u) = J u)
    (v : E) (z₁ z₂ z₃ : F)
    (h₁ : deriv c a = v+V z₁) (h₂ : iteratedDeriv 2 c a = V z₂)
    (h₃ : iteratedDeriv 3 c a = V z₃)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hV : ‖V‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hF₁ : ‖fderiv ℝ funct (c a)‖ ≤ D)
    (hF₂ : ‖iteratedFDeriv ℝ 2 funct (c a)‖ ≤ D)
    (hF₃ : ‖iteratedFDeriv ℝ 3 funct (c a)‖ ≤ D) :
    ‖z₁‖ ≤ A*D ∧ ‖z₂‖ ≤ A*D*(1+A*D)^2 ∧
      ‖z₃‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2)) := by
  have hzero (k : ℕ) (hk : k ≠ 0) : iteratedDeriv k (funct ∘ c) a = 0 := by
    rw [heq.iteratedDeriv_eq k,iteratedDeriv_const,ite_eq_right hk]
  have hfirst : fderiv ℝ funct (c a) (deriv c a) = 0 := by
    have h := (hf.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt a
      (hc.differentiableAt (by norm_num)).hasDerivAt
    rw [← h.deriv]
    simpa only [iteratedDeriv_one] using hzero 1 (by norm_num)
  have hJ₁ : J z₁ = -fderiv ℝ funct (c a) v := by
    rw [h₁,map_add,hJ] at hfirst
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hfirst)
  have hz₁ : ‖z₁‖ ≤ A*D := by
    calc
      _ ≤ A*‖J z₁‖ := norm_implicit_inverse J hJinv z₁
      _ = A*‖fderiv ℝ funct (c a) v‖ := by rw [hJ₁,norm_neg]
      _ ≤ A*(D*1) := mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul hF₁ hv (norm_nonneg _) hD)) hA
      _ = _ := by ring
  have hVnorm (u : F) : ‖V u‖ ≤ ‖u‖ :=
    (V.le_opNorm u).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hV (norm_nonneg u))
  have hc₁ : ‖deriv c a‖ ≤ 1+A*D := by
    rw [h₁]
    exact (norm_add_le _ _).trans (add_le_add hv ((hVnorm _).trans hz₁))
  have hU : 0 ≤ 1+A*D := by positivity
  have hs := iteratedDeriv_vcomp_two (hf.of_le (by norm_num)) (hc.of_le (by norm_num))
  rw [hzero 2 (by norm_num),h₂,hJ] at hs
  have hJ₂ : J z₂ = -iteratedFDeriv ℝ 2 funct (c a) (fun _ => deriv c a) := by
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs.symm)
  have hz₂ : ‖z₂‖ ≤ A*D*(1+A*D)^2 := by
    calc
      _ ≤ A*‖J z₂‖ := norm_implicit_inverse J hJinv z₂
      _ = A*‖iteratedFDeriv ℝ 2 funct (c a) (fun _ => deriv c a)‖ := by rw [hJ₂,norm_neg]
      _ ≤ A*(D*(1+A*D)^2) := by
        apply mul_le_mul_of_nonneg_left _ hA
        calc
          _ ≤ ‖iteratedFDeriv ℝ 2 funct (c a)‖*‖deriv c a‖^2 := by
            simpa using (iteratedFDeriv ℝ 2 funct (c a)).le_opNorm (fun _ => deriv c a)
          _ ≤ _ := mul_le_mul hF₂ (pow_le_pow_left₀ (norm_nonneg _) hc₁ _) (sq_nonneg _) hD
      _ = _ := by ring
  have hc₂ : ‖iteratedDeriv 2 c a‖ ≤ A*D*(1+A*D)^2 := by
    rw [h₂]
    exact (hVnorm z₂).trans hz₂
  have hZ₂ : 0 ≤ A*D*(1+A*D)^2 := by positivity
  have ht := iteratedDeriv_vcomp_three hf hc
  rw [hzero 3 (by norm_num),h₃,hJ] at ht
  have hJ₃ : J z₃ = -(iteratedFDeriv ℝ 3 funct (c a) (fun _ => deriv c a)+
      iteratedFDeriv ℝ 2 funct (c a) ![iteratedDeriv 2 c a,deriv c a]+
      2 • iteratedFDeriv ℝ 2 funct (c a) ![deriv c a,iteratedDeriv 2 c a]) := by
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using ht.symm)
  have htriple : ‖iteratedFDeriv ℝ 3 funct (c a) (fun _ => deriv c a)‖ ≤ D*(1+A*D)^3 :=
    (norm_multilinear_three _ _).trans
      (mul_le_mul hF₃ (pow_le_pow_left₀ (norm_nonneg _) hc₁ _) (by positivity) hD)
  have hpair₁ : ‖iteratedFDeriv ℝ 2 funct (c a) ![iteratedDeriv 2 c a,deriv c a]‖ ≤ D*(A*D*(1+A*D)^2)*(1+A*D) :=
    (norm_multilinear_two _ _ _).trans
      (mul_le_mul (mul_le_mul hF₂ hc₂ (norm_nonneg _) hD) hc₁ (norm_nonneg _) (mul_nonneg hD hZ₂))
  have hpair₂ : ‖iteratedFDeriv ℝ 2 funct (c a) ![deriv c a,iteratedDeriv 2 c a]‖ ≤ D*(1+A*D)*(A*D*(1+A*D)^2) :=
    (norm_multilinear_two _ _ _).trans
      (mul_le_mul (mul_le_mul hF₂ hc₁ (norm_nonneg _) hD) hc₂ (norm_nonneg _) (mul_nonneg hD hU))
  refine ⟨hz₁,hz₂,?_⟩
  calc
    _ ≤ A*‖J z₃‖ := norm_implicit_inverse J hJinv z₃
    _ ≤ A*(D*(1+A*D)^3+D*(A*D*(1+A*D)^2)*(1+A*D)+2*(D*(1+A*D)*(A*D*(1+A*D)^2))) := by
      rw [hJ₃,norm_neg]
      apply mul_le_mul_of_nonneg_left _ hA
      calc
        _ ≤ ‖iteratedFDeriv ℝ 3 funct (c a) (fun _ => deriv c a)‖+
            ‖iteratedFDeriv ℝ 2 funct (c a) ![iteratedDeriv 2 c a,deriv c a]‖+
            ‖2 • iteratedFDeriv ℝ 2 funct (c a) ![deriv c a,iteratedDeriv 2 c a]‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
        _ ≤ _ := by
          exact add_le_add (add_le_add htriple hpair₁)
            (norm_nsmul_le.trans (by simpa using mul_le_mul_of_nonneg_left hpair₂ (by norm_num : (0 : ℝ) ≤ 2)))
    _ = _ := by ring

lemma iteratedDeriv_clm {c : ℝ → E} {a : ℝ} {n : ℕ} (hc : ContDiffAt ℝ n c a)
    (L : E →L[ℝ] G) : iteratedDeriv n (L ∘ c) a = L (iteratedDeriv n c a) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left hc le_rfl]
  rfl

lemma iteratedDeriv_prod {f : ℝ → E} {g : ℝ → F} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f a) (hg : ContDiffAt ℝ n g a) :
    iteratedDeriv n (fun t => (f t,g t)) a = (iteratedDeriv n f a,iteratedDeriv n g a) := by
  apply Prod.ext
  · have hh := iteratedDeriv_clm (hf.prodMk hg) (ContinuousLinearMap.fst ℝ E F)
    exact hh.symm
  · have hh := iteratedDeriv_clm (hf.prodMk hg) (ContinuousLinearMap.snd ℝ E F)
    exact hh.symm

lemma affine_deriv (x h : E) : deriv (fun t : ℝ => x+t • h) = fun _ => h := by
  funext t
  have hh := (((hasDerivAt_id t).smul_const h).const_add x).deriv
  simp only [one_smul] at hh
  exact hh
lemma affine_second (x h : E) (a : ℝ) : iteratedDeriv 2 (fun t : ℝ => x+t • h) a = 0 := by
  rw [show 2 = 1+1 from rfl,iteratedDeriv_succ',affine_deriv,iteratedDeriv_const]
  rfl
lemma affine_third (x h : E) (a : ℝ) : iteratedDeriv 3 (fun t : ℝ => x+t • h) a = 0 := by
  rw [show 3 = 2+1 from rfl,iteratedDeriv_succ',affine_deriv,iteratedDeriv_const]
  rfl

theorem graph_bounds (funct : E × F → G) (x h : E) (z : ℝ → F) (a : ℝ)
    (hf : ContDiffAt ℝ 3 funct (x+a • h,z a)) (hz : ContDiffAt ℝ 3 z a)
    (heq : (fun t => funct (x+t • h,z t)) =ᶠ[𝓝 a] fun _ => 0)
    (J : F ≃L[ℝ] G) (hJ : ∀ u, fderiv ℝ funct (x+a • h,z a) (0,u) = J u)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
    (hF₁ : ‖fderiv ℝ funct (x+a • h,z a)‖ ≤ D)
    (hF₂ : ‖iteratedFDeriv ℝ 2 funct (x+a • h,z a)‖ ≤ D)
    (hF₃ : ‖iteratedFDeriv ℝ 3 funct (x+a • h,z a)‖ ≤ D) :
    ‖deriv z a‖ ≤ A*D ∧ ‖iteratedDeriv 2 z a‖ ≤ A*D*(1+A*D)^2 ∧
      ‖iteratedDeriv 3 z a‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2)) := by
  have hl : ContDiff ℝ 3 (fun t : ℝ => x+t • h) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have h₁ : deriv (fun t => (x+t • h,z t)) a = (h,0)+(ContinuousLinearMap.inr ℝ E F) (deriv z a) := by
    have hd := (((hasDerivAt_id a).smul_const h).const_add x).prodMk
      (hz.differentiableAt (by norm_num)).hasDerivAt
    simpa using hd.deriv
  have h₂ : iteratedDeriv 2 (fun t => (x+t • h,z t)) a = (ContinuousLinearMap.inr ℝ E F) (iteratedDeriv 2 z a) := by
    rw [iteratedDeriv_prod (hl.contDiffAt.of_le (by norm_num)) (hz.of_le (by norm_num)),affine_second]
    rfl
  have h₃ : iteratedDeriv 3 (fun t => (x+t • h,z t)) a = (ContinuousLinearMap.inr ℝ E F) (iteratedDeriv 3 z a) := by
    rw [iteratedDeriv_prod hl.contDiffAt hz,affine_third]
    rfl
  have hV : ‖ContinuousLinearMap.inr ℝ E F‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simp
  exact curve_bounds funct _ a hf (hl.contDiffAt.prodMk hz) heq (ContinuousLinearMap.inr ℝ E F) J hJ
    (h,0) (deriv z a) (iteratedDeriv 2 z a) (iteratedDeriv 3 z a) h₁ h₂ h₃ hA hD hJinv hV
    (by simpa using hh) hF₁ hF₂ hF₃

end
end CurrentKS.Implicit

end OAI
