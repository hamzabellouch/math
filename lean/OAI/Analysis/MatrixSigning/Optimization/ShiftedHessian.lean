import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.NegativeDirection
import OAI.Analysis.MatrixSigning.Potential.QuadraticDifferenceBound

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open Matrix CurrentKS.Difference
open scoped BigOperators

variable {N : ℕ}

def shiftedHessian (H : Matrix (Fin N) (Fin N) ℚ) (a : ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  H+(7*a) • 1

noncomputable def realQuadratic (H : Matrix (Fin N) (Fin N) ℚ)
    (u : EuclideanSpace ℝ (Fin N)) : ℝ :=
  u ⬝ᵥ ((H.map fun t : ℚ => (t:ℝ)) *ᵥ u)

lemma shiftedHessian_symm (H : Matrix (Fin N) (Fin N) ℚ) (hH : H.IsSymm) (a : ℚ) :
    (shiftedHessian H a).IsSymm := by
  exact hH.add (isSymm_one.smul _)

lemma realQuadratic_cast (H : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) :
    realQuadratic H (realVector v) = ((v ⬝ᵥ (H *ᵥ v):ℚ):ℝ) := by
  simp only [realQuadratic,realVector,WithLp.ofLp_toLp,dotProduct,mulVec,
    Rat.cast_sum,Rat.cast_mul,Matrix.map_apply]

lemma realQuadratic_shift (H : Matrix (Fin N) (Fin N) ℚ) (a : ℚ)
    (u : EuclideanSpace ℝ (Fin N)) :
    realQuadratic (shiftedHessian H a) u=realQuadratic H u+7*(a:ℝ)*‖u‖^2 := by
  have he : (shiftedHessian H a).map (fun t : ℚ => (t:ℝ)) =
      H.map (fun t : ℚ => (t:ℝ))+(7*(a:ℝ)) • 1 := by
    ext i j
    by_cases hi : i=j <;> simp [shiftedHessian,hi]
  rw [realQuadratic,he,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,pow_two,smul_eq_mul]

def computedCurvature (H : Matrix (Fin N) (Fin N) ℚ) (a M s ρ : ℚ) : Option (Fin N → ℚ) :=
  (negativeDirection (shiftedHessian H a) (a/(4096*M))).map
    (fun w => roundMesh ρ (fun i => s*(1-a/(1024*M))*w i))

lemma curvature_parameters {a M : ℚ} (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) :
    0 < a/(4096*M) ∧ a/(4096*M)≤1 ∧ 0 ≤ a/(1024*M) ∧ a/(1024*M)≤1 := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨by positivity,?_,by positivity,?_⟩
  · apply (div_le_one (by positivity : (0:ℚ)<4096*M)).mpr
    linarith
  · apply (div_le_one (by positivity : (0:ℚ)<1024*M)).mpr
    linarith

theorem computedCurvature_spec (H : Matrix (Fin N) (Fin N) ℚ) (hH : H.IsSymm)
    (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (a M s ρ : ℚ) (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) (hBn : ‖B‖ ≤ (M:ℝ))
    (herr : ∀ u,|realQuadratic H u-B u u| ≤ (a:ℝ)/16*‖u‖^2) :
    match computedCurvature H a M s ρ with
    | none => ∀ u,0 ≤ realQuadratic H u+7*(a:ℝ)*‖u‖^2
    | some q => ‖realVector q‖ ≤ (s:ℝ) ∧ B (realVector q) (realVector q) ≤ -6*(a:ℝ)*(s:ℝ)^2 := by
  have hpar := curvature_parameters ha ha1 hM
  have hd := negativeDirection_spec (shiftedHessian H a) (shiftedHessian_symm H hH a)
    (a/(4096*M)) hpar.1 hpar.2.1
  unfold computedCurvature
  cases he : negativeDirection (shiftedHessian H a) (a/(4096*M)) with
  | none =>
    simp only [he] at hd
    simp only [Option.map_none]
    intro u
    rw [← realQuadratic_shift]
    exact hd.dotProduct_mulVec_nonneg u
  | some w =>
    simp only [he] at hd
    simp only [Option.map_some]
    have hb : B (realVector w) (realVector w) ≤ -(111/16:ℝ)*(a:ℝ)*‖realVector w‖^2 := by
      have hn : realQuadratic (shiftedHessian H a) (realVector w)<0 := by
        rw [realQuadratic_cast]
        exact_mod_cast hd.2.2
      rw [realQuadratic_shift] at hn
      have herrw := (abs_le.mp (herr (realVector w))).1
      linarith
    have hr := curvature_rounding w s (a/(1024*M)) ρ hs hpar.2.2.1 hpar.2.2.2 hρ hmesh hd.2.1
    refine ⟨hr.2.1,?_⟩
    have hl : 1-(a:ℝ)/(4096*(M:ℝ)) ≤ ‖realVector w‖ := by
      simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hd.1
    have hq : ‖realVector (roundMesh ρ (fun i => s*(1-a/(1024*M))*w i))-
        (s:ℝ) • realVector w‖ ≤ 9*(s:ℝ)*((a:ℝ)/(1024*(M:ℝ)))/8 := by
      simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hr.2.2
    exact rounded_negative_curvature B _ (realVector w) (a:=(a:ℝ)) (M:=(M:ℝ))
      (s:=(s:ℝ)) (by exact_mod_cast ha) (by exact_mod_cast ha1) (by exact_mod_cast hM)
      (by exact_mod_cast hs) hBn hd.2.1 hl hb hr.2.1 hq

end CurrentKS.RationalRoot

end OAI
