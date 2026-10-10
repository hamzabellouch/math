import OAI.Analysis.MatrixScaling.Bounds
import OAI.Analysis.MatrixScaling.Gram

namespace OAI

/-! Spectral curves, strict convexity, and geodesic connections. -/

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {d : ℕ}

/-- A positive-definite geodesic in an eigenbasis for its Hermitian direction. -/
def spectralCurve (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ) (u : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  L * Matrix.diagonal (fun j => (Real.exp (h j*u) : ℂ)) * L.conjTranspose

theorem spectralCurve_posDef (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L)
    (h : Fin d → ℝ) (u : ℝ) : (spectralCurve L h u).PosDef := by
  have hd : (Matrix.diagonal (fun j => (Real.exp (h j*u) : ℂ))).PosDef :=
    Matrix.PosDef.diagonal (fun j => by exact_mod_cast Real.exp_pos (h j*u))
  exact hL.posDef_star_right_conjugate_iff.mpr hd

theorem spectralCurve_det (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ) (u : ℝ) :
    (spectralCurve L h u).det.re =
      Complex.normSq L.det * Real.exp ((∑ j, h j)*u) := by
  unfold spectralCurve
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose]
  have hp : (∏ j, (Real.exp (h j*u) : ℂ)) = (Real.exp ((∑ j, h j)*u) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.sum_mul]
  rw [hp]
  have he : L.det * (Real.exp ((∑ j, h j)*u) : ℂ) * star L.det =
      (Complex.normSq L.det : ℂ) * (Real.exp ((∑ j, h j)*u) : ℂ) := by
    rw [Complex.star_def, ← Complex.mul_conj]
    ring
  rw [he, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem spectralCurve_log_det (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L)
    (h : Fin d → ℝ) (u : ℝ) :
    Real.log (spectralCurve L h u).det.re =
      Real.log (Complex.normSq L.det) + (∑ j, h j)*u := by
  rw [spectralCurve_det, Real.log_mul _ (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  exact ne_of_gt (Complex.normSq_pos.mpr (hL.map Matrix.detMonoidHom).ne_zero)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {d : ℕ}

/-- A positive definite matrix has an invertible Gram factor, constructed
from its eigenbasis and positive eigenvalues. -/
theorem posDef_gram_factor {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ, IsUnit L ∧ L * L.conjTranspose = P := by
  let U := hP.1.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ := diagonal (fun j => (Real.sqrt (hP.1.eigenvalues j) : ℂ))
  have hD : IsUnit D := by
    apply (D.isUnit_iff_isUnit_det).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hP.eigenvalues_pos j)))
  have hdstar : D.conjTranspose = D := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [D, Matrix.conjTranspose_apply]
    · simp [D, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  have hdsq : D*D = diagonal (fun j => (hP.1.eigenvalues j : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    change (Real.sqrt (hP.1.eigenvalues j) : ℂ) * (Real.sqrt (hP.1.eigenvalues j) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_pos j).le]
  refine ⟨(U : Matrix (Fin d) (Fin d) ℂ)*D, (Unitary.isUnit_coe (U := U)).mul hD, ?_⟩
  rw [Matrix.conjTranspose_mul, hdstar, ← Matrix.mul_assoc,
    Matrix.mul_assoc (U : Matrix (Fin d) (Fin d) ℂ) D D, hdsq]
  exact hP.1.spectral_theorem.symm

theorem exists_spectralCurve_between {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) :
    ∃ (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ), IsUnit L ∧
      spectralCurve L h 0 = P ∧ spectralCurve L h 1 = Q := by
  obtain ⟨A,hA,hAA⟩ := posDef_gram_factor hP
  let B := A⁻¹ * Q * (A⁻¹).conjTranspose
  have hAi : IsUnit A⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hA
  have hB : B.PosDef := hAi.posDef_star_right_conjugate_iff.mpr hQ
  let U := hB.1.eigenvectorUnitary
  let L := A * (U : Matrix (Fin d) (Fin d) ℂ)
  let h := fun j => Real.log (hB.1.eigenvalues j)
  have hAU : IsUnit L := hA.mul (Unitary.isUnit_coe (U := U))
  have hzero : spectralCurve L h 0 = P := by
    simp only [spectralCurve, mul_zero, Real.exp_zero, Complex.ofReal_one, diagonal_one,
      Matrix.mul_one, L, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hu : (U : Matrix (Fin d) (Fin d) ℂ) *
        (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose = 1 := Unitary.coe_mul_star_self U
    rw [← Matrix.mul_assoc (U : Matrix (Fin d) (Fin d) ℂ), hu, Matrix.one_mul]
    exact hAA
  have hone : spectralCurve L h 1 = Q := by
    have hd : diagonal (fun j => (Real.exp (h j*1) : ℂ)) =
        diagonal (fun j => (hB.1.eigenvalues j : ℂ)) := by
      congr 1
      funext j
      simp only [h, mul_one, Real.exp_log (hB.eigenvalues_pos j)]
    have hspec : (U : Matrix (Fin d) (Fin d) ℂ) *
        diagonal (fun j => (hB.1.eigenvalues j : ℂ)) *
        (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose = B := hB.1.spectral_theorem.symm
    have hc : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp hA)
    have hcstar : (A⁻¹).conjTranspose * A.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hc, Matrix.conjTranspose_one]
    unfold spectralCurve
    rw [hd]
    change (A*(U : Matrix (Fin d) (Fin d) ℂ))*_ *
      (A*(U : Matrix (Fin d) (Fin d) ℂ)).conjTranspose = Q
    rw [Matrix.conjTranspose_mul]
    calc
      (A*(U : Matrix (Fin d) (Fin d) ℂ))*
          diagonal (fun j => (hB.1.eigenvalues j : ℂ))*
          ((U : Matrix (Fin d) (Fin d) ℂ).conjTranspose*A.conjTranspose) = A*B*A.conjTranspose := by
        have he := congrArg (fun X : Matrix (Fin d) (Fin d) ℂ => A*X*A.conjTranspose) hspec
        simpa only [Matrix.mul_assoc] using he
      _ = Q := by
        dsimp [B]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.one_mul,
          Matrix.mul_assoc, hcstar, Matrix.mul_one]
  exact ⟨L,h,hAU,hzero,hone⟩

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem expansion_common_kernel (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (v : Fin d → ℂ) (hv : ∀ i, T i *ᵥ v = 0) : v = 0 := by
  let S : Submodule ℂ (Fin d → ℂ) := ⨅ i, LinearMap.ker (T i).mulVecLin
  have hm (i : Fin n) : S.map (T i).mulVecLin = ⊥ := by
    apply le_antisymm _ bot_le
    rintro w ⟨z,hz,rfl⟩
    exact (iInf_le (fun i => LinearMap.ker (T i).mulVecLin) i) hz
  have hsup : (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)) = ⊥ :=
    iSup_eq_bot.mpr hm
  have hdim := congrArg (fun V : Submodule ℂ (Fin r → ℂ) => Module.finrank ℂ V) hsup
  have hd := (hexpand S).trans_eq hdim
  rw [finrank_bot] at hd
  have hz : Module.finrank ℂ S = 0 := by omega
  have he : S = ⊥ := Submodule.finrank_eq_zero.mp hz
  have hmem : v ∈ S := by
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hv
  simpa [he] using hmem

theorem collectiveMatrix_column_nonzero (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L) (j : Fin d) :
    ∃ (i : Fin n) (b : Fin r), collectiveMatrix T L b (i,j) ≠ 0 := by
  by_contra h
  push Not at h
  have hz : (fun a => L a j) = (0 : Fin d → ℂ) := by
    apply expansion_common_kernel T hexpand
    intro i
    ext b
    exact h i b
  have hcol : L *ᵥ (Pi.single j 1) = 0 := by
    ext a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hz] using congrFun hz a
  have he := Matrix.mulVec_injective_of_isUnit hL (hcol.trans (Matrix.mulVec_zero L).symm)
  have hj := congrFun he j
  simp at hj

theorem scalingMap_spectralCurve (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ) (u : ℝ) :
    scalingMap T (spectralCurve L h u) =
      collectiveMatrix T L * Matrix.diagonal (fun k : Fin n × Fin d =>
        (Real.exp (h k.2*u) : ℂ)) * (collectiveMatrix T L).conjTranspose := by
  have hi (i : Fin n) : T i * spectralCurve L h u * (T i).conjTranspose =
      (T i * L) * Matrix.diagonal (fun j => (Real.exp (h j*u) : ℂ)) *
        (T i * L).conjTranspose := by
    simp only [spectralCurve, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  ext a b
  simp only [scalingMap, Matrix.sum_apply, hi, Matrix.mul_apply,
    collectiveMatrix, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Prod.mk.injEq, ite_and]
  simp

theorem scalingPotential_strictConvex_spectralCurve
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L) (h : Fin d → ℝ)
    (j : Fin d) (hj : h j ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun u => scalingPotential T (spectralCurve L h u)) := by
  obtain ⟨i,b,hib⟩ := collectiveMatrix_column_nonzero T hexpand L hL j
  have hs := strictConvexOn_log_gram (collectiveMatrix T L) (fun k => h k.2) b (i,j) hib hj
  let c := (3/2 : ℝ)*Real.log (Complex.normSq L.det)
  let s := (3/2 : ℝ)*(∑ j, h j)
  have haff : ConcaveOn ℝ Set.univ (fun u : ℝ => c+s*u) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ x y hx hy hxy
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun z => c*z) hxy]
  have hc := hs.sub_concaveOn haff
  have he : (fun u => scalingPotential T (spectralCurve L h u)) =
      (fun u => Real.log (1 + collectiveMatrix T L * Matrix.diagonal
        (fun k : Fin n × Fin d => (Real.exp (h k.2*u) : ℂ)) * (collectiveMatrix T L).conjTranspose).det.re) -
      (fun u => c+s*u) := by
    funext u
    simp only [scalingPotential, scalingMap_spectralCurve, spectralCurve_log_det L hL,
      Pi.sub_apply, c, s]
    ring
  rw [he]
  exact hc

end Kaplansky

end

end OAI
