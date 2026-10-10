import OAI.Analysis.Quantum.PPTSquare.ChannelModel

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m]

lemma psd_trace_bound [DecidableEq n] {A : Mat n} (hA : A.PosSemidef) :
    (Matrix.trace A • (1 : Mat n) - A).PosSemidef := by
  let U : Mat n := hA.isHermitian.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hA.isHermitian.spectral_theorem
  have hD : (Matrix.diagonal (fun i => Matrix.trace A -
      (hA.isHermitian.eigenvalues i : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    have he : hA.isHermitian.eigenvalues i ≤ ∑ j, hA.isHermitian.eigenvalues j :=
      Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
    have hc : ((hA.isHermitian.eigenvalues i : ℝ) : ℂ) ≤
        ((∑ j, hA.isHermitian.eigenvalues j : ℝ) : ℂ) := by exact_mod_cast he
    simpa using sub_nonneg.mpr hc
  have hd : Matrix.diagonal (fun i => Matrix.trace A -
        (hA.isHermitian.eigenvalues i : ℂ)) =
      Matrix.trace A • (1 : Mat n) -
        Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have hh := hD.mul_mul_conjTranspose_same U
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, ← hspec] at hh
  exact hh

lemma trace_effect_real [DecidableEq n] {F : Map n m} (hF : CP F) :
    ((Matrix.trace (effect F)).re : ℂ) = Matrix.trace (effect F) := by
  have h := Complex.nonneg_iff.mp (effect_psd hF).trace_nonneg
  apply Complex.ext <;> simp [← h.2]

lemma effect_hilbertSchmidt [DecidableEq n] [DecidableEq m] {F : Map n m} (hF : CP F)
    (X : Mat n) :
    Matrix.trace ((effect F)ᴴ * X) = Matrix.trace ((1 : Mat m)ᴴ * F X) := by
  rw [(effect_psd hF).isHermitian.eq, Matrix.conjTranspose_one, Matrix.one_mul,
    effect_trace]

lemma coefficient_exact [DecidableEq n] {F : Map n m} (hF : CP F) :
    (coefficient F : ℂ) = 1 / (1 + Matrix.trace (effect F)) := by
  rw [← trace_effect_real hF]
  simp only [coefficient, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add]

lemma coefficient_trace [DecidableEq n] {F : Map n m} (hF : CP F) :
    (coefficient F : ℂ) * (1 + Matrix.trace (effect F)) = 1 := by
  rw [← trace_effect_real hF]
  have ht : 0 ≤ (Matrix.trace (effect F)).re :=
    (Complex.nonneg_iff.mp (effect_psd hF).trace_nonneg).1
  simp only [coefficient, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add]
  exact div_mul_cancel₀ _ (by exact_mod_cast (show (1 : ℝ) +
    (Matrix.trace (effect F)).re ≠ 0 by linarith))

lemma defect_psd [DecidableEq n] {F : Map n m} (hF : CP F) : (defect F).PosSemidef := by
  have hc : (0 : ℂ) ≤ coefficient F := by exact_mod_cast (coefficient_pos hF).le
  have he : defect F = (coefficient F : ℂ) •
      (Matrix.trace (effect F) • (1 : Mat n) - effect F) +
      (coefficient F : ℂ) • (1 : Mat n) := by
    have hs : (coefficient F : ℂ) * Matrix.trace (effect F) + (coefficient F : ℂ) = 1 := by
      linear_combination coefficient_trace hF
    rw [smul_sub, smul_smul]
    unfold defect
    have hs' : (coefficient F : ℂ) * Matrix.trace (effect F) = 1 - (coefficient F : ℂ) := by
      linear_combination hs
    rw [hs', sub_smul, one_smul]
    module
  rw [he]
  exact ((psd_trace_bound (effect_psd hF)).smul hc).add (Matrix.PosSemidef.one.smul hc)

end ChannelCompletion

namespace ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m]

lemma partial_trace_psd {k : Type} [Fintype k] {X : Mat (k × n)} (hX : X.PosSemidef) :
    Matrix.PosSemidef (fun a b : k => Matrix.trace (fun i j : n => X (a,i) (b,j))) := by
  have he : (fun a b : k => Matrix.trace (fun i j : n => X (a,i) (b,j))) =
      ∑ i : n, X.submatrix (fun a => (a,i)) (fun a => (a,i)) := by
    ext a b
    simp [Matrix.trace, Matrix.diag, Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun i _ => hX.submatrix _)

lemma flag_psd (d : ℕ) : (flagProjection d).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (Pi.single (flag d) (1 : ℂ))
  simpa [flagProjection, Matrix.single_eq_single_vecMulVec_single] using h

def prepareTrace (d : ℕ) : Map n (Space d) where
  toFun X := Matrix.trace X • flagProjection d
  map_add' X Y := by simp [add_smul]
  map_smul' c X := by simp [smul_smul]

lemma cp_prepareTrace (d : ℕ) : CP (prepareTrace (n := n) d) := by
  classical
  intro k _ X hX
  let Y : Mat k := fun a b => Matrix.trace (fun i j : n => X (a,i) (b,j))
  have hY : Y.PosSemidef := partial_trace_psd hX
  change (Y ⊗ₖ flagProjection d).PosSemidef
  exact hY.kronecker (flag_psd d)

def measureFlag (d : ℕ) (A : Mat n) : Map n (Space d) where
  toFun X := Matrix.trace (A * X) • flagProjection d
  map_add' X Y := by simp [Matrix.mul_add, add_smul]
  map_smul' c X := by simp [smul_smul]

lemma cp_measureFlag (d : ℕ) {A : Mat n} (hA : A.PosSemidef) : CP (measureFlag d A) := by
  classical
  let R : Mat n := CFC.sqrt A
  have hR : Rᴴ * R = A := by
    have hh : R.IsHermitian :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
    rw [hh.eq]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have he : measureFlag d A = (prepareTrace d).comp (ad R) := by
    ext X i j
    simp only [measureFlag, prepareTrace, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.comp_apply, ad_apply]
    rw [Matrix.trace_mul_cycle, hR]
  rw [he]
  exact cp_comp (cp_prepareTrace d) (cp_ad R)

end ChannelCompletion

end

end OAI
