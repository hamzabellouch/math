import Mathlib
import OAI.Analysis.Crouzeix.Definitions
import OAI.Analysis.Crouzeix.RationalEvaluation
import OAI.Analysis.Crouzeix.Realization

namespace OAI

/-! Rational Transfer. -/

noncomputable section

open Set Filter

open scoped Topology Matrix Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Realization

theorem ratFunc_denom_ne_zero_on_closedDisk (r : RatFunc ℂ) (C : ℝ)
    (h : ∀ z : ℂ, ‖z‖ < 1 → ‖RatFunc.eval (RingHom.id ℂ) z r‖ ≤ C) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → r.denom.eval z ≠ 0 := by
  let Z : Set ℂ := {z | r.denom.eval z = 0}
  have hf : Z.Finite := Polynomial.finite_setOfPred_isRoot r.denom_ne_zero
  have hd : Dense (Zᶜ) := by
    exact ((dense_univ (X := ℂ)).sdiff_finite hf).mono (fun _ hz => hz.2)
  let S : Set ℂ := {z | ‖r.num.eval z‖ ≤ C * ‖r.denom.eval z‖}
  have hS : IsClosed S := isClosed_le r.num.continuous.norm (r.denom.continuous.norm.const_mul C)
  have hs : Zᶜ ∩ Metric.ball (0 : ℂ) 1 ⊆ S := by
    rintro z ⟨hz, hz'⟩
    have hn : r.denom.eval z ≠ 0 := hz
    have hh := h z (by simpa only [Metric.mem_ball, dist_zero_right] using hz')
    simpa only [S, mem_ofPred_eq, RatFunc.eval, Polynomial.eval₂_id, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr hn)] using hh
  have hb : Metric.ball (0 : ℂ) 1 ⊆ S := by
    intro z hz
    apply closure_minimal hs hS
    exact Metric.isOpen_ball.closure_inter ⟨hd z, hz⟩
  have hc : Metric.closedBall (0 : ℂ) 1 ⊆ S := by
    simpa only [closure_ball (0 : ℂ) one_ne_zero] using closure_minimal hb hS
  intro z hz hn
  have hp := hc (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  change ‖r.num.eval z‖ ≤ C * ‖r.denom.eval z‖ at hp
  rw [hn, norm_zero, mul_zero] at hp
  have hp' : r.num.eval z = 0 := norm_le_zero_iff.mp hp
  have he := Polynomial.aeval_ne_zero_of_isCoprime r.isCoprime_num_denom z
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, hp', hn, ne_eq,
    not_true_eq_false, or_self] at he

theorem ratFunc_eval_quotient (p q : Polynomial ℂ) {z : ℂ} (hq : q.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z ((algebraMap _ (RatFunc ℂ)) p /
      (algebraMap _ (RatFunc ℂ)) q) = p.eval z / q.eval z := by
  let r : RatFunc ℂ := (algebraMap _ _) p / (algebraMap _ _) q
  have hq' : q ≠ 0 := by rintro rfl; simp at hq
  have hd : r.denom.eval z ≠ 0 := by
    intro hd
    obtain ⟨b, hb⟩ := RatFunc.denom_div_dvd p q
    apply hq
    rw [hb, Polynomial.eval_mul, hd, zero_mul]
  have he := congrArg (Polynomial.eval z)
    ((RatFunc.num_mul_eq_mul_denom_iff hq').mpr (show r = _ from rfl))
  simp only [Polynomial.eval_mul] at he
  change r.num.eval z / r.denom.eval z = _
  exact (div_eq_div_iff hd hq).mpr he

theorem map_ringInverse_of_isUnit {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) {x : A} (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  calc
    _ = (f (Ring.inverse x) * f x) * Ring.inverse (f x) := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ (hx.map f), mul_one]
    _ = _ := by rw [← map_mul, Ring.inverse_mul_cancel _ hx, map_one, one_mul]

section RationalMatrices

variable {n : ℕ}

def pencil (a : Coeff n) : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
  1 - (Polynomial.X : Polynomial ℂ) • a.map Polynomial.C

lemma mapMatrix_scalar {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (M : Matrix (Fin n) (Fin n) R) :
    f.mapMatrix (r • M) = f r • f.mapMatrix M := by
  ext i j
  exact map_mul f r (M i j)

lemma eval_constantMatrix (z : ℂ) (M : Coeff n) :
    (Polynomial.evalRingHom z).mapMatrix (M.map Polynomial.C) = M := by
  ext i j
  exact Polynomial.eval_C

lemma eval_pencil (z : ℂ) (a : Coeff n) :
    (Polynomial.evalRingHom z).mapMatrix (pencil a) = 1 - z • a := by
  rw [pencil, map_sub, map_one, mapMatrix_scalar, eval_constantMatrix]
  simp

def transferDenominator (a : Coeff n) : Polynomial ℂ := (pencil a).det

def transferNumerator (a b c d : Coeff n) : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
  transferDenominator a • d.map Polynomial.C +
    (Polynomial.X : Polynomial ℂ) • (c.map Polynomial.C * (pencil a).adjugate * b.map Polynomial.C)

def transferRational (a b c d : Coeff n) : RationalMatrix n := fun i j =>
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (transferNumerator a b c d i j) /
    (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (transferDenominator a)

lemma eval_transferDenominator (a : Coeff n) (z : ℂ) :
    (transferDenominator a).eval z = (1 - z • a).det := by
  exact ((Polynomial.evalRingHom z).map_det (pencil a)).trans
    (congrArg Matrix.det (eval_pencil z a))

lemma eval_transferNumerator (a b c d : Coeff n) (z : ℂ) :
    (Polynomial.evalRingHom z).mapMatrix (transferNumerator a b c d) =
      (1 - z • a).det • d + z • (c * (1 - z • a).adjugate * b) := by
  simp only [transferNumerator, map_add, mapMatrix_scalar, map_mul,
    eval_constantMatrix, RingHom.map_adjugate, eval_pencil]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, eval_transferDenominator]

lemma matrix_inverse_adjugate (M : Coeff n) :
    Ring.inverse M = M.det⁻¹ • M.adjugate := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_def, Ring.inverse_eq_inv]

theorem transferRational_eq (a b c d : Coeff n) {z : ℂ}
    (hz : IsUnit (1 - z • a)) :
    matrixRationalFunction (transferRational a b c d) z =
      d + z • (c * Ring.inverse (1 - z • a) * b) := by
  have hdet : (1 - z • a).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hz)
  have hq : (transferDenominator a).eval z ≠ 0 := by
    rwa [eval_transferDenominator]
  ext i j
  rw [matrixRationalFunction, transferRational, ratFunc_eval_quotient _ _ hq]
  have he := congrArg (fun M : Coeff n => M i j) (eval_transferNumerator a b c d z)
  change (transferNumerator a b c d i j).eval z = _ at he
  rw [he, eval_transferDenominator, matrix_inverse_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    mul_smul_comm, smul_mul_assoc]
  field_simp

def entryMap (i j : Fin n) : Coeff n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

end RationalMatrices

namespace Colligation

variable {n : ℕ}

def rational (C : Colligation (EuclideanSpace ℂ (Fin n))) : RationalMatrix n :=
  transferRational ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.b)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.c) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.d)

theorem rational_eq_transfer (C : Colligation (EuclideanSpace ℂ (Fin n)))
    {z : ℂ} (hz : ‖z‖ < 1) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (matrixRationalFunction C.rational z) = C.transfer z := by
  have hu : IsUnit (1 - z • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a) := by
    simpa only [map_sub, map_one, map_smul] using
      (C.one_sub_isUnit hz).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm
  rw [rational, transferRational_eq _ _ _ _ hu]
  simp only [map_add, map_smul, map_mul, StarAlgEquiv.apply_symm_apply]
  have hi : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n))
      (Ring.inverse (1 - z • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a)) =
        Ring.inverse ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n))
          (1 - z • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a)) :=
    map_ringInverse_of_isUnit (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toRingHom hu
  rw [hi]
  simp only [map_sub, map_one, map_smul, StarAlgEquiv.apply_symm_apply, transfer]

theorem norm_rational_le_openDisk (C : Colligation (EuclideanSpace ℂ (Fin n)))
    {z : ℂ} (hz : ‖z‖ < 1) : ‖matrixRationalFunction C.rational z‖ ≤ 1 := by
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (matrixRationalFunction C.rational z)‖ ≤ 1
  rw [C.rational_eq_transfer hz]
  exact C.norm_transfer_le hz

theorem rational_polesOutside (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    PolesOutside (Metric.closedBall (0 : ℂ) 1) C.rational := by
  intro i j z hz
  apply ratFunc_denom_ne_zero_on_closedDisk (C.rational i j) ‖entryMap i j‖ ?_ z
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  intro w hw
  change ‖entryMap i j (matrixRationalFunction C.rational w)‖ ≤ _
  calc
    _ ≤ ‖entryMap i j‖ * ‖matrixRationalFunction C.rational w‖ :=
      (entryMap i j).le_opNorm _
    _ ≤ ‖entryMap i j‖ * 1 :=
      mul_le_mul_of_nonneg_left (C.norm_rational_le_openDisk hw) (norm_nonneg _)
    _ = _ := mul_one _

theorem rational_extension (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) 1 ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction C.rational)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖matrixRationalFunction C.rational z‖ ≤ 1) := by
  obtain ⟨U, hU, hK, hF⟩ := rational_holomorphic_neighborhood C.rational C.rational_polesOutside
  refine ⟨⟨U,hU,hK,hF⟩, ?_⟩
  have hc : ContinuousOn (fun z => ‖matrixRationalFunction C.rational z‖)
      (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact (hF.continuousOn.mono hK).norm
  intro z hz
  apply le_on_closure (s := Metric.ball (0 : ℂ) 1)
    (fun w hw => C.norm_rational_le_openDisk
      (by simpa only [Metric.mem_ball, dist_zero_right] using hw)) hc continuousOn_const
  simpa only [closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right] using hz

end Colligation

section Transpose

variable {n : ℕ}

def conjugateVector (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => star (x.ofLp i))

lemma norm_conjugateVector (x : EuclideanSpace ℂ (Fin n)) :
    ‖conjugateVector x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, conjugateVector, norm_star]

lemma conjugate_apply (M : Coeff n) (x : EuclideanSpace ℂ (Fin n)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (M.map star) x =
      conjugateVector ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M (conjugateVector x)) := by
  apply WithLp.equiv 2 (Fin n → ℂ) |>.injective
  ext i
  simp only [WithLp.equiv_apply, Matrix.ofLp_toEuclideanCLM, conjugateVector,
    Matrix.mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma norm_conjugateMatrix_le (M : Coeff n) : ‖M.map star‖ ≤ ‖M‖ := by
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (M.map star)‖ ≤ ‖M‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M)
  intro x
  rw [conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector, ← Matrix.cstar_norm_def] using
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M).le_opNorm (conjugateVector x)

theorem norm_matrix_transpose (M : Coeff n) : ‖Mᵀ‖ = ‖M‖ := by
  have h (N : Coeff n) : ‖N.map star‖ = ‖N‖ := by
    apply le_antisymm (norm_conjugateMatrix_le N)
    have hh := norm_conjugateMatrix_le (N.map star)
    have he : (N.map star).map star = N := by ext i j; exact star_star _
    rwa [he] at hh
  rw [← h Mᵀ]
  exact Matrix.l2_opNorm_conjTranspose M

namespace Colligation

def diskExtremal (C : Colligation (EuclideanSpace ℂ (Fin n))) : RationalMatrix n :=
  C.rationalᵀ

theorem diskExtremal_function (C : Colligation (EuclideanSpace ℂ (Fin n))) (z : ℂ) :
    matrixRationalFunction C.diskExtremal z = (matrixRationalFunction C.rational z)ᵀ := rfl

theorem diskExtremal_polesOutside (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    PolesOutside (Metric.closedBall (0 : ℂ) 1) C.diskExtremal :=
  fun i j => C.rational_polesOutside j i

theorem diskExtremal_extension (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) 1 ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction C.diskExtremal)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖matrixRationalFunction C.diskExtremal z‖ ≤ 1) := by
  refine ⟨rational_holomorphic_neighborhood C.diskExtremal C.diskExtremal_polesOutside, ?_⟩
  intro z hz
  rw [C.diskExtremal_function, norm_matrix_transpose]
  exact C.rational_extension.2 z hz

end Colligation

end Transpose

end CrouzeixHilbert.Realization

end

end OAI
