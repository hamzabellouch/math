import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.QuadSmulVec

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def sqNorm (x : V → ℝ) : ℝ := ∑ i, (x i)^2

lemma quad_one (x : V → ℝ) : quad (1 : Matrix V V ℝ) x=sqNorm x := by
  simp only [quad,one_mulVec,dotProduct,sqNorm,pow_two]

omit [DecidableEq V] in
lemma quad_sub_matrix (A B : Matrix V V ℝ) (x : V → ℝ) :
    quad (A-B) x=quad A x-quad B x := by simp [quad,sub_mulVec,dotProduct_sub]

omit [DecidableEq V] in
lemma quad_entry_perturb (A B : Matrix V V ℝ) (e : ℝ) (he : 0≤e)
    (hentry : ∀ i j, |A i j-B i j|≤e) (x : V → ℝ) :
    |quad A x-quad B x|≤(Fintype.card V:ℝ)*e*sqNorm x := by
  have hc : (∑ i, |x i|)^2≤(Fintype.card V:ℝ)*sqNorm x := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V) (fun _ => (1:ℝ))
      (fun i => |x i|)
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      sq_abs,sqNorm] using hh
  rw [←quad_sub_matrix]
  change |∑ i, x i * ∑ j, (A i j-B i j)*x j| ≤ _
  calc
    _ ≤ ∑ i, |x i * ∑ j, (A i j-B i j)*x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i| * |∑ j, (A i j-B i j)*x j| := by simp only [abs_mul]
    _ ≤ ∑ i, |x i| * (∑ j, e * |x j|) := by
      gcongr with i hi
      calc
        _ ≤ ∑ j, |(A i j-B i j)*x j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by apply Finset.sum_le_sum; intro j _; rw [abs_mul]; gcongr; exact hentry i j
    _ = e*(∑ i, |x i|)^2 := by rw [←Finset.mul_sum,←Finset.sum_mul]; ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc he]

omit [DecidableEq V] in
lemma posSemidef_of_quad (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (h : ∀ x, 0≤quad M x) : M.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  exact ⟨hM,by simpa only [star_trivial,quad] using h⟩

def lowerRound (Q : Matrix V V ℝ) (e : ℝ) : Matrix V V ℝ :=
  Q-((Fintype.card V:ℝ)*e) • (1 : Matrix V V ℝ)

lemma lowerRound_bounds (A Q : Matrix V V ℝ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (e : ℝ) (he : 0≤e) (hentry : ∀ i j, |Q i j-A i j|≤e) :
    (A-lowerRound Q e).PosSemidef ∧
    (lowerRound Q e-(A-((2*(Fintype.card V:ℝ)*e) • (1 : Matrix V V ℝ)))).PosSemidef := by
  have hL : (lowerRound Q e).IsHermitian := hQ.sub ((isHermitian_one).smul (IsSelfAdjoint.all _))
  have hlow : (A-(2*(Fintype.card V:ℝ)*e) • (1:Matrix V V ℝ)).IsHermitian :=
    hA.sub ((isHermitian_one).smul (IsSelfAdjoint.all _))
  constructor
  · apply posSemidef_of_quad _ (hA.sub hL)
    intro x
    have hh := (abs_le.mp (quad_entry_perturb Q A e he hentry x)).2
    simp only [quad_sub_matrix,lowerRound,quad_smul_matrix,quad_one]
    linarith
  · apply posSemidef_of_quad _ (hL.sub hlow)
    intro x
    have hh := (abs_le.mp (quad_entry_perturb Q A e he hentry x)).1
    simp only [quad_sub_matrix,lowerRound,quad_smul_matrix,quad_one]
    linarith

lemma lowerRound_relative (A Q : Matrix V V ℝ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
    (lowerRound Q e-(1-ε) • A).PosSemidef := by
  apply posSemidef_of_quad _ ((hQ.sub ((isHermitian_one).smul (IsSelfAdjoint.all _))).sub (hA.smul (IsSelfAdjoint.all _)))
  intro x
  have hq := (abs_le.mp (quad_entry_perturb Q A e he hentry x)).1
  have hb := quad_nonneg _ hm x
  have hs : 0≤ sqNorm x := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [quad_sub_matrix,quad_smul_matrix,quad_one] at hb
  have hb' := mul_le_mul_of_nonneg_left (show m*sqNorm x≤quad A x by linarith) hε
  have hp := mul_le_mul_of_nonneg_right hprecision hs
  simp only [quad_sub_matrix,quad_smul_matrix,quad_one]
  nlinarith

lemma lowerRound_pos (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε) (hε1 : ε<1)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) : (lowerRound Q e).PosDef := by
  have hrel := lowerRound_relative A Q hA.isHermitian hQ e m ε he hε hentry hm hprecision
  have hh := (hA.smul (show 0<1-ε by linarith)).add_posSemidef hrel
  have heq : (1-ε) • A+(lowerRound Q e-(1-ε) • A)=lowerRound Q e := by abel
  rwa [heq] at hh

lemma lowerRound_det (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε) (hε1 : ε<1)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
    (1-ε)^(Fintype.card V)*A.det≤(lowerRound Q e).det := by
  have hh := det_mono_posDef ((1-ε) • A) (lowerRound Q e)
    (hA.smul (show 0<1-ε by linarith))
    (lowerRound_relative A Q hA.isHermitian hQ e m ε he hε hentry hm hprecision)
  simpa only [Matrix.det_smul,smul_eq_mul] using hh

end

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma posDef_mul_inverse_vec (A : Matrix V V ℝ) (hA : A.PosDef) (x : V → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ x)=x := by
  rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec]

lemma quad_inverse_vec (A : Matrix V V ℝ) (hA : A.PosDef) (x : V → ℝ) :
    quad A (A⁻¹ *ᵥ x)=quad A⁻¹ x := by
  unfold quad
  rw [posDef_mul_inverse_vec A hA x,dotProduct_comm]

lemma inverse_antitone (A B : Matrix V V ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hBA : (B-A).PosSemidef) : (A⁻¹-B⁻¹).PosSemidef := by
  apply posSemidef_of_quad _ (hA.inv.isHermitian.sub hB.inv.isHermitian)
  intro x
  have hh := quad_nonneg A hA.posSemidef ((A⁻¹ *ᵥ x)+(-1:ℝ) • (B⁻¹ *ᵥ x))
  rw [quad_add_scaled A hA.isHermitian,quad_inverse_vec A hA x] at hh
  rw [posDef_mul_inverse_vec A hA x,dotProduct_comm (B⁻¹ *ᵥ x) x] at hh
  change 0≤quad A⁻¹ x+2*(-1)*quad B⁻¹ x+(-1)^2*quad A (B⁻¹ *ᵥ x) at hh
  have hb := quad_nonneg _ hBA (B⁻¹ *ᵥ x)
  rw [quad_sub_matrix,quad_inverse_vec B hB x] at hb
  rw [quad_sub_matrix]
  nlinarith

lemma inv_smul_real (A : Matrix V V ℝ) (hA : A.PosDef) (t : ℝ) (ht : t≠0) :
    (t • A)⁻¹=t⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    mul_inv_cancel₀ ht,one_smul]

end MetricKMedianRecovery.Ellipsoid

end OAI
