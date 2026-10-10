import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.NormalizedDual
import OAI.Combinatorics.KMedianRecovery.Recovery.GridFloor

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def realVector (x : V → ℚ) : V → ℝ := fun i => (x i:ℝ)

def rationalQuad (H : Matrix V V ℚ) (a : V → ℚ) : ℚ := a ⬝ᵥ (H *ᵥ a)

def rationalCutShape (d : ℚ) (H : Matrix V V ℚ) (a : V → ℚ) : Matrix V V ℚ :=
  (d^2/(d^2-1)) • (H-(2/((d+1)*rationalQuad H a)) • vecMulVec (H *ᵥ a) (H *ᵥ a))

def rationalRootUpper (D : ℕ) (q : ℚ) : ℚ := sqrtUpperFraction q.num.natAbs q.den D

lemma rationalRootUpper_bounds (D : ℕ) (hD : 0<D) (q : ℚ) (hq : 0<q) :
    Real.sqrt (q:ℝ) ≤ (rationalRootUpper D q:ℝ) ∧
    (rationalRootUpper D q:ℝ) ≤ (1+1/(D:ℝ))*Real.sqrt (q:ℝ) := by
  have hn := Rat.num_pos.mpr hq
  have hp : 0<q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  have hc : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg hn.le
  have he : ((q.num.natAbs:ℚ)/(q.den:ℚ))=q := by
    rw [←Int.cast_natCast,hc,q.num_div_den]
  have her : (q.num.natAbs:ℝ)/(q.den:ℝ)=(q:ℝ) := by
    have hh := congrArg (fun z : ℚ => (z:ℝ)) he
    simpa only [Rat.cast_div,Rat.cast_natCast] using hh
  have hh := sqrtUpperFraction_bounds q.num.natAbs q.den D hp q.pos hD
  simpa only [her,rationalRootUpper] using hh

omit [DecidableEq V] in
lemma real_mulVec (H : Matrix V V ℚ) (x : V → ℚ) :
    realVector (H *ᵥ x)=realMatrix H *ᵥ realVector x := by
  ext i
  simp only [realVector,realMatrix,mulVec,dotProduct,Rat.cast_sum,Rat.cast_mul]

omit [DecidableEq V] in
lemma real_quad (H : Matrix V V ℚ) (x : V → ℚ) :
    (rationalQuad H x:ℝ)=quad (realMatrix H) (realVector x) := by
  simp only [rationalQuad,quad,realVector,realMatrix,mulVec,dotProduct,
    Rat.cast_sum,Rat.cast_mul]

omit [DecidableEq V] in
lemma real_cutShape (d : ℚ) (H : Matrix V V ℚ) (a : V → ℚ) :
    realMatrix (rationalCutShape d H a)=cutShape (d:ℝ) (realMatrix H) (realVector a) := by
  have hm := real_mulVec H a
  ext i j
  simp only [realMatrix,rationalCutShape,cutShape,Matrix.smul_apply,smul_eq_mul,
    Matrix.sub_apply,vecMulVec_apply,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,
    Rat.cast_one,Rat.cast_ofNat,Rat.cast_add,real_quad]
  rw [←hm]
  rfl

lemma sqrt_ratio (d q t : ℝ) (hd : 1≤d) (hq : 0<q)
    (htlo : Real.sqrt q≤t) (hthi : t≤(1+1/(32*d))*Real.sqrt q) :
    1-1/(32*d)≤Real.sqrt q/t ∧ Real.sqrt q/t≤1 := by
  have hs : 0<Real.sqrt q := Real.sqrt_pos.2 hq
  have ht : 0<t := hs.trans_le htlo
  have hδ : 0≤1/(32*d) := by positivity
  have hδ1 : 1/(32*d)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  constructor
  · apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left hthi (show 0≤1-1/(32*d) by linarith)
    have he : (1-1/(32*d))*((1+1/(32*d))*Real.sqrt q) =
        (1-(1/(32*d))^2)*Real.sqrt q := by ring
    rw [he] at hh
    have hz := mul_nonneg (sq_nonneg (1/(32*d))) hs.le
    nlinarith
  · exact (div_le_one ht).mpr htlo

end

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma quad_single (M : Matrix V V ℝ) (i : V) : quad M (Pi.single i 1)=M i i := by
  simp [quad]

lemma entry_bound_of_diagonal (M : Matrix V V ℝ) (hM : M.PosSemidef) (K : ℝ)
    (hdiag : ∀ i, M i i≤K) : ∀ i j, |M i j|≤K := by
  intro i j
  have he : (Pi.single j 1) ⬝ᵥ (M *ᵥ (Pi.single i 1))=M i j := by
    simp only [single_one_dotProduct,mulVec_single_one]
    exact (isHermitian_iff_isSymm.mp hM.isHermitian).apply _ _
  have hp := quad_nonneg M hM ((Pi.single i 1)+(1:ℝ) • (Pi.single j 1))
  have hm := quad_nonneg M hM ((Pi.single i 1)+(-1:ℝ) • (Pi.single j 1))
  rw [quad_add_scaled M hM.isHermitian,quad_single,quad_single,he] at hp hm
  exact abs_le.mpr ⟨by linarith [hdiag i,hdiag j],by linarith [hdiag i,hdiag j]⟩

lemma det_bound_of_diameters (M : Matrix V V ℝ) (hM : M.PosDef)
    (z : V → ℝ) (r : ℝ) (hr : 0<r)
    (hball : ∀ i, quad M (z+r • Pi.single i 1)≤1 ∧
      quad M (z+(-r) • Pi.single i 1)≤1) :
    M.det ≤ (Fintype.card V).factorial * (1/r^2)^(Fintype.card V) := by
  have hdiag (i : V) : M i i≤1/r^2 := by
    have hh := hball i
    rw [quad_add_scaled M hM.isHermitian,quad_single] at hh
    rw [quad_add_scaled M hM.isHermitian,quad_single] at hh
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith [quad_nonneg M hM.posSemidef z]
  have he := entry_bound_of_diagonal M hM.posSemidef (1/r^2) hdiag
  have hd := Matrix.det_le (abv:=AbsoluteValue.abs) he
  simpa only [AbsoluteValue.abs_apply,abs_of_pos hM.det_pos,nsmul_eq_mul] using hd

lemma cutMatrix_grows (M : Matrix V V ℝ) (hM : M.PosDef) (u : V → ℝ)
    (hu : quad M u=1) (hn : 2≤Fintype.card V) :
    (1+1/(Fintype.card V:ℝ))*M.det ≤ (cutMatrix (Fintype.card V) M u).det := by
  rw [cutMatrix_det _ (by exact_mod_cast (show 1<Fintype.card V by omega)) M hM u hu]
  have hh := mul_le_mul_of_nonneg_right (determinant_growth (Fintype.card V) hn) hM.det_pos.le
  simpa only [mul_div_assoc] using hh

lemma block_growth (n : ℕ) (hn : 1≤n) : (2:ℝ)≤(1+1/(n:ℝ))^n := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hq : (0:ℝ)≤1/(n:ℝ) := by positivity
  have hh := one_add_mul_le_pow (le_trans (show (-2:ℝ)≤0 by norm_num) hq) n
  simpa only [mul_one_div_cancel hn0,one_add_one_eq_two] using hh

lemma sequence_growth (M : ℕ → Matrix V V ℝ) (u : ℕ → V → ℝ)
    (hpos : ∀ t, (M t).PosDef) (hunit : ∀ t, quad (M t) (u t)=1)
    (hstep : ∀ t, M (t+1)=cutMatrix (Fintype.card V) (M t) (u t))
    (hn : 2≤Fintype.card V) (t : ℕ) :
    (1+1/(Fintype.card V:ℝ))^t*(M 0).det ≤ (M t).det := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hbase : 0≤1+1/(Fintype.card V:ℝ) := by positivity
    calc
      _ = (1+1/(Fintype.card V:ℝ))*
          ((1+1/(Fintype.card V:ℝ))^t*(M 0).det) := by rw [pow_succ]; ring
      _ ≤ (1+1/(Fintype.card V:ℝ))*(M t).det := mul_le_mul_of_nonneg_left ih hbase
      _ ≤ _ := by rw [hstep]; exact cutMatrix_grows (M t) (hpos t) (u t) (hunit t) hn

end MetricKMedianRecovery.Ellipsoid

end OAI
