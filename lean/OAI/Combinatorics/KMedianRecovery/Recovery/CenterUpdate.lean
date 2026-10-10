import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.InflationPos

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma cutShape_pos (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) : (cutShape d H a).PosDef := by
  rw [cutShape_inverse d hd H hH a ha]
  exact (cutMatrix_pos d hd H⁻¹ hH.inv (normalizedDual H a)).inv

noncomputable def centerUpdate (d : ℝ) (H : Matrix V V ℝ) (a c : V → ℝ) (t : ℝ) : V → ℝ :=
  c-(1/((d+1)*t)) • (H *ᵥ a)

lemma shape_center_contains (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a c x : V → ℝ) (ha : a≠0) (t : ℝ)
    (htlo : Real.sqrt (quad H a)≤t) (hthi : t≤(1+1/(32*d))*Real.sqrt (quad H a))
    (hx : quad H⁻¹ (x-c)≤1) (hcut : a ⬝ᵥ (x-c)≤0) :
    quad ((1-1/(8*d^2)) • cutMatrix d H⁻¹ (normalizedDual H a))
      (x-centerUpdate d H a c t)≤1 := by
  obtain ⟨hq,hu,hv⟩ := dual_normal_properties H hH a ha
  let u := normalizedDual H a
  have hs : 0<Real.sqrt (quad H a) := Real.sqrt_pos.mpr hq
  have ht : 0<t := hs.trans_le htlo
  have hr := sqrt_ratio d (quad H a) t hd.le hq htlo hthi
  have hc : u ⬝ᵥ (H⁻¹ *ᵥ (x-c))≤0 := by
    rw [bilinear_symm _ hH.inv.isHermitian]
    change (x-c) ⬝ᵥ (H⁻¹ *ᵥ normalizedDual H a)≤0
    rw [hv,dotProduct_smul,smul_eq_mul,dotProduct_comm]
    exact mul_nonpos_of_nonneg_of_nonpos (one_div_nonneg.mpr hs.le) hcut
  have hh := approximate_center_contains d hd H⁻¹ hH.inv u (x-c) hu hx hc
    (Real.sqrt (quad H a)/t) hr.1 hr.2
  have he : x-centerUpdate d H a c t=(x-c)+((Real.sqrt (quad H a)/t)/(d+1)) • u := by
    ext i
    simp only [centerUpdate,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,u,normalizedDual]
    field_simp
    ring
  rwa [he]

lemma inflatedShape_inverse (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) :
    ((1/(1-1/(8*d^2))) • cutShape d H a)⁻¹ =
      (1-1/(8*d^2)) • cutMatrix d H⁻¹ (normalizedDual H a) := by
  have hl : 0<1-1/(8*d^2) := by
    have hh := inflation_bounds d hd.le
    linarith
  rw [inv_smul_real _ (cutShape_pos d hd H hH a ha) _ (one_div_ne_zero hl.ne'),
    one_div,inv_inv,cutShape_inverse d hd H hH a ha,
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (cutMatrix_pos d hd H⁻¹ hH.inv (normalizedDual H a)).det_pos.ne')]

def upperRound (Q : Matrix V V ℝ) (e : ℝ) : Matrix V V ℝ :=
  Q+((Fintype.card V:ℝ)*e) • (1 : Matrix V V ℝ)

lemma upperRound_above (A Q : Matrix V V ℝ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (e : ℝ) (he : 0≤e) (hentry : ∀ i j, |Q i j-A i j|≤e) :
    (upperRound Q e-A).PosSemidef := by
  apply posSemidef_of_quad _ ((hQ.add ((isHermitian_one).smul (IsSelfAdjoint.all _))).sub hA)
  intro x
  have hh := (abs_le.mp (quad_entry_perturb Q A e he hentry x)).1
  have hadd (B C : Matrix V V ℝ) : quad (B+C) x=quad B x+quad C x := by
    simp only [quad,add_mulVec,dotProduct_add]
  simp only [quad_sub_matrix,hadd,quad_smul_matrix,quad_one]
  linarith

lemma upperRound_relative (A Q : Matrix V V ℝ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
    ((1+ε) • A-upperRound Q e).PosSemidef := by
  apply posSemidef_of_quad _ ((hA.smul (IsSelfAdjoint.all _)).sub
    (hQ.add ((isHermitian_one).smul (IsSelfAdjoint.all _))))
  intro x
  have hq := (abs_le.mp (quad_entry_perturb Q A e he hentry x)).2
  have hb := quad_nonneg _ hm x
  have hs : 0≤ sqNorm x := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [quad_sub_matrix,quad_smul_matrix,quad_one] at hb
  have hb' := mul_le_mul_of_nonneg_left (show m*sqNorm x≤quad A x by linarith) hε
  have hp := mul_le_mul_of_nonneg_right hprecision hs
  have hadd (B C : Matrix V V ℝ) : quad (B+C) x=quad B x+quad C x := by
    simp only [quad,add_mulVec,dotProduct_add]
  simp only [quad_sub_matrix,quad_smul_matrix,hadd,quad_one]
  nlinarith

lemma upperRound_pos (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e : ℝ) (he : 0≤e) (hentry : ∀ i j, |Q i j-A i j|≤e) :
    (upperRound Q e).PosDef := by
  have hh := hA.add_posSemidef (upperRound_above A Q hA.isHermitian hQ e he hentry)
  have heq : A+(upperRound Q e-A)=upperRound Q e := by abel
  rwa [heq] at hh

lemma upperRound_inverse_bounds (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε) (hε1 : ε<1)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
    (A⁻¹-(upperRound Q e)⁻¹).PosSemidef ∧
    ((upperRound Q e)⁻¹-(1-ε) • A⁻¹).PosSemidef := by
  have hR := upperRound_pos A Q hA hQ e he hentry
  have hrel := upperRound_relative A Q hA.isHermitian hQ e m ε he hε hentry hm hprecision
  have hl : 0<1-ε := by linarith
  have hinf : ((1/(1-ε)) • A-upperRound Q e).PosSemidef := by
    apply posSemidef_of_quad _ ((hA.isHermitian.smul (IsSelfAdjoint.all _)).sub hR.isHermitian)
    intro x
    have hh := quad_nonneg _ hrel x
    have hqm := quad_nonneg A hA.posSemidef x
    have hc : 1+ε≤1/(1-ε) := (le_div_iff₀ hl).mpr (by nlinarith [sq_nonneg ε])
    have hx := mul_le_mul_of_nonneg_right hc hqm
    rw [quad_sub_matrix,quad_smul_matrix] at hh ⊢
    linarith
  constructor
  · exact inverse_antitone A _ hA hR (upperRound_above A Q hA.isHermitian hQ e he hentry)
  · have hh := inverse_antitone _ _ hR (hA.smul (one_div_pos.mpr hl)) hinf
    rw [inv_smul_real _ hA _ (one_div_ne_zero hl.ne'),one_div,inv_inv] at hh
    exact hh

def gridShape (D : ℕ) (A : Matrix V V ℚ) : Matrix V V ℚ :=
  gridMatrix D A+((Fintype.card V:ℚ)/(D:ℚ)) • (1 : Matrix V V ℚ)

lemma real_gridShape (D : ℕ) (A : Matrix V V ℚ) :
    realMatrix (gridShape D A)=upperRound (realMatrix (gridMatrix D A)) (1/(D:ℝ)) := by
  ext i j
  simp only [gridShape,realMatrix,upperRound,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast]
  congr 1
  rw [div_eq_mul_inv,one_div]
  congr 1
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

end MetricKMedianRecovery.Ellipsoid

end OAI
