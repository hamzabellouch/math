import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CenterUpdate

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma rational_symm_of_real (A : Matrix V V ℚ) (hA : (realMatrix A).IsHermitian) : A.IsSymm := by
  have hh := (isHermitian_iff_isSymm.mp hA)
  ext i j
  exact Rat.cast_injective (hh.apply i j : (A j i:ℝ)=(A i j:ℝ))

omit [Fintype V] [DecidableEq V] in
lemma real_smul_matrix (r : ℚ) (A : Matrix V V ℚ) :
    realMatrix (r • A)=(r:ℝ) • realMatrix A := by
  ext i j
  simp only [realMatrix,Matrix.smul_apply,smul_eq_mul,Rat.cast_mul]

def rationalInflatedShape (H : Matrix V V ℚ) (a : V → ℚ) : Matrix V V ℚ :=
  (1/(1-1/(8*(Fintype.card V:ℚ)^2))) • rationalCutShape (Fintype.card V) H a

def rationalStepShape (D : ℕ) (H : Matrix V V ℚ) (a : V → ℚ) : Matrix V V ℚ :=
  gridShape D (rationalInflatedShape H a)

def rationalStepCenter (H : Matrix V V ℚ) (a c : V → ℚ) : V → ℚ :=
  c-(1/(((Fintype.card V:ℚ)+1)*rationalRootUpper (32*Fintype.card V) (rationalQuad H a))) • (H *ᵥ a)

omit [DecidableEq V] in
lemma real_inflatedShape (H : Matrix V V ℚ) (a : V → ℚ) :
    realMatrix (rationalInflatedShape H a)=
      (1/(1-1/(8*(Fintype.card V:ℝ)^2))) • cutShape (Fintype.card V) (realMatrix H) (realVector a) := by
  simp only [rationalInflatedShape,real_smul_matrix,real_cutShape,Rat.cast_div,
    Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast]

omit [DecidableEq V] in
lemma real_stepCenter (H : Matrix V V ℚ) (a c : V → ℚ) :
    realVector (rationalStepCenter H a c)=centerUpdate (Fintype.card V) (realMatrix H)
      (realVector a) (realVector c) (rationalRootUpper (32*Fintype.card V) (rationalQuad H a)) := by
  have hh := real_mulVec H a
  ext i
  simp only [rationalStepCenter,realVector,centerUpdate,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast]
  congr 2
  exact congrArg (fun v : V → ℝ => v i) hh

omit [Fintype V] [DecidableEq V] in
lemma realVector_ne_zero (a : V → ℚ) (ha : a≠0) : realVector a≠0 := by
  intro he
  apply ha
  ext i
  apply Rat.cast_injective (α:=ℝ)
  simpa only [realVector,Pi.zero_apply,Rat.cast_zero] using congrFun he i

lemma stepShape_pos_bounds (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) (m : ℝ)
    (hm : (realMatrix (rationalInflatedShape H a)-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)/(D:ℝ)≤(1/(8*(Fintype.card V:ℝ)^2))*m) :
    (realMatrix (rationalStepShape D H a)).PosDef ∧
    ((realMatrix (rationalInflatedShape H a))⁻¹-(realMatrix (rationalStepShape D H a))⁻¹).PosSemidef ∧
    ((realMatrix (rationalStepShape D H a))⁻¹-
      (1-1/(8*(Fintype.card V:ℝ)^2)) • (realMatrix (rationalInflatedShape H a))⁻¹).PosSemidef := by
  have hn' : 1<(Fintype.card V:ℝ) := by exact_mod_cast (show 1<Fintype.card V by omega)
  have hp : (realMatrix (rationalInflatedShape H a)).PosDef := by
    rw [real_inflatedShape]
    exact (cutShape_pos _ hn' _ hH _ (realVector_ne_zero a ha)).smul
      (one_div_pos.mpr (inflation_pos _ (by omega)))
  have hsym := realMatrix_symm _ (gridMatrix_symm D _ (rational_symm_of_real _ hp.isHermitian))
  have herr := gridMatrix_error D hD (rationalInflatedShape H a)
  have hh := upperRound_inverse_bounds _ _ hp hsym (1/(D:ℝ)) m (1/(8*(Fintype.card V:ℝ)^2))
    (by positivity) (by positivity) (by linarith [inflation_pos (Fintype.card V) (by omega)]) herr hm
    (by simpa only [div_eq_mul_inv,one_mul] using hprecision)
  have hpos := upperRound_pos _ _ hp hsym (1/(D:ℝ)) (by positivity) herr
  rw [rationalStepShape,real_gridShape]
  exact ⟨hpos,hh⟩

lemma rational_step_contains (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a c : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0)
    (x : V → ℝ) (hx : quad (realMatrix H)⁻¹ (x-realVector c)≤1)
    (hcut : realVector a ⬝ᵥ (x-realVector c)≤0) :
    quad (realMatrix (rationalStepShape D H a))⁻¹
      (x-realVector (rationalStepCenter H a c))≤1 := by
  have hn' : 1<(Fintype.card V:ℝ) := by exact_mod_cast (show 1<Fintype.card V by omega)
  have hq : 0<(rationalQuad H a:ℝ) := by
    rw [real_quad]
    exact (dual_normal_properties _ hH _ (realVector_ne_zero a ha)).1
  have hr := rationalRootUpper_bounds (32*Fintype.card V) (by omega) (rationalQuad H a)
    ((Rat.cast_pos (K:=ℝ)).mp hq)
  have hrr : (32*Fintype.card V:ℕ)=(32:ℝ)*(Fintype.card V:ℝ) := by push_cast; rfl
  rw [hrr,real_quad] at hr
  have hc := shape_center_contains _ hn' _ hH _ (realVector c) x (realVector_ne_zero a ha)
    _ hr.1 hr.2 hx hcut
  have hA : (realMatrix (rationalInflatedShape H a)).PosDef := by
    rw [real_inflatedShape]
    exact (cutShape_pos _ hn' _ hH _ (realVector_ne_zero a ha)).smul
      (one_div_pos.mpr (inflation_pos _ (by omega)))
  have hsym := realMatrix_symm _ (gridMatrix_symm D _ (rational_symm_of_real _ hA.isHermitian))
  have herr := gridMatrix_error D hD (rationalInflatedShape H a)
  have hR := upperRound_pos _ _ hA hsym _ (by positivity) herr
  have ho := inverse_antitone _ _ hA hR (upperRound_above _ _ hA.isHermitian hsym _ (by positivity) herr)
  rw [←real_gridShape] at ho
  have hh := quad_le_of_sub _ _ ho (x-realVector (rationalStepCenter H a c))
  rw [real_inflatedShape,inflatedShape_inverse _ hn' _ hH _ (realVector_ne_zero a ha),real_stepCenter] at hh
  simpa only [rationalStepShape,real_stepCenter] using hh.trans hc

lemma rational_step_growth (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) (m : ℝ)
    (hm : (realMatrix (rationalInflatedShape H a)-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)/(D:ℝ)≤(1/(8*(Fintype.card V:ℝ)^2))*m) :
    (1+1/(2*(Fintype.card V:ℝ)))*(realMatrix H)⁻¹.det≤
      (realMatrix (rationalStepShape D H a))⁻¹.det := by
  have hn' : 1<(Fintype.card V:ℝ) := by exact_mod_cast (show 1<Fintype.card V by omega)
  have hh := (stepShape_pos_bounds D hD H a hn hH ha m hm hprecision).2.2
  rw [real_inflatedShape,inflatedShape_inverse _ hn' _ hH _ (realVector_ne_zero a ha)] at hh
  exact robust_cut_det _ _ hH.inv _ (dual_normal_properties _ hH _ (realVector_ne_zero a ha)).2.1 hn hh

end MetricKMedianRecovery.Ellipsoid

end OAI
