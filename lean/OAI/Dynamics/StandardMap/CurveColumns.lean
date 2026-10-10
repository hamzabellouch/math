import OAI.Dynamics.StandardMap.TorusObservations

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
def complexPair (z:CurvePlane) : ℂ := ⟨z.1,z.2⟩
lemma complexPair_norm (z:CurvePlane) : ‖complexPair z‖≤2*‖z‖ := by
  have h:=Complex.norm_le_abs_re_add_abs_im (complexPair z)
  have h1:=norm_fst_le z
  have h2:=norm_snd_le z
  change |z.1|≤‖z‖ at h1
  change |z.2|≤‖z‖ at h2
  change ‖complexPair z‖≤|z.1|+|z.2| at h
  linarith
lemma complexPair_transfer (a:ℝ) (z:CurvePlane) :
    complexPair (pairTransfer a z)=transferStep a (complexPair z) := rfl
lemma curveIterVelocity_transfer (k:ℝ) (g v:ℝ → CurvePlane) (n:ℕ) (t:ℝ) :
    complexPair (curveIterVelocity k g v n t)=liftSegmentTransfer k (g t) 0 n (complexPair (v t)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change complexPair (pairTransfer (potential k (((liftStep k)^[n]) (g t)).1)
      (curveIterVelocity k g v n t))=_
    rw [complexPair_transfer,ih]
    change _=transferStep (liftSegmentCoefficient k (g t) 0 (n+1))
      (liftSegmentTransfer k (g t) 0 n (complexPair (v t)))
    congr 2
    unfold liftSegmentCoefficient
    rw [show (0:ℤ)+((n+1:ℕ):ℤ)-1=(n:ℤ) by omega]
    simp only [liftIter,zpow_natCast,Equiv.Perm.coe_pow]
lemma complex_operator_columns (A:ℂ →L[ℝ] ℂ) : ‖A‖≤‖A 1‖+‖A Complex.I‖ := by
  apply A.opNorm_le_bound (by positivity)
  intro z
  have he:z=z.re • (1:ℂ)+z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    _ = ‖z.re • A 1+z.im • A Complex.I‖ := by conv_lhs => rw [he]; rw [map_add,map_smul,map_smul]
    _ ≤ ‖z.re • A 1‖+‖z.im • A Complex.I‖ := norm_add_le _ _
    _ = |z.re| *‖A 1‖+|z.im| *‖A Complex.I‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖z‖*‖A 1‖+‖z‖*‖A Complex.I‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
    _ = _ := by ring
noncomputable def horizontalVelocity (k:ℝ) (n:ℕ) (z:CurvePlane) : CurvePlane :=
  curveIterVelocity k (fun t=>(t,z.2)) (fun _=>(1,0)) n z.1
noncomputable def verticalVelocity (k:ℝ) (n:ℕ) (z:CurvePlane) : CurvePlane :=
  curveIterVelocity k (fun t=>(z.1,t)) (fun _=>(0,1)) n z.2
lemma horizontalVelocity_eq (k:ℝ) (n:ℕ) (z:CurvePlane) :
    complexPair (horizontalVelocity k n z)=liftSegmentTransfer k z 0 n 1 := by
  convert! curveIterVelocity_transfer k (fun t=>(t,z.2)) (fun _=>(1,0)) n z.1 using 1
lemma verticalVelocity_eq (k:ℝ) (n:ℕ) (z:CurvePlane) :
    complexPair (verticalVelocity k n z)=liftSegmentTransfer k z 0 n Complex.I := by
  convert! curveIterVelocity_transfer k (fun t=>(z.1,t)) (fun _=>(0,1)) n z.2 using 1
lemma liftTransfer_columns_bound (k:ℝ) (n:ℕ) (z:CurvePlane) :
    ‖liftSegmentTransfer k z 0 n‖≤2*(‖horizontalVelocity k n z‖+‖verticalVelocity k n z‖) := by
  have h:=complex_operator_columns (liftSegmentTransfer k z 0 n)
  rw [← horizontalVelocity_eq,← verticalVelocity_eq] at h
  linarith [complexPair_norm (horizontalVelocity k n z),complexPair_norm (verticalVelocity k n z)]
lemma continuous_horizontalVelocity (k:ℝ) (n:ℕ) : Continuous (horizontalVelocity k n) := by
  have h:horizontalVelocity k n=fun z=>Complex.equivRealProdCLM (torusSegmentTransfer k (liftProjection z) 0 n 1) := by
    funext z
    rw [torusSegmentTransfer_lift,← horizontalVelocity_eq]
    rfl
  rw [h]
  apply Complex.equivRealProdCLM.continuous.comp
  exact ((continuous_torusSegmentTransfer k 0 n).comp
    ((AddCircle.continuous_mk' (1:ℝ)).prodMap (AddCircle.continuous_mk' (1:ℝ)))).clm_apply continuous_const
lemma continuous_verticalVelocity (k:ℝ) (n:ℕ) : Continuous (verticalVelocity k n) := by
  have h:verticalVelocity k n=fun z=>Complex.equivRealProdCLM (torusSegmentTransfer k (liftProjection z) 0 n Complex.I) := by
    funext z
    rw [torusSegmentTransfer_lift,← verticalVelocity_eq]
    rfl
  rw [h]
  apply Complex.equivRealProdCLM.continuous.comp
  exact ((continuous_torusSegmentTransfer k 0 n).comp
    ((AddCircle.continuous_mk' (1:ℝ)).prodMap (AddCircle.continuous_mk' (1:ℝ)))).clm_apply continuous_const
end StandardMapEntropy

end OAI
