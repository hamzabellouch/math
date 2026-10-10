import Mathlib
import OAI.Analysis.Conductivity.Sources.NestedGeometry

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def squareFaceBase : Fin 4 → Fin 2 → ℝ := ![![1,0],![0,1],![-1,0],![0,-1]]
def squareFaceDirection : Fin 4 → Fin 2 → ℝ := ![![0,1],![-1,0],![0,-1],![1,0]]
def squareFace (i : Fin 4) (a : ℝ) : Fin 2 → ℝ := squareFaceBase i+a • squareFaceDirection i

def squareFaceParameter (i : Fin 4) (v : Fin 2 → ℝ) : ℝ :=
  squareFaceDirection i 0*v 0+squareFaceDirection i 1*v 1

lemma squareFace_parameter (i : Fin 4) (a r : ℝ) :
    squareFaceParameter i (r • squareFace i a)=r*a := by
  fin_cases i <;> simp [squareFaceParameter,squareFace,squareFaceBase,squareFaceDirection]

lemma squareFace_max (i : Fin 4) {a : ℝ} (ha : |a|≤1) :
    max |squareFace i a 0| |squareFace i a 1|=1 := by
  fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,abs_neg,
    max_eq_left ha,max_eq_right ha]

lemma squareFace_determinant (i : Fin 4) (a : ℝ) :
    squareFace i a 0*squareFaceDirection i 1-
      squareFaceDirection i 0*squareFace i a 1=1 := by
  fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection]

lemma squareFace_min_max (v : Fin 2 → ℝ) (hm : max |v 0| |v 1|=1) :
    ∃ i : Fin 4, ∃ a : ℝ, |a|≤1 ∧ squareFace i a=v := by
  have h0 : |v 0|≤1 := le_max_left _ _ |>.trans hm.le
  have h1 : |v 1|≤1 := le_max_right _ _ |>.trans hm.le
  rcases max_cases |v 0| |v 1| with h | h
  · have he : |v 0|=1 := h.1.symm.trans hm
    rcases abs_cases (v 0) with hp | hn
    · refine ⟨0,v 1,h1,?_⟩
      have hv : v 0=1 := hp.1.symm.trans he
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]
    · refine ⟨2,-v 1,by simpa using h1,?_⟩
      have hv : v 0= -1 := by linarith [hn.1,he]
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]
  · have he : |v 1|=1 := h.1.symm.trans hm
    rcases abs_cases (v 1) with hp | hn
    · refine ⟨1,-v 0,by simpa using h0,?_⟩
      have hv : v 1=1 := hp.1.symm.trans he
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]
    · refine ⟨3,v 0,h0,?_⟩
      have hv : v 1= -1 := by linarith [hn.1,he]
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]

def sourceRadialCenter : ℝ := (1+sourceHole)/2
def sourceRadialWidth : ℝ := (1-sourceHole)/2

def sourceCollarRadius (j : Fin 4) (t b : ℝ) : ℝ :=
  sourceRadialCenter+sourceRadialWidth*(1-t)*squareFace j b 0

def sourceCollarPiece (i j : Fin 4) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0,
    sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1,
    (1-x 0)*squareFace j (x 2) 1]

def sourceRadial (x : Fin 3 → ℝ) : ℝ := max (|x 0|/sourceLength) |x 1|

def sourceCrossCoordinates (x : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(sourceRadial x-sourceRadialCenter)/sourceRadialWidth,x 2]

def sourceCollarTime (x : Fin 3 → ℝ) : ℝ :=
  1-max |sourceCrossCoordinates x 0| |sourceCrossCoordinates x 1|

lemma sourceCollarRadius_bounds (j : Fin 4) {t b : ℝ}
    (ht : t∈Icc 0 1) (hb : |b|≤1) :
    sourceHole≤ sourceCollarRadius j t b ∧ sourceCollarRadius j t b≤1 := by
  have hq : |squareFace j b 0|≤1 := (le_max_left _ _).trans (squareFace_max j hb).le
  have hq' := abs_le.mp hq
  have hprod : |(1-t)*squareFace j b 0|≤1 := by
    rw [abs_mul,abs_of_nonneg (by linarith [ht.2] : 0≤1-t)]
    nlinarith [ht.1,ht.2]
  have hh := abs_le.mp hprod
  dsimp [sourceCollarRadius,sourceRadialCenter,sourceRadialWidth,sourceHole]
  constructor <;> linarith

lemma sourceCollarPiece_radial (i j : Fin 4) {x : Fin 3 → ℝ}
    (ht : x 0∈Icc 0 1) (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceRadial (sourceCollarPiece i j x)=sourceCollarRadius j (x 0) (x 2) := by
  have hr : 0≤ sourceCollarRadius j (x 0) (x 2) := by
    have hh := (sourceCollarRadius_bounds j ht hb).1
    dsimp [sourceHole] at hh
    linarith
  have hL : 0<sourceLength := by norm_num [sourceLength]
  simp only [sourceRadial,sourceCollarPiece,Matrix.cons_val_zero,Matrix.cons_val_one,
    abs_mul,abs_of_pos hL,abs_of_nonneg hr]
  have he : sourceLength*sourceCollarRadius j (x 0) (x 2)*|squareFace i (x 1) 0|/sourceLength =
      sourceCollarRadius j (x 0) (x 2)*|squareFace i (x 1) 0| := by
    field_simp
  rw [he,←mul_max_of_nonneg _ _ hr,squareFace_max i ha,mul_one]

lemma sourceCollarPiece_cross (i j : Fin 4) {x : Fin 3 → ℝ}
    (ht : x 0∈Icc 0 1) (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceCrossCoordinates (sourceCollarPiece i j x)=(1-x 0) • squareFace j (x 2) := by
  ext k; fin_cases k
  · change (sourceRadial (sourceCollarPiece i j x)-sourceRadialCenter)/sourceRadialWidth=
      (1-x 0)*squareFace j (x 2) 0
    rw [sourceCollarPiece_radial i j ht ha hb,sourceCollarRadius]
    simp only [add_sub_cancel_left]
    have hw : sourceRadialWidth≠0 := by norm_num [sourceRadialWidth,sourceHole]
    field_simp
  · simp [sourceCrossCoordinates,sourceCollarPiece]

lemma sourceCollarPiece_time (i j : Fin 4) {x : Fin 3 → ℝ}
    (ht : x 0∈Icc 0 1) (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceCollarTime (sourceCollarPiece i j x)=x 0 := by
  rw [sourceCollarTime,sourceCollarPiece_cross i j ht ha hb]
  simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (by linarith [ht.2] : 0≤1-x 0)]
  rw [←mul_max_of_nonneg _ _ (by linarith [ht.2] : 0≤1-x 0),squareFace_max j hb]
  ring

def sourceCollarJacobian (i j : Fin 4) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![-sourceLength*sourceRadialWidth*squareFace j (x 2) 0*squareFace i (x 1) 0,
       sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFaceDirection i 0,
       sourceLength*sourceRadialWidth*(1-x 0)*squareFaceDirection j 0*squareFace i (x 1) 0],
    ![-sourceRadialWidth*squareFace j (x 2) 0*squareFace i (x 1) 1,
       sourceCollarRadius j (x 0) (x 2)*squareFaceDirection i 1,
       sourceRadialWidth*(1-x 0)*squareFaceDirection j 0*squareFace i (x 1) 1],
    ![-squareFace j (x 2) 1,0,(1-x 0)*squareFaceDirection j 1]]

def sourceCollarDerivative (i j : Fin 4) (x : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' (sourceCollarJacobian i j x)).toContinuousLinearMap

lemma squareFace_coord_hasFDeriv (i : Fin 4) (k : Fin 2) (l : Fin 3) (x : Fin 3 → ℝ) :
    HasFDerivAt (fun y : Fin 3 → ℝ => squareFace i (y l) k)
      (squareFaceDirection i k • (ContinuousLinearMap.proj l : (Fin 3 → ℝ) →L[ℝ] ℝ)) x := by
  convert (hasFDerivAt_const (𝕜 := ℝ) (squareFaceBase i k) x).add
      ((hasFDerivAt_apply (𝕜 := ℝ) l x).mul_const (squareFaceDirection i k)) using 1 <;> first | rfl | simp

lemma sourceCollarPiece_hasFDeriv (i j : Fin 4) (x : Fin 3 → ℝ) :
    HasFDerivAt (sourceCollarPiece i j) (sourceCollarDerivative i j x) x := by
  have ht := (hasFDerivAt_const (1:ℝ) x).sub (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  have hr := (hasFDerivAt_const sourceRadialCenter x).add
    ((ht.const_mul sourceRadialWidth).mul (squareFace_coord_hasFDeriv j 0 2 x))
  have hf0 := (hr.const_mul sourceLength).mul (squareFace_coord_hasFDeriv i 0 1 x)
  have hf1 := hr.mul (squareFace_coord_hasFDeriv i 1 1 x)
  have hf2 := ht.mul (squareFace_coord_hasFDeriv j 1 2 x)
  have hcoord (k : Fin 3) : HasFDerivAt (fun y => sourceCollarPiece i j y k)
      ((ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (sourceCollarDerivative i j x)) x := by
    fin_cases k
    · convert hf0 using 1 <;> try rfl
      ext y
      simp [sourceCollarDerivative,sourceCollarJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,Matrix.mulVecBilin,
        Matrix.mulVec,Fin.sum_univ_succ,dotProduct,sourceCollarRadius]
      ring
    · convert hf1 using 1 <;> try rfl
      ext y
      simp [sourceCollarDerivative,sourceCollarJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,Matrix.mulVecBilin,
        Matrix.mulVec,Fin.sum_univ_succ,dotProduct,sourceCollarRadius]
      ring
    · convert hf2 using 1 <;> try rfl
      ext y
      simp [sourceCollarDerivative,sourceCollarJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,Matrix.mulVecBilin,
        Matrix.mulVec,Fin.sum_univ_succ,dotProduct,sourceCollarRadius]
      ring
  have hfull := hasFDerivAt_pi.mpr hcoord
  convert hfull using 1
  rfl

lemma sourceCollarPiece_contDiff (i j : Fin 4) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceCollarPiece i j) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases k <;> simp [sourceCollarPiece,sourceCollarRadius,squareFace] <;> fun_prop

lemma sourceCollarJacobian_det (i j : Fin 4) (x : Fin 3 → ℝ) :
    (sourceCollarJacobian i j x).det =
      -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0) := by
  rw [Matrix.det_fin_three]
  simp [sourceCollarJacobian]
  calc
    _= -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)*
        (squareFace i (x 1) 0*squareFaceDirection i 1-
          squareFaceDirection i 0*squareFace i (x 1) 1)*
        (squareFace j (x 2) 0*squareFaceDirection j 1-
          squareFaceDirection j 0*squareFace j (x 2) 1) := by ring
    _= _ := by rw [squareFace_determinant,squareFace_determinant]; ring

lemma sourceCollarJacobian_det_ne_zero (i j : Fin 4) {x : Fin 3 → ℝ}
    (ht : x 0∈Ico 0 1) (hb : |x 2|≤1) :
    (sourceCollarJacobian i j x).det≠0 := by
  rw [sourceCollarJacobian_det]
  have hr : 0<sourceCollarRadius j (x 0) (x 2) := by
    have hh := (sourceCollarRadius_bounds j ⟨ht.1,ht.2.le⟩ hb).1
    have hd : 0<sourceHole := by norm_num [sourceHole]
    exact hd.trans_le hh
  have hL : 0<sourceLength := by norm_num [sourceLength]
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hL.ne') hr.ne') hw.ne')
    (sub_pos.mpr ht.2).ne'

end ScalarConductivity

end

end OAI
