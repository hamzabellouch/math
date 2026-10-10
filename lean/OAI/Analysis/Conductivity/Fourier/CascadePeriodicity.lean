import Mathlib
import OAI.Analysis.Conductivity.Branching.Ending
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly
import OAI.Analysis.Conductivity.Fourier.AngularPeriodization

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def angularInteger (n : Fin 2 → ℤ) : Fin 3 → ℤ := ![0,n 0,n 1]

lemma angularShift_apply (T : ℝ) (n : Fin 2 → ℤ) (i : Fin 3) :
    angularShift T n i=T*(angularInteger n i:ℝ) := by
  fin_cases i <;> simp [angularShift,angularInteger]

lemma sin_int_angular_shift (q : ℤ) (n : Fin 2 → ℤ) (x : Coord3) (i : Fin 3) :
    sin ((q:ℝ)*(x+angularShift (2*Real.pi) n) i)=sin ((q:ℝ)*x i) := by
  have he : (q:ℝ)*(x+angularShift (2*Real.pi) n) i=
      (q:ℝ)*x i+((q*angularInteger n i:ℤ):ℝ)*(2*Real.pi) := by
    simp only [Pi.add_apply,angularShift_apply,Int.cast_mul]
    ring
  rw [he,sin_add_int_mul_two_pi]

lemma cos_int_angular_shift (q : ℤ) (n : Fin 2 → ℤ) (x : Coord3) (i : Fin 3) :
    cos ((q:ℝ)*(x+angularShift (2*Real.pi) n) i)=cos ((q:ℝ)*x i) := by
  have he : (q:ℝ)*(x+angularShift (2*Real.pi) n) i=
      (q:ℝ)*x i+((q*angularInteger n i:ℤ):ℝ)*(2*Real.pi) := by
    simp only [Pi.add_apply,angularShift_apply,Int.cast_mul]
    ring
  rw [he,cos_add_int_mul_two_pi]

lemma cascadeTerm_angularPeriodic (L K A : ℝ) (k : ℤ) (j : ℕ) :
    AngularPeriodic (2*Real.pi) (cascadeTerm L K k A j) := by
  intro n x
  have hc := cos_int_angular_shift (k*2^j) n x (cascadeAxis j)
  push_cast at hc
  simpa only [cascadeTerm,Pi.add_apply,angularShift,Matrix.cons_val_zero,add_zero] using
    congrArg (fun z => (A*cascadeRatio L K^j)*
      cascadeProfile L K (cascadePhase (cascadeLength L K) k j (x 0))*z) hc

lemma cascadeValue_angularPeriodic (L K A : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (cascadeValue L K k A) := by
  intro n x
  apply tsum_congr
  intro j
  exact cascadeTerm_angularPeriodic L K A k j n x

lemma crossingTensor_angularPeriodic (L : ℝ) (a b : Fin 3) :
    AngularPeriodic (2*Real.pi) (crossingTensor L a b) := by
  intro n x
  have hs (i : Fin 3) : sin ((x+angularShift (2*Real.pi) n) i)=sin (x i) := by
    simpa using sin_int_angular_shift 1 n x i
  have hc (i : Fin 3) : cos ((x+angularShift (2*Real.pi) n) i)=cos (x i) := by
    simpa using cos_int_angular_shift 1 n x i
  have hs2 (i : Fin 3) : sin (2*(x+angularShift (2*Real.pi) n) i)=sin (2*x i) := by
    simpa using sin_int_angular_shift 2 n x i
  have hc2 (i : Fin 3) : cos (2*(x+angularShift (2*Real.pi) n) i)=cos (2*x i) := by
    simpa using cos_int_angular_shift 2 n x i
  have hzero : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  ext i j
  simp only [crossingTensor,crossingXX,crossingYY,crossingXY,crossingHxx,crossingHxy,
    one_mul,hs,hc,hs2,hc2,hzero]

lemma angularShift_dilation (q : ℤ) (n : Fin 2 → ℤ) (x c d : Coord3) :
    (q:ℝ) • (x+angularShift (2*Real.pi) n-c)-d=
      ((q:ℝ) • (x-c)-d)+angularShift (2*Real.pi) (fun i => q*n i) := by
  have hshift : (q:ℝ) • angularShift (2*Real.pi) n=
      angularShift (2*Real.pi) (fun i => q*n i) := by
    ext i
    fin_cases i
    · change (q:ℝ)*0=0
      ring
    · change (q:ℝ)*((2*Real.pi)*(n 0:ℝ))=(2*Real.pi)*((q*n 0:ℤ):ℝ)
      push_cast
      ring
    · change (q:ℝ)*((2*Real.pi)*(n 1:ℝ))=(2*Real.pi)*((q*n 1:ℤ):ℝ)
      push_cast
      ring
  rw [smul_sub,smul_add,smul_sub,hshift]
  abel

lemma cascadeStageTensor_angularPeriodic (L K : ℝ) (k : ℤ) (j : ℕ) :
    AngularPeriodic (2*Real.pi) (cascadeStageTensor L K k j) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  unfold cascadeStageTensor
  rw [hs]
  split_ifs
  · rfl
  · have he := angularShift_dilation (k*2^j) n x (cascadeCenter (cascadeLength L K) k j)
        (Pi.single 0 (K+2+L))
    push_cast at he
    rw [he,crossingTensor_angularPeriodic]

lemma cascadeTensor_angularPeriodic (L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (cascadeTensor L K k) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  have hi : cascadeIndex (cascadeLength L K) k (x+angularShift (2*Real.pi) n)=
      cascadeIndex (cascadeLength L K) k x := by simp only [cascadeIndex,hs]
  unfold cascadeTensor
  rw [hs,hi]
  split_ifs
  · exact cascadeStageTensor_angularPeriodic L K k _ n x
  · rfl

lemma cascadeValue_one_angularPeriodic (L K A : ℝ) :
    AngularPeriodic (2*Real.pi) (cascadeValue L K 1 A) := by
  simpa only [Int.cast_one] using (cascadeValue_angularPeriodic L K A (1:ℤ))

lemma cascadeTensor_one_angularPeriodic (L K : ℝ) :
    AngularPeriodic (2*Real.pi) (cascadeTensor L K 1) := by
  simpa only [Int.cast_one] using (cascadeTensor_angularPeriodic L K (1:ℤ))

lemma finiteEndingValue_angularPeriodic (a J L K : ℝ) :
    AngularPeriodic (2*Real.pi) (finiteEndingValue a J L K) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  have he : x+angularShift (2*Real.pi) n-Pi.single 0 (J+2)=
      (x-Pi.single 0 (J+2))+angularShift (2*Real.pi) n := by abel
  unfold finiteEndingValue
  rw [hs]
  split_ifs
  · unfold pureModeValue
    rw [hs]
    have hh := cos_int_angular_shift 1 n x 1
    simpa using congrArg (fun z => initialConnectorProfile a (1/2) J (x 0)*z) hh
  · rw [he]
    apply cascadeValue_one_angularPeriodic

lemma finiteEndingTensor_angularPeriodic (a J L K : ℝ) :
    AngularPeriodic (2*Real.pi) (finiteEndingTensor a J L K) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  have he : x+angularShift (2*Real.pi) n-Pi.single 0 (J+2)=
      (x-Pi.single 0 (J+2))+angularShift (2*Real.pi) n := by abel
  unfold finiteEndingTensor
  rw [hs]
  split_ifs
  · rfl
  · rw [he]
    exact cascadeTensor_one_angularPeriodic L K n (x-Pi.single 0 (J+2))

end ScalarConductivity

end

end OAI
