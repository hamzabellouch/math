import Mathlib
import OAI.Probability.IsingPerceptron.BoundedTiltAverage

namespace OAI

/-! Gaussian Family Generator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianFamily_hasFDerivAt {U T X XX : ℝ × ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hU : Measurable U) (hT : Measurable T) (hX : Measurable X) (hXX : Measurable XX)
    {K CT CX CXX : ℝ} (hK : ∀ p, |U p| ≤ K)
    (hCT : ∀ p, p.1 ∈ I → |T p| ≤ CT) (hCX : ∀ p, |X p| ≤ CX) (hCXX : ∀ p, |XX p| ≤ CXX)
    (hd : ∀ p, p.1 ∈ I → HasFDerivAt U (pairLinear (T p) (X p)) p)
    (dx : ∀ t y, HasDerivAt (fun x => U (t,x)) (X (t,y)) y)
    (dxx : ∀ t y, HasDerivAt (fun x => X (t,x)) (XX (t,y)) y)
    (a v d : ℝ) {m : ℝ} (hm : 0 < m) (hs : ∀ t ∈ I, m ≤ a+v*t)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTransform (a+v*q.1) d (fun y => U (q.1,y)) q.2)
      (pairLinear
        (gaussianTiltAverage (a+v*p.1) d (fun y => U (p.1,y)) (fun y => T (p.1,y)) p.2 +
          v/2*gaussianTiltAverage (a+v*p.1) d (fun y => U (p.1,y))
            (fun y => XX (p.1,y)+d*(X (p.1,y))^2) p.2)
        (gaussianTiltAverage (a+v*p.1) d (fun y => U (p.1,y)) (fun y => X (p.1,y)) p.2)) p := by
  let r := Real.sqrt (a+v*p.1)
  let ν := (gaussianReal 0 1).tilted (fun z => d*U (p.1,p.2+r*z))
  have hU0 : Measurable (fun z => U (p.1,p.2+r*z)) := hU.comp (by fun_prop)
  have hX0 : Measurable (fun z => X (p.1,p.2+r*z)) := hX.comp (by fun_prop)
  have hT0 : Measurable (fun z => T (p.1,p.2+r*z)) := hT.comp (by fun_prop)
  have hiX : Integrable (fun z => X (p.1,p.2+r*z)) ν :=
    integrable_tilt_of_bound (gaussianReal 0 1) hU0 hX0.aestronglyMeasurable
      (fun z => hK _) (B := fun _ => CX) (fun z => by simpa only [Real.norm_eq_abs] using hCX _)
      (integrable_const _) d
  have hiT : Integrable (fun z => T (p.1,p.2+r*z)) ν :=
    integrable_tilt_of_bound (gaussianReal 0 1) hU0 hT0.aestronglyMeasurable
      (fun z => hK _) (B := fun _ => CT) (fun z => by simpa only [Real.norm_eq_abs] using hCT (p.1,p.2+r*z) hp)
      (integrable_const _) d
  have hiZX : Integrable (fun z => z*X (p.1,p.2+r*z)) ν := by
    apply integrable_tilt_of_bound (gaussianReal 0 1) hU0 (measurable_id.mul hX0).aestronglyMeasurable
      (fun z => hK _) (B := fun z => |z| * CX) ?_ ?_ d
    · intro z
      change |z*X (p.1,p.2+r*z)| ≤ _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCX _) (abs_nonneg _)
    · exact (((memLp_id_gaussianReal 1).integrable le_rfl).abs).mul_const _
  have hefun : (fun z => T (p.1,p.2+r*z)+X (p.1,p.2+r*z)*(v/(2*r)*z)) =
      fun z => T (p.1,p.2+r*z)+(v/(2*r))*(z*X (p.1,p.2+r*z)) := by ext z; ring
  have hiA : Integrable (fun z => T (p.1,p.2+r*z)+X (p.1,p.2+r*z)*(v/(2*r)*z)) ν := by
    rw [hefun]; exact hiT.add (hiZX.const_mul _)
  have hraw := gaussianFamily_raw_hasFDerivAt hI hU hT hX hK hCT hCX hd a v d hm hs hp
  change HasFDerivAt _ (∫ z, pairLinear (T (p.1,p.2+r*z)+X (p.1,p.2+r*z)*(v/(2*r)*z))
    (X (p.1,p.2+r*z)) ∂ν) p at hraw
  rw [integral_pairLinear ν hiA hiX] at hraw
  have he : (∫ z, T (p.1,p.2+r*z)+X (p.1,p.2+r*z)*(v/(2*r)*z) ∂ν) =
      (∫ z, T (p.1,p.2+r*z) ∂ν) + v/2*(∫ z, XX (p.1,p.2+r*z)+d*(X (p.1,p.2+r*z))^2 ∂ν) := by
    rw [hefun,integral_add hiT (hiZX.const_mul _),integral_const_mul]
    have hibp := gaussian_tilted_ibp
      (U := fun y => U (p.1,y)) (D := fun y => X (p.1,y)) (DD := fun y => XX (p.1,y))
      (hU.comp (by fun_prop)) (hX.comp (by fun_prop)) (hXX.comp (by fun_prop))
      (fun y => hK _) (fun y => hCX _) (fun y => hCXX _) (dx p.1) (dxx p.1) r d p.2
    change (∫ z, z*X (p.1,p.2+r*z) ∂ν) = r*(∫ z, XX (p.1,p.2+r*z)+d*(X (p.1,p.2+r*z))^2 ∂ν) at hibp
    rw [hibp]
    have hr : r ≠ 0 := (Real.sqrt_pos.2 (hm.trans_le (hs _ hp))).ne'
    field_simp [hr]
  rw [he] at hraw
  exact hraw

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

structure GaussianFamily (I : Set ℝ) where
  U : ℝ × ℝ → ℝ
  X : ℝ × ℝ → ℝ
  XX : ℝ × ℝ → ℝ
  T : ℝ × ℝ → ℝ
  KU : ℝ
  KX : ℝ
  KXX : ℝ
  KT : ℝ
  mU : Measurable U
  mX : Measurable X
  mXX : Measurable XX
  mT : Measurable T
  bU : ∀ p, |U p| ≤ KU
  bX : ∀ p, |X p| ≤ KX
  bXX : ∀ p, |XX p| ≤ KXX
  bT : ∀ p, p.1 ∈ I → |T p| ≤ KT
  derivative : ∀ p, p.1 ∈ I → HasFDerivAt U (pairLinear (T p) (X p)) p
  spatial : ∀ t x, HasDerivAt (fun y => U (t,y)) (X (t,x)) x
  second : ∀ t x, HasDerivAt (fun y => X (t,y)) (XX (t,x)) x

def familyAverage (a v d : ℝ) (U A : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage (a+v*p.1) d (fun y => U (p.1,y)) (fun y => A (p.1,y)) p.2

def familyTransform (a v d : ℝ) (U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTransform (a+v*p.1) d (fun y => U (p.1,y)) p.2

lemma familyAverage_measurable {U A : ℝ × ℝ → ℝ} (hU : Measurable U)
    (hA : Measurable A) (a v d : ℝ) : Measurable (familyAverage a v d U A) := by
  exact measurable_gaussianTiltAverage_param (hU.comp (by fun_prop)) (hA.comp (by fun_prop))
    (by fun_prop) (by fun_prop) d

lemma familyTransform_measurable {U : ℝ × ℝ → ℝ} (hU : Measurable U)
    (a v d : ℝ) : Measurable (familyTransform a v d U) := by
  exact measurable_gaussianTransform_param (hU.comp (by fun_prop)) (by fun_prop) (by fun_prop) d

lemma familyAverage_bound {U A : ℝ × ℝ → ℝ} (hU : Measurable U)
    (hA : Measurable A) {K C : ℝ} (hK : ∀ p, |U p| ≤ K) (hC : ∀ p, |A p| ≤ C)
    (a v d : ℝ) (p : ℝ × ℝ) : |familyAverage a v d U A p| ≤ C := by
  exact gaussianTiltAverage_abs_le _ _ (hU.comp (by fun_prop)) (fun y => hK _)
    (hA.comp (by fun_prop)) (fun y => hC _) p.2

lemma familyAverage_local_bound {U A : ℝ × ℝ → ℝ} {I : Set ℝ} (hU : Measurable U)
    (hA : Measurable A) {K C : ℝ} (hK : ∀ p, |U p| ≤ K)
    (hC : ∀ p, p.1 ∈ I → |A p| ≤ C) (a v d : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    |familyAverage a v d U A p| ≤ C := by
  exact gaussianTiltAverage_abs_le _ _ (hU.comp (by fun_prop)) (fun y => hK _)
    (hA.comp (by fun_prop)) (fun y => hC (p.1,y) hp) p.2

lemma square_bound {x C : ℝ} (h : |x| ≤ C) : |x^2| ≤ C^2 := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

namespace GaussianFamily
variable {I : Set ℝ} (F : GaussianFamily I)

def newX (a v d : ℝ) := familyAverage a v d F.U F.X

def newXX (a v d : ℝ) (p : ℝ × ℝ) :=
  familyAverage a v d F.U F.XX p +
    d*(familyAverage a v d F.U (fun q => (F.X q)^2) p - (F.newX a v d p)^2)

def newT (a v d : ℝ) (p : ℝ × ℝ) :=
  familyAverage a v d F.U F.T p +
    v/2*familyAverage a v d F.U (fun q => F.XX q+d*(F.X q)^2) p

lemma bound_newX (a v d : ℝ) (p : ℝ × ℝ) : |F.newX a v d p| ≤ F.KX :=
  familyAverage_bound F.mU F.mX F.bU F.bX a v d p

lemma bound_newXX (a v d : ℝ) (p : ℝ × ℝ) :
    |F.newXX a v d p| ≤ F.KXX+2*|d| * F.KX^2 := by
  have h1 := familyAverage_bound F.mU F.mXX F.bU F.bXX a v d p
  have h2 := familyAverage_bound F.mU (F.mX.pow_const 2) F.bU
    (fun q => square_bound (F.bX q)) a v d p
  have h3 := square_bound (F.bound_newX a v d p)
  unfold newXX
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hs := abs_sub (familyAverage a v d F.U (fun q => (F.X q)^2) p) ((F.newX a v d p)^2)
  calc
    _ ≤ F.KXX+|d| * (F.KX^2+F.KX^2) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left (hs.trans (add_le_add h2 h3)) (abs_nonneg _))
    _ = _ := by ring

lemma bound_newT (a v d : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    |F.newT a v d p| ≤ F.KT+|v|/2*(F.KXX+|d| * F.KX^2) := by
  have h1 := familyAverage_local_bound F.mU F.mT F.bU F.bT a v d hp
  have hB : ∀ q, |F.XX q+d*(F.X q)^2| ≤ F.KXX+|d| * F.KX^2 := by
    intro q
    refine (abs_add_le _ _).trans (add_le_add (F.bXX q) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (square_bound (F.bX q)) (abs_nonneg _)
  have h2 := familyAverage_bound F.mU (F.mXX.add (measurable_const.mul (F.mX.pow_const 2))) F.bU hB a v d p
  unfold newT
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity))

lemma spatial_newX (a v d t x : ℝ) :
    HasDerivAt (fun y => familyTransform a v d F.U (t,y)) (F.newX a v d (t,x)) x := by
  convert gaussianTransform_hasDerivAt (F.mU.comp (by fun_prop)) (F.mX.comp (by fun_prop))
    (fun y => F.bU _) (fun y => F.bX _) (F.spatial t) (a+v*t) d x using 1 <;> rfl

lemma spatial_newXX (a v d t x : ℝ) :
    HasDerivAt (fun y => F.newX a v d (t,y)) (F.newXX a v d (t,x)) x := by
  have h := gaussianTiltAverage_hasDerivAt (F.mU.comp (by fun_prop)) (F.mX.comp (by fun_prop))
    (F.mX.comp (by fun_prop)) (F.mXX.comp (by fun_prop))
    (fun y => F.bU _) (fun y => F.bX _) (fun y => F.bX _) (fun y => F.bXX _)
    (F.spatial t) (F.second t) (a+v*t) d x
  convert h using 1 <;> try rfl
  simp [newX,newXX,familyAverage,pow_two]
  rfl

lemma measurable_newXX (a v d : ℝ) : Measurable (F.newXX a v d) :=
  (familyAverage_measurable F.mU F.mXX _ _ _).add (measurable_const.mul
    ((familyAverage_measurable F.mU (F.mX.pow_const 2) _ _ _).sub
      ((familyAverage_measurable F.mU F.mX _ _ _).pow_const 2)))

lemma measurable_newT (a v d : ℝ) : Measurable (F.newT a v d) :=
  (familyAverage_measurable F.mU F.mT _ _ _).add (measurable_const.mul
    (familyAverage_measurable F.mU (F.mXX.add (measurable_const.mul (F.mX.pow_const 2))) _ _ _))

 
def transform (hI : IsOpen I) (a v : ℝ) {d : ℝ} (hd : 0 ≤ d)
    {m : ℝ} (hm : 0 < m) (hs : ∀ t ∈ I, m ≤ a+v*t) : GaussianFamily I where
  U := familyTransform a v d F.U
  X := F.newX a v d
  XX := F.newXX a v d
  T := F.newT a v d
  KU := F.KU
  KX := F.KX
  KXX := F.KXX+2*|d| * F.KX^2
  KT := F.KT+|v|/2*(F.KXX+|d| * F.KX^2)
  mU := familyTransform_measurable F.mU a v d
  mX := familyAverage_measurable F.mU F.mX a v d
  mXX := F.measurable_newXX a v d
  mT := F.measurable_newT a v d
  bU := fun p => gaussianTransform_abs_le (F.mU.comp (by fun_prop)) (fun y => F.bU _) _ hd _
  bX := F.bound_newX a v d
  bXX := F.bound_newXX a v d
  bT := fun p hp => F.bound_newT a v d hp
  derivative := fun p hp => gaussianFamily_hasFDerivAt hI F.mU F.mT F.mX F.mXX F.bU F.bT F.bX F.bXX
    F.derivative F.spatial F.second a v d hm hs hp
  spatial := F.spatial_newX a v d
  second := F.spatial_newXX a v d

end GaussianFamily
end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTilt_integrable {U A : ℝ → ℝ} (hU : Measurable U) (hA : Measurable A)
    {K C : ℝ} (hK : ∀ y, |U y| ≤ K) (hC : ∀ y, |A y| ≤ C) (s d x : ℝ) :
    Integrable (fun z => A (x+Real.sqrt s*z))
      ((gaussianReal 0 1).tilted (fun z => d*U (x+Real.sqrt s*z))) := by
  exact integrable_tilt_of_bound (gaussianReal 0 1) (hU.comp (by fun_prop))
    (hA.comp (by fun_prop)).aestronglyMeasurable (fun z => hK _)
    (B := fun _ => C) (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hC (x+Real.sqrt s*z)) (integrable_const _) d

lemma gaussianTiltAverage_add {U A B : ℝ → ℝ} (hU : Measurable U)
    (hA : Measurable A) (hB : Measurable B) {K CA CB : ℝ} (hK : ∀ y, |U y| ≤ K)
    (hCA : ∀ y, |A y| ≤ CA) (hCB : ∀ y, |B y| ≤ CB) (s d x : ℝ) :
    gaussianTiltAverage s d U (fun y => A y+B y) x =
      gaussianTiltAverage s d U A x+gaussianTiltAverage s d U B x :=
  integral_add (gaussianTilt_integrable hU hA hK hCA s d x) (gaussianTilt_integrable hU hB hK hCB s d x)

lemma gaussianTiltAverage_mul_const (s d c : ℝ) (U A : ℝ → ℝ) (x : ℝ) :
    gaussianTiltAverage s d U (fun y => A y*c) x = gaussianTiltAverage s d U A x*c :=
  integral_mul_const _ _

lemma gaussianTiltAverage_const_mul (s d c : ℝ) (U A : ℝ → ℝ) (x : ℝ) :
    gaussianTiltAverage s d U (fun y => c*A y) x = c*gaussianTiltAverage s d U A x :=
  integral_const_mul _ _

lemma gaussianTiltAverage_const {U : ℝ → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ y, |U y| ≤ K) (s d c x : ℝ) :
    gaussianTiltAverage s d U (fun _ => c) x = c := by
  have hE : Integrable (fun z => Real.exp (d*U (x+Real.sqrt s*z))) (gaussianReal 0 1) :=
    exp_mul_integrable_of_bound _ (hU.comp (by fun_prop)) (fun z => hK _) d
  let : IsProbabilityMeasure ((gaussianReal 0 1).tilted (fun z => d*U (x+Real.sqrt s*z))) :=
    isProbabilityMeasure_tilted hE
  simp [gaussianTiltAverage]

lemma gaussianTiltAverage_nonneg (s d : ℝ) (U A : ℝ → ℝ) (hA : ∀ y, 0 ≤ A y) (x : ℝ) :
    0 ≤ gaussianTiltAverage s d U A x := integral_nonneg (fun _ => hA _)

lemma gaussianTiltAverage_mono {U A B : ℝ → ℝ} (hU : Measurable U)
    (hA : Measurable A) (hB : Measurable B) {K CA CB : ℝ} (hK : ∀ y, |U y| ≤ K)
    (hCA : ∀ y, |A y| ≤ CA) (hCB : ∀ y, |B y| ≤ CB) (hAB : ∀ y, A y ≤ B y) (s d x : ℝ) :
    gaussianTiltAverage s d U A x ≤ gaussianTiltAverage s d U B x :=
  integral_mono (gaussianTilt_integrable hU hA hK hCA s d x) (gaussianTilt_integrable hU hB hK hCB s d x)
    (fun _ => hAB _)

lemma gaussianTiltAverage_sq_le {U A : ℝ → ℝ} (hU : Measurable U) (hA : Measurable A)
    {K C : ℝ} (hK : ∀ y, |U y| ≤ K) (hC : ∀ y, |A y| ≤ C) (s d x : ℝ) :
    (gaussianTiltAverage s d U A x)^2 ≤ gaussianTiltAverage s d U (fun y => (A y)^2) x := by
  let m := gaussianTiltAverage s d U A x
  have hA2 : ∀ y, |(A y)^2| ≤ C^2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC y) 2
  have hAi := gaussianTilt_integrable hU hA hK hC s d x
  have hA2i := gaussianTilt_integrable hU (hA.pow_const 2) hK hA2 s d x
  have h : 0 ≤ gaussianTiltAverage s d U (fun y => (A y-m)^2) x :=
    gaussianTiltAverage_nonneg _ _ _ _ (fun y => sq_nonneg _) _
  have he : (fun y => (A y-m)^2) = (fun y => (A y)^2-(2*m)*A y+m^2) := by ext y; ring
  rw [he] at h
  unfold gaussianTiltAverage at h
  simp only at h
  erw [integral_add (hA2i.sub (hAi.const_mul (2*m))) (integrable_const (m^2)),
    integral_sub hA2i (hAi.const_mul (2*m)),integral_const_mul] at h
  have hc := gaussianTiltAverage_const hU hK s d (m^2) x
  change (∫ _ : ℝ, m^2 ∂(gaussianReal 0 1).tilted (fun z => d*U (x+Real.sqrt s*z))) = m^2 at hc
  rw [hc] at h
  change 0 ≤ gaussianTiltAverage s d U (fun y => (A y)^2) x - (2*m)*m + m^2 at h
  change m^2 ≤ _
  nlinarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma familyAverage_add_at {U A B : ℝ × ℝ → ℝ} (hU : Measurable U)
    (hA : Measurable A) (hB : Measurable B) {K CA CB : ℝ} (hKU : ∀ q, |U q| ≤ K)
    (a v d : ℝ) (p : ℝ × ℝ) (hCA : ∀ y, |A (p.1,y)| ≤ CA)
    (hCB : ∀ y, |B (p.1,y)| ≤ CB) :
    familyAverage a v d U (fun q => A q+B q) p =
      familyAverage a v d U A p+familyAverage a v d U B p := by
  exact gaussianTiltAverage_add (hU.comp (by fun_prop)) (hA.comp (by fun_prop)) (hB.comp (by fun_prop))
    (fun y => hKU _) hCA hCB _ _ _

lemma familyAverage_const_mul (U A : ℝ × ℝ → ℝ) (a v d b : ℝ) (p : ℝ × ℝ) :
    familyAverage a v d U (fun q => b*A q) p = b*familyAverage a v d U A p :=
  gaussianTiltAverage_const_mul _ _ _ _ _ _

lemma familyAverage_sum {n : ℕ} {U : ℝ × ℝ → ℝ} {A : Fin n → ℝ × ℝ → ℝ}
    (hU : Measurable U) (hA : ∀ i, Measurable (A i)) {K : ℝ} {C : Fin n → ℝ}
    (hK : ∀ q, |U q| ≤ K) (hC : ∀ i q, |A i q| ≤ C i) (a v d : ℝ) (p : ℝ × ℝ) :
    familyAverage a v d U (fun q => ∑ i, A i q) p = ∑ i, familyAverage a v d U (A i) p := by
  apply integral_finsetSum
  intro i _
  exact gaussianTilt_integrable (hU.comp (by fun_prop)) ((hA i).comp (by fun_prop))
    (fun y => hK _) (fun y => hC i _) _ _ _

namespace GaussianFamily
variable {I : Set ℝ} (F : GaussianFamily I)

lemma average_generator (a v d e : ℝ) (p : ℝ × ℝ) :
    familyAverage a v d F.U (fun q => F.XX q+e*(F.X q)^2) p =
      familyAverage a v d F.U F.XX p + e*familyAverage a v d F.U (fun q => (F.X q)^2) p := by
  erw [familyAverage_add_at F.mU F.mXX (measurable_const.mul (F.mX.pow_const 2)) F.bU a v d p
    (fun y => F.bXX _) (CA := F.KXX) (CB := |e| * F.KX^2),familyAverage_const_mul]
  intro y
  change |e*(F.X (p.1,y))^2| ≤ _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (square_bound (F.bX _)) (abs_nonneg _)

lemma generator_identity (a v d : ℝ) (p : ℝ × ℝ) :
    F.newXX a v d p+d*(F.newX a v d p)^2 =
      familyAverage a v d F.U (fun q => F.XX q+d*(F.X q)^2) p := by
  rw [F.average_generator]
  unfold newXX
  ring

lemma cancellation (a v d b e : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    F.newT a v d p+(b-v)/2*(F.newXX a v d p+d*(F.newX a v d p)^2) =
      familyAverage a v d F.U (fun q => F.T q+b/2*(F.XX q+e*(F.X q)^2)) p -
        ((e-d)*b)/2*familyAverage a v d F.U (fun q => (F.X q)^2) p := by
  have hbound : ∀ y, |b/2*(F.XX (p.1,y)+e*(F.X (p.1,y))^2)| ≤
      |b/2| * (F.KXX+|e| * F.KX^2) := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (bounded_generator (fun y => F.bX (p.1,y)) (fun y => F.bXX (p.1,y)) e y) (abs_nonneg _)
  erw [familyAverage_add_at F.mU F.mT
    (measurable_const.mul (F.mXX.add (measurable_const.mul (F.mX.pow_const 2)))) F.bU a v d p
    (fun y => F.bT (p.1,y) hp) hbound,familyAverage_const_mul,F.generator_identity]
  unfold newT
  erw [F.average_generator a v d d,F.average_generator a v d e]
  ring

lemma squared_newX_le (a v d : ℝ) (p : ℝ × ℝ) :
    (F.newX a v d p)^2 ≤ familyAverage a v d F.U (fun q => (F.X q)^2) p :=
  gaussianTiltAverage_sq_le (F.mU.comp (by fun_prop)) (F.mX.comp (by fun_prop))
    (fun y => F.bU _) (fun y => F.bX _) _ _ _

 
def terminal {f f' f'' : ℝ → ℝ} (hf : Measurable f) (hf' : Measurable f') (hf'' : Measurable f'')
    {K C D : ℝ} (hK : ∀ x, |f x| ≤ K) (hC : ∀ x, |f' x| ≤ C) (hD : ∀ x, |f'' x| ≤ D)
    (hder : ∀ x, HasDerivAt f (f' x) x) (hder' : ∀ x, HasDerivAt f' (f'' x) x) : GaussianFamily I where
  U := fun p => f p.2
  X := fun p => f' p.2
  XX := fun p => f'' p.2
  T := fun _ => 0
  KU := K
  KX := C
  KXX := D
  KT := 0
  mU := hf.comp measurable_snd
  mX := hf'.comp measurable_snd
  mXX := hf''.comp measurable_snd
  mT := measurable_const
  bU := fun p => hK _
  bX := fun p => hC _
  bXX := fun p => hD _
  bT := fun p _ => by simp
  derivative := fun p _ => by
    have h := (hder p.2).comp_hasFDerivAt p (hasFDerivAt_snd (𝕜 := ℝ))
    convert h using 1 <;> try rfl
    simp [pairLinear]
  spatial := fun t x => hder x
  second := fun t x => hder' x

end GaussianFamily
end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma monotone_fin_cons {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (hm : Monotone c)
    (ha : ∀ i, a ≤ c i) : Monotone (Fin.cons a c) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; exact le_rfl
    · intro _; exact ha j
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact False.elim (by simp at h)
    · intro h
      exact hm (Fin.succ_le_succ_iff.mp h)

lemma familyAverage_congr_fiber {U A B : ℝ × ℝ → ℝ} {a v d : ℝ} {p : ℝ × ℝ}
    (h : ∀ y, A (p.1,y)=B (p.1,y)) :
    familyAverage a v d U A p = familyAverage a v d U B p := by
  apply integral_congr_ae
  exact ae_of_all _ (fun z => h _)

lemma familyAverage_weightedSum {n : ℕ} {U : ℝ × ℝ → ℝ} {c : Fin n → ℝ × ℝ → ℝ}
    (hU : Measurable U) (hc : ∀ i, Measurable (c i)) {K C : ℝ}
    (hK : ∀ q, |U q| ≤ K) (hC : ∀ i q, |c i q| ≤ C) (w : Fin n → ℝ)
    (a v d : ℝ) (p : ℝ × ℝ) :
    familyAverage a v d U (fun q => ∑ i, w i*c i q) p =
      ∑ i, w i*familyAverage a v d U (c i) p := by
  erw [familyAverage_sum hU (fun i => measurable_const.mul (hc i)) hK
    (C := fun i => |w i| * C) (fun i q => ?_) a v d p]
  · apply Finset.sum_congr rfl
    intro i _
    exact familyAverage_const_mul U (c i) a v d (w i) p
  · change |w i*c i q| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC i q) (abs_nonneg _)

 

structure VariationCertificate {I : Set ℝ} (F : GaussianFamily I) (n : ℕ)
    (b e : ℝ) (w : Fin n → ℝ) where
  c : Fin n → ℝ × ℝ → ℝ
  measurable : ∀ i, Measurable (c i)
  nonneg : ∀ i p, 0 ≤ c i p
  bound : ∀ i p, |c i p| ≤ F.KX^2
  monotone : ∀ p, Monotone (fun i => c i p)
  leading : ∀ i p, (F.X p)^2 ≤ c i p
  formula : ∀ p, p.1 ∈ I → F.T p+b/2*(F.XX p+e*(F.X p)^2) =
    -(1/2:ℝ)*∑ i, w i*c i p

namespace VariationCertificate
variable {I : Set ℝ} {F : GaussianFamily I} {n : ℕ} {b e : ℝ} {w : Fin n → ℝ}
  (V : VariationCertificate F n b e w)

def prependC (a v d : ℝ) : Fin (n+1) → ℝ × ℝ → ℝ :=
  Fin.cons (familyAverage a v d F.U (fun q => (F.X q)^2))
    (fun i => familyAverage a v d F.U (V.c i))

lemma measurable_prependC (a v d : ℝ) (i : Fin (n+1)) : Measurable (V.prependC a v d i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact familyAverage_measurable F.mU (F.mX.pow_const 2) _ _ _
  · exact familyAverage_measurable F.mU (V.measurable i) _ _ _

lemma nonneg_prependC (a v d : ℝ) (i : Fin (n+1)) (p : ℝ × ℝ) :
    0 ≤ V.prependC a v d i p := by
  refine Fin.cases ?_ (fun i => ?_) i
  · change 0 ≤ familyAverage a v d F.U (fun q => (F.X q)^2) p
    exact gaussianTiltAverage_nonneg (a+v*p.1) d (fun y => F.U (p.1,y))
      (fun y => (F.X (p.1,y))^2) (fun y => sq_nonneg _) p.2
  · change 0 ≤ familyAverage a v d F.U (V.c i) p
    exact gaussianTiltAverage_nonneg (a+v*p.1) d (fun y => F.U (p.1,y))
      (fun y => V.c i (p.1,y)) (fun y => V.nonneg i _) p.2

lemma bound_prependC (a v d : ℝ) (i : Fin (n+1)) (p : ℝ × ℝ) :
    |V.prependC a v d i p| ≤ F.KX^2 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact familyAverage_bound F.mU (F.mX.pow_const 2) F.bU (fun q => square_bound (F.bX q)) _ _ _ _
  · exact familyAverage_bound F.mU (V.measurable i) F.bU (V.bound i) _ _ _ _

lemma head_le_prependTail (a v d : ℝ) (i : Fin n) (p : ℝ × ℝ) :
    familyAverage a v d F.U (fun q => (F.X q)^2) p ≤ familyAverage a v d F.U (V.c i) p := by
  exact gaussianTiltAverage_mono (F.mU.comp (by fun_prop)) ((F.mX.pow_const 2).comp (by fun_prop))
    ((V.measurable i).comp (by fun_prop)) (fun y => F.bU _) (fun y => square_bound (F.bX _))
    (fun y => V.bound i _) (fun y => V.leading i _) _ _ _

lemma leading_prependC (a v d : ℝ) (i : Fin (n+1)) (p : ℝ × ℝ) :
    (F.newX a v d p)^2 ≤ V.prependC a v d i p := by
  refine Fin.cases (F.squared_newX_le a v d p) (fun i => ?_) i
  exact (F.squared_newX_le a v d p).trans (V.head_le_prependTail a v d i p)

lemma monotone_prependC (a v d : ℝ) (p : ℝ × ℝ) : Monotone (fun i => V.prependC a v d i p) := by
  have hmono : Monotone (fun i => familyAverage a v d F.U (V.c i) p) := by
    intro i j hij
    exact gaussianTiltAverage_mono (F.mU.comp (by fun_prop)) ((V.measurable i).comp (by fun_prop))
      ((V.measurable j).comp (by fun_prop)) (fun y => F.bU _) (fun y => V.bound i _)
      (fun y => V.bound j _) (fun y => V.monotone _ hij) _ _ _
  have h := monotone_fin_cons (familyAverage a v d F.U (fun q => (F.X q)^2) p) _ hmono
    (fun i => V.head_le_prependTail a v d i p)
  convert h using 1
  ext i
  refine Fin.cases rfl (fun i => rfl) i

lemma formula_prependC (a v d : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    F.newT a v d p+(b-v)/2*(F.newXX a v d p+d*(F.newX a v d p)^2) =
      -(1/2:ℝ)*∑ i : Fin (n+1), ((Fin.cons ((e-d)*b) w : Fin (n+1) → ℝ) i)*(V.prependC a v d i p) := by
  rw [F.cancellation a v d b e hp]
  have heq : familyAverage a v d F.U (fun q => F.T q+b/2*(F.XX q+e*(F.X q)^2)) p =
      familyAverage a v d F.U (fun q => -(1/2:ℝ)*∑ i, w i*V.c i q) p :=
    familyAverage_congr_fiber (fun y => V.formula (p.1,y) hp)
  rw [heq,familyAverage_const_mul,
    familyAverage_weightedSum F.mU V.measurable F.bU V.bound w a v d p,Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,prependC]
  ring

 

def prepend (hI : IsOpen I) (a v : ℝ) {d : ℝ} (hd : 0 ≤ d)
    {m : ℝ} (hm : 0 < m) (hs : ∀ t ∈ I, m ≤ a+v*t) :
    VariationCertificate (F.transform hI a v hd hm hs) (n+1) (b-v) d (Fin.cons ((e-d)*b) w) where
  c := V.prependC a v d
  measurable := V.measurable_prependC a v d
  nonneg := V.nonneg_prependC a v d
  bound := V.bound_prependC a v d
  leading := V.leading_prependC a v d
  monotone := V.monotone_prependC a v d
  formula := fun _ hp => V.formula_prependC a v d hp

 

def empty {G : GaussianFamily I} (hT : ∀ p, G.T p=0) (e : ℝ) :
    VariationCertificate G 0 0 e (fun i => Fin.elim0 i) where
  c := fun i => Fin.elim0 i
  measurable := fun i => Fin.elim0 i
  nonneg := fun i => Fin.elim0 i
  bound := fun i => Fin.elim0 i
  leading := fun i => Fin.elim0 i
  monotone := fun p i => Fin.elim0 i
  formula := fun p _ => by simp [hT p]

end VariationCertificate
end IsingPerceptron

 

 

open scoped BigOperators
namespace IsingPerceptron

 
def FinTailNonneg {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, 0 ≤ ∑ i : Fin n, if j ≤ i then w i else 0

lemma FinTailNonneg.succ {n : ℕ} {w : Fin (n+1) → ℝ} (h : FinTailNonneg w) :
    FinTailNonneg (fun i : Fin n => w i.succ) := by
  intro j
  have hh := h j.succ
  simpa [Fin.sum_univ_succ,Fin.succ_le_succ_iff] using hh

lemma FinTailNonneg.total {n : ℕ} {w : Fin n → ℝ} (h : FinTailNonneg w) :
    0 ≤ ∑ i, w i := by
  cases n with
  | zero => simp
  | succ n => simpa using h 0

 
lemma finite_tail_pairing_nonneg {n : ℕ} (w c : Fin n → ℝ) (hw : FinTailNonneg w)
    (hc : ∀ i, 0 ≤ c i) (hm : Monotone c) : 0 ≤ ∑ i, w i*c i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnext := ih (fun i : Fin n => w i.succ) (fun i => c i.succ-c 0) hw.succ
      (fun i => sub_nonneg.mpr (hm (Fin.zero_le _)))
      (fun i j hij => sub_le_sub_right (hm (Fin.succ_le_succ_iff.mpr hij)) _)
    have hfirst := mul_nonneg (hc 0) hw.total
    have he : (∑ i : Fin (n+1), w i*c i) =
        c 0*(∑ i : Fin (n+1), w i)+∑ i : Fin n, w i.succ*(c i.succ-c 0) := by
      rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib,← Finset.sum_mul]
      ring
    rw [he]
    exact add_nonneg hfirst hnext

end IsingPerceptron

end

end OAI
