import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

theorem leading_frequency_SL2_alignment {h : Fin 2 → ℤ} (hh : h≠0) :
    ∃ (k : ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ),
      0<k ∧ A.det=1 ∧ h ᵥ* A=![0,k] := by
  have hg : 0<Int.gcd (h 0) (h 1) := by
    apply Nat.pos_of_ne_zero
    intro he
    have hz := Int.gcd_eq_zero_iff.mp he
    apply hh
    ext i
    fin_cases i
    · exact hz.1
    · exact hz.2
  obtain ⟨u,v,huv,h0,h1⟩ := Int.exists_gcd_one hg
  let a := Int.gcdA u v
  let b := Int.gcdB u v
  have hab : u*a+v*b=1 := by
    simpa only [huv,Int.natCast_one] using (Int.gcd_eq_gcd_ab u v).symm
  refine ⟨Int.gcd (h 0) (h 1),!![v,a;-u,b],by exact_mod_cast hg,?_,?_⟩
  · rw [Matrix.det_fin_two_of]
    nlinarith
  · ext i
    fin_cases i
    · simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one]
      change h 0*v+h 1*(-u)=0
      calc
        _ = (u*(Int.gcd (h 0) (h 1):ℤ))*v+(v*(Int.gcd (h 0) (h 1):ℤ))*(-u) :=
          congrArg₂ (fun x y : ℤ => x*v+y*(-u)) h0 h1
        _ = 0 := by ring
    · simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one]
      change h 0*a+h 1*b=(Int.gcd (h 0) (h 1):ℤ)
      calc
        _ = (u*a+v*b)*(Int.gcd (h 0) (h 1):ℤ) := by
          calc
            _ = (u*(Int.gcd (h 0) (h 1):ℤ))*a+(v*(Int.gcd (h 0) (h 1):ℤ))*b :=
              congrArg₂ (fun x y : ℤ => x*a+y*b) h0 h1
            _ = _ := by ring
        _ = _ := by rw [hab,one_mul]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularIntMap (A : Matrix (Fin 2) (Fin 2) ℤ) :
    UnitAddTorus (Fin 2) →+ UnitAddTorus (Fin 2) where
  toFun x := ![A 0 0 • x 0+A 0 1 • x 1,A 1 0 • x 0+A 1 1 • x 1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [smul_add] <;> abel

lemma angularIntMap_continuous (A : Matrix (Fin 2) (Fin 2) ℤ) :
    Continuous (angularIntMap A) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    exact (continuous_apply 0 |>.zsmul _).add (continuous_apply 1 |>.zsmul _)

lemma angularIntMap_surjective {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    Function.Surjective (angularIntMap A) := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [Matrix.det_fin_two] using hA
  intro y
  refine ⟨![A 1 1 • y 0- A 0 1 • y 1,-A 1 0 • y 0+A 0 0 • y 1],?_⟩
  ext i
  fin_cases i
  · change A 0 0 • (A 1 1 • y 0-A 0 1 • y 1)+
      A 0 1 • (-A 1 0 • y 0+A 0 0 • y 1)=y 0
    calc
      _ = (A 0 0*A 1 1-A 0 1*A 1 0) • y 0 := by module
      _ = _ := by rw [hd,one_smul]
  · change A 1 0 • (A 1 1 • y 0-A 0 1 • y 1)+
      A 1 1 • (-A 1 0 • y 0+A 0 0 • y 1)=y 1
    calc
      _ = (A 0 0*A 1 1-A 0 1*A 1 0) • y 1 := by module
      _ = _ := by rw [hd,one_smul]

lemma angularIntMap_measurePreserving {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    MeasurePreserving (angularIntMap A) (volume : Measure (UnitAddTorus (Fin 2))) volume :=
  AddMonoidHom.measurePreserving (angularIntMap_continuous A) (angularIntMap_surjective hA) rfl

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularNormalization (A : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  (A 0 0:ℝ)^2+(A 0 1:ℝ)^2+(A 1 0:ℝ)^2+(A 1 1:ℝ)^2+1

def normalizedAngularTensor (s : Fin 3 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Fin 3 → ℝ :=
  let a : ℝ := A 0 0
  let b : ℝ := A 0 1
  let c : ℝ := A 1 0
  let d : ℝ := A 1 1
  let M := angularNormalization A
  ![M*(s 0*d^2-2*s 1*b*d+s 2*b^2),
    M*(-s 0*c*d+s 1*(a*d+b*c)-s 2*a*b),
    M*(s 0*c^2-2*s 1*a*c+s 2*a^2)]

lemma angularNormalization_pos (A : Matrix (Fin 2) (Fin 2) ℤ) :
    0<angularNormalization A := by unfold angularNormalization; positivity

lemma twoCoordinate_cauchy (a b x y : ℝ) :
    (a*x+b*y)^2≤(a^2+b^2)*(x^2+y^2) := by
  nlinarith [sq_nonneg (a*y-b*x)]

theorem normalizedAngularTensor_lower {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (x y : ℝ) :
    (1/2)*(x^2+y^2)≤normalizedAngularTensor s A 0*x^2+
      2*normalizedAngularTensor s A 1*x*y+normalizedAngularTensor s A 2*y^2 := by
  let a : ℝ := A 0 0
  let b : ℝ := A 0 1
  let c : ℝ := A 1 0
  let d : ℝ := A 1 1
  let M := angularNormalization A
  have hdZ : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using hA
  have hd : a*d-b*c=1 := by
    dsimp [a,b,c,d]
    exact_mod_cast hdZ
  let u := d*x-c*y
  let v := -b*x+a*y
  have hx : a*u+c*v=x := by
    calc
      _ = (a*d-b*c)*x := by dsimp [u,v]; ring
      _ = _ := by rw [hd,one_mul]
  have hy : b*u+d*v=y := by
    calc
      _ = (a*d-b*c)*y := by dsimp [u,v]; ring
      _ = _ := by rw [hd,one_mul]
  have hn : x^2+y^2≤M*(u^2+v^2) := by
    calc
      _ = (a*u+c*v)^2+(b*u+d*v)^2 := by rw [hx,hy]
      _ ≤ (a^2+c^2)*(u^2+v^2)+(b^2+d^2)*(u^2+v^2) :=
        add_le_add (twoCoordinate_cauchy a c u v) (twoCoordinate_cauchy b d u v)
      _ ≤ M*(u^2+v^2) := by
        dsimp [M,angularNormalization,a,b,c,d]
        nlinarith [sq_nonneg u,sq_nonneg v]
  have he : normalizedAngularTensor s A 0*x^2+
      2*normalizedAngularTensor s A 1*x*y+normalizedAngularTensor s A 2*y^2=
      M*(s 0*u^2+2*s 1*u*v+s 2*v^2) := by
    dsimp [normalizedAngularTensor,M,u,v,a,b,c,d]
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left (hs u v) (angularNormalization_pos A).le
  nlinarith

end ScalarConductivity

end

end OAI
