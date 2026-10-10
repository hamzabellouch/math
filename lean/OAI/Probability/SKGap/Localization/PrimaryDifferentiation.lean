import Mathlib
import OAI.Probability.SKGap.Matrix.PrimaryMatrix
import OAI.Probability.SKGap.Matrix.DiscreteMatrixCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

def primaryState (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) :
    ℕ → VectorFields n × VectorFields n
  | 0 => (spin,fun x i => h i+∑ a,J i a*spin x a)
  | k+1 =>
      let s := primaryState j J h k
      let m : VectorFields n := fun x i => Real.tanh (s.2 x i)
      let b : Spin n→ℝ := siteMean (fun x i => 1-(m x i)^2)
      (m,fun x i => h i+∑ a,J i a*m x a-j*b x*s.1 x i)

def primaryDiagonal (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    ℕ→Fin n→ℝ := fun k i => scalarVariance ((primaryState j J h k).2 x i)

def formalField (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    Interaction n :=
  SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+1)

def formalMag (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℕ→Interaction n
  | 0 => 1
  | k+1 => Matrix.diagonal (primaryDiagonal j J h x k)*formalField j J h x k

lemma primaryDiagonal_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    ∀ k i, |primaryDiagonal j J h x k i|≤1 := by
  intro k i
  rw [primaryDiagonal,abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

lemma primaryState_mag_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (x : Spin n) (i : Fin n) : |(primaryState j J h k).1 x i|≤1 := by
  cases k with
  | zero => simp [primaryState,abs_spin_eq_one]
  | succ k => exact (Real.abs_tanh_lt_one _).le

lemma formalMag_previous (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalMag j J h x k =
      Matrix.diagonal (SKGap.Noncrossing.Primary.previousDiagonal (primaryDiagonal j J h x) k)*
        SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) k := by
  cases k <;> simp [formalMag,formalField,SKGap.Noncrossing.Primary.previousDiagonal,
    SKGap.Noncrossing.Primary.primaryMatrix]

lemma formalField_succ (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalField j J h x (k+1) = J*formalMag j J h x (k+1)-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k := by
  change SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+2) =
    J*(Matrix.diagonal (primaryDiagonal j J h x k)*
      SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+1))-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k
  rw [formalMag_previous,SKGap.Noncrossing.Primary.primaryMatrix,Matrix.mul_assoc]

def differentiationBound (j R B : ℝ) : ℕ→ℝ
  | 0 => B+1
  | k+1 =>
    let C := differentiationBound j R B k
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    B+1+(R*T+|j| *(C+Q+2*C*Q))+T

lemma differentiationBound_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0≤differentiationBound j R B k := by
  induction k with
  | zero => dsimp [differentiationBound]; positivity
  | succ k hk => dsimp only [differentiationBound]; positivity

lemma onsager_derivative_error {F G : VectorFields n} {x : Spin n} {H P : Interaction n}
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) {C R : ℝ} (hn : 0<n)
    (hC : 0≤C) (hR : 0≤R) (hJ : SKGap.opNorm J≤R)
    (hF : ShapeBound (derivativeMatrix F x) C) (hFE : ‖derivativeMatrix F x-H‖≤C)
    (hGE : ‖derivativeMatrix G x-P‖≤C) (hG : SKGap.opNorm (derivativeMatrix G x)≤C)
    (hGb : ∀ i,|G x i|≤1) :
    let m : VectorFields n := fun y i => Real.tanh (F y i)
    let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖ ≤
      R*T+|j| *(C+Q+2*C*Q) := by
  let m : VectorFields n := fun y i => Real.tanh (F y i)
  let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
  let T := C+8*C^2
  let Q := 2*T+4*T^2
  change ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
    (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖≤_
  have hT : 0≤T := by dsimp [T]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hm : ShapeBound (derivativeMatrix m x) T := tanh_derivative_shape hC hF
  have hmE : ‖derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H‖≤T := by
    convert tanh_derivative_formal_error hC hF hFE using 1
    dsimp [T]
    ring
  have hbQ : (n:ℝ)*‖derivativeVector b x‖^2≤Q^2 :=
    siteMean_derivative_square_bound hn (variance_derivative_opNorm hT
      (fun i => (Real.abs_tanh_lt_one _).le) hm)
  have hp : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x‖≤Q+2*C*Q :=
    product_derivative_error hn hQ hG hGb hbQ
  have hb : |b x|≤1 := by
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hv (i : Fin n) : |1-(m x i)^2|≤1 := by
      change |scalarVariance (F x i)|≤1
      rw [abs_of_pos (scalarVariance_pos _)]
      exact scalarVariance_le_one _
    simpa only [b,siteMean,SKGap.Noncrossing.Diagram.mean,Fintype.card_fin] using
      SKGap.Noncrossing.Primary.mean_abs_le_one hv
  have hpE : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • P‖≤C+Q+2*C*Q := by
    have he : derivativeMatrix (fun y i => b y*G y i) x-b x • P =
        (derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x)+
          b x • (derivativeMatrix G x-P) := by module
    rw [he]
    apply (norm_add_le _ _).trans
    have hs : ‖b x • (derivativeMatrix G x-P)‖≤C := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (by simpa using hGE)
    have hh := add_le_add hp hs
    linarith
  have hd : derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x =
      J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x := by
    rw [derivativeMatrix_sub,derivativeMatrix_linear]
    congr 1
    convert derivativeMatrix_smul j (fun y i => b y*G y i) x using 1
    congr 1
    funext y i
    ring
  rw [hd]
  have he : J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P) =
      J*(derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H)-
        j • (derivativeMatrix (fun y i => b y*G y i) x-b x • P) := by
    simp only [mul_sub,smul_sub,mul_smul]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact (SKGap.frobenius_mul_le_opNorm _ _).trans (mul_le_mul hJ hmE (norm_nonneg _) hR)
  · rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hpE (abs_nonneg _)

theorem primary_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    ‖derivativeMatrix (primaryState j J h k).2 x-formalField j J h x k‖≤C ∧
    ‖derivativeMatrix (primaryState j J h k).1 x-formalMag j J h x k‖≤C ∧
    SKGap.opNorm (derivativeMatrix (primaryState j J h k).1 x)≤C ∧
    ShapeBound (derivativeMatrix (primaryState j J h k).2 x) C := by
  induction k with
  | zero =>
    have hd : derivativeMatrix (primaryState j J h 0).2 x=J := by
      change derivativeMatrix (fun y i => h i+∑ a,J i a*spin y a) x=J
      rw [derivativeMatrix_linear,derivativeMatrix_spin,mul_one]
    have hm : derivativeMatrix (primaryState j J h 0).1 x=1 := derivativeMatrix_spin x
    have hf : formalField j J h x 0=J := rfl
    change _≤B+1 ∧ _≤B+1 ∧ _≤B+1 ∧ ShapeBound _ (B+1)
    rw [hd,hm,hf,formalMag,sub_self,norm_zero,sub_self,norm_zero]
    refine ⟨by positivity,by positivity,(SKGap.opNorm_one_le).trans ?_,?_⟩
    · linarith
    · exact (show ShapeBound J B by simpa only [hf] using hformal 0 le_rfl).mono (by linarith)
  | succ k ih =>
    obtain ⟨hFE,hGE,hG,hF⟩ := ih (fun l hl => hformal l (hl.trans (Nat.le_succ _)))
    let C := differentiationBound j R B k
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    let E := R*T+|j| *(C+Q+2*C*Q)
    have hC : 0≤C := differentiationBound_nonneg hR hB k
    have hT : 0≤T := by dsimp [T]; positivity
    have hQ : 0≤Q := by dsimp [Q]; positivity
    have hE : 0≤E := by dsimp [E]; positivity
    have hnext : differentiationBound j R B (k+1)=B+1+E+T := rfl
    have hFE' : ‖derivativeMatrix (primaryState j J h (k+1)).2 x-formalField j J h x (k+1)‖≤E := by
      have hh := onsager_derivative_error (F := (primaryState j J h k).2)
        (G := (primaryState j J h k).1) j J h hn hC hR hJ hF hFE hGE hG
        (primaryState_mag_bounded j J h k x)
      have hb : siteMean (fun y i => 1-(Real.tanh ((primaryState j J h k).2 y i))^2) x =
          SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k) := by
        simp only [siteMean,SKGap.Noncrossing.Diagram.mean,primaryDiagonal,scalarVariance,Fintype.card_fin]
      dsimp only at hh
      rw [hb] at hh
      rw [formalField_succ]
      exact hh
    have hGE' : ‖derivativeMatrix (primaryState j J h (k+1)).1 x-formalMag j J h x (k+1)‖≤T := by
      have hh := tanh_derivative_formal_error hC hF hFE
      change ‖derivativeMatrix (fun y i => Real.tanh ((primaryState j J h k).2 y i)) x-
        Matrix.diagonal (fun i => scalarVariance ((primaryState j J h k).2 x i))*formalField j J h x k‖≤T
      convert hh using 1
      dsimp [T]
      ring
    have hG' : SKGap.opNorm (derivativeMatrix (primaryState j J h (k+1)).1 x)≤T :=
      (tanh_derivative_shape hC hF).1
    have hF' : ShapeBound (derivativeMatrix (primaryState j J h (k+1)).2 x) (B+E) :=
      (hformal (k+1) le_rfl).perturb hFE'
    rw [hnext]
    exact ⟨hFE'.trans (by linarith),hGE'.trans (by linarith),hG'.trans (by linarith),
      hF'.mono (by linarith)⟩

theorem primary_average_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    let T := C+8*C^2
    (n:ℝ)*‖derivativeVector (siteMean (fun y i =>
        scalarVariance ((primaryState j J h k).2 y i))) x‖^2≤(2*T+4*T^2)^2 := by
  have hC := differentiationBound_nonneg (j:=j) hR hB k
  have hF := (primary_differentiation J h x hn hR hB hJ k hformal).2.2.2
  apply siteMean_derivative_square_bound hn
  exact variance_derivative_opNorm (by positivity)
    (fun i => (Real.abs_tanh_lt_one _).le) (tanh_derivative_shape hC hF)

end SKGapCutoff.Primary

end
end

end OAI
