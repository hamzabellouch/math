import OAI.Analysis.InterpolatedFactors.CornerGaussian

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
namespace FreeGroupFactorMain.CircularRotation

def q : ℂ := (Real.sqrt 2 : ℂ)⁻¹

theorem q_star : star q=q := by
  simp only [q,Complex.star_def,map_inv₀,Complex.conj_ofReal]

theorem q_sq : q^2=1/2 := by
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rw [q,inv_pow,hs]
  norm_num

theorem two_q_mul {A : Type u_1} [AddCommGroup A] [Module ℂ A] (X : A) :
    q • (q • X+q • X)=X := by
  rw [smul_add,smul_smul,← add_smul,← pow_two,q_sq]
  norm_num

theorem qI_star : star (q*Complex.I)=-(q*Complex.I) := by
  rw [star_mul,q_star,Complex.star_def,Complex.conj_I]
  ring

section

variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def plus (X Y : A) : A := q • X+(q*Complex.I) • Y
def minus (X Y : A) : A := q • X-(q*Complex.I) • Y

omit [StarRing A] [StarModule ℂ A] in
theorem plus_add_minus (X Y : A) : q • (plus X Y+minus X Y)=X := by
  rw [plus,minus]
  have he : q • X+(q*Complex.I) • Y+(q • X-(q*Complex.I) • Y)=q • X+q • X := by abel
  rw [he,two_q_mul]

omit [StarRing A] [StarModule ℂ A] in
theorem plus_sub_minus (X Y : A) : (-q*Complex.I) • (plus X Y-minus X Y)=Y := by
  have he : plus X Y-minus X Y=(q*Complex.I) • Y+(q*Complex.I) • Y := by unfold plus minus;abel
  rw [he,smul_add,smul_smul,← add_smul]
  have hc : (-q*Complex.I)*(q*Complex.I)+(-q*Complex.I)*(q*Complex.I)=1 := by
    calc
      _ = -2*q^2*Complex.I^2 := by ring
      _ = 1 := by rw [q_sq,Complex.I_sq];norm_num
  rw [hc,one_smul]

theorem paired_plus (X Y : A) : plus X Y+star (minus X Y)=plus (X+star X) (Y+star Y) := by
  simp only [plus,minus,star_sub,star_smul,q_star,qI_star,neg_smul,smul_add]
  abel

theorem paired_minus (X Y : A) : minus X Y+star (plus X Y)=minus (X+star X) (Y+star Y) := by
  simp only [plus,minus,star_add,star_smul,q_star,qI_star,neg_smul,smul_add]
  abel

theorem generation (X Y : A) (M : StarSubalgebra ℂ A) :
    (X+star X∈M ∧ Y+star Y∈M) ↔
      (plus X Y+star (minus X Y)∈M ∧ minus X Y+star (plus X Y)∈M) := by
  rw [paired_plus,paired_minus]
  constructor
  · rintro ⟨hX,hY⟩
    exact ⟨add_mem (M.smul_mem hX _) (M.smul_mem hY _),sub_mem (M.smul_mem hX _) (M.smul_mem hY _)⟩
  · rintro ⟨hP,hM⟩
    constructor
    · rw [← plus_add_minus (X+star X) (Y+star Y)]
      exact M.smul_mem (add_mem hP hM) _
    · rw [← plus_sub_minus (X+star X) (Y+star Y)]
      exact M.smul_mem (sub_mem hP hM) _

theorem contraction (X Y a Z : A)
    (hXX : star X*a*X=Z) (hYY : star Y*a*Y=Z)
    (hXY : star X*a*Y=0) (hYX : star Y*a*X=0) :
    star (plus X Y)*a*plus X Y=Z ∧ star (minus X Y)*a*minus X Y=Z ∧
      star (plus X Y)*a*minus X Y=0 ∧ star (minus X Y)*a*plus X Y=0 := by
  have h1 : q*q=1/2 := by rw [← pow_two,q_sq]
  have h2 : (q*Complex.I)*(q*Complex.I)=-(1/2) := by
    calc
      _ = q^2*Complex.I^2 := by ring
      _ = -(1/2) := by rw [q_sq,Complex.I_sq];ring
  simp only [plus,minus,star_add,star_sub,star_smul,q_star,qI_star,add_mul,sub_mul,mul_add,mul_sub,
    smul_mul_assoc,mul_smul_comm]
  simp only [hXX,hYY,hXY,hYX,smul_zero,add_zero,zero_add,sub_zero,zero_sub]
  simp only [smul_smul,mul_neg,neg_neg,h1,h2]
  repeat' constructor
  all_goals match_scalars
  all_goals ring_nf
  all_goals norm_num [q_sq,Complex.I_sq]

end

variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def realFirst (X Y : A) : A := q • (X+Y)
def realSecond (X Y : A) : A := (-q*Complex.I) • (X-Y)

theorem inverse_paired (X Y : A) :
    realFirst X Y+star (realFirst X Y)=q • ((X+star Y)+(Y+star X)) ∧
    realSecond X Y+star (realSecond X Y)=(-q*Complex.I) • ((X+star Y)-(Y+star X)) := by
  constructor
  · simp only [realFirst,star_smul,q_star,star_add,smul_add]
    abel
  · have hs : star (-q*Complex.I)=q*Complex.I := by
      rw [star_mul,star_neg,q_star,Complex.star_def,Complex.conj_I]
      ring
    simp only [realSecond,star_smul,hs,star_sub]
    simp only [smul_sub,neg_mul,neg_smul,smul_add]
    abel

theorem inverse_contraction (X Y a Z : A)
    (hXX : star X*a*X=Z) (hYY : star Y*a*Y=Z)
    (hXY : star X*a*Y=0) (hYX : star Y*a*X=0) :
    star (realFirst X Y)*a*realFirst X Y=Z ∧ star (realSecond X Y)*a*realSecond X Y=Z ∧
      star (realFirst X Y)*a*realSecond X Y=0 ∧ star (realSecond X Y)*a*realFirst X Y=0 := by
  have hs : star (-q*Complex.I)=q*Complex.I := by
    rw [star_mul,star_neg,q_star,Complex.star_def,Complex.conj_I]
    ring
  simp only [realFirst,realSecond,star_smul,star_add,star_sub,q_star,hs,
    add_mul,sub_mul,mul_add,mul_sub,smul_mul_assoc,mul_smul_comm]
  simp only [hXX,hYY,hXY,hYX,add_zero,zero_add,sub_zero,zero_sub]
  repeat' constructor
  all_goals match_scalars
  all_goals ring_nf
  all_goals norm_num [q_sq,Complex.I_sq]

variable {S : Type u_4} {P : Type u_5}
abbrev PairedIndex (S : Type u_6) (P : Type u_7) := S ⊕ (P×Bool)

def flip : PairedIndex S P → PairedIndex S P
  | .inl i => .inl i
  | .inr (j,b) => .inr (j,!b)

def rotate (R : PairedIndex S P → A) : PairedIndex S P → A
  | .inl i => R (.inl i)
  | .inr (j,false) => plus (R (.inr (j,false))) (R (.inr (j,true)))
  | .inr (j,true) => minus (R (.inr (j,false))) (R (.inr (j,true)))

 theorem rotate_covariance [DecidableEq S] [DecidableEq P] (R : PairedIndex S P → A) (a Z : A)
    (h : ∀ i j,star (R i)*a*R j=if i=j then Z else 0) (i j : PairedIndex S P) :
    star (rotate R i)*a*rotate R j=if i=j then Z else 0 := by
  rcases i with i | ⟨i,b⟩ <;> rcases j with j | ⟨j,c⟩
  · exact h (.inl i) (.inl j)
  · cases c <;> simp [rotate,plus,minus,mul_add,mul_sub,h]
  · cases b <;> simp [rotate,plus,minus,star_add,star_sub,star_smul,add_mul,h]
  · by_cases hij : i=j
    · subst j
      have hXX : star (R (.inr (i,false)))*a*R (.inr (i,false))=Z := by simpa using h (.inr (i,false)) (.inr (i,false))
      have hYY : star (R (.inr (i,true)))*a*R (.inr (i,true))=Z := by simpa using h (.inr (i,true)) (.inr (i,true))
      have hXY : star (R (.inr (i,false)))*a*R (.inr (i,true))=0 := by simpa using h (.inr (i,false)) (.inr (i,true))
      have hYX : star (R (.inr (i,true)))*a*R (.inr (i,false))=0 := by simpa using h (.inr (i,true)) (.inr (i,false))
      have hh := contraction _ _ a Z hXX hYY hXY hYX
      cases b <;> cases c
      · simpa only [rotate,ite_true] using hh.1
      · simpa [rotate] using hh.2.2.1
      · simpa [rotate] using hh.2.2.2
      · simpa only [rotate,ite_true] using hh.2.1
    · cases b <;> cases c <;>
        simp [rotate,plus,minus,star_add,star_sub,star_smul,add_mul,mul_add,mul_sub,h,hij]

theorem rotate_generation (R : PairedIndex S P → A) (M : StarSubalgebra ℂ A) :
    (∀ i,R i+star (R i)∈M) ↔ (∀ i,rotate R i+star (rotate R (flip i))∈M) := by
  constructor
  · intro h i
    rcases i with i | ⟨j,(_|_)⟩
    · exact h (.inl i)
    · exact ((generation _ _ M).mp ⟨h (.inr (j,false)),h (.inr (j,true))⟩).1
    · exact ((generation _ _ M).mp ⟨h (.inr (j,false)),h (.inr (j,true))⟩).2
  · intro h i
    rcases i with i | ⟨j,(_|_)⟩
    · exact h (.inl i)
    · exact ((generation _ _ M).mpr ⟨h (.inr (j,false)),h (.inr (j,true))⟩).1
    · exact ((generation _ _ M).mpr ⟨h (.inr (j,false)),h (.inr (j,true))⟩).2
end FreeGroupFactorMain.CircularRotation

end

end OAI
