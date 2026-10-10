import OAI.Geometry.QuadricBundles.Equalizer

namespace OAI

universe u1 u2

namespace QuadricCounterexample
open Polynomial
noncomputable section

structure GraphScalars where
  a : ℂ
  s : ℂ
  b : ℂ
  c : ℂ
  a_cube : a^3 = -1
  determinant : s*(1-s) = 1+b*c
  relative_trace : s+a^2*(1-s)+(Real.sqrt 2 : ℂ)*a=0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0

namespace GraphScalars
variable (T : GraphScalars)

def N₁ : ℂ[X] := X^2-X+1
def N₂ : ℂ[X] := X^2+C ((Real.sqrt 2 : ℂ)*T.a)*X+C (T.a^2)
def N₂other : ℂ[X] := X^2-C ((Real.sqrt 2 : ℂ)*T.a)*X+C (T.a^2)
def P₁ : ℂ[X] := C T.c*X^2+C (1-2*T.s)*X-C T.b
def P₂ : ℂ[X] := C T.c*X^2+C (T.a^2*(1-T.s)-T.s)*X-C (T.a^2*T.b)
def L : ℂ[X] := C T.s-C T.c*X
def J : ℂ[X] := C T.b-C (1-T.s)*X

lemma a_twentyfour : T.a^24=1 := by
  rw [show (24 : ℕ)=3*8 by norm_num,pow_mul,T.a_cube]; norm_num

lemma sqrt_two_square : (Real.sqrt 2 : ℂ)^2=2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

lemma N₁_dvd : N₁ ∣ (X : ℂ[X])^24-1 := by
  have h : ((X : ℂ[X])^3+1) ∣ (X^3)^8-(-1)^8 := by
    simpa using sub_dvd_pow_sub_pow (X^3 : ℂ[X]) (-1) 8
  have hd : N₁ ∣ (X : ℂ[X])^3+1 := ⟨X+1,by unfold N₁; ring⟩
  convert hd.trans h using 1; ring

lemma N₂_factor : T.N₂*T.N₂other = (X : ℂ[X])^4+C (T.a^4) := by
  unfold N₂ N₂other
  have hs : (C (Real.sqrt 2 : ℂ) : ℂ[X])^2=2 := by
    rw [← map_pow,sqrt_two_square]; norm_num [map_ofNat]
  simp only [map_mul,map_pow]
  linear_combination -(C T.a*X)^2*hs

lemma N₂_dvd : T.N₂ ∣ (X : ℂ[X])^24-1 := by
  have h : ((X : ℂ[X])^4+C (T.a^4)) ∣ (X^4)^6-(-C (T.a^4))^6 := by
    simpa only [sub_neg_eq_add] using sub_dvd_pow_sub_pow (X^4 : ℂ[X]) (-C (T.a^4)) 6
  have hh : (-C (T.a^4) : ℂ[X])^6=1 := by
    rw [Even.neg_pow (by decide : Even (6 : ℕ))]
    rw [← map_pow,← pow_mul,show (4*6 : ℕ)=24 by norm_num,T.a_twentyfour,map_one]
  have hd : T.N₂ ∣ (X : ℂ[X])^4+C (T.a^4) := ⟨T.N₂other,T.N₂_factor.symm⟩
  convert hd.trans h using 1
  rw [hh,← pow_mul]

lemma N_coprime : IsCoprime N₁ T.N₂ := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).mpr
  intro z
  by_contra! hz
  have h1 : z^2-z+1=0 := by simpa [N₁] using hz.1
  have h2 : z^2+(Real.sqrt 2 : ℂ)*T.a*z+T.a^2=0 := by simpa [N₂] using hz.2
  have hz3 : z^3=-1 := by linear_combination (z+1)*h1
  have hz4 : z^4+T.a^4=0 := by
    linear_combination (z^2-(Real.sqrt 2 : ℂ)*T.a*z+T.a^2)*h2 +
      (T.a*z)^2*sqrt_two_square
  have ha := T.a_cube
  have hza : z = -T.a := by
    linear_combination -hz4+z*(hz3)+T.a*ha
  rw [hza,neg_pow,ha] at hz3
  norm_num at hz3

lemma exists_N_quotient : ∃ Q : ℂ[X], X^24-1=N₁*T.N₂*Q :=
  T.N_coprime.mul_dvd N₁_dvd T.N₂_dvd

def Nquotient : ℂ[X] := T.exists_N_quotient.choose
lemma Nquotient_spec : (X : ℂ[X])^24-1=N₁*T.N₂*T.Nquotient := T.exists_N_quotient.choose_spec

lemma N₁_comp_L : N₁.comp T.L=C T.c*T.P₁ := by
  unfold N₁ L P₁
  simp only [sub_comp,pow_comp,X_comp,add_comp,one_comp]
  have hd := congrArg (C : ℂ →+* ℂ[X]) T.determinant
  simp only [map_mul,map_sub,map_one,map_add] at hd
  simp only [map_sub,map_mul,map_one,map_ofNat]
  linear_combination -hd

lemma N₂_comp_L : T.N₂.comp T.L=C T.c*T.P₂ := by
  unfold N₂ L P₂
  simp only [add_comp,pow_comp,X_comp,mul_comp,C_comp]
  have hd := congrArg (C : ℂ →+* ℂ[X]) T.determinant
  have ht := congrArg (C : ℂ →+* ℂ[X]) T.relative_trace
  simp only [map_mul,map_sub,map_one,map_add,map_pow,map_zero] at hd ht
  simp only [map_sub,map_mul,map_one,map_pow]
  linear_combination (C T.s-C T.c*X)*ht-(C T.a)^2*hd

lemma P_coprime : IsCoprime T.P₁ T.P₂ := by
  have h := T.N_coprime.map (Polynomial.aeval T.L).toRingHom
  have h1 : Polynomial.aeval T.L N₁ = N₁.comp T.L := by simp [aeval_def,comp]
  have h2 : Polynomial.aeval T.L T.N₂ = T.N₂.comp T.L := by simp [aeval_def,comp]
  change IsCoprime (Polynomial.aeval T.L N₁) (Polynomial.aeval T.L T.N₂) at h
  rw [h1,h2,T.N₁_comp_L,T.N₂_comp_L] at h
  exact (h.of_isCoprime_of_dvd_left (dvd_mul_left _ _)).of_isCoprime_of_dvd_right (dvd_mul_left _ _)

lemma P_product_dvd : T.P₁*T.P₂ ∣ T.L^24-1 := by
  refine ⟨C (T.c^2)*(T.Nquotient.comp T.L),?_⟩
  have h := congrArg (fun p : ℂ[X] ↦ p.comp T.L) T.Nquotient_spec
  simp only [sub_comp,pow_comp,X_comp,one_comp,mul_comp,T.N₁_comp_L,T.N₂_comp_L] at h
  rw [h,map_pow]
  ring

lemma J_mod_P₁ : T.J+X*T.L = -T.P₁ := by
  unfold J L P₁
  simp only [map_sub,map_mul,map_one,map_ofNat]
  ring

lemma J_mod_P₂ : C (T.a^2)*T.J+X*T.L = -T.P₂ := by
  unfold J L P₂
  simp only [map_sub,map_mul,map_one,map_pow]
  ring

lemma P₁_dvd_mixed : T.P₁ ∣ T.J^24-X^24 := by
  have hd : T.P₁ ∣ T.L^24-1 := dvd_mul_right _ _ |>.trans T.P_product_dvd
  have hJ : T.P₁ ∣ T.J-(-X*T.L) := by
    refine ⟨-1,?_⟩
    linear_combination T.J_mod_P₁
  have hp := hJ.trans (sub_dvd_pow_sub_pow T.J (-X*T.L) 24)
  have hm := dvd_mul_of_dvd_right hd (X^24)
  convert dvd_add hp hm using 1; ring

lemma P₂_dvd_mixed : T.P₂ ∣ T.J^24-X^24 := by
  have hd : T.P₂ ∣ T.L^24-1 := dvd_mul_left _ _ |>.trans T.P_product_dvd
  have hJ : T.P₂ ∣ C (T.a^2)*T.J-(-X*T.L) := by
    refine ⟨-1,?_⟩
    linear_combination T.J_mod_P₂
  have hp := hJ.trans (sub_dvd_pow_sub_pow (C (T.a^2)*T.J) (-X*T.L) 24)
  have hm := dvd_mul_of_dvd_right hd (X^24)
  have ha : (C (T.a^2) : ℂ[X])^24=1 := by
    rw [← map_pow,← pow_mul,mul_comm 2 24,pow_mul,T.a_twentyfour,one_pow,map_one]
  rw [mul_pow,ha,one_mul] at hp
  convert dvd_add hp hm using 1; ring

lemma exists_graph_quotients : ∃ R R' : ℂ[X],
    T.L^24-1=T.P₁*T.P₂*R ∧ T.J^24-X^24=T.P₁*T.P₂*R' := by
  obtain ⟨R,hR⟩ := T.P_product_dvd
  obtain ⟨R',hR'⟩ := T.P_coprime.mul_dvd T.P₁_dvd_mixed T.P₂_dvd_mixed
  exact ⟨R,R',hR,hR'⟩

def sameQuotient : ℂ[X] := T.exists_graph_quotients.choose
def mixedQuotient : ℂ[X] := T.exists_graph_quotients.choose_spec.choose
lemma sameQuotient_spec : T.L^24-1=T.P₁*T.P₂*T.sameQuotient :=
  T.exists_graph_quotients.choose_spec.choose_spec.1
lemma mixedQuotient_spec : T.J^24-X^24=T.P₁*T.P₂*T.mixedQuotient :=
  T.exists_graph_quotients.choose_spec.choose_spec.2

def graphOne (mixed : Bool) (x y : ℂ) : ℂ := if mixed then x*y-1 else y-x
def graphTwo (mixed : Bool) (x y : ℂ) : ℂ := if mixed then x*y-T.a^2 else y-T.a^2*x
def graphThree (mixed : Bool) (x y : ℂ) : ℂ :=
  if mixed then y*((1-T.s)*x+T.c)-(T.b*x+T.s) else y*(T.c*x+1-T.s)-(T.s*x+T.b)
def betaPolynomial (mixed : Bool) : ℂ[X] := if mixed then T.J else T.L

def liftBeta (mixed : Bool) (x y : ℂ) : ℂ :=
  (if mixed then y^24 else 1)+graphOne mixed x y*T.graphTwo mixed x y*
    ((T.betaPolynomial mixed).eval y)^2*
    ((if mixed then T.mixedQuotient else T.sameQuotient).eval y)

lemma liftBeta_one {mixed : Bool} {x y : ℂ} (h : graphOne mixed x y=0) :
    T.liftBeta mixed x y = if mixed then y^24 else 1 := by
  simp [liftBeta,h]
lemma liftBeta_two {mixed : Bool} {x y : ℂ} (h : T.graphTwo mixed x y=0) :
    T.liftBeta mixed x y = if mixed then y^24 else 1 := by
  simp [liftBeta,h]

lemma eval_P₁_same {x y : ℂ} (h : T.graphThree false x y=0) :
    T.P₁.eval y = -graphOne false x y*T.L.eval y := by
  simp only [graphThree,Bool.false_eq_true,↓reduceIte] at h
  simp only [P₁,L,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphOne,
    Bool.false_eq_true,↓reduceIte]
  linear_combination h

lemma eval_P₂_same {x y : ℂ} (h : T.graphThree false x y=0) :
    T.P₂.eval y = -T.graphTwo false x y*T.L.eval y := by
  simp only [graphThree,Bool.false_eq_true,↓reduceIte] at h
  simp only [P₂,L,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphTwo,
    Bool.false_eq_true,↓reduceIte]
  linear_combination T.a^2*h

lemma eval_P₁_mixed {x y : ℂ} (h : T.graphThree true x y=0) :
    T.P₁.eval y = graphOne true x y*T.J.eval y := by
  simp only [graphThree,↓reduceIte] at h
  simp only [P₁,J,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphOne,↓reduceIte]
  linear_combination y*h

lemma eval_P₂_mixed {x y : ℂ} (h : T.graphThree true x y=0) :
    T.P₂.eval y = T.graphTwo true x y*T.J.eval y := by
  simp only [graphThree,↓reduceIte] at h
  simp only [P₂,J,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphTwo,↓reduceIte]
  linear_combination y*h

lemma liftBeta_three {mixed : Bool} {x y : ℂ} (h : T.graphThree mixed x y=0) :
    T.liftBeta mixed x y=((T.betaPolynomial mixed).eval y)^24 := by
  cases mixed
  · have he := congrArg (Polynomial.eval y) T.sameQuotient_spec
    simp only [eval_sub,eval_pow,eval_one,eval_mul,T.eval_P₁_same h,T.eval_P₂_same h] at he
    simp only [liftBeta,betaPolynomial,Bool.false_eq_true,↓reduceIte]
    linear_combination -he
  · have he := congrArg (Polynomial.eval y) T.mixedQuotient_spec
    simp only [eval_sub,eval_pow,eval_X,eval_mul,T.eval_P₁_mixed h,T.eval_P₂_mixed h] at he
    simp only [liftBeta,betaPolynomial,↓reduceIte]
    linear_combination -he

lemma betaPolynomial_ne_zero {mixed : Bool} {x y : ℂ} (h : T.graphThree mixed x y=0) :
    (T.betaPolynomial mixed).eval y ≠ 0 := by
  have hd := T.determinant
  cases mixed
  · have hh : (T.L.eval y)*(T.c*x+1-T.s)=1 := by
      simp only [graphThree,Bool.false_eq_true,↓reduceIte] at h
      simp only [L,eval_sub,eval_C,eval_mul,eval_X]
      linear_combination -T.c*h+hd
    intro hf
    change T.L.eval y=0 at hf
    rw [hf,zero_mul] at hh
    norm_num at hh
  · have hh : (T.J.eval y)*((1-T.s)*x+T.c)= -1 := by
      simp only [graphThree,↓reduceIte] at h
      simp only [J,eval_sub,eval_C,eval_mul,eval_X]
      linear_combination -(1-T.s)*h-hd
    intro hf
    change T.J.eval y=0 at hf
    rw [hf,zero_mul] at hh
    norm_num at hh

lemma a_ne_zero : T.a ≠ 0 := by
  intro h
  have hc := T.a_cube
  rw [h] at hc
  norm_num at hc

lemma liftBeta_ne_zero {mixed : Bool} {x y : ℂ}
    (h : graphOne mixed x y*T.graphTwo mixed x y*T.graphThree mixed x y=0) :
    T.liftBeta mixed x y ≠ 0 := by
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [T.liftBeta_one h]
      cases mixed
      · norm_num
      · apply pow_ne_zero
        intro hy
        simp [graphOne,hy] at h
    · rw [T.liftBeta_two h]
      cases mixed
      · norm_num
      · apply pow_ne_zero
        intro hy
        simp only [graphTwo,↓reduceIte,hy,mul_zero,zero_sub,neg_eq_zero] at h
        exact (pow_ne_zero 2 T.a_ne_zero) h
  · rw [T.liftBeta_three h]
    exact pow_ne_zero _ (T.betaPolynomial_ne_zero h)

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open MvPolynomial
noncomputable section
abbrev BPoly := MvPolynomial (Fin 2) ℂ

def affineLinear (a b : ℂ) : BPoly := C a*X 0+C b

lemma affineLinear_regular_variable (a b : ℂ) : (1 : Fin 2) ∉ (affineLinear a b).vars := by
  intro h
  have hf := vars_add_subset (C a*X (0 : Fin 2)) (C b)
  have hg := vars_mul (C a : BPoly) (X 0)
  simp only [vars_C,vars_X,Finset.empty_union] at hg
  simp only [vars_C,Finset.union_empty] at hf
  have : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := hg (hf h)
  norm_num at this

lemma affineLinear_ne_zero_of_left {a b : ℂ} (ha : a ≠ 0) : affineLinear a b ≠ 0 := by
  intro he
  have h0 := congrArg (MvPolynomial.eval (fun _ : Fin 2 ↦ (0 : ℂ))) he
  have h1 := congrArg (MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℂ))) he
  simp only [affineLinear,map_add,map_mul,eval_C,eval_X,map_zero,mul_zero,zero_add] at h0
  simp only [affineLinear,map_mul,eval_C,eval_X,map_zero,mul_one,h0,add_zero] at h1
  exact ha h1

lemma affineLinear_ne_zero_of_right {a b : ℂ} (hb : b ≠ 0) : affineLinear a b ≠ 0 := by
  intro he
  have h := congrArg (MvPolynomial.eval (fun _ : Fin 2 ↦ (0 : ℂ))) he
  exact hb (by simpa [affineLinear] using h)

lemma determinant_graph_irreducible (p q r s : ℂ) (hd : p*s-q*r ≠ 0)
    (hn : p ≠ 0 ∨ q ≠ 0) :
    Irreducible ((C p*X 0+C q)*X 1+(C r*X 0+C s) : BPoly) := by
  apply MvPolynomial.irreducible_mul_X_add
  · rcases hn with h | h
    · exact affineLinear_ne_zero_of_left h
    · exact affineLinear_ne_zero_of_right h
  · exact affineLinear_regular_variable p q
  · exact affineLinear_regular_variable r s
  · apply IsCoprime.isRelPrime
    refine ⟨C (-r/(p*s-q*r)),C (p/(p*s-q*r)),?_⟩
    have h : (-r/(p*s-q*r))*p+(p/(p*s-q*r))*r=0 := by ring
    have h' : (-r/(p*s-q*r))*q+(p/(p*s-q*r))*s=1 := by
      calc
        _ = (p*s-q*r)/(p*s-q*r) := by ring
        _ = 1 := div_self hd
    calc
      (C (-r/(p*s-q*r)) : BPoly)*(C p*X 0+C q)+C (p/(p*s-q*r))*(C r*X 0+C s)
        = C ((-r/(p*s-q*r))*p+(p/(p*s-q*r))*r)*X 0+
          C ((-r/(p*s-q*r))*q+(p/(p*s-q*r))*s) := by
            simp only [map_add,map_mul]; ring
      _ = 1 := by rw [h,h']; simp

namespace GraphScalars
variable (T : GraphScalars)
def G1 (mixed : Bool) : BPoly := if mixed then X 0*X 1-1 else X 1-X 0
def G2 (mixed : Bool) : BPoly := if mixed then X 0*X 1-C (T.a^2) else X 1-C (T.a^2)*X 0
def G3 (mixed : Bool) : BPoly :=
  if mixed then X 1*(C (1-T.s)*X 0+C T.c)-(C T.b*X 0+C T.s)
  else X 1*(C T.c*X 0+C (1-T.s))-(C T.s*X 0+C T.b)

@[simp] lemma eval_G1 (mixed : Bool) (x y : ℂ) :
    MvPolynomial.eval ![x,y] (G1 mixed)=graphOne mixed x y := by
  cases mixed <;> simp [G1,graphOne]
@[simp] lemma eval_G2 (mixed : Bool) (x y : ℂ) :
    MvPolynomial.eval ![x,y] (T.G2 mixed)=T.graphTwo mixed x y := by
  cases mixed <;> simp [G2,graphTwo]
@[simp] lemma eval_G3 (mixed : Bool) (x y : ℂ) :
    MvPolynomial.eval ![x,y] (T.G3 mixed)=T.graphThree mixed x y := by
  cases mixed <;> simp only [G3,graphThree,Bool.false_eq_true,↓reduceIte,map_sub,map_mul,eval_X,eval_C,map_add,Matrix.cons_val_zero,Matrix.cons_val_one]; ring

lemma G1_irreducible (mixed : Bool) : Irreducible (G1 mixed) := by
  cases mixed
  · convert determinant_graph_irreducible 0 1 (-1) 0 (by norm_num) (by norm_num) using 1;
      simp [G1]; ring
  · convert determinant_graph_irreducible 1 0 0 (-1) (by norm_num) (by norm_num) using 1;
      simp [G1]; ring

lemma G2_irreducible (mixed : Bool) : Irreducible (T.G2 mixed) := by
  cases mixed
  · convert determinant_graph_irreducible 0 1 (-T.a^2) 0
      (by simpa using pow_ne_zero 2 T.a_ne_zero) (by norm_num) using 1;
      simp [G2]; ring
  · convert determinant_graph_irreducible 1 0 0 (-T.a^2)
      (by simpa using pow_ne_zero 2 T.a_ne_zero) (by norm_num) using 1;
      simp [G2]; ring

lemma G3_irreducible (mixed : Bool) : Irreducible (T.G3 mixed) := by
  have hd := T.determinant
  cases mixed
  · have hh : T.c*(-T.b)-(1-T.s)*(-T.s) ≠ 0 := by
      have : T.c*(-T.b)-(1-T.s)*(-T.s)=1 := by linear_combination hd
      rw [this]; norm_num
    convert determinant_graph_irreducible T.c (1-T.s) (-T.s) (-T.b) hh
      (Or.inl T.c_ne_zero) using 1; simp only [G3,Bool.false_eq_true,↓reduceIte,map_neg]; ring
  · have hh : (1-T.s)*(-T.s)-T.c*(-T.b) ≠ 0 := by
      have : (1-T.s)*(-T.s)-T.c*(-T.b)= -1 := by linear_combination -hd
      rw [this]; norm_num
    convert determinant_graph_irreducible (1-T.s) T.c (-T.b) (-T.s) hh
      (Or.inr T.c_ne_zero) using 1; simp only [G3,↓reduceIte,map_neg]; ring

lemma a_square_ne_one : T.a^2 ≠ 1 := by
  intro ha
  have ht := T.relative_trace
  rw [ha] at ht
  have hh : (Real.sqrt 2 : ℂ)*T.a= -1 := by linear_combination ht
  have hs := congrArg (fun z : ℂ ↦ z^2) hh
  rw [mul_pow,sqrt_two_square,ha] at hs
  norm_num at hs

lemma G1_G2_relPrime (mixed : Bool) : IsRelPrime (G1 mixed) (T.G2 mixed) := by
  apply (G1_irreducible mixed).isRelPrime_iff_not_dvd.mpr
  rintro ⟨p,hp⟩
  have he := congrArg (MvPolynomial.eval ![(1:ℂ),1]) hp
  simp only [map_mul,eval_G1,eval_G2] at he
  have hz : graphOne mixed 1 1=0 := by cases mixed <;> norm_num [graphOne]
  have hj : T.graphTwo mixed 1 1=1-T.a^2 := by cases mixed <;> norm_num [graphTwo]
  rw [hz,hj,zero_mul] at he
  exact T.a_square_ne_one (sub_eq_zero.mp he).symm

lemma G1_G3_relPrime (mixed : Bool) : IsRelPrime (G1 mixed) (T.G3 mixed) := by
  cases mixed
  · apply (G1_irreducible false).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),0]) hp
    simp [graphOne,graphThree] at he
    exact T.b_ne_zero he
  · apply IsRelPrime.symm
    apply (T.G3_irreducible true).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),T.s/T.c]) hp
    simp [graphOne,graphThree,T.c_ne_zero] at he

lemma G2_G3_relPrime (mixed : Bool) : IsRelPrime (T.G2 mixed) (T.G3 mixed) := by
  cases mixed
  · apply (T.G2_irreducible false).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),0]) hp
    simp [graphTwo,graphThree] at he
    exact T.b_ne_zero he
  · apply IsRelPrime.symm
    apply (T.G3_irreducible true).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),T.s/T.c]) hp
    simp [graphTwo,graphThree,T.c_ne_zero] at he
    exact T.a_ne_zero he

lemma graphProduct_squarefree (mixed : Bool) : Squarefree (G1 mixed*T.G2 mixed*T.G3 mixed) := by
  apply squarefree_mul_iff.mpr
  refine ⟨?_,squarefree_mul_iff.mpr ⟨T.G1_G2_relPrime mixed,
    (G1_irreducible mixed).squarefree,(T.G2_irreducible mixed).squarefree⟩,
    (T.G3_irreducible mixed).squarefree⟩
  exact (T.G1_G3_relPrime mixed).mul_left (T.G2_G3_relPrime mixed)

lemma graphProduct_dvd_of_eval_zero (mixed : Bool) (p : BPoly)
    (h : ∀ x y : ℂ, graphOne mixed x y*T.graphTwo mixed x y*T.graphThree mixed x y=0 →
      MvPolynomial.eval ![x,y] p=0) : G1 mixed*T.G2 mixed*T.G3 mixed ∣ p := by
  let J : Ideal BPoly := Ideal.span {G1 mixed*T.G2 mixed*T.G3 mixed}
  have hJ : J.IsRadical := isRadical_iff_span_singleton.mp
    (T.graphProduct_squarefree mixed).isRadical
  apply Ideal.mem_span_singleton.mp
  change p ∈ J
  rw [← hJ.radical,← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro z hz
  rw [MvPolynomial.zeroLocus_span] at hz
  have he := hz _ (Set.mem_singleton _)
  have hz' : z=![z 0,z 1] := by ext i; fin_cases i <;> rfl
  rw [hz'] at he ⊢
  simpa only [aeval_eq_eval] using h (z 0) (z 1) (by simpa only [map_mul,aeval_eq_eval,
    eval_G1,eval_G2,eval_G3] using he)
end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix

noncomputable def source_a : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) / 3)
noncomputable def source_s : ℂ :=
  1 / 2 - Complex.I * (1 + 2 * (Real.sqrt 2 : ℂ)) / (2 * (Real.sqrt 3 : ℂ))
noncomputable def source_A : Matrix (Fin 2) (Fin 2) ℂ := !![source_a, 0; 0, source_a⁻¹]
noncomputable def source_B : Matrix (Fin 2) (Fin 2) ℂ :=
  !![source_s, 1; (Real.sqrt 2 : ℂ) / 3, 1 - source_s]

lemma source_a_eq : source_a = 1 / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  unfold source_a
  rw [show Complex.I * (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

lemma sqrt_two_sq_complex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

lemma sqrt_three_sq_complex : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

lemma sqrt_three_ne_zero_complex : (Real.sqrt 3 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))

lemma source_a_inv_eq : source_a⁻¹ = 1 / 2 - (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  apply inv_eq_of_mul_eq_one_right
  rw [source_a_eq]
  calc
    (1 / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I) *
      (1 / 2 - (Real.sqrt 3 : ℂ) / 2 * Complex.I) =
      1 / 4 - (Real.sqrt 3 : ℂ) ^ 2 * Complex.I ^ 2 / 4 := by ring
    _ = 1 := by rw [sqrt_three_sq_complex, Complex.I_sq]; norm_num

lemma source_a_add_inv : source_a + source_a⁻¹ = 1 := by
  rw [source_a_inv_eq, source_a_eq]
  ring

lemma source_a_ne_zero : source_a ≠ 0 := Complex.exp_ne_zero _

lemma source_a_mul_inv : source_a * source_a⁻¹ = 1 := mul_inv_cancel₀ source_a_ne_zero

lemma source_s_mul_complement : source_s * (1 - source_s) =
    1 + (Real.sqrt 2 : ℂ) / 3 := by
  unfold source_s
  field_simp
  ring_nf
  rw [sqrt_three_sq_complex, sqrt_two_sq_complex, Complex.I_sq]
  ring

open Polynomial
noncomputable section

lemma source_a_square : source_a ^ 2 - source_a + 1 = 0 := by
  have h := congrArg (fun z : ℂ ↦ source_a * z) source_a_add_inv
  rw [mul_add, source_a_mul_inv] at h
  linear_combination h

lemma source_a_cube : source_a ^ 3 = -1 := by
  linear_combination (source_a + 1) * source_a_square

lemma source_a_twentyfour : source_a ^ 24 = 1 := by
  rw [show (24 : ℕ) = 3 * 8 by norm_num, pow_mul, source_a_cube]
  norm_num

end
end QuadricCounterexample

namespace QuadricCounterexample
noncomputable section

lemma source_graph_trace : source_s+source_a^2*(1-source_s)+
    (Real.sqrt 2 : ℂ)*source_a=0 := by
  have hh : source_a⁻¹*source_s+source_a*(1-source_s)= -(Real.sqrt 2 : ℂ) := by
    rw [source_a_inv_eq,source_a_eq]
    unfold source_s
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have ha := source_a_mul_inv
  linear_combination source_a*hh-source_s*ha

def sourceGraphScalars : GraphScalars where
  a := source_a
  s := source_s
  b := 1
  c := (Real.sqrt 2 : ℂ)/3
  a_cube := source_a_cube
  determinant := by simpa only [one_mul] using source_s_mul_complement
  relative_trace := source_graph_trace
  b_ne_zero := one_ne_zero
  c_ne_zero := div_ne_zero (by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2))
    (by norm_num)

namespace GraphScalars
variable (T : GraphScalars)

def swapped : GraphScalars where
  a := T.a⁻¹
  s := 1-T.s
  b := T.c
  c := T.b
  a_cube := by rw [inv_pow,T.a_cube]; norm_num
  determinant := by have h:=T.determinant; linear_combination h
  relative_trace := by
    have h:=T.relative_trace
    field_simp [T.a_ne_zero]
    linear_combination h
  b_ne_zero := T.c_ne_zero
  c_ne_zero := T.b_ne_zero

@[simp] lemma swapped_swapped : T.swapped.swapped=T := by
  cases T
  simp [swapped]

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix MvPolynomial
noncomputable section

def affineRepresentative {R : Type u1} [Zero R] [One R] (i : Fin 2) (z : R) : Fin 2 → R :=
  if i=0 then ![1,z] else ![z,1]

@[simp] lemma affineRepresentative_index {R : Type u2} [Zero R] [One R]
    (i : Fin 2) (z : R) : affineRepresentative i z i=1 := by
  fin_cases i <;> simp [affineRepresentative]

lemma affineRepresentative_change (i j : Fin 2) {z : ℂ} (h : i=j ∨ z ≠ 0) :
    affineRepresentative i z = scalarFactor i j z •
      affineRepresentative j (scalarCoordinateChange i j z) := by
  rcases h with rfl | hz
  · simp [scalarFactor,scalarCoordinateChange]
  · fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
      simp [affineRepresentative,scalarFactor,scalarCoordinateChange,hz]

def matrixGraphValue (M : TwoMatrix) (i : StandardChart) (z : BaseCoordinates) : ℂ :=
  let X := affineRepresentative i.1 z.1
  let Y := affineRepresentative i.2 z.2
  Y 0*(M 1 0*X 0+M 1 1*X 1)-Y 1*(M 0 0*X 0+M 0 1*X 1)

def matrixGraphPolynomial (M : TwoMatrix) (i : StandardChart) : BasePolynomial :=
  let x := affineRepresentative i.1 (X 0 : BasePolynomial)
  let y := affineRepresentative i.2 (X 1 : BasePolynomial)
  y 0*(C (M 1 0)*x 0+C (M 1 1)*x 1)-y 1*(C (M 0 0)*x 0+C (M 0 1)*x 1)

@[simp] lemma baseEval_matrixGraphPolynomial (M : TwoMatrix) (i : StandardChart)
    (z : BaseCoordinates) : baseEval (matrixGraphPolynomial M i) z=matrixGraphValue M i z := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [baseEval,matrixGraphPolynomial,matrixGraphValue,affineRepresentative]

lemma matrixGraphValue_change (M : TwoMatrix) (i j : StandardChart) (z : BaseCoordinates)
    (hz : z ∈ coordinateOverlap i j) :
    matrixGraphValue M i z=firstFactor i j z*secondFactor i j z*
      matrixGraphValue M j (coordinateChange i j z) := by
  have hi := ((coordinateOverlap_iff i j z).mp hz).1
  have hj := ((coordinateOverlap_iff i j z).mp hz).2
  have hx := affineRepresentative_change i.1 j.1 hi
  have hy := affineRepresentative_change i.2 j.2 hj
  unfold matrixGraphValue
  rw [hx,hy]
  simp only [Pi.smul_apply,smul_eq_mul,firstFactor,secondFactor,coordinateChange]
  ring

def matrixBranchDenominator (M : TwoMatrix) (i : StandardChart) (z : BaseCoordinates) : ℂ :=
  M i.2 0*affineRepresentative i.1 z.1 0+M i.2 1*affineRepresentative i.1 z.1 1

lemma matrixGraphValue_zero_iff (M : TwoMatrix) (i : StandardChart) (z : BaseCoordinates) :
    matrixGraphValue M i z=0 ↔ M *ᵥ affineRepresentative i.1 z.1=
      matrixBranchDenominator M i z • affineRepresentative i.2 z.2 := by
  constructor
  · intro h
    ext k
    fin_cases k <;> rcases i with ⟨i,j⟩ <;> fin_cases j <;>
      simp only [matrixGraphValue,affineRepresentative,↓reduceIte,Fin.isValue,Fin.zero_eta,
        Fin.mk_one,one_ne_zero,mulVec,Fin.sum_univ_two,dotProduct,
        Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
        one_mul,matrixBranchDenominator,mul_one] at h ⊢ <;> first | linear_combination h | linear_combination -h
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [mulVec,Fin.sum_univ_two,dotProduct,Pi.smul_apply,smul_eq_mul] at h0 h1
    dsimp only [matrixGraphValue]
    rw [h0,h1]
    ring

lemma matrixBranchDenominator_change (M : TwoMatrix) (i j : StandardChart)
    (z : BaseCoordinates) (hz : z ∈ coordinateOverlap i j) (h : matrixGraphValue M i z=0) :
    matrixBranchDenominator M i z*secondFactor i j z=
      firstFactor i j z*matrixBranchDenominator M j (coordinateChange i j z) := by
  have hv := (matrixGraphValue_zero_iff M i z).mp h
  have hx := affineRepresentative_change i.1 j.1 (((coordinateOverlap_iff i j z).mp hz).1)
  have hy := affineRepresentative_change i.2 j.2 (((coordinateOverlap_iff i j z).mp hz).2)
  rw [hx,hy,mulVec_smul] at hv
  have hj := congrFun hv j.2
  simp only [Pi.smul_apply,smul_eq_mul,affineRepresentative_index,mul_one,
    mulVec,dotProduct,Fin.sum_univ_two] at hj
  exact hj.symm

namespace GraphScalars
variable (T : GraphScalars)

def matrices (k : Fin 3) : TwoMatrix :=
  ![(1 : TwoMatrix),!![T.a,0;0,T.a⁻¹],!![T.s,T.b;T.c,1-T.s]] k

def chartScalars (i : StandardChart) : GraphScalars := if i.2=0 then T.swapped else T

def mixedChart (i : StandardChart) : Bool := decide (i.1 ≠ i.2)

def chartProduct (i : StandardChart) : BasePolynomial :=
  G1 (mixedChart i)*(T.chartScalars i).G2 (mixedChart i)*(T.chartScalars i).G3 (mixedChart i)

def divisorPolynomial (i : StandardChart) : BasePolynomial :=
  matrixGraphPolynomial (T.matrices 0) i*matrixGraphPolynomial (T.matrices 1) i*
    matrixGraphPolynomial (T.matrices 2) i

def chartUnit (i : StandardChart) : ℂ := if i.2=0 then -T.a else T.a⁻¹

lemma chartUnit_ne_zero (i : StandardChart) : T.chartUnit i ≠ 0 := by
  unfold chartUnit
  split_ifs <;> simpa using T.a_ne_zero

lemma divisorPolynomial_eq (i : StandardChart) :
    T.divisorPolynomial i=C (T.chartUnit i)*T.chartProduct i := by
  apply MvPolynomial.funext
  intro z
  have hz : z=![z 0,z 1] := by ext k; fin_cases k <;> rfl
  rw [hz]
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [divisorPolynomial,matrixGraphPolynomial,affineRepresentative,matrices,
      chartUnit,chartProduct,chartScalars,mixedChart,swapped,G1,G2,G3] <;>
    field_simp [T.a_ne_zero] <;> ring

lemma divisorPolynomial_reduced (i : StandardChart) : Squarefree (T.divisorPolynomial i) := by
  have hu : IsUnit (C (T.chartUnit i) : BasePolynomial) :=
    (isUnit_iff_ne_zero.mpr (T.chartUnit_ne_zero i)).map C
  rw [T.divisorPolynomial_eq]
  apply Squarefree.squarefree_of_dvd ?_ ((T.chartScalars i).graphProduct_squarefree (mixedChart i))
  change C (T.chartUnit i)*T.chartProduct i ∣ T.chartProduct i
  exact hu.mul_left_dvd.mpr (dvd_refl _)

lemma divisorPolynomial_nonzero (i : StandardChart) : T.divisorPolynomial i ≠ 0 :=
  (T.divisorPolynomial_reduced i).ne_zero

lemma divisorPolynomial_change (i j : StandardChart) (z : BaseCoordinates)
    (hz : z ∈ coordinateOverlap i j) :
    baseEval (T.divisorPolynomial i) z = (firstFactor i j z*secondFactor i j z)^3*
      baseEval (T.divisorPolynomial j) (coordinateChange i j z) := by
  simp only [divisorPolynomial,baseEval_mul,baseEval_matrixGraphPolynomial]
  rw [matrixGraphValue_change _ i j z hz,matrixGraphValue_change (T.matrices 1) i j z hz,
    matrixGraphValue_change (T.matrices 2) i j z hz]
  ring

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix MvPolynomial
noncomputable section
namespace GraphScalars
variable (T : GraphScalars)

def branchGraph (k : Fin 3) (mixed : Bool) (x y : ℂ) : ℂ :=
  ![graphOne mixed x y,T.graphTwo mixed x y,T.graphThree mixed x y] k

def branchDenominator (k : Fin 3) (mixed : Bool) (x : ℂ) : ℂ :=
  ![if mixed then x else 1,
    if mixed then T.a⁻¹*x else T.a⁻¹,
    if mixed then (1-T.s)*x+T.c else T.c*x+1-T.s] k

lemma liftBeta_branch_one (mixed : Bool) (x y : ℂ)
    (h : graphOne mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator 0 mixed x)^24=1 := by
  rw [T.liftBeta_one h]
  cases mixed
  · simp [branchDenominator]
  · have he : x*y=1 := sub_eq_zero.mp h
    change y^24*x^24=1
    rw [← mul_pow,mul_comm y x,he,one_pow]

lemma liftBeta_branch_two (mixed : Bool) (x y : ℂ)
    (h : T.graphTwo mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator 1 mixed x)^24=1 := by
  rw [T.liftBeta_two h]
  cases mixed
  · simp [branchDenominator,inv_pow,T.a_twentyfour]
  · have he : x*y=T.a^2 := sub_eq_zero.mp h
    change y^24*(T.a⁻¹*x)^24=1
    calc
      y^24*(T.a⁻¹*x)^24 = (T.a⁻¹)^24*(x*y)^24 := by ring
      _ = 1 := by
        rw [he,inv_pow,← pow_mul,mul_comm 2 24,pow_mul,T.a_twentyfour]
        norm_num

lemma liftBeta_branch_three (mixed : Bool) (x y : ℂ)
    (h : T.graphThree mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator 2 mixed x)^24=1 := by
  rw [T.liftBeta_three h,← mul_pow]
  cases mixed
  · have he : T.L.eval y*(T.c*x+1-T.s)=1 := by
      simp only [graphThree,Bool.false_eq_true,↓reduceIte] at h
      simp only [L,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
      linear_combination -T.c*h+T.determinant
    change (T.L.eval y*(T.c*x+1-T.s))^24=1
    rw [he,one_pow]
  · have he : T.J.eval y*((1-T.s)*x+T.c)= -1 := by
      simp only [graphThree,↓reduceIte] at h
      simp only [J,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
      linear_combination -(1-T.s)*h-T.determinant
    change (T.J.eval y*((1-T.s)*x+T.c))^24=1
    rw [he]
    norm_num

lemma liftBeta_branch (k : Fin 3) (mixed : Bool) (x y : ℂ)
    (h : T.branchGraph k mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator k mixed x)^24=1 := by
  fin_cases k
  · exact T.liftBeta_branch_one mixed x y h
  · exact T.liftBeta_branch_two mixed x y h
  · exact T.liftBeta_branch_three mixed x y h

@[simp] lemma baseEval_pow (p : BasePolynomial) (n : ℕ) (z : BaseCoordinates) :
    baseEval (p^n) z=baseEval p z^n := map_pow (MvPolynomial.eval _) _ _

def liftPolynomial (mixed : Bool) : BasePolynomial :=
  (if mixed then X 1^24 else 1)+G1 mixed*T.G2 mixed*
    (Polynomial.aeval (X 1) (T.betaPolynomial mixed))^2*
    (Polynomial.aeval (X 1) (if mixed then T.mixedQuotient else T.sameQuotient))

lemma eval_aeval_snd (p : Polynomial ℂ) (z : BaseCoordinates) :
    baseEval (Polynomial.aeval (X 1 : BasePolynomial) p) z=p.eval z.2 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,baseEval,Polynomial.eval_add] at hp hq ⊢; rw [hp,hq]
  | monomial n a => simp [Polynomial.aeval_monomial,baseEval]

lemma eval_liftPolynomial (mixed : Bool) (z : BaseCoordinates) :
    baseEval (T.liftPolynomial mixed) z=T.liftBeta mixed z.1 z.2 := by
  cases mixed <;>
    simp only [liftPolynomial,liftBeta,Bool.false_eq_true,↓reduceIte,baseEval_add,baseEval_mul,
      baseEval_pow,eval_aeval_snd] <;> simp [baseEval]

def chartLift (i : StandardChart) : BasePolynomial :=
  (T.chartScalars i).liftPolynomial (mixedChart i)

lemma eval_chartLift (i : StandardChart) (z : BaseCoordinates) :
    baseEval (T.chartLift i) z=(T.chartScalars i).liftBeta (mixedChart i) z.1 z.2 :=
  (T.chartScalars i).eval_liftPolynomial _ _

lemma matrixGraphValue_eq_branch (k : Fin 3) (i : StandardChart) (z : BaseCoordinates) :
    matrixGraphValue (T.matrices k) i z =
      (if i.2=0 then -1 else 1)*
      (if k=1 then (T.chartScalars i).a⁻¹ else 1)*
      (T.chartScalars i).branchGraph k (mixedChart i) z.1 z.2 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrixGraphValue,affineRepresentative,matrices,chartScalars,swapped,
      mixedChart,branchGraph,graphOne,graphTwo,graphThree] <;>
    field_simp [T.a_ne_zero] <;> first | (solve | ring) | (left; ring)

lemma matrixBranchDenominator_eq (k : Fin 3) (i : StandardChart) (z : BaseCoordinates) :
    matrixBranchDenominator (T.matrices k) i z=
      (T.chartScalars i).branchDenominator k (mixedChart i) z.1 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrixBranchDenominator,affineRepresentative,matrices,chartScalars,
      swapped,mixedChart,branchDenominator] <;> ring

lemma chartLift_branch (k : Fin 3) (i : StandardChart) (z : BaseCoordinates)
    (h : matrixGraphValue (T.matrices k) i z=0) :
    baseEval (T.chartLift i) z*(matrixBranchDenominator (T.matrices k) i z)^24=1 := by
  rw [T.matrixGraphValue_eq_branch] at h
  have hn : (if i.2=0 then (-1 : ℂ) else 1)≠0 := by split_ifs <;> norm_num
  have hn' : (if k=1 then (T.chartScalars i).a⁻¹ else 1)≠0 := by
    split_ifs
    · exact inv_ne_zero (T.chartScalars i).a_ne_zero
    · exact one_ne_zero
  have hh := (mul_eq_zero.mp h).resolve_left (mul_ne_zero hn hn')
  rw [T.eval_chartLift,T.matrixBranchDenominator_eq]
  exact (T.chartScalars i).liftBeta_branch _ _ _ _ hh

lemma divisor_zero_branch (i : StandardChart) (z : BaseCoordinates)
    (h : baseEval (T.divisorPolynomial i) z=0) :
    ∃ k : Fin 3, matrixGraphValue (T.matrices k) i z=0 := by
  simp only [divisorPolynomial,baseEval_mul,baseEval_matrixGraphPolynomial,mul_eq_zero] at h
  rcases h with (h|h)|h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩

lemma chartLift_unit (i : StandardChart) (z : BaseCoordinates)
    (h : baseEval (T.divisorPolynomial i) z=0) : baseEval (T.chartLift i) z ≠ 0 := by
  obtain ⟨k,hk⟩ := T.divisor_zero_branch i z h
  exact left_ne_zero_of_mul_eq_one (T.chartLift_branch k i z hk)

lemma chartLift_change (i j : StandardChart) (z : BaseCoordinates)
    (hz : z ∈ coordinateOverlap i j) (h : baseEval (T.divisorPolynomial i) z=0) :
    secondFactor i j z^24*baseEval (T.chartLift j) (coordinateChange i j z)=
      baseEval (T.chartLift i) z*firstFactor i j z^24 := by
  obtain ⟨k,hk⟩ := T.divisor_zero_branch i z h
  have hg := matrixGraphValue_change (T.matrices k) i j z hz
  have hs := firstFactor_ne_zero hz
  have ht := secondFactor_ne_zero hz
  have hkj : matrixGraphValue (T.matrices k) j (coordinateChange i j z)=0 := by
    rw [hk] at hg
    exact (mul_eq_zero.mp hg.symm).resolve_left (mul_ne_zero hs ht)
  have hi := T.chartLift_branch k i z hk
  have hj := T.chartLift_branch k j (coordinateChange i j z) hkj
  have hd := matrixBranchDenominator_change (T.matrices k) i j z hz hk
  have hd' : matrixBranchDenominator (T.matrices k) i z ≠ 0 := by
    exact fun he ↦ by simp [he] at hi
  have hdp := congrArg (fun a : ℂ ↦ a^24) hd
  simp only [mul_pow] at hdp
  apply mul_right_cancel₀ (pow_ne_zero 24 hd')
  calc
    _ = baseEval (T.chartLift j) (coordinateChange i j z)*
        (matrixBranchDenominator (T.matrices k) i z^24*secondFactor i j z^24) := by ring
    _ = firstFactor i j z^24 := by rw [hdp]; linear_combination firstFactor i j z^24*hj
    _ = _ := by linear_combination -firstFactor i j z^24*hi

def equalizerData : EqualizerData where
  divisor := T.divisorPolynomial
  lift := T.chartLift
  reduced := T.divisorPolynomial_reduced
  nonzero := T.divisorPolynomial_nonzero
  divisor_change := T.divisorPolynomial_change
  lift_change := T.chartLift_change
  lift_unit := T.chartLift_unit

end GraphScalars

def sourceBundle : AlgebraicRankTwoBundle := sourceGraphScalars.equalizerData.bundle

end
end QuadricCounterexample

end OAI
