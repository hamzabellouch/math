import Mathlib

namespace OAI

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma minpoly_reverse_eval_ne_zero (b : L) (hb : IsAlgebraic ℚ b) (t : ℚ)
    (ht : 1-b*algebraMap ℚ L t ≠ 0) : (minpoly ℚ b).reverse.eval t ≠ 0 := by
  intro hz
  by_cases ht0 : t = 0
  · subst t
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, (minpoly.monic hb.isIntegral).leadingCoeff] at hz
    exact one_ne_zero hz
  let : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht0)
  have hp : (minpoly ℚ b).IsRoot t⁻¹ := by
    have he := (eval₂_reverse_eq_zero_iff (RingHom.id ℚ) t⁻¹ (minpoly ℚ b))
    simp only [invOf_eq_inv, inv_inv, eval₂_id] at he
    exact he.mp hz
  have he := minpoly.root hb.isIntegral hp
  apply ht
  rw [← he, ← map_mul, inv_mul_cancel₀ ht0, map_one, sub_self]

/-- A scalar-rational common denominator for an algebraic linear reciprocal. -/
lemma reciprocal_denominator (b : L) (hb : IsAlgebraic ℚ b) :
    ∃ (P : ℚ[X]) (R : L[X]), P.coeff 0 = 1 ∧
      (1-C b*X)*R = P.map (algebraMap ℚ L) ∧
      ∀ t : ℚ, 1-b*algebraMap ℚ L t ≠ 0 → P.eval t ≠ 0 := by
  by_cases hb0 : b = 0
  · subst b
    exact ⟨1,1,by simp,by simp,by simp⟩
  let p := minpoly ℚ b
  have hm : p.Monic := minpoly.monic hb.isIntegral
  let : Invertible b := invertibleOfNonzero hb0
  have hz : (p.reverse.map (algebraMap ℚ L)).IsRoot b⁻¹ := by
    rw [IsRoot, eval_map]
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℚ L) b p).mpr (minpoly.aeval ℚ b)
    simpa only [invOf_eq_inv] using h
  obtain ⟨R,hR⟩ := (dvd_iff_isRoot.mpr hz)
  refine ⟨p.reverse,C (-b⁻¹)*R,?_,?_,minpoly_reverse_eval_ne_zero b hb⟩
  · rw [coeff_zero_reverse, hm.leadingCoeff]
  · calc
      _ = (X-C b⁻¹)*R := by
        have he : (1-C b*X)*C (-b⁻¹) = X-C b⁻¹ := by
          have hc : C b*C b⁻¹ = (1 : L[X]) := by rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
          rw [map_neg]
          calc
            _ = (C b*C b⁻¹)*X-C b⁻¹ := by ring
            _ = _ := by rw [hc, one_mul]
        rw [← mul_assoc, he]
      _ = _ := hR.symm

/-- Coefficientwise transport by a rational linear functional. -/
def polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) : ℚ[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange ℓ (map_zero ℓ)))
@[simp] lemma coeff_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (n : ℕ) :
    (polyLinear ℓ p).coeff n = ℓ (p.coeff n) := rfl
lemma polyLinear_add (ℓ : L →ₗ[ℚ] ℚ) (p q : L[X]) :
    polyLinear ℓ (p+q) = polyLinear ℓ p + polyLinear ℓ q := by
  ext n
  simp only [coeff_polyLinear, coeff_add, map_add]
lemma polyLinear_monomial (ℓ : L →ₗ[ℚ] ℚ) (n : ℕ) (a : L) :
    polyLinear ℓ (monomial n a) = monomial n (ℓ a) := by
  ext k
  simp only [coeff_polyLinear, coeff_monomial]
  split_ifs <;> simp
lemma eval_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (t : ℚ) :
    (polyLinear ℓ p).eval t = ℓ (p.eval (algebraMap ℚ L t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [polyLinear_add, eval_add, hp, hq, map_add]
  | monomial n a =>
    rw [polyLinear_monomial, eval_monomial, eval_monomial]
    have he : a*(algebraMap ℚ L t)^n = (t^n) • a := by
      rw [Algebra.smul_def, map_pow, mul_comm]
    rw [he, map_smul]
    exact mul_comm _ _

lemma polyLinear_eq_zero_iff (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) :
    polyLinear ℓ p = 0 ↔ ∀ t : ℚ, ℓ (p.eval (algebraMap ℚ L t)) = 0 := by
  simp_rw [← eval_polyLinear]
  exact ⟨fun he _ => by rw [he, eval_zero], fun h => Polynomial.funext fun t => by simpa using h t⟩

/-- The first three formal coefficients of the Cayley curve force annihilation
of 1, b and b². No analytic continuity is used. -/
lemma cayley_annihilation (b : L) (hb : IsAlgebraic ℚ b) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, 1-b*(algebraMap ℚ L t) ≠ 0)
    (h : ∀ t : ℚ, ℓ ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) = 0) :
    ℓ 1 = 0 ∧ ℓ b = 0 ∧ ℓ (b^2) = 0 := by
  obtain ⟨P,R,hP,hR,_hPreg⟩ := reciprocal_denominator b hb
  have hR' : R-(C b*R)*X = P.map (algebraMap ℚ L) := by
    convert hR using 1
    ring
  let T := R+(C b*R)*X
  have hT : polyLinear ℓ T = 0 := by
    apply (polyLinear_eq_zero_iff ℓ T).mpr
    intro t
    have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
    have he : T.eval (algebraMap ℚ L t) =
        (P.eval t) • ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) := by
      dsimp only [T]
      simp only [eval_add, eval_mul, eval_C, eval_X, Algebra.smul_def]
      rw [← hRt]
      rw [← mul_div_assoc, eq_div_iff (hd t)]
      ring
    rw [he, map_smul, h t, smul_zero]
  have h0 : R.coeff 0 = 1 := by
    have he := congrArg (fun p : L[X] => p.coeff 0) hR'
    simpa only [coeff_sub, coeff_mul_X_zero, sub_zero, coeff_map, hP, map_one] using he
  have h1 : R.coeff 1-b = algebraMap ℚ L (P.coeff 1) := by
    have he := congrArg (fun p : L[X] => p.coeff 1) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, h0, mul_one, coeff_map] using he
  have h2 : R.coeff 2-b*R.coeff 1 = algebraMap ℚ L (P.coeff 2) := by
    have he := congrArg (fun p : L[X] => p.coeff 2) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, coeff_map] using he
  have ht0 : ℓ 1 = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 0) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X_zero, add_zero, h0, coeff_zero] using he
  have ht1 : ℓ (R.coeff 1) + ℓ b = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 1) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul, h0, mul_one,
      map_add, coeff_zero] using he
  have ht2 : ℓ (R.coeff 2) + ℓ (b*R.coeff 1) = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul,
      map_add, coeff_zero] using he
  have hlQ (c : ℚ) : ℓ (algebraMap ℚ L c) = 0 := by
    have he : algebraMap ℚ L c = c • (1:L) := by rw [Algebra.smul_def, mul_one]
    rw [he, map_smul, ht0, smul_zero]
  have hh1 := congrArg ℓ h1
  rw [map_sub, hlQ] at hh1
  have hb0 : ℓ b = 0 := by linarith
  have hh2 := congrArg ℓ h2
  rw [map_sub, hlQ] at hh2
  have hbR : ℓ (b*R.coeff 1) = 0 := by linarith
  have hR1 : R.coeff 1 = algebraMap ℚ L (P.coeff 1)+b := sub_eq_iff_eq_add.mp h1
  rw [hR1, mul_add, map_add] at hbR
  have he : b*algebraMap ℚ L (P.coeff 1) = (P.coeff 1) • b := by
    rw [Algebra.smul_def, mul_comm]
  rw [he, map_smul, hb0, smul_zero, zero_add, ← sq] at hbR
  exact ⟨ht0,hb0,hbR⟩

end EuclideanFiveColor.AlgebraicCayley

end

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma linearFraction_polynomials (a b c d : L) (hc : c ≠ 0)
    (hb : IsAlgebraic ℚ (-d/c)) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, c+d*algebraMap ℚ L t ≠ 0) :
    ∃ P Q : ℚ[X], ∀ t : ℚ, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t * ℓ ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
  obtain ⟨Q,R,hQ,hR,hQreg⟩ := reciprocal_denominator (-d/c) hb
  clear hQ
  have hdn (t : ℚ) : 1-(-d/c)*algebraMap ℚ L t ≠ 0 := by
    intro hh
    apply hd t
    have he : c+d*algebraMap ℚ L t = c*(1-(-d/c)*algebraMap ℚ L t) := by
      field_simp
      ring
    rw [he, hh, mul_zero]
  let U : L[X] := (C (a/c)+C (b/c)*X)*R
  refine ⟨polyLinear ℓ U,Q,fun t => ⟨hQreg t (hdn t),?_⟩⟩
  rw [eval_polyLinear]
  have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
  simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
  have he : U.eval (algebraMap ℚ L t) =
      (Q.eval t) • ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
    dsimp only [U]
    simp only [eval_mul, eval_add, eval_C, eval_X, Algebra.smul_def]
    rw [← hRt, ← mul_div_assoc, eq_div_iff (hd t)]
    field_simp
    ring
  rw [he, map_smul, smul_eq_mul]

/-- Finite simultaneous avoidance for rational functions with no rational poles. -/
lemma rational_functions_avoid {ι : Type*} (s : Finset ι) (f : ι → ℚ → ℚ)
    (hpoly : ∀ i ∈ s, ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧ P.eval t = Q.eval t*f i t)
    (hn : ∀ i ∈ s, ∃ t, f i t ≠ 0) :
    ∃ t, ∀ i ∈ s, f i t ≠ 0 := by
  classical
  choose P Q hQ using fun i : s => hpoly i i.property
  have hP (i : s) : P i ≠ 0 := by
    obtain ⟨t,ht⟩ := hn i i.property
    intro he
    have hh := (hQ i t).2
    rw [he, eval_zero] at hh
    exact mul_ne_zero (hQ i t).1 ht hh.symm
  have hz : (∏ i : s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => hP _)
  obtain ⟨t,ht⟩ : ∃ t : ℚ, (∏ i : s, P i).eval t ≠ 0 := by
    by_contra! hn
    exact hz (Polynomial.funext fun t => by simpa using hn t)
  refine ⟨t,fun i hi hh => ?_⟩
  have hpt : (P ⟨i,hi⟩).eval t ≠ 0 := by
    rw [eval_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht _ (Finset.mem_univ _)
  apply hpt
  rw [(hQ ⟨i,hi⟩ t).2, hh, mul_zero]

/-- An affine-line rational curve escaping each hyperplane also escapes their finite union. -/
lemma finite_hyperplanes_avoid {T : Type*} [Nonempty T]
    (f : T → L) (line : T → T → ℚ → T)
    (hzero : ∀ a b, line a b 0 = a) (hone : ∀ a b, line a b 1 = b)
    (hline : ∀ a b (ℓ : L →ₗ[ℚ] ℚ), ∃ P Q : ℚ[X], ∀ t,
      Q.eval t ≠ 0 ∧ P.eval t = Q.eval t * ℓ (f (line a b t)))
    (s : Finset (L →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ∃ t, ℓ (f t) ≠ 0) :
    ∃ t, ∀ ℓ ∈ s, ℓ (f t) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary T, by simp⟩
  | @insert ℓ s hℓ ih =>
    obtain ⟨a,ha⟩ := ih (fun ψ hψ => hs ψ (Finset.mem_insert_of_mem hψ))
    obtain ⟨b,hb⟩ := hs ℓ (Finset.mem_insert_self _ _)
    obtain ⟨t,ht⟩ := rational_functions_avoid (insert ℓ s)
      (fun ψ t => ψ (f (line a b t))) (fun ψ _ => hline a b ψ) (by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact ⟨1,by simpa only [hone] using hb⟩
        · exact ⟨0,by simpa only [hzero] using ha ψ hψ⟩)
    exact ⟨line a b t,ht⟩
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley
variable (N : IntermediateField ℚ ℂ)
def realSlice : Subfield ℝ := N.toSubfield.comap Complex.ofRealHom
def asN : realSlice N →+* N where
  toFun a := ⟨(a : ℝ),a.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp
@[simp] lemma coe_asN (a : realSlice N) : ((asN N a : N) : ℂ) = (a : ℝ) := rfl
variable (hi : Complex.I ∈ N)
def iN : N := ⟨Complex.I, hi⟩
@[simp] lemma coe_iN : ((iN N hi : N) : ℂ) = Complex.I := rfl
lemma iN_sq : iN N hi ^2 = -1 := by ext; exact Complex.I_sq
lemma cayley_den_ne (a : realSlice N) : 1-iN N hi*asN N a ≠ 0 := by
  intro h
  have hh := congrArg (fun z : N => (z : ℂ).re) h
  simp [iN, asN] at hh

def realCayley (a : realSlice N) : N :=
  (1+iN N hi*asN N a)/(1-iN N hi*asN N a)
lemma cayley_real_norm (a : realSlice N) : ‖((realCayley N hi a : N) : ℂ)‖ = 1 := by
  change ‖(1+Complex.I*(a:ℝ))/(1-Complex.I*(a:ℝ))‖ = 1
  have hn : ‖(1+Complex.I*(a:ℝ))‖ = ‖(1-Complex.I*(a:ℝ))‖ := by
    have he : conj (1+Complex.I*(a:ℝ)) = 1-Complex.I*(a:ℝ) := by simp; ring
    rw [← he, Complex.norm_conj]
  rw [norm_div, hn, div_self]
  apply norm_ne_zero_iff.mpr
  intro hz
  have he := congrArg Complex.re hz
  simp at he

variable [FiniteDimensional ℚ N]
lemma cayley_functional_escape
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (ℓ : N →ₗ[ℚ] ℚ) (hℓ : ℓ ≠ 0) :
    ∃ a : realSlice N, ℓ (realCayley N hi a) ≠ 0 := by
  by_contra! hh
  have hx (a : realSlice N) : ℓ 1 = 0 ∧ ℓ (iN N hi*asN N a) = 0 ∧
      ℓ ((asN N a)^2) = 0 := by
    have he (t : ℚ) : asN N (a*algebraMap ℚ (realSlice N) t) =
        asN N a*algebraMap ℚ N t := by simp
    have hd (t : ℚ) : 1-(iN N hi*asN N a)*algebraMap ℚ N t ≠ 0 := by
      simpa only [he, mul_assoc] using cayley_den_ne N hi (a*algebraMap ℚ (realSlice N) t)
    have ha (t : ℚ) : ℓ ((1+(iN N hi*asN N a)*algebraMap ℚ N t)/
        (1-(iN N hi*asN N a)*algebraMap ℚ N t)) = 0 := by
      simpa only [realCayley, he, mul_assoc] using hh (a*algebraMap ℚ (realSlice N) t)
    obtain ⟨h1,hia,hsa⟩ := cayley_annihilation (iN N hi*asN N a)
      (Algebra.IsAlgebraic.isAlgebraic _) ℓ hd ha
    rw [mul_pow, iN_sq, neg_one_mul, map_neg, neg_eq_zero] at hsa
    exact ⟨h1,hia,hsa⟩
  have hreal (a : realSlice N) : ℓ (asN N a) = 0 := by
    have h1 := (hx (a+1)).2.2
    have h2 := (hx (a-1)).2.2
    have he : (asN N (a+1))^2-(asN N (a-1))^2 = (4:ℚ) • asN N a := by
      simp only [map_add, map_one, map_sub, Algebra.smul_def, map_ofNat]
      ring
    have hh := congrArg ℓ he
    rw [map_sub, h1,h2,sub_self,map_smul,smul_eq_mul] at hh
    linarith
  apply hℓ
  ext z
  let a : realSlice N := ⟨(z:ℂ).re,hre z⟩
  let b : realSlice N := ⟨(z:ℂ).im,him z⟩
  have he : z = asN N a+iN N hi*asN N b := by
    apply Subtype.ext
    change (z:ℂ) = (z:ℂ).re+Complex.I*(z:ℂ).im
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  rw [he,map_add,hreal,(hx b).2.1,add_zero]
  rfl

def realLine (a b : realSlice N) (t : ℚ) : realSlice N :=
  a+algebraMap ℚ (realSlice N) t*(b-a)
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_zero (a b : realSlice N) : realLine N a b 0 = a := by simp [realLine]
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_one (a b : realSlice N) : realLine N a b 1 = b := by simp [realLine]
lemma cayley_line_polynomials (a b : realSlice N) (ℓ : N →ₗ[ℚ] ℚ) :
    ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t*ℓ (realCayley N hi (realLine N a b t)) := by
  let A := 1+iN N hi*asN N a
  let B := iN N hi*(asN N b-asN N a)
  let C := 1-iN N hi*asN N a
  let D := -iN N hi*(asN N b-asN N a)
  have he (t : ℚ) : asN N (realLine N a b t) =
      asN N a+algebraMap ℚ N t*(asN N b-asN N a) := by simp [realLine]
  have hd (t : ℚ) : C+D*algebraMap ℚ N t = 1-iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [C,D]; ring
  have hn (t : ℚ) : A+B*algebraMap ℚ N t = 1+iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [A,B]; ring
  obtain ⟨P,Q,hPQ⟩ := linearFraction_polynomials A B C D (cayley_den_ne N hi a)
    (Algebra.IsAlgebraic.isAlgebraic _) ℓ (fun t => by rw [hd]; exact cayley_den_ne N hi _)
  refine ⟨P,Q,fun t => ?_⟩
  simpa only [hn,hd,realCayley] using hPQ t

lemma cayley_finite_avoid
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (s : Finset (N →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ℓ ≠ 0) :
    ∃ a : realSlice N, ∀ ℓ ∈ s, ℓ (realCayley N hi a) ≠ 0 :=
  finite_hyperplanes_avoid (realCayley N hi) (realLine N)
    (realLine_zero N) (realLine_one N) (cayley_line_polynomials N hi) s
    (fun ℓ hℓ => cayley_functional_escape N hi hre him ℓ (hs ℓ hℓ))
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

def General (s : Finset V) : Prop :=
  ∀ t ⊆ s, t.card ≤ finrank ℚ V → LinearIndepOn ℚ id (t : Set V)

omit [FiniteDimensional ℚ V] in
/-- Finite general-position sets from avoidance of finitely many proper subspaces. -/
lemma exists_general (A : Set V) (hd : 2 ≤ finrank ℚ V)
    (ha : ∀ P : Finset (Submodule ℚ V), (∀ p ∈ P, p < ⊤) →
      ∃ x ∈ A, ∀ p ∈ P, x ∉ p) (n : ℕ) :
    ∃ s : Finset V, s.card = n ∧ (s : Set V) ⊆ A ∧ General s := by
  classical
  induction n with
  | zero =>
    refine ⟨∅,rfl,by simp,?_⟩
    intro t ht _
    have : t = ∅ := Finset.subset_empty.mp ht
    simp [this, linearIndepOn_empty]
  | succ n ih =>
    obtain ⟨s,hs,hA,hg⟩ := ih
    let B := s.powerset.filter (fun t => t.card < finrank ℚ V)
    let P := B.image (fun t : Finset V => Submodule.span ℚ (t : Set V))
    have hP : ∀ p ∈ P, p < ⊤ := by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      have hc : t.card < finrank ℚ V := (Finset.mem_filter.mp ht).2
      apply Submodule.lt_top_of_finrank_lt_finrank
      exact (finrank_span_finset_le_card t).trans_lt hc
    obtain ⟨x,hx,havoid⟩ := ha P hP
    have havo (t : Finset V) (ht : t ⊆ s) (hc : t.card < finrank ℚ V) :
        x ∉ Submodule.span ℚ (t : Set V) := by
      apply havoid _
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ht,hc⟩,rfl⟩
    have hxs : x ∉ s := by
      intro hh
      exact havo {x} (Finset.singleton_subset_iff.mpr hh) (by simpa only [Finset.card_singleton] using (show 1 < finrank ℚ V by omega))
        (Submodule.subset_span (by simp))
    refine ⟨insert x s,by simp [hxs,hs],?_,?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hA hy
    · intro t ht hc
      by_cases hxt : x ∈ t
      · have hts : t.erase x ⊆ s := by
          intro y hy
          obtain ⟨hyx,hyt⟩ := Finset.mem_erase.mp hy
          exact (Finset.mem_insert.mp (ht hyt)).resolve_left hyx
        have hct : (t.erase x).card < finrank ℚ V := by
          rw [Finset.card_erase_of_mem hxt]
          have hp := Finset.card_pos.mpr ⟨x,hxt⟩
          omega
        have hli := hg (t.erase x) hts hct.le
        have hn := havo (t.erase x) hts hct
        have hh := (linearIndepOn_id_insert (K := ℚ) (by simp : x ∉ (t.erase x : Set V))).mpr ⟨hli,hn⟩
        simpa only [← Finset.coe_insert, Finset.insert_erase hxt] using hh
      · exact hg t (by
          intro y hy
          exact (Finset.mem_insert.mp (ht hy)).resolve_left (fun he => hxt (he ▸ hy))) hc

lemma General.spans {s t : Finset V} (hs : General s) (ht : t ⊆ s)
    (hc : t.card = finrank ℚ V) : Submodule.span ℚ (t : Set V) = ⊤ := by
  have hli := hs t ht hc.le
  have hr : finrank ℚ (Submodule.span ℚ (t : Set V)) = finrank ℚ V :=
    (finrank_span_finset_eq_card hli).trans hc
  exact Submodule.eq_top_of_finrank_eq hr

end EuclideanFiveColor.GeneralPosition
end

noncomputable section
open Module
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley

def generatingSet (s : Finset ℂ) : Finset ℂ :=
  {Complex.I} ∪ s.image (fun z => (z.re : ℂ)) ∪ s.image (fun z => (z.im : ℂ))
def generatedField (s : Finset ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (generatingSet s : Set ℂ)
lemma generatedField_I (s : Finset ℂ) : Complex.I ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp [generatingSet]
lemma generatedField_real (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.re : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩))
lemma generatedField_imag (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.im : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
lemma generatedField_contains (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) : z ∈ generatedField s := by
  rw [← Complex.re_add_im z]
  exact (generatedField s).add_mem (generatedField_real s z hz)
    ((generatedField s).mul_mem (generatedField_imag s z hz) (generatedField_I s))
lemma generatedField_conj (s : Finset ℂ) {z : ℂ} (hz : z ∈ generatedField s) :
    conj z ∈ generatedField s := by
  induction hz using IntermediateField.adjoin_induction ℚ with
  | mem z hz =>
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have : z = Complex.I := Finset.mem_singleton.mp hz
        rw [this,Complex.conj_I]
        exact (generatedField s).neg_mem (generatedField_I s)
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa using generatedField_real s w hw
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      simpa using generatedField_imag s w hw
  | algebraMap r => simp
  | add x y hx hy ihx ihy => simpa using (generatedField s).add_mem ihx ihy
  | inv x hx ihx => simpa using (generatedField s).inv_mem ihx
  | mul x y hx hy ihx ihy => simpa using (generatedField s).mul_mem ihx ihy
lemma generatedField_re_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).re : ℂ) ∈ generatedField s := by
  rw [Complex.re_eq_add_conj]
  exact (generatedField s).div_mem ((generatedField s).add_mem z.property
    (generatedField_conj s z.property)) (by norm_cast; exact (generatedField s).natCast_mem 2)
lemma generatedField_im_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).im : ℂ) ∈ generatedField s := by
  rw [Complex.im_eq_sub_conj]
  exact (generatedField s).div_mem ((generatedField s).sub_mem z.property
    (generatedField_conj s z.property)) ((generatedField s).mul_mem
      (by norm_cast; exact (generatedField s).natCast_mem 2) (generatedField_I s))

lemma generatedField_finite (s : Finset ℂ) (hs : ∀ z ∈ s, IsAlgebraic ℚ z) :
    FiniteDimensional ℚ (generatedField s) := by
  have hiAlg : IsAlgebraic ℚ Complex.I := IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]; exact isAlgebraic_one.neg)
  apply IntermediateField.finiteDimensional_adjoin
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_union.mp hz with hz | hz
    · have : z = Complex.I := Finset.mem_singleton.mp hz
      rw [this]
      exact hiAlg.isIntegral
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      rw [Complex.re_eq_add_conj, div_eq_mul_inv]
      exact ((hs w hw).add (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
        (hs w hw))).mul (isAlgebraic_natCast 2).inv |>.isIntegral
  · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    rw [Complex.im_eq_sub_conj, div_eq_mul_inv]
    exact ((hs w hw).sub (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
      (hs w hw))).mul ((isAlgebraic_natCast 2).mul hiAlg).inv |>.isIntegral

lemma finrank_ge_two (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) : 2 ≤ finrank ℚ N := by
  have hp : 0 < finrank ℚ N := finrank_pos
  by_contra! hh
  have he : finrank ℚ N = 1 := by omega
  obtain ⟨q,hq⟩ := (finrank_eq_one_iff_of_nonzero' (1:N) one_ne_zero).mp he (iN N hi)
  have hqc := congrArg (fun z : N => (z:ℂ).im) hq
  simp [iN,Algebra.smul_def] at hqc

lemma cayley_subspaces_avoid (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N)
    (P : Finset (Submodule ℚ N)) (hP : ∀ p ∈ P, p < ⊤) :
    ∃ x : N, ‖(x:ℂ)‖ = 1 ∧ ∀ p ∈ P, x ∉ p := by
  classical
  choose ℓ hn hker using fun p : P => Submodule.exists_le_ker_of_lt_top p.val (hP p p.property)
  let s : Finset (N →ₗ[ℚ] ℚ) := Finset.univ.image ℓ
  have hs : ∀ ψ ∈ s, ψ ≠ 0 := by
    intro ψ hψ
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hψ
    exact hn p
  obtain ⟨a,ha⟩ := cayley_finite_avoid N hi hre him s hs
  refine ⟨realCayley N hi a,cayley_real_norm N hi a,fun p hp hx => ?_⟩
  exact ha (ℓ ⟨p,hp⟩) (Finset.mem_image.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,rfl⟩) (hker ⟨p,hp⟩ hx)

lemma numberField_general_position (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N) (n : ℕ) :
    ∃ s : Finset N, s.card = n ∧ (∀ z ∈ s, ‖(z:ℂ)‖ = 1) ∧ GeneralPosition.General s := by
  obtain ⟨s,hs,hA,hg⟩ := GeneralPosition.exists_general {z : N | ‖(z:ℂ)‖ = 1}
    (finrank_ge_two N hi) (cayley_subspaces_avoid N hi hre him) n
  exact ⟨s,hs,hA,hg⟩
end EuclideanFiveColor.AlgebraicCayley
end

end OAI
