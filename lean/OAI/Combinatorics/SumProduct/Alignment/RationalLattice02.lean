import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators
noncomputable section
end
end
 

 
section
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace Polynomial
open scoped _root_.Polynomial
variable {K : Type*} [Field K] [CharZero K]
lemma eq_of_eval_nat_eq {p q : K[X]} (h : ∀ m : ℕ, p.eval (m : K) = q.eval (m : K)) : p = q := by
  apply _root_.Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
  rintro x ⟨m,rfl⟩
  exact h m
end Polynomial
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

lemma polynomial_substitute_eval {ι : Type*} (P : MvPolynomial ι ℚ)
    (p : ι → ℝ[X]) (t : ℝ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap ℚ ℝ)) p P).eval t =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => (p i).eval t) P := by
  have h := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom t)
    (Polynomial.C.comp (algebraMap ℚ ℝ)) p P
  have hc : (Polynomial.evalRingHom t).comp (Polynomial.C.comp (algebraMap ℚ ℝ)) =
      algebraMap ℚ ℝ := by
    ext q
    simp
  rw [hc] at h
  exact h

 

theorem natpow_polynomial (g : G) (i : Fin n) :
    ∃ p : ℝ[X], ∀ m : ℕ, p.eval (m : ℝ) = c.coord (g^m) i := by
  have aux : ∀ l : ℕ, ∀ hl : l<n, ∃ p : ℝ[X],
      ∀ m : ℕ, p.eval (m : ℝ) = c.coord (g^m) ⟨l,hl⟩ := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro hl
      choose p hp using (fun j : Fin l => ih j.val j.isLt (lt_trans j.isLt hl))
      let x : (Fin l ⊕ Fin l) → ℝ[X] := Sum.elim p
        (fun j => Polynomial.C (c.coord g ⟨j.val,lt_trans j.isLt hl⟩))
      let Q : ℝ[X] := Polynomial.C (c.coord g ⟨l,hl⟩) +
        MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap ℚ ℝ)) x (c.correction ⟨l,hl⟩)
      obtain ⟨P,hP0,hP⟩ := Polynomial.exists_antidifference Q
      refine ⟨P,?_⟩
      intro m
      induction m with
      | zero => simpa [c.one_coord] using hP0
      | succ m hm =>
        have he := congrArg (Polynomial.eval (m : ℝ)) hP
        simp only [Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_add,
          Polynomial.eval_one,Polynomial.eval_X] at he
        have hx : (fun a => (x a).eval (m : ℝ)) =
            Sum.elim (fun j => c.coord (g^m) ⟨j.val,lt_trans j.isLt hl⟩)
              (fun j => c.coord g ⟨j.val,lt_trans j.isLt hl⟩) := by
          funext j
          cases j with
          | inl j => exact hp j m
          | inr j => simp [x]
        simp only [Q,Polynomial.eval_add,Polynomial.eval_C,polynomial_substitute_eval,hx] at he
        rw [pow_succ,c.mul_coord]
        rw [Nat.cast_succ,add_comm (m:ℝ) 1]
        linarith
  exact aux i.val i.isLt

def powerPolynomial (g : G) (i : Fin n) : ℝ[X] := (natpow_polynomial c g i).choose
lemma powerPolynomial_nat (g : G) (i : Fin n) (m : ℕ) :
    (powerPolynomial c g i).eval (m : ℝ) = c.coord (g^m) i :=
  (natpow_polynomial c g i).choose_spec m

 
def realPower (g : G) (t : ℝ) : G :=
  c.coord.symm (fun i => (powerPolynomial c g i).eval t)

lemma realPower_coord (g : G) (t : ℝ) (i : Fin n) :
    c.coord (realPower c g t) i = (powerPolynomial c g i).eval t := by
  simp [realPower]

lemma realPower_nat (g : G) (m : ℕ) : realPower c g m = g^m := by
  apply c.coord.injective
  funext i
  rw [realPower_coord,powerPolynomial_nat]

@[simp] lemma realPower_zero (g : G) : realPower c g 0 = 1 := by
  simpa using realPower_nat c g 0
@[simp] lemma realPower_one (g : G) : realPower c g 1 = g := by
  simpa using realPower_nat c g 1

lemma realPower_continuous (g : G) : Continuous (realPower c g) :=
  c.coord.symm.continuous.comp (continuous_pi fun i => (powerPolynomial c g i).continuous)

end RationalLattice

namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

def evalPath (p : Fin n → ℝ[X]) (t : ℝ) : G := c.coord.symm (fun i => (p i).eval t)
def pathMul (p q : Fin n → ℝ[X]) (i : Fin n) : ℝ[X] :=
  p i + q i + MvPolynomial.eval₂ (C.comp (algebraMap ℚ ℝ))
    (Sum.elim (fun j => p ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => q ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i)

lemma evalPath_coord (p : Fin n → ℝ[X]) (t : ℝ) (i : Fin n) :
    c.coord (evalPath c p t) i = (p i).eval t := by simp [evalPath]
lemma evalPath_C (g : G) (t : ℝ) : evalPath c (fun i => C (c.coord g i)) t = g := by
  simp [evalPath]
lemma evalPath_comp (p : Fin n → ℝ[X]) (q : ℝ[X]) (t : ℝ) :
    evalPath c (fun i => (p i).comp q) t = evalPath c p (q.eval t) := by
  simp [evalPath,Polynomial.eval_comp]
lemma evalPath_mul (p q : Fin n → ℝ[X]) (t : ℝ) :
    evalPath c (pathMul c p q) t = evalPath c p t * evalPath c q t := by
  apply c.coord.injective
  funext i
  rw [evalPath_coord,c.mul_coord]
  simp only [pathMul,Polynomial.eval_add,polynomial_substitute_eval,evalPath_coord]
  congr 2
  funext a
  cases a <;> rfl

lemma evalPath_ext_nat {p q : Fin n → ℝ[X]}
    (h : ∀ m : ℕ, evalPath c p (m:ℝ) = evalPath c q (m:ℝ)) :
    ∀ t : ℝ, evalPath c p t = evalPath c q t := by
  have hpq : p=q := by
    funext i
    apply Polynomial.eq_of_eval_nat_eq
    intro m
    have h' := congrArg (fun g => c.coord g i) (h m)
    simpa [evalPath] using h'
  rw [hpq]
  exact fun _ => rfl

lemma realPower_add_nat (g : G) (t : ℝ) (m : ℕ) :
    realPower c g (t+m) = realPower c g t * g^m := by
  let p := powerPolynomial c g
  let q : Fin n → ℝ[X] := fun i => (p i).comp (X+C (m:ℝ))
  let r := pathMul c p (fun i => C (c.coord (g^m) i))
  have hq (s : ℝ) : evalPath c q s = realPower c g (s+m) := by
    simp [q,realPower,evalPath,p]
  have hr (s : ℝ) : evalPath c r s = realPower c g s * g^m := by
    rw [evalPath_mul,evalPath_C]
    rfl
  have he : ∀ k : ℕ, evalPath c q k = evalPath c r k := by
    intro k
    rw [hq,hr,← Nat.cast_add,realPower_nat,realPower_nat,pow_add]
  simpa only [hq,hr] using evalPath_ext_nat c he t

 

theorem realPower_add (g : G) (s t : ℝ) :
    realPower c g (s+t) = realPower c g s * realPower c g t := by
  let p := powerPolynomial c g
  let q : Fin n → ℝ[X] := fun i => (p i).comp (C s+X)
  let r := pathMul c (fun i => C (c.coord (realPower c g s) i)) p
  have hq (v : ℝ) : evalPath c q v = realPower c g (s+v) := by
    simp [q,realPower,evalPath,p]
  have hr (v : ℝ) : evalPath c r v = realPower c g s * realPower c g v := by
    rw [evalPath_mul,evalPath_C]
    rfl
  have he : ∀ k : ℕ, evalPath c q k = evalPath c r k := by
    intro k
    rw [hq,hr,realPower_nat]
    exact realPower_add_nat c g s k
  simpa only [hq,hr] using evalPath_ext_nat c he t

lemma realPower_neg (g : G) (s : ℝ) : realPower c g (-s) = (realPower c g s)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← realPower_add,add_neg_cancel,realPower_zero]

end RationalLattice
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

abbrev ParamPoly (n : ℕ) := Polynomial (MvPolynomial (Fin n) ℚ)

def parameterEval (x : Fin n → ℝ) : MvPolynomial (Fin n) ℚ →+* ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x

@[simp] lemma parameterEval_X (x : Fin n → ℝ) (i : Fin n) :
    parameterEval x (MvPolynomial.X i) = x i := by simp [parameterEval]

lemma universal_substitute_eval {ι : Type*} (P : MvPolynomial ι ℚ)
    (p : ι → ParamPoly n) (x : Fin n → ℝ) (t : ℝ) :
    (MvPolynomial.eval₂ (C.comp MvPolynomial.C) p P).eval₂ (parameterEval x) t =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (fun i => (p i).eval₂ (parameterEval x) t) P := by
  have h := MvPolynomial.eval₂_comp_left (Polynomial.eval₂RingHom (parameterEval x) t)
    (C.comp MvPolynomial.C) p P
  have hc : (Polynomial.eval₂RingHom (parameterEval x) t).comp (C.comp MvPolynomial.C) =
      algebraMap ℚ ℝ := by
    ext q
    simp [parameterEval]
  rw [hc] at h
  exact h

 

theorem universal_natpow_polynomial (i : Fin n) :
    ∃ P : ParamPoly n, ∀ (g : G) (m : ℕ),
      P.eval₂ (parameterEval (c.coord g)) (m:ℝ) = c.coord (g^m) i := by
  have aux : ∀ l : ℕ, ∀ hl : l<n, ∃ P : ParamPoly n, ∀ (g:G) (m:ℕ),
      P.eval₂ (parameterEval (c.coord g)) (m:ℝ) = c.coord (g^m) ⟨l,hl⟩ := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro hl
      choose p hp using (fun j : Fin l => ih j.val j.isLt (lt_trans j.isLt hl))
      let x : (Fin l ⊕ Fin l) → ParamPoly n := Sum.elim p
        (fun j => C (MvPolynomial.X ⟨j.val,lt_trans j.isLt hl⟩))
      let Q : ParamPoly n := C (MvPolynomial.X ⟨l,hl⟩) +
        MvPolynomial.eval₂ (C.comp MvPolynomial.C) x (c.correction ⟨l,hl⟩)
      obtain ⟨P,hP0,hP⟩ := Polynomial.exists_antidifference_algebra Q
      refine ⟨P,?_⟩
      intro g m
      induction m with
      | zero =>
        have he := congrArg (parameterEval (c.coord g)) hP0
        simpa [Polynomial.eval₂_at_apply,← Polynomial.eval₂_at_apply,
          c.one_coord] using he
      | succ m hm =>
        have he := congrArg (Polynomial.eval₂ (parameterEval (c.coord g)) (m:ℝ)) hP
        simp only [Polynomial.eval₂_sub,Polynomial.eval₂_comp,Polynomial.eval₂_add,
          Polynomial.eval₂_one,Polynomial.eval₂_X] at he
        have hx : (fun a => (x a).eval₂ (parameterEval (c.coord g)) (m:ℝ)) =
            Sum.elim (fun j => c.coord (g^m) ⟨j.val,lt_trans j.isLt hl⟩)
              (fun j => c.coord g ⟨j.val,lt_trans j.isLt hl⟩) := by
          funext j
          cases j with
          | inl j => exact hp j g m
          | inr j => simp [x,parameterEval]
        simp only [Q,Polynomial.eval₂_add,Polynomial.eval₂_C,universal_substitute_eval,hx] at he
        simp only [parameterEval_X] at he
        rw [pow_succ,c.mul_coord]
        rw [Nat.cast_succ,add_comm (m:ℝ) 1]
        linarith
  exact aux i.val i.isLt

def universalPowerPolynomial (i : Fin n) : ParamPoly n := (universal_natpow_polynomial c i).choose
lemma universalPowerPolynomial_nat (g : G) (i : Fin n) (m : ℕ) :
    (universalPowerPolynomial c i).eval₂ (parameterEval (c.coord g)) (m:ℝ) =
      c.coord (g^m) i := (universal_natpow_polynomial c i).choose_spec g m

theorem powerPolynomial_eq_universal (g : G) (i : Fin n) :
    powerPolynomial c g i = (universalPowerPolynomial c i).map (parameterEval (c.coord g)) := by
  apply Polynomial.eq_of_eval_nat_eq
  intro m
  rw [powerPolynomial_nat,Polynomial.eval_map,universalPowerPolynomial_nat]

lemma realPower_coord_universal (g : G) (t : ℝ) (i : Fin n) :
    c.coord (realPower c g t) i =
      (universalPowerPolynomial c i).eval₂ (parameterEval (c.coord g)) t := by
  rw [realPower_coord,powerPolynomial_eq_universal,Polynomial.eval_map]

end RationalLattice

end
end
end
end
end

end OAI
