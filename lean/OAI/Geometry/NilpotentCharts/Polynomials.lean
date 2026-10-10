import Mathlib

namespace OAI

/-! Polynomial maps, triangular differential equations and rationality on integer grids. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawPolynomial
open MvPolynomial
variable {σ τ : Type*}
def IsPoly (f : (σ → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial σ ℝ, ∀ x, MvPolynomial.eval x p = f x

lemma IsPoly.congr {f g : (σ → ℝ) → ℝ} (hf : IsPoly f) (h : ∀ x, f x = g x) : IsPoly g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun x => (hp x).trans (h x)⟩
lemma isPoly_const (c : ℝ) : IsPoly (fun _ : σ → ℝ => c) := ⟨C c,by simp⟩
lemma isPoly_coordinate (i : σ) : IsPoly (fun x : σ → ℝ => x i) := ⟨X i,by simp⟩
lemma IsPoly.add {f g : (σ → ℝ) → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x + g x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun x => by simp [hp,hq]⟩
lemma IsPoly.neg {f : (σ → ℝ) → ℝ} (hf : IsPoly f) : IsPoly (fun x => -f x) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨-p,fun x => by simp [hp]⟩
lemma IsPoly.sub {f g : (σ → ℝ) → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma IsPoly.mul {f g : (σ → ℝ) → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x * g x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun x => by simp [hp,hq]⟩
lemma IsPoly.pow {f : (σ → ℝ) → ℝ} (hf : IsPoly f) (k : ℕ) : IsPoly (fun x => f x ^ k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,fun x => by simp [hp]⟩
lemma isPoly_sum {ι : Type*} (S : Finset ι) (f : ι → (σ → ℝ) → ℝ)
    (hf : ∀ i ∈ S, IsPoly (f i)) : IsPoly (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isPoly_const (σ := σ) 0
  | @insert i S hi ih =>
    simpa [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self ..)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma IsPoly.comp {f : (τ → ℝ) → ℝ} {g : (σ → ℝ) → (τ → ℝ)} (hf : IsPoly f)
    (hg : ∀ i, IsPoly (fun x => g x i)) : IsPoly (fun x => f (g x)) := by
  classical
  obtain ⟨p,hp⟩ := hf
  choose q hq using hg
  refine ⟨MvPolynomial.bind₁ q p,fun x => ?_⟩
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x (MvPolynomial.bind₁ q p) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => MvPolynomial.eval x (q i)) p = _
  simp only [hq,hp]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def IsPolyVec {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (f : (σ → ℝ) → E) : Prop :=
  ∀ j, IsPoly (fun x => b.equivFun (f x) j)
lemma isPolyVec_const {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (v : E) :
    IsPolyVec b (fun _ : σ → ℝ => v) := fun coordinate => isPoly_const (b.equivFun v coordinate)
lemma IsPolyVec.congr {n : ℕ} {b : Module.Basis (Fin n) ℝ E} {f g : (σ → ℝ) → E}
    (hf : IsPolyVec b f) (h : ∀ x, f x = g x) : IsPolyVec b g := by
  intro j
  exact (hf j).congr (fun x => congrArg (fun v => b.equivFun v j) (h x))
lemma IsPolyVec.smul {n : ℕ} {b : Module.Basis (Fin n) ℝ E} {f : (σ → ℝ) → ℝ} {g : (σ → ℝ) → E}
    (hf : IsPoly f) (hg : IsPolyVec b g) : IsPolyVec b (fun x => f x • g x) := by
  intro j
  simpa only [map_smul,Pi.smul_apply,smul_eq_mul] using hf.mul (hg j)
lemma isPolyVec_sum {n : ℕ} {b : Module.Basis (Fin n) ℝ E} {ι : Type*} (S : Finset ι)
    (f : ι → (σ → ℝ) → E) (hf : ∀ i ∈ S, IsPolyVec b (f i)) :
    IsPolyVec b (fun x => ∑ i ∈ S, f i x) := by
  intro j
  simpa only [map_sum,Finset.sum_apply] using isPoly_sum S
    (fun i x => b.equivFun (f i x) j) (fun i hi => hf i hi j)
lemma IsPolyVec.linear {n : ℕ} {b : Module.Basis (Fin n) ℝ E} {f : (σ → ℝ) → E}
    (hf : IsPolyVec b f) (L : E →ₗ[ℝ] E) : IsPolyVec b (fun x => L (f x)) := by
  apply (isPolyVec_sum Finset.univ (fun i x => b.equivFun (f x) i • L (b i))
    (fun i _ => IsPolyVec.smul (hf i) (isPolyVec_const b (L (b i))))).congr
  intro x
  simp only [← map_smul,← map_sum,Module.Basis.sum_equivFun]
end RawPolynomial

open Polynomial
namespace RawPolynomial
variable {A : Type*} [CommRing A] [Algebra ℝ A]

def primitive (p : A[X]) : A[X] :=
  p.sum fun n a => monomial (n+1) ((algebraMap ℝ A (n+1 : ℝ)⁻¹) * a)

lemma derivative_primitive (p : A[X]) : (primitive p).derivative = p := by
  rw [primitive,Polynomial.sum_def,Polynomial.derivative_sum]
  conv_rhs => rw [← Polynomial.sum_monomial_eq p,Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.derivative_monomial_succ]
  congr 1
  have hn : (k+1 : ℝ) ≠ 0 := by positivity
  have he : algebraMap ℝ A ((k+1 : ℝ)⁻¹) * (k+1) = 1 := by
    rw [show (k+1 : A) = algebraMap ℝ A (k+1 : ℝ) by simp,← map_mul,inv_mul_cancel₀ hn,map_one]
  calc
    _ = (algebraMap ℝ A ((k+1 : ℝ)⁻¹) * (k+1)) * p.coeff k := by ring
    _ = _ := by rw [he,one_mul]

@[simp] lemma primitive_eval_zero (p : A[X]) : (primitive p).eval 0 = 0 := by
  simp [primitive,Polynomial.sum_def,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

lemma primitive_hasDerivAt (p : A[X]) (φ : A →+* ℝ) (t : ℝ) :
    HasDerivAt (fun t => (primitive p).eval₂ φ t) (p.eval₂ φ t) t := by
  have h := ((primitive p).map φ).hasDerivAt t
  simpa only [Polynomial.eval_map,Polynomial.derivative_map,derivative_primitive] using h

end RawPolynomial

namespace RawPolynomial
open Polynomial
variable {A : Type*} [CommRing A] [Algebra ℝ A]
@[simp] lemma primitive_eval₂_zero (p : A[X]) (φ : A →+* ℝ) : (primitive p).eval₂ φ 0 = 0 := by
  simp [primitive,Polynomial.sum_def,Polynomial.eval₂_finsetSum,Polynomial.eval₂_monomial]

omit [Algebra ℝ A] in
lemma eval₂_hasDerivAt (p : A[X]) (φ : A →+* ℝ) (t : ℝ) :
    HasDerivAt (fun t => p.eval₂ φ t) (p.derivative.eval₂ φ t) t := by
  simpa only [Polynomial.eval_map,Polynomial.derivative_map] using (p.map φ).hasDerivAt t

lemma eval₂_substitute {ι : Type*} (p : MvPolynomial ι ℝ) (q : ι → A[X])
    (φ : A →ₐ[ℝ] ℝ) (t : ℝ) :
    (MvPolynomial.eval₂ (algebraMap ℝ A[X]) q p).eval₂ φ.toRingHom t =
      MvPolynomial.eval (fun i => (q i).eval₂ φ.toRingHom t) p := by
  have h := MvPolynomial.eval₂_comp_left (Polynomial.eval₂RingHom φ.toRingHom t)
    (algebraMap ℝ A[X]) q p
  have hc : (Polynomial.eval₂RingHom φ.toRingHom t).comp (algebraMap ℝ A[X]) = RingHom.id ℝ := by
    ext r
    simp
  rw [hc] at h
  exact h

lemma eq_of_hasDerivAt_eq {f g d : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (d t) t)
    (hg : ∀ t, HasDerivAt g (d t) t) (h0 : f 0 = g 0) : f = g := by
  apply eq_of_fderiv_eq (fun t => (hf t).differentiableAt) (fun t => (hg t).differentiableAt)
    (fun t => (hf t).hasFDerivAt.fderiv.trans (hg t).hasFDerivAt.fderiv.symm) 0 h0

 

lemma triangular_ode_polynomial {n : ℕ}
    (M : Fin n → Fin n → MvPolynomial (Fin n) ℝ)
    (hM : ∀ j i (a : Fin n → ℝ), MvPolynomial.eval a (M j i) =
      MvPolynomial.eval (fun k => if k < j then a k else 0) (M j i))
    (Y : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (hY0 : ∀ a b, Y a b 0 = a)
    (hY : ∀ a b t (j : Fin n), HasDerivAt (fun t => Y a b t j)
      (b j + ∑ i : Fin j.val,
        (MvPolynomial.eval (t • b) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          b ⟨i.val,lt_trans i.isLt j.isLt⟩ -
        MvPolynomial.eval (Y a b t) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          deriv (fun t => Y a b t ⟨i.val,lt_trans i.isLt j.isLt⟩) t)) t) :
    ∀ j : Fin n, ∃ p : Polynomial (MvPolynomial (Fin n ⊕ Fin n) ℝ),
      ∀ a b t, p.eval₂ (MvPolynomial.eval (Sum.elim a b)) t = Y a b t j := by
  classical
  let R := MvPolynomial (Fin n ⊕ Fin n) ℝ
  have aux : ∀ k : ℕ, ∀ hk : k < n, ∃ p : R[X],
      ∀ a b t, p.eval₂ (MvPolynomial.eval (Sum.elim a b)) t = Y a b t ⟨k,hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let j : Fin n := ⟨k,hk⟩
      let up : Fin k → Fin n := fun i => ⟨i.val,lt_trans i.isLt hk⟩
      choose p hp using (fun i : Fin k => ih i.val i.isLt (lt_trans i.isLt hk))
      let B : Fin n → R[X] := fun i => C (MvPolynomial.X (Sum.inr i)) * X
      let S : Fin n → R[X] := fun i => if hi : i.val < k then p ⟨i.val,hi⟩ else 0
      let Q : R[X] := C (MvPolynomial.X (Sum.inr j)) + ∑ i : Fin k,
        (MvPolynomial.eval₂ (algebraMap ℝ R[X]) B (M j (up i)) * C (MvPolynomial.X (Sum.inr (up i))) -
        MvPolynomial.eval₂ (algebraMap ℝ R[X]) S (M j (up i)) * (p i).derivative)
      refine ⟨C (MvPolynomial.X (Sum.inl j)) + primitive Q, ?_⟩
      intro a b t
      let φ : R →ₐ[ℝ] ℝ := MvPolynomial.aeval (Sum.elim a b)
      have hφ : (φ : R →+* ℝ) = MvPolynomial.eval (Sum.elim a b) := rfl
      have hφX (u : Fin n ⊕ Fin n) : φ.toRingHom (MvPolynomial.X u) = Sum.elim a b u := by
        change MvPolynomial.eval (Sum.elim a b) (MvPolynomial.X u) = _
        exact MvPolynomial.eval_X u
      have hB : ∀ r : ℝ, (fun i => (B i).eval₂ φ.toRingHom r) = r • b := by
        intro r
        ext i
        simp only [B,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X,
          hφX,Sum.elim_inr,Pi.smul_apply,smul_eq_mul]
        exact mul_comm _ _
      have hS : ∀ r : ℝ, (fun i => (S i).eval₂ φ.toRingHom r) =
          fun i => if i < j then Y a b r i else 0 := by
        intro r
        ext i
        change (if hi : i.val < k then p ⟨i.val,hi⟩ else 0).eval₂ φ.toRingHom r =
          if i.val < k then Y a b r i else 0
        split_ifs with hi
        · exact hp ⟨i.val,hi⟩ a b r
        · exact Polynomial.eval₂_zero _ _
      have hd : ∀ (i : Fin k) r, ((p i).derivative).eval₂ φ.toRingHom r =
          deriv (fun r => Y a b r (up i)) r := by
        intro i r
        have hh : (fun r => (p i).eval₂ φ.toRingHom r) = fun r => Y a b r (up i) :=
          funext (hp i a b)
        have H := eval₂_hasDerivAt (p i) φ.toRingHom r
        rw [hh] at H
        exact H.deriv.symm
      have hQ : ∀ r, Q.eval₂ φ.toRingHom r = b j + ∑ i : Fin k,
          (MvPolynomial.eval (r • b) (M j (up i)) * b (up i) -
          MvPolynomial.eval (Y a b r) (M j (up i)) * deriv (fun r => Y a b r (up i)) r) := by
        intro r
        simp only [Q,Polynomial.eval₂_add,Polynomial.eval₂_finsetSum,Polynomial.eval₂_sub,
          Polynomial.eval₂_mul,Polynomial.eval₂_C,eval₂_substitute,hB,hS,hd]
        simp only [hφX,Sum.elim_inr]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [← hM]
      have H : (fun r => (C (MvPolynomial.X (Sum.inl j)) + primitive Q).eval₂ φ.toRingHom r) =
          fun r => Y a b r j := by
        apply eq_of_hasDerivAt_eq
          (fun r => (eval₂_hasDerivAt (C (MvPolynomial.X (Sum.inl j)) + primitive Q) φ.toRingHom r))
        · intro r
          simpa only [Polynomial.derivative_add,Polynomial.derivative_C,derivative_primitive,
            zero_add,hQ] using hY a b r j
        · simp only [Polynomial.eval₂_add,Polynomial.eval₂_C,primitive_eval₂_zero,
            hφX,Sum.elim_inl,add_zero,hY0]
      exact congrFun H t
  intro j
  exact aux j.val j.isLt
end RawPolynomial

namespace RawPolynomial
open Polynomial
lemma triangular_ode_prefix {n : ℕ}
    (F : Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hF : ∀ j i a c, (∀ k, k < j → a k = c k) → F j i a = F j i c)
    (Y : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (hY0 : ∀ a b, Y a b 0 = a)
    (hY : ∀ a b t (j : Fin n), HasDerivAt (fun t => Y a b t j)
      (b j + ∑ i : Fin j.val,
        (F j ⟨i.val,lt_trans i.isLt j.isLt⟩ (t • b) * b ⟨i.val,lt_trans i.isLt j.isLt⟩ -
        F j ⟨i.val,lt_trans i.isLt j.isLt⟩ (Y a b t) *
          deriv (fun t => Y a b t ⟨i.val,lt_trans i.isLt j.isLt⟩) t)) t) :
    ∀ (j : Fin n) a b c d, (∀ k, k < j → a k = c k) → (∀ k, k < j → b k = d k) →
      ∀ t, Y a b t j - a j - t * b j = Y c d t j - c j - t * d j := by
  have aux : ∀ k : ℕ, ∀ hk : k < n, ∀ a b c d,
      (∀ i : Fin n, i.val < k → a i = c i) → (∀ i : Fin n, i.val < k → b i = d i) →
      ∀ t, Y a b t ⟨k,hk⟩ - a ⟨k,hk⟩ - t * b ⟨k,hk⟩ =
        Y c d t ⟨k,hk⟩ - c ⟨k,hk⟩ - t * d ⟨k,hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk a b c d ha hb t
      let j : Fin n := ⟨k,hk⟩
      let up : Fin k → Fin n := fun i => ⟨i.val,lt_trans i.isLt hk⟩
      have hlow : ∀ i : Fin k, ∀ r, Y a b r (up i) = Y c d r (up i) := by
        intro i r
        have H := ih i.val i.isLt (lt_trans i.isLt hk) a b c d
          (fun z hz => ha z (lt_trans hz i.isLt)) (fun z hz => hb z (lt_trans hz i.isLt)) r
        have hai := ha (up i) i.isLt
        have hbi := hb (up i) i.isLt
        change Y a b r (up i) - a (up i) - r * b (up i) =
          Y c d r (up i) - c (up i) - r * d (up i) at H
        rw [hai,hbi] at H
        linarith
      have hd : ∀ (i : Fin k) r, deriv (fun r => Y a b r (up i)) r =
          deriv (fun r => Y c d r (up i)) r := by
        intro i r
        rw [show (fun r => Y a b r (up i)) = (fun r => Y c d r (up i)) from funext (hlow i)]
      have hFt : ∀ i : Fin k, ∀ r : ℝ, F j (up i) (r • b) = F j (up i) (r • d) := by
        intro i r
        apply hF
        intro z hz
        simp only [Pi.smul_apply,smul_eq_mul,hb z hz]
      have hFY : ∀ i : Fin k, ∀ r, F j (up i) (Y a b r) = F j (up i) (Y c d r) := by
        intro i r
        apply hF
        intro z hz
        exact hlow ⟨z.val,hz⟩ r
      let S : ℝ → ℝ := fun r => ∑ i : Fin k,
        (F j (up i) (r • b) * b (up i) - F j (up i) (Y a b r) * deriv (fun r => Y a b r (up i)) r)
      have hS : ∀ r, (∑ i : Fin k,
          (F j (up i) (r • d) * d (up i) - F j (up i) (Y c d r) * deriv (fun r => Y c d r (up i)) r)) = S r := by
        intro r
        apply Finset.sum_congr rfl
        intro i _
        rw [hFt i r,hFY i r,hd i r,hb (up i) i.isLt]
      have H : (fun r => Y a b r j - a j - r * b j) = fun r => Y c d r j - c j - r * d j := by
        apply eq_of_hasDerivAt_eq (d := S)
        · intro r
          convert ((hY a b r j).sub_const (a j)).sub ((hasDerivAt_id r).mul_const (b j)) using 1 <;>
            first | rfl | (simp only [S,up,one_mul,add_sub_cancel_left]; congr 2)
        · intro r
          convert ((hY c d r j).sub_const (c j)).sub ((hasDerivAt_id r).mul_const (d j)) using 1 <;>
            first | rfl | simpa only [one_mul,add_sub_cancel_left] using (hS r).symm
        · simp only [hY0,zero_mul,sub_self]
      exact congrFun H t
  intro j a b c d ha hb t
  exact aux j.val j.isLt a b c d ha hb t
end RawPolynomial

namespace RawPolynomial
open Polynomial
lemma triangular_ode_collection {n : ℕ}
    (M : Fin n → Fin n → MvPolynomial (Fin n) ℝ)
    (hM : ∀ j i (a : Fin n → ℝ), MvPolynomial.eval a (M j i) =
      MvPolynomial.eval (fun k => if k < j then a k else 0) (M j i))
    (Y : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (hY0 : ∀ a b, Y a b 0 = a)
    (hY : ∀ a b t (j : Fin n), HasDerivAt (fun t => Y a b t j)
      (b j + ∑ i : Fin j.val,
        (MvPolynomial.eval (t • b) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          b ⟨i.val,lt_trans i.isLt j.isLt⟩ -
        MvPolynomial.eval (Y a b t) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          deriv (fun t => Y a b t ⟨i.val,lt_trans i.isLt j.isLt⟩) t)) t) :
    ∀ j : Fin n, ∃ Q : MvPolynomial (Fin j.val ⊕ Fin j.val) ℝ, ∀ a b,
      Y a b 1 j = a j + b j + MvPolynomial.eval
        (Sum.elim (fun k => a ⟨k.val,lt_trans k.isLt j.isLt⟩)
          (fun k => b ⟨k.val,lt_trans k.isLt j.isLt⟩)) Q := by
  classical
  have hF : ∀ j i (a c : Fin n → ℝ), (∀ k, k < j → a k = c k) →
      MvPolynomial.eval a (M j i) = MvPolynomial.eval c (M j i) := by
    intro j i a c hac
    rw [hM j i a,hM j i c]
    apply congrArg (fun u : Fin n → ℝ => MvPolynomial.eval u (M j i))
    funext k
    by_cases hk : k < j
    · simp only [ite_eq_left hk,hac k hk]
    · simp only [ite_eq_right hk]
  intro j
  obtain ⟨p,hp⟩ := triangular_ode_polynomial M hM Y hY0 hY j
  let A : ((Fin j.val ⊕ Fin j.val) → ℝ) → Fin n → ℝ :=
    fun u i => if hi : i.val < j.val then u (Sum.inl ⟨i.val,hi⟩) else 0
  let B : ((Fin j.val ⊕ Fin j.val) → ℝ) → Fin n → ℝ :=
    fun u i => if hi : i.val < j.val then u (Sum.inr ⟨i.val,hi⟩) else 0
  let g : ((Fin j.val ⊕ Fin j.val) → ℝ) → (Fin n ⊕ Fin n) → ℝ :=
    fun u => Sum.elim (A u) (B u)
  have hg : ∀ i, IsPoly (fun u => g u i) := by
    intro i
    cases i with
    | inl i =>
      by_cases hi : i.val < j.val
      · simpa only [g,Sum.elim_inl,A,dite_eq_left hi] using isPoly_coordinate (σ := Fin j.val ⊕ Fin j.val) (Sum.inl ⟨i.val,hi⟩)
      · simpa only [g,Sum.elim_inl,A,dite_eq_right hi] using isPoly_const (σ := Fin j.val ⊕ Fin j.val) 0
    | inr i =>
      by_cases hi : i.val < j.val
      · simpa only [g,Sum.elim_inr,B,dite_eq_left hi] using isPoly_coordinate (σ := Fin j.val ⊕ Fin j.val) (Sum.inr ⟨i.val,hi⟩)
      · simpa only [g,Sum.elim_inr,B,dite_eq_right hi] using isPoly_const (σ := Fin j.val ⊕ Fin j.val) 0
  have hpPoly : IsPoly (fun u => MvPolynomial.eval u (p.eval 1)) := ⟨p.eval 1,fun _ => rfl⟩
  obtain ⟨Q,hQ⟩ := hpPoly.comp hg
  refine ⟨Q,?_⟩
  intro a b
  let u : (Fin j.val ⊕ Fin j.val) → ℝ := Sum.elim
    (fun k => a ⟨k.val,lt_trans k.isLt j.isLt⟩) (fun k => b ⟨k.val,lt_trans k.isLt j.isLt⟩)
  have ha : ∀ k, k < j → a k = A u k := by
    intro k hk
    simp only [A,dite_eq_left (show k.val < j.val from hk),u,Sum.elim_inl]
  have hb : ∀ k, k < j → b k = B u k := by
    intro k hk
    simp only [B,dite_eq_left (show k.val < j.val from hk),u,Sum.elim_inr]
  have hzA : A u j = 0 := dite_eq_right (lt_irrefl _)
  have hzB : B u j = 0 := dite_eq_right (lt_irrefl _)
  have H := triangular_ode_prefix (fun j i a => MvPolynomial.eval a (M j i)) hF Y hY0 hY
    j a b (A u) (B u) ha hb 1
  simp only [hzA,hzB,sub_zero,one_mul,mul_zero] at H
  have he : MvPolynomial.eval u Q = Y (A u) (B u) 1 j := by
    rw [hQ]
    change MvPolynomial.eval (Sum.elim (A u) (B u)) (p.eval 1) = _
    rw [← Polynomial.eval₂_at_one]
    exact hp (A u) (B u) 1
  change Y a b 1 j = a j + b j + MvPolynomial.eval u Q
  linarith
end RawPolynomial

namespace RawPolynomial
open MvPolynomial

lemma rational_projection : ∃ ρ : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, ρ (q : ℝ) = q := by
  let ι : ℚ →ₗ[ℚ] ℝ := Algebra.linearMap ℚ ℝ
  obtain ⟨ρ,hρ⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr Rat.cast_injective)
  exact ⟨ρ, fun q => congrArg (fun f : ℚ →ₗ[ℚ] ℚ => f q) hρ⟩

lemma rational_of_integer_values {σ : Type*} (p : MvPolynomial σ ℝ)
    (hp : ∀ x : σ → ℤ, ∃ z : ℤ, eval (fun i => (x i : ℝ)) p = z) :
    ∃ q : MvPolynomial σ ℚ, map (algebraMap ℚ ℝ) q = p := by
  classical
  obtain ⟨ρ,hρ⟩ := rational_projection
  let q : MvPolynomial σ ℚ := ∑ d ∈ p.support, monomial d (ρ (p.coeff d))
  have hq : ∀ x : σ → ℚ, eval x q = ρ (eval (fun i => (x i : ℝ)) p) := by
    intro x
    simp only [q,map_sum,MvPolynomial.eval_monomial]
    rw [MvPolynomial.eval_eq,map_sum]
    change (∑ d ∈ p.support, ρ (p.coeff d) * d.prod (fun i e => x i ^ e)) =
      ∑ d ∈ p.support, ρ (p.coeff d * d.prod (fun i e => (x i : ℝ) ^ e))
    apply Finset.sum_congr rfl
    intro d hd
    have hcast : ((d.prod (fun i e => x i ^ e) : ℚ) : ℝ) =
        d.prod (fun i e => (x i : ℝ) ^ e) := by
      simp [Finsupp.prod]
    rw [← hcast,mul_comm (p.coeff d)]
    change _ = ρ ((d.prod (fun i e => x i ^ e)) • p.coeff d)
    rw [map_smul]
    simp only [smul_eq_mul,mul_comm]
  refine ⟨q,?_⟩
  apply MvPolynomial.funext_set (s := fun _ : σ => Set.range (fun z : ℤ => (z : ℝ)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective)
  intro x hx
  choose z hz using (fun i => hx i (Set.mem_univ i))
  have he : x = fun i => (z i : ℝ) := funext (fun i => (hz i).symm)
  rw [he,MvPolynomial.eval_map]
  have hval := hq (fun i => (z i : ℚ))
  obtain ⟨v,hv⟩ := hp z
  have hvals : eval (fun i => (z i : ℚ)) q = (v : ℚ) := by
    simp only [Rat.cast_intCast,hv] at hval
    exact hval.trans (by simpa only [Rat.cast_intCast] using hρ (v : ℚ))
  calc
    eval₂ (algebraMap ℚ ℝ) (fun i => (z i : ℝ)) q =
        ((eval (fun i => (z i : ℚ)) q : ℚ) : ℝ) := by
      have H := (MvPolynomial.eval₂_comp_left (algebraMap ℚ ℝ) (RingHom.id ℚ) (fun i => (z i : ℚ)) q).symm
      rw [RingHom.comp_id] at H
      have hzq : (algebraMap ℚ ℝ) ∘ (fun i => (z i : ℚ)) = (fun i => (z i : ℝ)) := by
        funext i
        change (((z i : ℚ) : ℝ)) = (z i : ℝ)
        exact Rat.cast_intCast (z i)
      rw [hzq] at H
      exact H
    _ = (v : ℝ) := by rw [hvals]; simp
    _ = eval (fun i => (z i : ℝ)) p := hv.symm
end RawPolynomial

namespace RawPolynomial
open MvPolynomial
variable {σ E : Type*} [AddCommGroup E] [Module ℝ E]

lemma IsPolyVec.linear_apply {n : ℕ} {b : Module.Basis (Fin n) ℝ E}
    {f : (σ → ℝ) → E} (hf : IsPolyVec b f) (L : E →ₗ[ℝ] ℝ) : IsPoly (fun x => L (f x)) := by
  apply (isPoly_sum Finset.univ (fun i x => b.equivFun (f x) i * L (b i))
    (fun i _ => (hf i).mul (isPoly_const _))).congr
  intro x
  simp only [← smul_eq_mul,← map_smul,← map_sum,Module.Basis.sum_equivFun]

 

lemma IsPolyVec.mem_span_integer_grid {n : ℕ} {b : Module.Basis (Fin n) ℝ E}
    {f : (σ → ℝ) → E} (hf : IsPolyVec b f) (a : σ → ℝ) :
    f a ∈ Submodule.span ℝ (Set.range (fun x : σ → ℤ => f (fun i => (x i : ℝ)))) := by
  classical
  let W := Submodule.span ℝ (Set.range (fun x : σ → ℤ => f (fun i => (x i : ℝ))))
  by_contra hn
  obtain ⟨L,hL,hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨p,hp⟩ := hf.linear_apply L
  have he : p = 0 := by
    apply MvPolynomial.funext_set (fun _ : σ => Set.range (fun z : ℤ => (z : ℝ)))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective)
    intro x hx
    choose z hz using (fun i => hx i (Set.mem_univ i))
    have hxz : x = (fun i => (z i : ℝ)) := funext (fun i => (hz i).symm)
    rw [hp,hxz,map_zero]
    have hm : L (f (fun i => (z i : ℝ))) ∈ W.map L :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨z,rfl⟩)
    rw [hW,Submodule.mem_bot] at hm
    exact hm
  apply hL
  calc L (f a) = MvPolynomial.eval a p := (hp a).symm
       _ = 0 := by rw [he,map_zero]
end RawPolynomial

namespace RawPolynomial
variable {σ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma IsPoly.comp_differentiable {f : (σ → ℝ) → ℝ} (hf : IsPoly f)
    {g : E → σ → ℝ} (hg : ∀ i, Differentiable ℝ (fun x => g x i)) :
    Differentiable ℝ (fun x => f (g x)) := by
  obtain ⟨p,hp⟩ := hf
  have he : (fun x => f (g x)) = fun x => MvPolynomial.eval (g x) p := funext (fun x => (hp _).symm)
  rw [he]
  clear hp he
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval_C] using (differentiable_const (c := a))
  | add p q hp hq =>
    simp only [MvPolynomial.eval_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval_mul,MvPolynomial.eval_X]
    exact hp.mul (hg i)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
lemma IsPolyVec.comp_differentiable {n : ℕ} {b : Module.Basis (Fin n) ℝ F}
    {f : (σ → ℝ) → F} (hf : IsPolyVec b f) {g : E → σ → ℝ}
    (hg : ∀ i, Differentiable ℝ (fun x => g x i)) : Differentiable ℝ (fun x => f (g x)) := by
  have H : Differentiable ℝ (fun x => b.equivFun (f (g x))) :=
    differentiable_pi.mpr (fun i => (hf i).comp_differentiable hg)
  have he : (fun x => f (g x)) = fun x => b.equivFun.toContinuousLinearEquiv.symm (b.equivFun (f (g x))) := by
    funext x
    exact (b.equivFun.symm_apply_apply _).symm
  rw [he]
  exact b.equivFun.toContinuousLinearEquiv.symm.toContinuousLinearMap.differentiable.comp H

omit [FiniteDimensional ℝ F] in
lemma isPolyVec_linear_coordinates {n m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (L : (Fin n → ℝ) →ₗ[ℝ] F) (f : (σ → ℝ) → Fin n → ℝ)
    (hf : ∀ i, IsPoly (fun x => f x i)) : IsPolyVec b (fun x => L (f x)) := by
  intro j
  let A : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj j).comp (b.equivFun.toLinearMap.comp L)
  apply (isPoly_sum Finset.univ (fun i x => f x i * A (Pi.single i 1))
    (fun i _ => (hf i).mul (isPoly_const _))).congr
  intro x
  change (∑ i : Fin n, f x i * A (Pi.single i 1)) = A (f x)
  simp only [← smul_eq_mul,← map_smul,← map_sum]
  congr 1
  ext i
  simp [Pi.single_apply]
end RawPolynomial
end

end OAI
