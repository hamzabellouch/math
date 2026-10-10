import OAI.NumberTheory.Ostmann.Characters.PolynomialGiantRows

namespace OAI

/-! # Variables absent from the arithmetic coefficient tests

Clearing ancestor denominators introduces only variables from the existing
slots. In particular a compensation type omitted from those slots stays absent
from every coefficient polynomial and every minor formed from them.
-/

namespace Ostmann

namespace PolynomialGiantRows

variable {σ : Type*}

def UsesOnly (T : PolynomialGiantRows σ) (S : Finset σ) : Prop :=
  T.rows.a.vars ⊆ S ∧ T.rows.b.vars ⊆ S ∧ T.rows.c.vars ⊆ S ∧
    T.rows.d.vars ⊆ S ∧ T.denominator.vars ⊆ S

private theorem vars_mul_subset [DecidableEq σ] {f g : MvPolynomial σ ℤ} {S : Finset σ}
    (hf : f.vars ⊆ S) (hg : g.vars ⊆ S) : (f * g).vars ⊆ S :=
  (MvPolynomial.vars_mul f g).trans (Finset.union_subset hf hg)

private theorem vars_sub_subset [DecidableEq σ] {f g : MvPolynomial σ ℤ} {S : Finset σ}
    (hf : f.vars ⊆ S) (hg : g.vars ⊆ S) : (f - g).vars ⊆ S :=
  (MvPolynomial.vars_sub_subset (p := f) (q := g)).trans (Finset.union_subset hf hg)

theorem usesOnly_identity (S : Finset σ) : (identity : PolynomialGiantRows σ).UsesOnly S := by
  simp [UsesOnly, identity, GiantRows.identity]

theorem usesOnly_reverse [DecidableEq σ] (T : PolynomialGiantRows σ) (S : Finset σ) (hT : T.UsesOnly S)
    (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) (hu : u.vars ⊆ S) :
    (T.reverse left v w u).UsesOnly S := by
  obtain ⟨ha, hb, hc, hd, hden⟩ := hT
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, ite_true, UsesOnly]
  · exact ⟨vars_sub_subset (vars_mul_subset hv hc) (vars_mul_subset hw ha),
      vars_sub_subset (vars_mul_subset hv hd) (vars_mul_subset hw hb),
      vars_mul_subset hu hc, vars_mul_subset hu hd, vars_mul_subset hden hu⟩
  · exact ⟨vars_mul_subset hu ha, vars_mul_subset hu hb,
      vars_sub_subset (vars_mul_subset hv hc) (vars_mul_subset hw ha),
      vars_sub_subset (vars_mul_subset hv hd) (vars_mul_subset hw hb),
      vars_mul_subset hden hu⟩

/-- A two-by-two minor has no variables beyond those of its four entries. -/
theorem minor_usesOnly [DecidableEq σ] {a b c d : MvPolynomial σ ℤ} {S : Finset σ}
    (ha : a.vars ⊆ S) (hb : b.vars ⊆ S) (hc : c.vars ⊆ S) (hd : d.vars ⊆ S) :
    (a * d - b * c).vars ⊆ S :=
  vars_sub_subset (vars_mul_subset ha hd) (vars_mul_subset hb hc)

/-- Changing all variables outside the indicated slots leaves both normalized
coefficient rows unchanged. This supplies the independence needed for the
separate compensation-prime prior in the coincidence estimate. -/
theorem normalized_eq_of_agree {K : Type*} [Field K]
    (T : PolynomialGiantRows σ) (S : Finset σ) (hT : T.UsesOnly S)
    (x y : σ → K) (hxy : ∀ i ∈ S, x i = y i) :
    T.normalized (MvPolynomial.eval₂Hom (Int.castRingHom K) x) =
      T.normalized (MvPolynomial.eval₂Hom (Int.castRingHom K) y) := by
  have heval (f : MvPolynomial σ ℤ) (hf : f.vars ⊆ S) :
      MvPolynomial.eval₂Hom (Int.castRingHom K) x f =
        MvPolynomial.eval₂Hom (Int.castRingHom K) y f :=
    MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hxy i (hf hi)) rfl
  obtain ⟨ha, hb, hc, hd, hden⟩ := hT
  apply GiantRows.ext <;>
    simp only [normalized, heval _ ha, heval _ hb, heval _ hc, heval _ hd, heval _ hden]

/-- Forming a rank test doubles the available coefficient degree bound. -/
theorem minor_degree_le {a b c d : MvPolynomial σ ℤ} (D : ℕ)
    (ha : a.totalDegree ≤ D) (hb : b.totalDegree ≤ D)
    (hc : c.totalDegree ≤ D) (hd : d.totalDegree ≤ D) :
    (a * d - b * c).totalDegree ≤ 2 * D := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

end PolynomialGiantRows

theorem polynomialAncestorRows_usesOnly {σ : Type*} [DecidableEq σ]
    (steps : List (PolynomialReversal σ)) (S : Finset σ)
    (h : ∀ s ∈ steps, s.v.vars ⊆ S ∧ s.w.vars ⊆ S ∧ s.u.vars ⊆ S) :
    (polynomialAncestorRows steps).UsesOnly S := by
  induction steps with
  | nil => exact PolynomialGiantRows.usesOnly_identity S
  | cons s steps ih =>
    have hs := h s (by simp)
    exact PolynomialGiantRows.usesOnly_reverse _ S
      (ih fun t ht => h t (by simp [ht])) s.left s.v s.w s.u hs.1 hs.2.1 hs.2.2

end Ostmann

end OAI
