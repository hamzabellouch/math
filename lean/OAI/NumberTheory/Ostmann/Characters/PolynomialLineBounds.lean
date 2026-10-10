import OAI.NumberTheory.Ostmann.Characters.PolynomialLineFlags
import OAI.NumberTheory.Ostmann.Characters.PolynomialVariableSupport

namespace OAI

/-! # Degree, value and variable bounds for the actual line tests -/

namespace Ostmann

namespace PolynomialGiantRows

theorem numeratorLine_degree_le {σ : Type*} (T : PolynomialGiantRows σ)
    (v w : MvPolynomial σ ℤ) (D d : ℕ) (hT : T.DegreeLE D)
    (hv : v.totalDegree ≤ d) (hw : w.totalDegree ≤ d) :
    (T.numeratorLine v w).a.totalDegree ≤ D + d ∧
      (T.numeratorLine v w).b.totalDegree ≤ D + d := by
  obtain ⟨ha, hb, hc, hd, _⟩ := hT
  constructor <;> apply (MvPolynomial.totalDegree_sub _ _).trans <;> apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

theorem numeratorLine_value_le {σ : Type*} (T : PolynomialGiantRows σ)
    (v w : MvPolynomial σ ℤ) (φ : MvPolynomial σ ℤ →+* ℝ)
    (H U : ℝ) (hU : 0 ≤ U) (hT : T.ValueLE φ H)
    (hv : |φ v| ≤ U) (hw : |φ w| ≤ U) :
    |φ (T.numeratorLine v w).a| ≤ 2 * U * H ∧
      |φ (T.numeratorLine v w).b| ≤ 2 * U * H := by
  obtain ⟨ha, hb, hc, hd, _⟩ := hT
  have hm (f g : MvPolynomial σ ℤ) (hf : |φ f| ≤ U) (hg : |φ g| ≤ H) :
      |φ (f * g)| ≤ U * H := by
    rw [map_mul, abs_mul]
    exact mul_le_mul hf hg (abs_nonneg _) hU
  constructor
  · change |φ (v * T.rows.c - w * T.rows.a)| ≤ _
    rw [map_sub]
    exact (abs_sub _ _).trans (by linarith [hm v T.rows.c hv hc, hm w T.rows.a hw ha])
  · change |φ (v * T.rows.d - w * T.rows.b)| ≤ _
    rw [map_sub]
    exact (abs_sub _ _).trans (by linarith [hm v T.rows.d hv hd, hm w T.rows.b hw hb])

theorem numeratorLine_vars_subset {σ : Type*} [DecidableEq σ]
    (T : PolynomialGiantRows σ) (v w : MvPolynomial σ ℤ) (S : Finset σ)
    (hT : T.UsesOnly S) (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) :
    (T.numeratorLine v w).a.vars ⊆ S ∧ (T.numeratorLine v w).b.vars ⊆ S := by
  have hm (f g : MvPolynomial σ ℤ) (hf : f.vars ⊆ S) (hg : g.vars ⊆ S) :
      (f * g).vars ⊆ S := (MvPolynomial.vars_mul f g).trans (Finset.union_subset hf hg)
  obtain ⟨ha, hb, hc, hd, _⟩ := hT
  constructor
  · exact (MvPolynomial.vars_sub_subset (p := v * T.rows.c) (q := w * T.rows.a)).trans
      (Finset.union_subset (hm v T.rows.c hv hc) (hm w T.rows.a hw ha))
  · exact (MvPolynomial.vars_sub_subset (p := v * T.rows.d) (q := w * T.rows.b)).trans
      (Finset.union_subset (hm v T.rows.d hv hd) (hm w T.rows.b hw hb))

end PolynomialGiantRows

theorem lineTestPolynomials_degree_le {σ J : Type*} (L : J → PolynomialGiantLine σ)
    (i : J) (D : ℕ) (hL : ∀ j, (L j).a.totalDegree ≤ D ∧ (L j).b.totalDegree ≤ D)
    (s : Bool ⊕ J) : (lineTestPolynomials L i s).totalDegree ≤ 2 * D := by
  rcases s with b | j
  · cases b
    · exact (hL i).1.trans (by omega)
    · exact (hL i).2.trans (by omega)
  · exact PolynomialGiantRows.minor_degree_le D (hL i).1 (hL i).2 (hL j).1 (hL j).2

theorem lineTestPolynomials_value_le {σ J : Type*} (L : J → PolynomialGiantLine σ)
    (i : J) (φ : MvPolynomial σ ℤ →+* ℝ) (H : ℝ) (hH : 1 ≤ H)
    (hL : ∀ j, |φ (L j).a| ≤ H ∧ |φ (L j).b| ≤ H)
    (s : Bool ⊕ J) : |φ (lineTestPolynomials L i s)| ≤ 2 * H ^ 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hh : H ≤ 2 * H ^ 2 := by nlinarith
  rcases s with b | j
  · cases b
    · exact (hL i).1.trans hh
    · exact (hL i).2.trans hh
  · exact PolynomialGiantRows.minor_value_le φ _ _ _ _ H hH0
      (hL i).1 (hL i).2 (hL j).1 (hL j).2

theorem lineTestPolynomials_vars_subset {σ J : Type*} [DecidableEq σ]
    (L : J → PolynomialGiantLine σ) (i : J) (S : Finset σ)
    (hL : ∀ j, (L j).a.vars ⊆ S ∧ (L j).b.vars ⊆ S) (s : Bool ⊕ J) :
    (lineTestPolynomials L i s).vars ⊆ S := by
  rcases s with b | j
  · cases b
    · exact (hL i).1
    · exact (hL i).2
  · exact PolynomialGiantRows.minor_usesOnly (hL i).1 (hL i).2 (hL j).1 (hL j).2

theorem integerTestValue_real_cast {A : Type*} {n : ℕ} (value : A → ℤ)
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → A) :
    (integerTestValue value F x : ℝ) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun j => (value (x j) : ℝ)) F := by
  simpa [integerTestValue, Int.castRingHom] using
    MvPolynomial.map_eval₂Hom (RingHom.id ℤ) (fun j => value (x j)) (Int.castRingHom ℝ) F

end Ostmann

end OAI
