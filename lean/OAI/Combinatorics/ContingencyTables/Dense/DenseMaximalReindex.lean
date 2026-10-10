import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanDraw
import OAI.Combinatorics.ContingencyTables.Transport.TableReindex
import Mathlib.Data.Finset.Max

namespace OAI

/-! # Dense draws with arbitrary choices of the reference row and column -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
private lemma maximal_index_exists (R : Option I → ℕ) : ∃ i,∀ j,R j ≤ R i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ R Finset.univ_nonempty
  exact ⟨i,fun j => hi j (Finset.mem_univ j)⟩

def maximalIndex (R : Option I → ℕ) : Option I := Classical.choose (maximal_index_exists R)

def maximalReindex (R : Option I → ℕ) : Option I ≃ Option I :=
  Equiv.swap none (maximalIndex R)

abbrev maximalMargin (R : Option I → ℕ) : Option I → ℕ := fun i => R (maximalReindex R i)

lemma maximalMargin_max (R : Option I → ℕ) (i : I) :
    maximalMargin R (some i) ≤ maximalMargin R none := by
  unfold maximalMargin maximalReindex
  rw [Equiv.swap_apply_left]
  exact Classical.choose_spec (maximal_index_exists R) _

lemma maximalMargin_lower (R : Option I → ℕ) (L : ℕ) (hR : ∀ i,L ≤ R i) :
    ∀ i,L ≤ maximalMargin R i := fun _i => hR _

lemma maximalMargin_total (R : Option I → ℕ) : ∑ i,maximalMargin R i=∑ i,R i :=
  (maximalReindex R).sum_comp R

variable {q : ℕ}

abbrev reindexedDrawBits (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I×J ≃ Fin q) (h : ℕ) : ℕ :=
  denseDrawBits (maximalMargin R) (maximalMargin P) d e h

/-- Move a largest row and column to the distinguished indices inside the
sampler, then transport the output back to the fixed original indices. -/
def reindexedBooleanDraw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (e : I×J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (fallback : Table R P)
    (bits : Fin (reindexedDrawBits R P d e h) → Bool) : Table R P :=
  (tableReindex (maximalReindex R) (maximalReindex P) R P).symm
    (denseBooleanDraw (maximalMargin R) (maximalMargin P) d hd
      (maximalMargin_lower R _ hR) (maximalMargin_lower P _ hP) e
      (by rw [maximalMargin_total,maximalMargin_total]; exact htotal) h a
      ((tableReindex (maximalReindex R) (maximalReindex P) R P) fallback) bits)

def reindexedBooleanDrawLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (e : I×J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (fallback : Table R P) : RationalLaw (Table R P) :=
  mapLaw (uniformLaw (α := Fin (reindexedDrawBits R P d e h) → Bool))
    (reindexedBooleanDraw R P d hd hR hP e htotal h a fallback)

/-- The fixed reference used by the outer chain need not maximize either
residual margin. The actual Boolean draw retains the same TV guarantee. -/
theorem reindexedBooleanDraw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I×J) ≤ d) (htotal : ∑ i,R i=∑ j,P j)
    (e : I×J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4*d^8)))
    (h : ℕ) (a : Grid (I := Fin q) (4*d^8)) (fallback : Table R P) :
    let _ : Nonempty (Table R P) := ⟨fallback⟩
    (variation (reindexedBooleanDrawLaw R P d hd hR hP e htotal h a fallback)
      (uniformLaw (α := Table R P)) : ℝ) ≤ (2:ℝ)^(-(h:ℝ)) := by
  let E := tableReindex (maximalReindex R) (maximalReindex P) R P
  let : Nonempty (Table R P) := ⟨fallback⟩
  let : Nonempty (Table (maximalMargin R) (maximalMargin P)) := ⟨E fallback⟩
  have heq : (∑ i,maximalMargin R i)=∑ j,maximalMargin P j := by
    rw [maximalMargin_total,maximalMargin_total]
    exact htotal
  have hdraw := denseBooleanDraw_variation (maximalMargin R) (maximalMargin P) d hd
    (maximalMargin_lower R _ hR) (maximalMargin_lower P _ hP)
    (maximalMargin_max R) (maximalMargin_max P) hdimR hdimP hfree heq e hPL hCheeger h a (E fallback)
  dsimp only at ⊢
  unfold reindexedBooleanDrawLaw reindexedBooleanDraw
  rw [mapLaw_equiv_output]
  change (variation (equivLaw E.symm (denseBooleanDrawLaw (maximalMargin R) (maximalMargin P)
    d hd (maximalMargin_lower R _ hR) (maximalMargin_lower P _ hP) e heq h a (E fallback)))
    (uniformLaw (α := Table R P)) : ℝ) ≤ _
  rw [← uniform_equiv E.symm,variation_equiv]
  exact hdraw


/-- Relabeling preserves the polynomial Boolean-source bound. A bound on
row margins already bounds every integer quotient width. -/
theorem reindexedDrawBits_polynomial (R : Option I → ℕ) (P : Option J → ℕ)
    (d C b h : ℕ) (e : I×J ≃ Fin q) (hq : q ≤ d)
    (hR : ∀ i,R i ≤ C) (hb : Nat.clog 2 (C+2) ≤ b) :
    reindexedDrawBits R P d e h ≤ 25*(d+b+h+1)^62 := by
  apply denseDrawBits_polynomial (maximalMargin R) (maximalMargin P) d C b h e hq
  · intro p
    exact (Nat.div_le_self _ _).trans ((min_le_left _ _).trans (hR _))
  · exact hb

end
end ContingencyTables.GridBoundary

end OAI
