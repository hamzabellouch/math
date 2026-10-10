import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.PowerSeries.WellKnown
import OAI.NumberTheory.PiExponent.Analysis.HilbertSeries

namespace OAI

namespace PiExponentJets.W64

variable {σ : Type*}

noncomputable def exponentDegreeEquivSym (n : ℕ) :
    {d : σ →₀ ℕ | d.degree = n} ≃ Sym σ n := by
  classical
  exact
    { toFun := fun d => ⟨d.1.toMultiset, by
        rw [Finsupp.card_toMultiset]
        exact d.2⟩
      invFun := fun m => ⟨Multiset.toFinsupp m.1, by
        have hc := Finsupp.card_toMultiset (Multiset.toFinsupp m.1)
        rw [Multiset.toFinsupp_toMultiset] at hc
        change (Multiset.toFinsupp m.1).degree = n
        exact hc.symm.trans m.2⟩
      left_inv := fun d => Subtype.ext (Multiset.toFinsupp.apply_symm_apply d.1)
      right_inv := fun m => Subtype.ext (Multiset.toFinsupp.symm_apply_apply m.1) }

theorem card_exponents_degree [Fintype σ] (n : ℕ) :
    Nat.card {d : σ →₀ ℕ | d.degree = n} = (Fintype.card σ).multichoose n := by
  classical
  rw [Nat.card_congr (exponentDegreeEquivSym n), Nat.card_eq_fintype_card]
  exact Sym.card_sym_eq_multichoose σ n

variable {k : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem quotientSection_bot_finrank (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) := by
  let e := LinearEquiv.ofBijective
    (Ideal.Quotient.mkₐ k (⊥ : Ideal (MvPolynomial σ k))).toLinearMap
    ((Ideal.Quotient.mk_bijective_iff_eq_bot (⊥ : Ideal (MvPolynomial σ k))).mpr rfl)
  exact e.finrank_map_eq (MvPolynomial.homogeneousSubmodule σ k n)

theorem quotientSection_bot_finrank_multichoose [Fintype σ] (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      (Fintype.card σ).multichoose n := by
  rw [quotientSection_bot_finrank, homogeneousSection_finrank, card_exponents_degree]

theorem sectionHilbertSeries_bot [Fintype σ] (hσ : 0 < Fintype.card σ) :
    sectionHilbertSeries (⊥ : Ideal (MvPolynomial σ k)) =
      (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ (Fintype.card σ) hσ]
  ext n
  rw [coeff_sectionHilbertSeries, PowerSeries.coeff_mk,
    quotientSection_bot_finrank_multichoose, Nat.multichoose_eq]
  congr 1
  have hs : Fintype.card σ + n - 1 = (Fintype.card σ - 1) + n := by omega
  rw [hs]
  exact Nat.choose_symm_add.symm

end PiExponentJets.W64

end OAI
