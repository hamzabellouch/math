import OAI.NumberTheory.Ostmann.Arithmetic.CRTResidueAverage
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLines

namespace OAI

/-! # Joint CRT factorization in the two giant environments -/

namespace Ostmann

open scoped BigOperators

theorem uniform_equiv_pi_average {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] {X : I → Type*} [∀ i, Fintype (X i)]
    (e : A ≃ ∀ i, X i) (f : ∀ i, X i → ℝ) :
    (Fintype.card A : ℝ)⁻¹ * (∑ a, ∏ i, f i (e a i)) =
      ∏ i, (Fintype.card (X i) : ℝ)⁻¹ * ∑ x, f i x := by
  classical
  rw [e.sum_comp (fun x => ∏ i, f i (x i)), Fintype.card_congr e, Fintype.card_pi]
  rw [← Fintype.prod_sum]
  simp only [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

noncomputable def crtUnitPairEquiv {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j))) :
    ((ZMod (∏ i, a i))ˣ × (ZMod (∏ i, a i))ˣ) ≃
      (∀ i, (ZMod (a i))ˣ × (ZMod (a i))ˣ) :=
  ((crtUnitEquiv a hc).toEquiv.prodCongr (crtUnitEquiv a hc).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow I (fun i => (ZMod (a i))ˣ)
      (fun i => (ZMod (a i))ˣ)).symm

noncomputable def crtExternalPairEquiv {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j))) :
    (ZMod (∏ i, a i) × (ZMod (∏ i, a i))ˣ) ≃
      (∀ i, ZMod (a i) × (ZMod (a i))ˣ) :=
  ((ZMod.prodEquivPi a hc).toEquiv.prodCongr (crtUnitEquiv a hc).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow I (fun i => ZMod (a i))
      (fun i => (ZMod (a i))ˣ)).symm

theorem crtUnitPairEquiv_apply {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (u v : (ZMod (∏ i, a i))ˣ) (i : I) :
    crtUnitPairEquiv a hc (u, v) i = (crtUnitEquiv a hc u i, crtUnitEquiv a hc v i) := rfl

theorem crtExternalPairEquiv_apply {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (u : ZMod (∏ i, a i)) (v : (ZMod (∏ i, a i))ˣ) (i : I) :
    crtExternalPairEquiv a hc (u, v) i = (ZMod.prodEquivPi a hc u i, crtUnitEquiv a hc v i) := rfl

/-- The local line tests multiply when both giant coordinates are unit residues. -/
theorem crt_unit_pair_average {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (f : ∀ i, (ZMod (a i))ˣ × (ZMod (a i))ˣ → ℝ) :
    (Fintype.card ((ZMod (∏ i, a i))ˣ × (ZMod (∏ i, a i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, f i (crtUnitPairEquiv a hc z i)) =
    ∏ i, (Fintype.card ((ZMod (a i))ˣ × (ZMod (a i))ˣ) : ℝ)⁻¹ * ∑ z, f i z :=
  uniform_equiv_pi_average (crtUnitPairEquiv a hc) f

/-- The same exact factorization with the first giant an external integer. -/
theorem crt_external_pair_average {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (f : ∀ i, ZMod (a i) × (ZMod (a i))ˣ → ℝ) :
    (Fintype.card (ZMod (∏ i, a i) × (ZMod (∏ i, a i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, f i (crtExternalPairEquiv a hc z i)) =
    ∏ i, (Fintype.card (ZMod (a i) × (ZMod (a i))ˣ) : ℝ)⁻¹ * ∑ z, f i z :=
  uniform_equiv_pi_average (crtExternalPairEquiv a hc) f

end Ostmann

end OAI
