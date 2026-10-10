/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import OAI.AlgebraicGeometry.CartierSections.InfinitesimalCharts
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.MvPowerSeries.Equiv

namespace OAI

/-!
# Completion coordinates for étale charts

Compatible infinitesimal isomorphisms identify an étale chart completion with a
power-series ring. Expansion through a Noetherian local completion is faithfully flat.
-/

namespace CartierSections

attribute [local instance 10001] scalarTower_self
section CompletionIsomorphism
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Evaluation of an adic completion commutes with reduction to a lower ideal power. -/
theorem completion_eval_factor (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  have hx := congrArg (Ideal.Quotient.factor (show (I^m • ⊤ : Ideal R) ≤ I^m
    from le_of_eq (Ideal.mul_top _))) (x.property h)
  simpa [AdicCompletion.evalₐ, AdicCompletion.eval,
    AdicCompletion.transitionMap, Submodule.factorPow] using hx

/-- Evaluation on infinitesimal neighbourhoods is compatible with the maps induced
by an algebra map. -/
theorem quotientPowerMap_eval_compatible (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := I.map (algebraMap R A)) h)).comp
      ((quotientPowerMap I n).comp (AdicCompletion.evalₐ I n)) =
        (quotientPowerMap I m).comp (AdicCompletion.evalₐ I m) := by
  rw [← AlgHom.comp_assoc, quotientPowerMap_factor I h, AlgHom.comp_assoc]
  congr 1
  ext x
  exact completion_eval_factor I h x

/-- The completion map induced by an algebra map. -/
noncomputable def chartCompletionMap (I : Ideal R) :
    AdicCompletion I R →ₐ[R] AdicCompletion (I.map (algebraMap R A)) A :=
  AdicCompletion.liftAlgHom _
    (fun n => (quotientPowerMap I n).comp (AdicCompletion.evalₐ I n))
    (quotientPowerMap_eval_compatible I)

@[simp] theorem chartCompletionMap_eval (I : Ideal R) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ (I.map (algebraMap R A)) n (chartCompletionMap I x) =
      quotientPowerMap I n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftAlgHom _ _ (quotientPowerMap_eval_compatible I) n x

/-- Étale charts with trivial residue extension have the same completion.
This is derived from formal lifting and uniqueness at every order. -/
theorem chartCompletionMap_bijective [Algebra.FormallyEtale R A]
    (I : Ideal R) (hI : Function.Bijective (quotientBaseMap (A := A) I)) :
    Function.Bijective (chartCompletionMap (A := A) I) := by
  classical
  let J := I.map (algebraMap R A)
  let e (n : ℕ) := AlgEquiv.ofBijective (quotientPowerMap (A := A) I n)
    (etale_quotient_power_bijective I hI n)
  let g (n : ℕ) : AdicCompletion J A →ₐ[R] R ⧸ I^n :=
    (e n).symm.toAlgHom.comp ((AdicCompletion.evalₐ J n).restrictScalars R)
  have hg {m n : ℕ} (h : m ≤ n) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp (g n) = g m := by
    ext x
    apply (e m).injective
    change quotientPowerMap I m
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) ((e n).symm (AdicCompletion.evalₐ J n x))) = _
    have hfac := AlgHom.congr_fun (quotientPowerMap_factor (A := A) I h)
      ((e n).symm (AdicCompletion.evalₐ J n x))
    simp only [AlgHom.comp_apply] at hfac
    rw [← hfac]
    change Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)
      (e n ((e n).symm (AdicCompletion.evalₐ J n x))) = e m ((e m).symm (AdicCompletion.evalₐ J m x))
    rw [(e n).apply_symm_apply, (e m).apply_symm_apply]
    exact completion_eval_factor J h x
  let inv : AdicCompletion J A →ₐ[R] AdicCompletion I R :=
    AdicCompletion.liftAlgHom I g (fun h => hg h)
  have hleft : Function.LeftInverse inv (chartCompletionMap (A := A) I) := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change (e n).symm (AdicCompletion.evalₐ J n (chartCompletionMap I x)) = _
    rw [chartCompletionMap_eval]
    exact (e n).symm_apply_apply _
  have hright : Function.RightInverse inv (chartCompletionMap (A := A) I) := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [chartCompletionMap_eval, AdicCompletion.evalₐ_liftAlgHom]
    exact (e n).apply_symm_apply _
  exact ⟨hleft.injective, hright.surjective⟩

noncomputable def chartCompletionEquiv [Algebra.FormallyEtale R A]
    (I : Ideal R) (hI : Function.Bijective (quotientBaseMap (A := A) I)) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion (I.map (algebraMap R A)) A :=
  AlgEquiv.ofBijective (chartCompletionMap I) (chartCompletionMap_bijective I hI)
end CompletionIsomorphism
/-- Formal coordinates on the completion of an étale polynomial chart. -/
noncomputable def polynomialChartSeriesEquiv
    {σ k A : Type*} [Finite σ] [CommRing k] [CommRing A]
    [Algebra (MvPolynomial σ k) A] [Algebra.FormallyEtale (MvPolynomial σ k) A]
    (hI : Function.Bijective
      (quotientBaseMap (A := A) (MvPolynomial.idealOfVars σ k))) :
    MvPowerSeries σ k ≃ₐ[MvPolynomial σ k]
      AdicCompletion ((MvPolynomial.idealOfVars σ k).map (algebraMap (MvPolynomial σ k) A)) A :=
  (MvPowerSeries.toAdicCompletionAlgEquiv σ k).trans
    (chartCompletionEquiv (MvPolynomial.idealOfVars σ k) hI)

@[simp] theorem polynomialChartSeriesEquiv_coe
    {σ k A : Type*} [Finite σ] [CommRing k] [CommRing A]
    [Algebra (MvPolynomial σ k) A] [Algebra.FormallyEtale (MvPolynomial σ k) A]
    (hI : Function.Bijective
      (quotientBaseMap (A := A) (MvPolynomial.idealOfVars σ k))) (p : MvPolynomial σ k) :
    polynomialChartSeriesEquiv hI (p : MvPowerSeries σ k) =
      algebraMap A _ (algebraMap (MvPolynomial σ k) A p) := by
  exact (polynomialChartSeriesEquiv hI).commutes p
/-- The expansion map attached to an isomorphism with the maximal-ideal completion. -/
noncomputable def completionExpansion
    {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S]
    (e : S ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A) : A →+* S :=
  e.symm.toRingHom.comp (algebraMap A _)

/-- Formal expansion through a Noetherian completion is faithfully flat. -/
theorem completionExpansion_faithfullyFlat
    {A S : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing S]
    (e : S ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    letI : Algebra A S := (completionExpansion e).toAlgebra
    Module.FaithfullyFlat A S := by
  let : Algebra A S := (completionExpansion e).toAlgebra
  have : Module.FaithfullyFlat A (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let eA : S ≃ₐ[A] AdicCompletion (IsLocalRing.maximalIdeal A) A :=
    { e with commutes' := fun a => e.apply_symm_apply (algebraMap A _ a) }
  exact Module.FaithfullyFlat.of_linearEquiv A _ eA.toLinearEquiv

/-- A formal expansion through a Noetherian local completion reflects units. -/
theorem completionExpansion_isLocalHom
    {A S : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing S]
    (e : S ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    IsLocalHom (completionExpansion e) := by
  constructor
  intro a ha
  apply (isUnit_map_iff (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a).mp
  have h := ha.map e.toMonoidHom
  simpa [completionExpansion] using h
section ChartExpansion
variable {k A σ : Type*} [CommRing k] [CommRing A] [IsLocalRing A]
  [Algebra k A] [Algebra (MvPolynomial σ k) A] [IsScalarTower k (MvPolynomial σ k) A]

/-- Expansion in completion coordinates as an algebra map over the coefficient ring. -/
noncomputable def chartSeriesExpansion
    (e : MvPowerSeries σ k ≃ₐ[MvPolynomial σ k]
      AdicCompletion (IsLocalRing.maximalIdeal A) A) : A →ₐ[k] MvPowerSeries σ k :=
  (e.symm.restrictScalars k).toAlgHom.comp
    (IsScalarTower.toAlgHom k A (AdicCompletion (IsLocalRing.maximalIdeal A) A))

@[simp] theorem chartSeriesExpansion_toRingHom
    (e : MvPowerSeries σ k ≃ₐ[MvPolynomial σ k]
      AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    (chartSeriesExpansion e).toRingHom = completionExpansion e.toRingEquiv := rfl

@[simp] theorem chartSeriesExpansion_coordinate
    (e : MvPowerSeries σ k ≃ₐ[MvPolynomial σ k]
      AdicCompletion (IsLocalRing.maximalIdeal A) A) (i : σ) :
    chartSeriesExpansion e (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)) =
      MvPowerSeries.X i := by
  apply e.injective
  change e (e.symm (algebraMap A _ (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)))) = _
  rw [e.apply_symm_apply]
  have he : e ((MvPolynomial.X i : MvPolynomial σ k) : MvPowerSeries σ k) =
      algebraMap (MvPolynomial σ k) _ (MvPolynomial.X i) := by
    simpa only [MvPowerSeries.algebraMap_apply', Algebra.algebraMap_self,
      MvPowerSeries.map_id, RingHom.id_apply] using e.commutes (MvPolynomial.X i)
  simpa only [MvPolynomial.coe_X,
    IsScalarTower.algebraMap_apply (MvPolynomial σ k) A (AdicCompletion (IsLocalRing.maximalIdeal A) A)] using he.symm
end ChartExpansion
end CartierSections

end OAI
