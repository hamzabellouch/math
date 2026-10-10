import Mathlib
import OAI.Algebra.FrobeniusObstruction.LinearChange
import OAI.Algebra.FrobeniusObstruction.FormTensor

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι κ k : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [CommRing k] (ell : ℕ)

def reindex (e : ι ≃ κ) : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := κ) (k := k) ell :=
  AlgEquiv.ofAlgHom (includeVariables ell e) (includeVariables ell e.symm)
    (by apply algHom_ext; intro i; simp)
    (by apply algHom_ext; intro i; simp)

@[simp] theorem reindex_coordinate (e : ι ≃ κ) (i : ι) :
    reindex (k := k) ell e (coordinate ell i) = coordinate ell (e i) :=
  includeVariables_coordinate ell e i

@[simp] theorem partial_reindex [CharP k ell] (e : ι ≃ κ) (i : ι)
    (a : Ring (ι := ι) (k := k) ell) :
    partialDeriv ell (e i) (reindex ell e a) = reindex ell e (partialDeriv ell i a) := by
  let f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := κ) (k := k) ell :=
    (reindex ell e).toAlgHom
  have H : (partialDeriv (k := k) ell (e i)).toLinearMap.comp f.toLinearMap =
      f.toLinearMap.comp (partialDeriv ell i).toLinearMap := by
    apply relativeDeriv_ext ell f
    · simp
    · simp
    · intro x y; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
        Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]; ring
    · intro x y; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring
    · intro j
      change partialDeriv ell (e i) (reindex ell e (coordinate ell j)) =
        reindex ell e (partialDeriv ell i (coordinate ell j))
      rw [reindex_coordinate]
      simp only [coordinate, partial_coordinate]
      by_cases hij : i = j
      · subst j; simp
      · simp [hij, e.injective.ne hij]
  exact LinearMap.congr_fun H a

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.FormsReindex
open Frobenius MixedForms
open scoped TensorProduct
variable {ι κ k : Type*} [DecidableEq ι] [DecidableEq κ]
  [CommRing k] (ell : ℕ)

def vec (e : ι ≃ κ) : (ι → k) ≃ₗ[k] (κ → k) :=
  LinearEquiv.piCongrLeft' k (fun _ : ι => k) e

def exterior (e : ι ≃ κ) : ExteriorAlgebra k (ι → k) ≃ₐ[k] ExteriorAlgebra k (κ → k) :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map (vec (k := k) e).toLinearMap)
    (ExteriorAlgebra.map (vec (k := k) e).symm.toLinearMap)
    (by ext v; simp)
    (by ext v; simp)

@[simp] theorem exterior_gen (e : ι ≃ κ) (i : ι) :
    exterior (k := k) e (gen i) = gen (e i) := by
  change ExteriorAlgebra.map (vec e).toLinearMap (ExteriorAlgebra.ι k (Pi.single i 1)) = _
  rw [ExteriorAlgebra.map_apply_ι]
  congr 1
  funext j
  simp only [vec, Pi.single_apply]
  by_cases h : j = e i
  · subst j; simp
  · have h' : e.symm j ≠ i := by intro he; exact h (by simpa using congrArg e he)
    simp [h, h']

variable [Fintype ι] [Fintype κ]

abbrev QForms (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  MixedForms.Forms (k := k) (A := Ring (ι := ι) (k := k) ell) (ι := ι)

def equiv (e : ι ≃ κ) : QForms (k := k) ell ι ≃ₐ[k] QForms (k := k) ell κ :=
  Algebra.TensorProduct.congr (Frobenius.reindex ell e) (exterior e)

@[simp] theorem equiv_tmul (e : ι ≃ κ) (a : Ring (ι := ι) (k := k) ell)
    (x : ExteriorAlgebra k (ι → k)) : equiv ell e (a ⊗ₜ[k] x) =
      Frobenius.reindex ell e a ⊗ₜ[k] exterior e x := rfl

@[simp] theorem equiv_d [CharP k ell] (e : ι ≃ κ) (x : QForms (k := k) ell ι) :
    equiv ell e (d (partialDeriv ell) x) = d (partialDeriv ell) (equiv ell e x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    simp only [d_tmul, map_sum, equiv_tmul, map_mul, exterior_gen]
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro i _
    rw [partial_reindex]

@[simp] theorem equiv_coeff (e : ι ≃ κ) (a : Ring (ι := ι) (k := k) ell) :
    equiv ell e (coeff a) = coeff (Frobenius.reindex ell e a) := by
  change equiv ell e (a ⊗ₜ[k] (1 : ExteriorAlgebra k (ι → k))) =
    Frobenius.reindex ell e a ⊗ₜ[k] (1 : ExteriorAlgebra k (κ → k))
  rw [equiv_tmul, map_one]

@[simp] theorem equiv_gradient [CharP k ell] (e : ι ≃ κ)
    (a : Ring (ι := ι) (k := k) ell) :
    equiv ell e (gradient (partialDeriv ell) a) =
      gradient (partialDeriv ell) (Frobenius.reindex ell e a) := by
  rw [← d_coeff, equiv_d, equiv_coeff, d_coeff]

@[simp] theorem equiv_delta [CharP k ell] (e : ι ≃ κ)
    (a : Ring (ι := ι) (k := k) ell) (x : QForms (k := k) ell ι) :
    equiv ell e (delta (partialDeriv ell) a x) =
      delta (partialDeriv ell) (Frobenius.reindex ell e a) (equiv ell e x) := by
  simp only [delta_apply, map_mul, equiv_gradient]

end BoundaryOnly.FormalObstruction.FormsReindex

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
variable (ell : ℕ) (hell : 0 < ell)

                                                                               
omit [DecidableEq ι] in
theorem quotientCoeff_coordinate_mul (i : ι) (e : ι →₀ ℕ)
    (he : Good ell e) (hes : Good ell (Finsupp.single i 1 + e))
    (x : Ring (ι := ι) (k := k) ell) :
    quotientCoeff ell (Finsupp.single i 1 + e) hes (coordinate ell i * x) =
      quotientCoeff ell e he x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotientCoeff ell (Finsupp.single i 1 + e) hes
    (Ideal.Quotient.mk _ (MvPowerSeries.X i) * Ideal.Quotient.mk _ f) = _
  rw [← map_mul, quotientCoeff_mk, quotientCoeff_mk]
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  simp

                                                                             
theorem eq_smul_top_of_coordinate_annihilate
    (x : Ring (ι := ι) (k := k) ell) (hx : ∀ i, coordinate ell i * x = 0) :
    x = quotientCoeff ell (topExponent ell) (topExponent_good hell) x • topMonomial ell := by
  apply quotient_ext
  intro e he
  rw [map_smul]
  change quotientCoeff ell e he x = _ *
    quotientCoeff ell e he (Ideal.Quotient.mk _ (MvPowerSeries.monomial (topExponent ell) (1 : k)))
  rw [quotientCoeff_mk, MvPowerSeries.coeff_monomial]
  by_cases het : e = topExponent ell
  · subst e
    simp
  · rw [ite_eq_right het, mul_zero]
    have hlt : ∃ i, e i < ell - 1 := by
      by_contra hn
      push Not at hn
      apply het
      ext i
      have hi := he i
      simp only [topExponent_apply]
      exact Nat.le_antisymm (by omega) (hn i)
    obtain ⟨i, hi⟩ := hlt
    have hs : Good ell (Finsupp.single i 1 + e) := by
      intro j
      by_cases hij : i = j
      · subst j; simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
      · simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hij), zero_add]
          using he j
    have hshift := quotientCoeff_coordinate_mul ell i e he hs x
    rw [hx, map_zero] at hshift
    exact hshift.symm

include hell in
                                                                           
                                                                          
                                 
theorem automorphism_top (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell)
    (hf : Function.Bijective f) :
    ∃ c : k, c ≠ 0 ∧ f (topMonomial ell) = c • topMonomial ell := by
  have hx (i : ι) : coordinate ell i * f (topMonomial ell) = 0 := by
    obtain ⟨y, hy⟩ := hf.2 (coordinate ell i)
    have ha : augmentation ell hell y = 0 := by
      rw [← augmentation_comp ell hell f, AlgHom.comp_apply, hy, augmentation_coordinate]
    rw [← hy, ← map_mul, mul_comm, topMonomial_mul hell]
    change f ((augmentation ell hell y) • topMonomial ell) = 0
    rw [ha, zero_smul, map_zero]
  refine ⟨_, ?_, eq_smul_top_of_coordinate_annihilate ell hell _ hx⟩
  intro hc
  have hz := eq_smul_top_of_coordinate_annihilate ell hell _ hx
  rw [hc, zero_smul, ← map_zero f] at hz
  exact topMonomial_ne_zero hell (hf.1 hz)

end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
