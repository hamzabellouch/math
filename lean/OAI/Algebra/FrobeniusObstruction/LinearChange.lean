import Mathlib
import OAI.Algebra.FrobeniusObstruction.Derivations
import OAI.Algebra.FrobeniusObstruction.NilpotentInverse

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
variable (ell : ℕ) (hell : 0 < ell)

def augmentation : Ring (ι := ι) (k := k) ell →ₐ[k] k :=
  { constantHom ell hell with commutes' := constantHom_algebraMap ell hell }

omit [DecidableEq ι] in
@[simp] theorem augmentation_coordinate (i : ι) :
    augmentation (k := k) ell hell (coordinate ell i) = 0 := by
  change MvPowerSeries.constantCoeff (MvPowerSeries.X i : Series (k := k)) = 0
  simp

def maximalIdeal : Ideal (Ring (ι := ι) (k := k) ell) :=
  RingHom.ker (augmentation ell hell)

theorem maximalIdeal_nilpotent [CharP k ell] [Fact ell.Prime] :
    IsNilpotent (maximalIdeal (ι := ι) (k := k) ell hell) := by
  let : IsNoetherianRing (Ring (ι := ι) (k := k) ell) :=
    IsNoetherianRing.of_finite k _
  apply (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (maximalIdeal (ι := ι) (k := k) ell hell))).mpr
  intro x hx
  apply mem_nilradical.mpr
  refine ⟨ell, frobenius_zero_of_constant x ?_⟩
  have hx' : constantHom ell hell x = 0 := hx
  rw [hx', zero_pow (by omega)]

                                                                      
                                                    
theorem augmentation_comp (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell) :
    (augmentation ell hell).comp f = augmentation ell hell := by
  apply algHom_ext
  intro i
  rw [AlgHom.comp_apply, augmentation_coordinate]
  have hz : ((augmentation ell hell) (f (coordinate ell i)))^ell = 0 := by
    rw [← map_pow, ← map_pow, coordinate_pow, map_zero, map_zero]
  exact eq_zero_of_pow_eq_zero hz

theorem endomorphism_difference_mem
    (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell) (x) :
    f x - x ∈ maximalIdeal ell hell := by
  change augmentation ell hell (f x - x) = 0
  rw [map_sub, ← AlgHom.comp_apply, augmentation_comp, sub_self]

                                                                       
                                                                   
theorem bijective_of_tangent_identity [CharP k ell] [Fact ell.Prime]
    (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell)
    (hfirst : ∀ x ∈ maximalIdeal ell hell,
      f x - x ∈ (maximalIdeal ell hell)^2) : Function.Bijective f :=
  NilpotentInverse.bijective_of_first_jet _ (maximalIdeal_nilpotent ell hell) f
    (endomorphism_difference_mem ell hell f) hfirst

                                                                       
omit [Fintype ι] [DecidableEq ι] in
theorem monomial_mem_coordinate_pow (e : ι →₀ ℕ) :
    Ideal.Quotient.mk _ (MvPowerSeries.monomial e (1 : k)) ∈
      (Ideal.span (Set.range (coordinate (ι := ι) (k := k) ell)))^e.degree := by
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i b e hi hb ih =>
      rw [map_add, Finsupp.degree_single]
      rw [pow_add (Ideal.span (Set.range (coordinate (ι := ι) (k := k) ell))) b e.degree]
      rw [← one_mul (1 : k), ← MvPowerSeries.monomial_mul_monomial,
        map_mul, ← MvPowerSeries.X_pow_eq, map_pow]
      exact Ideal.mul_mem_mul
        (Ideal.pow_mem_pow
          (show coordinate (k := k) ell i ∈ Ideal.span (Set.range (coordinate (ι := ι) (k := k) ell)) from
            Ideal.subset_span ⟨i, rfl⟩) b) ih

                                                                          
                                                  
theorem maximalIdeal_eq_span : maximalIdeal (ι := ι) (k := k) ell hell =
    Ideal.span (Set.range (coordinate (ι := ι) (k := k) ell)) := by
  apply le_antisymm
  · intro x hx
    rw [monomial_expansion ell x]
    apply Submodule.sum_mem
    intro v _
    by_cases he : exponent ell v = 0
    · have hc : coefficients ell x v = 0 := by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
        change MvPowerSeries.coeff (exponent ell v) f = 0
        rw [he, MvPowerSeries.coeff_zero_eq_constantCoeff]
        exact hx
      rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · apply (Ideal.span (Set.range (coordinate (ι := ι) (k := k) ell))).restrictScalars k |>.smul_mem
      have hd : 1 ≤ (exponent ell v).degree := by
        have := (Finsupp.degree_eq_zero_iff (exponent ell v)).not.mpr he
        omega
      exact (show (Ideal.span (Set.range (coordinate (ι := ι) (k := k) ell)))^
          (exponent ell v).degree ≤ _ from
        (Ideal.pow_le_pow_right hd).trans_eq (pow_one (Ideal.span (Set.range (coordinate (ι := ι) (k := k) ell)))))
          (monomial_mem_coordinate_pow ell (exponent ell v))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact augmentation_coordinate ell hell i

theorem bijective_of_coordinate_first_jet [CharP k ell] [Fact ell.Prime]
    (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell)
    (hfirst : ∀ i, f (coordinate ell i) - coordinate ell i ∈ (maximalIdeal ell hell)^2) :
    Function.Bijective f := by
  apply bijective_of_tangent_identity ell hell f
  rw [maximalIdeal_eq_span] at *
  apply NilpotentInverse.first_jet_of_generators _ f
  · intro x
    rw [← maximalIdeal_eq_span ell hell]
    exact endomorphism_difference_mem ell hell f x
  · exact hfirst

                                                                          
theorem endomorphism_pow_mem
    (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell)
    (n : ℕ) {x} (hx : x ∈ (maximalIdeal ell hell)^n) : f x ∈ (maximalIdeal ell hell)^n := by
  have hf : Ideal.map f.toRingHom (maximalIdeal (ι := ι) (k := k) ell hell) ≤ maximalIdeal ell hell := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro y hy
    change augmentation ell hell (f y) = 0
    rw [← AlgHom.comp_apply, augmentation_comp]
    exact hy
  have hfn : Ideal.map f.toRingHom ((maximalIdeal (ι := ι) (k := k) ell hell)^n) ≤ (maximalIdeal ell hell)^n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hf n
  exact hfn (Ideal.mem_map_of_mem f.toRingHom hx)

def linearCoordinates (M : Matrix ι ι k) (i : ι) : Ring (ι := ι) (k := k) ell :=
  ∑ j, M i j • coordinate ell j

omit [DecidableEq ι] in
@[simp] theorem augmentation_linearCoordinates (M : Matrix ι ι k) (i : ι) :
    augmentation ell hell (linearCoordinates ell M i) = 0 := by
  simp [linearCoordinates]

section Prime
variable [CharP k ell] [Fact ell.Prime]

include hell in
theorem linearCoordinates_pow (M : Matrix ι ι k) (i : ι) :
    (linearCoordinates ell M i)^ell = 0 := by
  apply frobenius_zero_of_constant
  change (augmentation ell hell (linearCoordinates ell M i))^ell = 0
  rw [augmentation_linearCoordinates, zero_pow (by omega)]

def linearSubst (M : Matrix ι ι k) : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell :=
  eval ell (linearCoordinates ell M) (linearCoordinates_pow ell hell M)

@[simp] theorem linearSubst_coordinate (M : Matrix ι ι k) (i : ι) :
    linearSubst ell hell M (coordinate ell i) = linearCoordinates ell M i :=
  eval_coordinate ell _ _ i

theorem linearSubst_comp (M N : Matrix ι ι k) :
    (linearSubst ell hell M).comp (linearSubst ell hell N) = linearSubst ell hell (N*M) := by
  apply algHom_ext
  intro i
  simp only [AlgHom.comp_apply, linearSubst_coordinate, linearCoordinates,
    map_sum, map_smul, linearSubst_coordinate, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

@[simp] theorem linearSubst_one :
    linearSubst (ι := ι) (k := k) ell hell 1 = AlgHom.id k _ := by
  apply algHom_ext
  intro i
  simp [linearCoordinates, Matrix.one_apply]

theorem linearSubst_injective (M : Matrix ι ι k) (hM : IsUnit M.det) :
    Function.Injective (linearSubst ell hell M) := by
  have hi : (linearSubst ell hell M⁻¹).comp (linearSubst ell hell M) = AlgHom.id k _ := by
    rw [linearSubst_comp, Matrix.mul_nonsing_inv M hM, linearSubst_one]
  intro x y h
  have ht := congrArg (linearSubst ell hell M⁻¹) h
  change ((linearSubst ell hell M⁻¹).comp (linearSubst ell hell M)) x =
    ((linearSubst ell hell M⁻¹).comp (linearSubst ell hell M)) y at ht
  simpa only [hi, AlgHom.id_apply] using ht

                                                                      
                                                                    
theorem bijective_of_invertible_first_jet
    (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell)
    (M : Matrix ι ι k) (hM : IsUnit M.det)
    (hfirst : ∀ i, f (coordinate ell i) - linearCoordinates ell M i ∈ (maximalIdeal ell hell)^2) :
    Function.Bijective f := by
  let g := linearSubst ell hell M⁻¹
  have hi : g.comp (linearSubst ell hell M) = AlgHom.id k _ := by
    dsimp only [g]
    rw [linearSubst_comp, Matrix.mul_nonsing_inv M hM, linearSubst_one]
  have hgf : Function.Bijective (g.comp f) := by
    apply bijective_of_coordinate_first_jet ell hell
    intro i
    have ht := endomorphism_pow_mem ell hell g 2 (hfirst i)
    rw [map_sub, ← linearSubst_coordinate ell hell M i] at ht
    have hic := AlgHom.congr_fun hi (coordinate ell i)
    change g ((linearSubst ell hell M) (coordinate ell i)) = coordinate ell i at hic
    rw [hic] at ht
    exact ht
  have hg : Function.Injective g := by
    apply linearSubst_injective ell hell
    simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using hM.inv
  constructor
  · intro x y h
    apply hgf.1
    change g (f x) = g (f y)
    rw [h]
  · intro y
    obtain ⟨x, hx⟩ := hgf.2 (g y)
    exact ⟨x, hg hx⟩

end Prime
end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
variable (ell : ℕ) (htwo : 1 < ell)

def tangentCoeff (i : ι) : Ring (ι := ι) (k := k) ell →ₗ[k] k :=
  quotientCoeff ell (Finsupp.single i 1) (by
    intro j
    by_cases h : i = j
    · subst j; simpa using htwo
    · simp [Finsupp.single_eq_of_ne (Ne.symm h)]; omega)

@[simp] theorem tangentCoeff_mk (i : ι) (f : Series (ι := ι) (k := k)) :
    tangentCoeff ell htwo i (Ideal.Quotient.mk _ f) =
      MvPowerSeries.coeff (Finsupp.single i 1) f := rfl

@[simp] theorem tangentCoeff_coordinate (i j : ι) :
    tangentCoeff (k := k) ell htwo i (coordinate ell j) = if i = j then 1 else 0 := by
  simp [coordinate, MvPowerSeries.coeff_X, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

@[simp] theorem tangentCoeff_one (i : ι) :
    tangentCoeff (k := k) ell htwo i 1 = 0 := by
  change tangentCoeff (k := k) ell htwo i (Ideal.Quotient.mk _ (1 : Series (ι := ι) (k := k))) = 0
  rw [tangentCoeff_mk, MvPowerSeries.coeff_one]
  simp

def firstJetError : Ring (ι := ι) (k := k) ell →ₗ[k] Ring (ι := ι) (k := k) ell :=
  LinearMap.id - (augmentation (ι := ι) (k := k) ell (by omega)).toLinearMap.smulRight (1 : Ring (ι := ι) (k := k) ell) -
    ∑ i, (tangentCoeff ell htwo i).smulRight (coordinate ell i)

@[simp] theorem firstJetError_apply (x : Ring (ι := ι) (k := k) ell) :
    firstJetError ell htwo x = x - augmentation ell (by omega) x • 1 -
      ∑ i, tangentCoeff ell htwo i x • coordinate ell i := by
  simp [firstJetError]

@[simp] theorem firstJetError_one : firstJetError (ι := ι) (k := k) ell htwo 1 = 0 := by
  simp

@[simp] theorem firstJetError_coordinate (i : ι) :
    firstJetError (k := k) ell htwo (coordinate ell i) = 0 := by
  simp

                                                                            
                                                                                  
theorem firstJetError_mem_square (x : Ring (ι := ι) (k := k) ell) :
    firstJetError ell htwo x ∈ (maximalIdeal ell (by omega))^2 := by
  rw [monomial_expansion ell x, map_sum]
  apply Submodule.sum_mem
  intro v _
  rw [map_smul]
  refine (((maximalIdeal (ι := ι) (k := k) ell (by omega))^2).restrictScalars k).smul_mem _ ?_
  by_cases hz : (exponent ell v).degree = 0
  · have he := (Finsupp.degree_eq_zero_iff _).mp hz
    have hm : monomial (k := k) ell v = 1 := by simp [monomial, he]
    rw [hm, firstJetError_one]
    exact Submodule.zero_mem _
  by_cases ho : (exponent ell v).degree = 1
  · obtain ⟨i, hi⟩ : exponent ell v ∈ Set.range (fun i : ι => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact ho
    have hm : monomial (k := k) ell v = coordinate ell i := by
      simp [monomial, ← hi, coordinate, MvPowerSeries.X_def]
    rw [hm, firstJetError_coordinate]
    exact Submodule.zero_mem _
  · have he : exponent ell v ≠ 0 := (Finsupp.degree_eq_zero_iff _).not.mp hz
    have hs (i : ι) : Finsupp.single i 1 ≠ exponent ell v := by
      intro hi
      apply ho
      simp [← hi]
    have ha : augmentation ell (by omega) (monomial (k := k) ell v) = 0 := by
      change MvPowerSeries.constantCoeff (MvPowerSeries.monomial (exponent ell v) (1:k)) = 0
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial]
      simp [Ne.symm he]
    have hc (i : ι) : tangentCoeff ell htwo i (monomial (k := k) ell v) = 0 := by
      simp [monomial, MvPowerSeries.coeff_monomial, hs i]
    rw [firstJetError_apply, ha, zero_smul, sub_zero]
    simp only [hc, zero_smul, Finset.sum_const_zero, sub_zero]
    rw [maximalIdeal_eq_span]
    apply Ideal.pow_le_pow_right (show 2 ≤ (exponent ell v).degree by omega)
    exact monomial_mem_coordinate_pow ell (exponent ell v)

                                                                             
                                             
theorem bijective_of_tangent_matrix [CharP k ell] [Fact ell.Prime]
    (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell)
    (hM : IsUnit (Matrix.det (fun i j => tangentCoeff ell htwo j (f (coordinate ell i))))) :
    Function.Bijective f := by
  apply bijective_of_invertible_first_jet ell (by omega) f _ hM
  intro i
  have ha : augmentation ell (by omega) (f (coordinate ell i)) = 0 := by
    rw [← AlgHom.comp_apply, augmentation_comp, augmentation_coordinate]
  simpa only [firstJetError_apply, ha, zero_smul, sub_zero, linearCoordinates]
    using firstJetError_mem_square ell htwo (f (coordinate ell i))

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k S : Type*} [Fintype ι] [DecidableEq ι] [CommRing k]
  [CommRing S] [Algebra k S] (ell : ℕ) [CharP k ell]

                                                                                
theorem derivation_chain_rule (f : Ring (ι := ι) (k := k) ell →ₐ[k] S)
    (D : Derivation k S S) (x : Ring (ι := ι) (k := k) ell) :
    D (f x) = ∑ i, f (partialDeriv ell i x) * D (f (coordinate ell i)) := by
  let u := D.toLinearMap.comp f.toLinearMap
  let v : Ring (ι := ι) (k := k) ell →ₗ[k] S :=
    ∑ i, D (f (coordinate ell i)) • (f.toLinearMap.comp (partialDeriv ell i).toLinearMap)
  have hv (x) : v x = ∑ i, f (partialDeriv ell i x) * D (f (coordinate ell i)) := by
    simp only [v, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      Derivation.coeFn_coe, AlgHom.toLinearMap_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have h : u = v := by
    apply relativeDeriv_ext ell f
    · simp [u]
    · rw [hv]; simp
    · intro x y
      simp only [u, LinearMap.comp_apply, Derivation.coeFn_coe,
        AlgHom.toLinearMap_apply, map_mul, Derivation.leibniz, smul_eq_mul]
      ring
    · intro x y
      rw [hv, hv, hv, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring
    · intro i
      rw [hv]
      simp only [coordinate, partial_coordinate, u, LinearMap.comp_apply, Derivation.coeFn_coe,
        AlgHom.toLinearMap_apply, apply_ite f, map_one, map_zero, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (LinearMap.congr_fun h x).trans (hv x)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem partial_chain_rule (f : Ring (ι := ι) (k := k) ell →ₐ[k]
    Ring (ι := κ) (k := k) ell) (j : κ) (x : Ring (ι := ι) (k := k) ell) :
    partialDeriv ell j (f x) = ∑ i, f (partialDeriv ell i x) *
      partialDeriv ell j (f (coordinate ell i)) :=
  derivation_chain_rule ell f (partialDeriv ell j) x

end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
