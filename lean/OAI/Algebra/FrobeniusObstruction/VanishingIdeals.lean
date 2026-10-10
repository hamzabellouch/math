import Mathlib
import OAI.Algebra.FrobeniusObstruction.CoordinateMaps
import OAI.Algebra.FrobeniusObstruction.ThreeParameters

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k] (ell : ℕ)

                                                                          
                                                                            
                                                                                 
theorem bijective_of_specialFiber
    (f : Ring (ι := ι) (k := ThreeParameters.Ring k) ell →ₐ[ThreeParameters.Ring k]
      Ring (ι := ι) (k := ThreeParameters.Ring k) ell)
    (g : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (h : ∀ x, mapCoefficients ell (ThreeParameters.augmentation k) (f x) =
      g (mapCoefficients ell (ThreeParameters.augmentation k) x)) :
    Function.Bijective f := by
  let b := monomialBasis (ι := ι) (k := ThreeParameters.Ring k) ell
  let b₀ := monomialBasis (ι := ι) (k := k) ell
  let A := LinearMap.toMatrix b b f.toLinearMap
  let A₀ := LinearMap.toMatrix b₀ b₀ g.toLinearEquiv.toLinearMap
  have hm : (ThreeParameters.augmentation k).mapMatrix A = A₀ := by
    ext v w
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    dsimp only [A, A₀]
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    change ThreeParameters.augmentation k ((b.repr (f (b w))) v) =
      (b₀.repr (g (b₀ w))) v
    dsimp only [b, b₀]
    simp only [monomialBasis_apply, monomialBasis_repr]
    rw [← coefficients_mapCoefficients, h, mapCoefficients_monomial]
  have hu₀ : IsUnit A₀.det := g.toLinearEquiv.isUnit_det b₀ b₀
  have hd : ThreeParameters.augmentation k A.det ≠ 0 := by
    rw [RingHom.map_det, hm]
    exact isUnit_iff_ne_zero.mp hu₀
  have hu : IsUnit A.det := ThreeParameters.isUnit_of_augmentation_ne_zero k _ hd
  let e := Matrix.toLinearEquiv b A hu
  have he : ∀ x, e x = f x := by
    intro x
    rw [Matrix.toLinearEquiv_apply]
    change (Matrix.toLin b b (LinearMap.toMatrix b b f.toLinearMap)) x = _
    rw [Matrix.toLin_toMatrix]
    rfl
  exact ⟨fun x y hxy => e.injective (by rw [he, he, hxy]), fun y =>
    ⟨e.symm y, by rw [← he, e.apply_symm_apply]⟩⟩

noncomputable def liftInverse
    (f : Ring (ι := ι) (k := ThreeParameters.Ring k) ell →ₐ[ThreeParameters.Ring k]
      Ring (ι := ι) (k := ThreeParameters.Ring k) ell)
    (g : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (h : ∀ x, mapCoefficients ell (ThreeParameters.augmentation k) (f x) =
      g (mapCoefficients ell (ThreeParameters.augmentation k) x)) :
    Ring (ι := ι) (k := ThreeParameters.Ring k) ell ≃ₐ[ThreeParameters.Ring k]
      Ring (ι := ι) (k := ThreeParameters.Ring k) ell :=
  AlgEquiv.ofBijective f (bijective_of_specialFiber ell f g h)

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.ThreeParameters
variable (k : Type*) [Field k]

instance parameterNontrivial : Nontrivial (Ring k) := ⟨⟨w k, 0, w_ne_zero k⟩⟩

instance parameterCharP (ell : ℕ) [CharP k ell] : CharP (Ring k) ell :=
  (Algebra.charP_iff k (Ring k) ell).mp inferInstance

                                                                       
                                                                                  
theorem pow_eq_augmentation (ell : ℕ) [Fact ell.Prime] [CharP k ell]
    (b : Ring k) : b ^ ell = (algebraMap k (Ring k) (augmentation k b)) ^ ell := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
    | C c => simp only [augmentation_mk, MvPolynomial.constantCoeff_C]; rfl
    | add p q hp hq =>
      simp only [map_add, add_pow_char, hp, hq]
    | mul_X p i hp =>
      have hs : s k i ^ ell = 0 :=
        pow_eq_zero_of_le (Fact.out : ell.Prime).two_le (s_sq k i)
      simp only [map_mul, augmentation_mk, MvPolynomial.constantCoeff_X,
        mul_zero, map_zero, mul_pow]
      change _ * s k i ^ ell = (0 : Ring k) ^ ell
      rw [hs, mul_zero, zero_pow (Fact.out : ell.Prime).ne_zero]

 theorem augmentation_zero_pow (ell : ℕ) [Fact ell.Prime] [CharP k ell]
    (b : Ring k) (hb : augmentation k b = 0) : b ^ ell = 0 := by
  rw [pow_eq_augmentation k ell, hb, map_zero, zero_pow (Fact.out : ell.Prime).ne_zero]

end BoundaryOnly.FormalObstruction.ThreeParameters

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι κ k l S : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing k] [CommRing l]
variable (ell : ℕ)

omit [DecidableEq ι] in
@[simp] theorem mapCoefficients_algebraMap (f : k →+* l) (a : k) :
    mapCoefficients (ι := ι) ell f (algebraMap k _ a) = algebraMap l _ (f a) := by
  change Ideal.Quotient.mk _ (MvPowerSeries.map f (MvPowerSeries.C a)) = _
  rw [MvPowerSeries.map_C]
  rfl

omit [DecidableEq ι] in
@[simp] theorem mapCoefficients_smul (f : k →+* l) (a : k)
    (x : Ring (ι := ι) (k := k) ell) :
    mapCoefficients ell f (a • x) = f a • mapCoefficients ell f x := by
  rw [Algebra.smul_def a x, Algebra.smul_def (f a) (mapCoefficients ell f x),
    map_mul, mapCoefficients_algebraMap]

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k l : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [CommRing l]
variable (ell : ℕ)
variable [Algebra k l]

def baseChange : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := l) ell :=
  { mapCoefficients ell (algebraMap k l) with
    commutes' := fun a => by
      change mapCoefficients ell (algebraMap k l) (algebraMap k _ a) = _
      rw [mapCoefficients_algebraMap]
      exact (IsScalarTower.algebraMap_apply k l (Ring (ι := ι) (k := l) ell) a).symm }

omit [DecidableEq ι] in
@[simp] theorem baseChange_coordinate (i : ι) :
    baseChange (k := k) (l := l) ell (coordinate ell i) = coordinate ell i :=
  mapCoefficients_coordinate ell _ i

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k] (ell : ℕ)

                                                                         
def reduction : Ring (ι := ι) (k := ThreeParameters.Ring k) ell →ₐ[k]
    Ring (ι := ι) (k := k) ell :=
  { mapCoefficients ell (ThreeParameters.augmentation k) with
    commutes' := fun a => by
      change mapCoefficients ell (ThreeParameters.augmentation k)
        (algebraMap k (Ring (ι := ι) (k := ThreeParameters.Ring k) ell) a) = _
      rw [IsScalarTower.algebraMap_apply k (ThreeParameters.Ring k) (Ring (ι := ι) (k := ThreeParameters.Ring k) ell)]
      change mapCoefficients ell (ThreeParameters.augmentation k)
        (@algebraMap (ThreeParameters.Ring k) (Ring (ι := ι) (k := ThreeParameters.Ring k) ell) inferInstance inferInstance inferInstance (algebraMap k (ThreeParameters.Ring k) a)) = _
      rw [mapCoefficients_algebraMap, ThreeParameters.augmentation_algebraMap] }

omit [DecidableEq ι] in
@[simp] theorem reduction_coordinate (i : ι) :
    reduction (k := k) ell (coordinate ell i) = coordinate ell i :=
  mapCoefficients_coordinate ell _ i

omit [DecidableEq ι] in
@[simp] theorem reduction_base (a : ThreeParameters.Ring k) :
    reduction (ι := ι) (k := k) ell (@algebraMap (ThreeParameters.Ring k) (Ring (ι := ι) (k := ThreeParameters.Ring k) ell) inferInstance inferInstance inferInstance a) =
      algebraMap k _ (ThreeParameters.augmentation k a) :=
  mapCoefficients_algebraMap ell _ a

@[simp] theorem reduction_baseChange (x : Ring (ι := ι) (k := k) ell) :
    reduction ell (baseChange (l := ThreeParameters.Ring k) ell x) = x := by
  have h : (reduction (ι := ι) (k := k) ell).comp
      (baseChange (l := ThreeParameters.Ring k) ell) = AlgHom.id k _ := by
    apply algHom_ext
    intro i
    simp only [AlgHom.comp_apply, baseChange_coordinate, reduction_coordinate, AlgHom.id_apply]
  exact AlgHom.congr_fun h x

theorem specialFiber_of_coordinates
    (f : Ring (ι := ι) (k := ThreeParameters.Ring k) ell →ₐ[ThreeParameters.Ring k]
      Ring (ι := ι) (k := ThreeParameters.Ring k) ell)
    (g : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell)
    (h : ∀ i, reduction ell (f (coordinate ell i)) = g (coordinate ell i))
    (x : Ring (ι := ι) (k := ThreeParameters.Ring k) ell) :
    reduction ell (f x) = g (reduction ell x) := by
  have hm (v : Box (ι := ι) ell) :
      reduction ell (f (monomial ell v)) = g (reduction ell (monomial ell v)) := by
    rw [monomial_eq_prod]
    simp only [Finsupp.prod, map_prod, map_pow, h, reduction_coordinate]
  have hs (a : ThreeParameters.Ring k) (z : Ring (ι := ι) (k := ThreeParameters.Ring k) ell) :
      reduction ell (a • z) = ThreeParameters.augmentation k a • reduction ell z :=
    mapCoefficients_smul ell _ a z
  rw [monomial_expansion ell x]
  simp only [map_sum, map_smul, hs, hm]

end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
