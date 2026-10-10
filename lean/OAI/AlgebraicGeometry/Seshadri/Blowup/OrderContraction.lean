import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.PlaneCharts

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial
variable (K : Type) [Field K]

def chartExponent (i : Fin 2) : (Fin 2 →₀ ℕ) →+ (Fin 2 →₀ ℕ) where
  toFun d := Finsupp.equivFunOnFinite.symm (fun j => if j = i then d 0 + d 1 else d j)
  map_zero' := by ext j; simp
  map_add' d e := by
    ext j
    change (if j = i then (d + e) 0 + (d + e) 1 else (d + e) j) =
      (if j = i then d 0 + d 1 else d j) + (if j = i then e 0 + e 1 else e j)
    simp only [Finsupp.add_apply]
    split_ifs <;> omega

@[simp] lemma chartExponent_apply (i j : Fin 2) (d : Fin 2 →₀ ℕ) :
    chartExponent i d j = if j = i then d 0 + d 1 else d j := rfl

lemma chartExponent_injective (i : Fin 2) : Function.Injective (chartExponent i) := by
  intro d e h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  fin_cases i <;> simp [chartExponent_apply] at h0 h1
  all_goals ext j; fin_cases j <;> simpa using (by omega : _ )

lemma chartExponent_self (i : Fin 2) (d : Fin 2 →₀ ℕ) :
    chartExponent i d i = Finsupp.degree d := by
  simp only [chartExponent_apply, ite_true]
  rw [Finsupp.degree_eq_sum]
  simp

lemma chartSubstitution_eq_mapDomain (i : Fin 2) :
    chartSubstitution K i = AddMonoidAlgebra.mapDomainRingHom K (chartExponent i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change chartSubstitution K i (C c) = _
    rw [substitution_C]
    change AddMonoidAlgebra.single 0 c =
      AddMonoidAlgebra.mapDomain (chartExponent i) (AddMonoidAlgebra.single 0 c)
    rw [AddMonoidAlgebra.mapDomain_single, map_zero]
  · intro j
    change chartSubstitution K i (X j) = _
    rw [chartSubstitution, MvPolynomial.eval₂Hom_X']
    change (if j = i then AddMonoidAlgebra.single (Finsupp.single i 1) 1 else
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 *
        AddMonoidAlgebra.single (Finsupp.single j 1) 1) =
      AddMonoidAlgebra.mapDomain (chartExponent i)
        (AddMonoidAlgebra.single (Finsupp.single j 1) 1)
    rw [AddMonoidAlgebra.mapDomain_single]
    split_ifs with h
    · subst j
      congr 1
      ext j
      fin_cases i <;> fin_cases j <;> simp [chartExponent_apply]
    · rw [AddMonoidAlgebra.single_mul_single, one_mul]
      congr 1
      ext q
      fin_cases i <;> fin_cases j <;> fin_cases q <;> simp_all [chartExponent_apply]

lemma chartSubstitution_injective (i : Fin 2) : Function.Injective (chartSubstitution K i) := by
  rw [chartSubstitution_eq_mapDomain]
  exact AddMonoidAlgebra.mapDomain_injective (chartExponent_injective i)

lemma variable_pow_dvd_iff {σ : Type} [DecidableEq σ]
    (i : σ) (m : ℕ) (p : MvPolynomial σ K) :
    X i ^ m ∣ p ↔ ∀ d : σ →₀ ℕ, d i < m → p.coeff d = 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h d hd
    have he : ¬ Finsupp.single i m ≤ d := by
      simpa only [Finsupp.single_le_iff] using (not_le.mpr hd)
    rw [← MvPolynomial.coeff_modMonomial_of_not_le p he, h, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply]
  · intro h
    ext d
    by_cases hd : Finsupp.single i m ≤ d
    · simp [MvPolynomial.coeff_modMonomial_of_le p hd]
    · rw [MvPolynomial.coeff_modMonomial_of_not_le p hd, AddMonoidAlgebra.coeff_zero]
      exact h d (by simpa only [Finsupp.single_le_iff, not_le] using hd)

lemma substitution_coeff (i : Fin 2) (p : PlaneRing K) (d : Fin 2 →₀ ℕ) :
    (chartSubstitution K i p).coeff (chartExponent i d) = p.coeff d := by
  rw [chartSubstitution_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective (chartExponent_injective i)
    (AddMonoidAlgebra.coeff p) d

lemma substitution_coeff_outside (i : Fin 2) (p : PlaneRing K) (d : Fin 2 →₀ ℕ)
    (hd : d ∉ Set.range (chartExponent i)) :
    (chartSubstitution K i p).coeff d = 0 := by
  rw [chartSubstitution_eq_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range (AddMonoidAlgebra.coeff p) d hd

lemma substitution_variable_pow_dvd_iff (i : Fin 2) (m : ℕ) (p : PlaneRing K) :
    X i ^ m ∣ chartSubstitution K i p ↔ p ∈ originIdeal K ^ m := by
  rw [variable_pow_dvd_iff, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h d hd
    rw [← substitution_coeff K i p d]
    exact h _ (by simpa only [chartExponent_self] using hd)
  · intro h d hd
    by_cases he : d ∈ Set.range (chartExponent i)
    · obtain ⟨e, rfl⟩ := he
      rw [substitution_coeff]
      exact h e (by simpa only [chartExponent_self] using hd)
    · exact substitution_coeff_outside K i p d he

lemma chart_exceptional_pow_dvd_iff (i : Fin 2) (m : ℕ) (p : PlaneRing K) :
    (ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) ^ m ∣
      ReesGrading.chartBase (originIdeal K) (coordinate K i) p ↔
        p ∈ originIdeal K ^ m := by
  have he := map_dvd_iff (chartEquiv K i)
    (a := (ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) ^ m)
    (b := ReesGrading.chartBase (originIdeal K) (coordinate K i) p)
  rw [← he]
  change toPolynomial K i ((ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) ^ m) ∣
    toPolynomial K i (ReesGrading.chartBase (originIdeal K) (coordinate K i) p) ↔ _
  rw [map_pow (toPolynomial K i)
    (ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) m,
    toPolynomial_base, substitution_self, toPolynomial_base]
  exact substitution_variable_pow_dvd_iff K i m p

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.FlatContraction
noncomputable section
open TensorProduct
variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.Flat R A]

theorem contraction (J : Ideal S) :
    (J.map (Algebra.TensorProduct.includeRight (R := R) (A := A))).comap
        (algebraMap A (A ⊗[R] S)) =
      (J.comap (algebraMap R S)).map (algebraMap R A) := by
  let I := J.comap (algebraMap R S)
  let q : R ⧸ I →ₐ[R] S ⧸ J := Ideal.quotientMapₐ J (Algebra.ofId R S) le_rfl
  have hq : Function.Injective q := Ideal.quotientMap_injective
  have ht := Module.Flat.lTensor_preserves_injective_linearMap
    (M := A) q.toLinearMap hq
  ext a
  change algebraMap A (A ⊗[R] S) a ∈ J.map _ ↔ a ∈ I.map (algebraMap R A)
  have hleft : algebraMap A (A ⊗[R] S) a ∈ J.map
      (Algebra.TensorProduct.includeRight (R := R) (A := A)) ↔
      a ⊗ₜ[R] (1 : S ⧸ J) = 0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← (Algebra.TensorProduct.tensorQuotientEquiv (R := R) A S A J).symm.map_eq_zero_iff]
    change (Algebra.TensorProduct.tensorQuotientEquiv (R := R) A S A J).symm
      (Ideal.Quotient.mk _ (a ⊗ₜ[R] (1 : S))) = 0 ↔ _
    simp
  have hright : a ∈ I.map (algebraMap R A) ↔ a ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).map_eq_zero_iff]
    rfl
  rw [hleft, hright]
  constructor
  · intro h
    apply ht
    simpa using h
  · intro h
    have he := congrArg (q.toLinearMap.lTensor A) h
    simpa using he

end
end MaximalSeshadri.FlatContraction

namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading TensorProduct
variable (K : Type) [Field K]

def exceptionalChartIdeal (i : Fin 2) : Ideal (chart (originIdeal K) (coordinate K i)) :=
  Ideal.span {chartBase (originIdeal K) (coordinate K i) (X i)}

lemma exceptionalChart_comap_pow (i : Fin 2) (m : ℕ) :
    ((exceptionalChartIdeal K i)^m).comap (chartBase (originIdeal K) (coordinate K i)) =
      (originIdeal K)^m := by
  ext p
  change chartBase (originIdeal K) (coordinate K i) p ∈
    (Ideal.span {chartBase (originIdeal K) (coordinate K i) (X i)})^m ↔ _
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact chart_exceptional_pow_dvd_iff K i m p

lemma flat_chart_order {A : Type} [CommRing A] [Algebra (PlaneRing K) A]
    [Module.Flat (PlaneRing K) A] (i : Fin 2) (m : ℕ) :
    letI : Algebra (PlaneRing K) (chart (originIdeal K) (coordinate K i)) :=
      (chartBase (originIdeal K) (coordinate K i)).toAlgebra
    (((exceptionalChartIdeal K i)^m).map
      (Algebra.TensorProduct.includeRight (R := PlaneRing K) (A := A))).comap
      (algebraMap A (A ⊗[PlaneRing K] chart (originIdeal K) (coordinate K i))) =
      ((originIdeal K).map (algebraMap (PlaneRing K) A))^m := by
  let : Algebra (PlaneRing K) (chart (originIdeal K) (coordinate K i)) :=
    (chartBase (originIdeal K) (coordinate K i)).toAlgebra
  rw [FlatContraction.contraction]
  change (((exceptionalChartIdeal K i)^m).comap
    (chartBase (originIdeal K) (coordinate K i))).map _ = _
  rw [exceptionalChart_comap_pow, Ideal.map_pow]

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme}

lemma comap_pow (I : X.IdealSheafData) (f : Y ⟶ X) (m : ℕ) :
    (I^m).comap f = (I.comap f)^m := by
  have hc : ∀ y : Y, ∃ (U : Y.affineOpens) (V : X.affineOpens),
      y ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    intro y
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyU, hUV⟩
  choose U V hy hUV using hc
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    rw [comap_ideal (I^m) f (U y) (V y) (hUV y)]
    change (I.ideal (V y)^m).map _ = ((I.comap f).ideal (U y))^m
    rw [Ideal.map_pow, comap_ideal I f (U y) (V y) (hUV y)]

lemma specIdeal_pow {R : Type} [CommRing R] (I : Ideal R) (m : ℕ) :
    specIdeal (I^m) = (specIdeal I)^m := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simpa only [specIdeal_top, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using
    Ideal.map_pow (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I m

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

lemma invertible_of_affine_equation [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X)
    (r : Γ(Y, ⊤)) (hr : IsRegular r)
    (hI : (I.comap f).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r}) :
    InvertiblePullbackIdeal I f := by
  apply invertible_of_local_equations
  intro y
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  refine ⟨U, trivial, U.1.topIso.inv r, ?_, ?_⟩
  · exact regular_map_flat U.1.topIso.inv.hom (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso U.1.topIso.inv)) hr
  · rw [IdealPullback.comap_ι_top, hI, Ideal.map_span, Set.image_singleton]

lemma invertible_Spec_of_span_regular {R S : Type} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) (r : S) (hr : IsRegular r)
    (hI : I.map f = Ideal.span {r}) :
    InvertiblePullbackIdeal (IdealPullback.specIdeal I)
      (Spec.map (CommRingCat.ofHom f)) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of S)
  apply invertible_of_affine_equation _ _ (e.inv r)
  · exact regular_map_flat e.inv.hom (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso e.inv)) hr
  · rw [IdealPullback.specIdeal_comap, IdealPullback.specIdeal_top, hI,
      Ideal.map_span, Set.image_singleton]

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry

lemma specIdeal_map {R S : Type} [CommRing R] [CommRing S]
    (J : Ideal S) (f : R →+* S) :
    (specIdeal J).map (Spec.map (CommRingCat.ofHom f)) = specIdeal (J.comap f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [map_top, specIdeal_top, specIdeal_top]
  apply Ideal.comap_injective_of_surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp,
    ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f), CommRingCat.hom_comp,
    ← Ideal.comap_comap, Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv),
    Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)]
  rfl

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.FlatContraction
noncomputable section
open TensorProduct
variable {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.Flat R A]

lemma includeRight_flat :
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).Flat := by
  have he : (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).toRingHom =
      (Algebra.TensorProduct.comm R S A).toRingHom.comp (algebraMap S (S ⊗[R] A)) := by
    ext x
    simp
  rw [he]
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R S A).bijective)

end
end MaximalSeshadri.FlatContraction


end

end OAI
