import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Regular.Flat
import OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength

namespace OAI

noncomputable section

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace PiExponentSiegel.W17.ConeLocalLength

open RingTheory.Sequence

section Units

variable {R τ M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem ofList_map_mul_units (xs : List τ) (a u : τ → R) (hu : ∀ x, IsUnit (u x)) :
    Ideal.ofList (xs.map (fun x => a x * u x)) = Ideal.ofList (xs.map a) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (List.mem_map.mpr ⟨x, hx, rfl⟩))
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    apply (Ideal.mul_unit_mem_iff_mem _ (hu x)).mp
    exact Ideal.subset_span (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem isRegular_map_mul_units (xs : List τ) (a u : τ → R) (hu : ∀ x, IsUnit (u x))
    (hreg : IsRegular M (xs.map a)) :
    IsRegular M (xs.map (fun x => a x * u x)) := by
  refine ⟨⟨?_⟩, ?_⟩
  · intro i hi
    have hi' : i < xs.length := by simpa only [List.length_map] using hi
    have ha := hreg.regular_mod_prev i (by simpa only [List.length_map] using hi')
    simp only [List.getElem_map] at ha ⊢
    have hI : Ideal.ofList ((xs.map (fun x => a x * u x)).take i) =
        Ideal.ofList ((xs.map a).take i) := by
      simp only [← List.map_take]
      exact ofList_map_mul_units (xs.take i) a u hu
    have hN : (Ideal.ofList ((xs.map (fun x => a x * u x)).take i) •
        (⊤ : Submodule R M)) = Ideal.ofList ((xs.map a).take i) • ⊤ :=
      congrArg (fun J : Ideal R => J • (⊤ : Submodule R M)) hI
    exact Eq.mp (congrArg (fun N : Submodule R M =>
      IsSMulRegular (M ⧸ N) (a xs[i] * u xs[i])) hN.symm)
      (ha.mul ((hu xs[i]).isSMulRegular _))
  · rw [ofList_map_mul_units xs a u hu]
    exact hreg.top_ne_smul

end Units

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

def coneLocalCoordinate : Localization.AtPrime (conePrime k σ P) :=
  algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)) (MvPolynomial.X none)

theorem coneLocalCoordinate_isUnit : IsUnit (coneLocalCoordinate k σ P) :=
  IsLocalization.map_units (Localization.AtPrime (conePrime k σ P))
    (⟨MvPolynomial.X none, homogenizing_coordinate_not_mem_conePrime k σ P⟩ :
      (conePrime k σ P).primeCompl)

theorem homogenized_local_eq_affine_mul_coordinate (f : AffineRing k σ) :
    algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
      (PiExponentJets.W22.homogenize f) =
    affineLocalToConeLocal k σ P (algebraMap (AffineRing k σ) (Localization.AtPrime P) f) *
      coneLocalCoordinate k σ P ^ f.totalDegree := by
  let e := conePrimeLocalizationEquiv k σ P
  have ha : e (affineLocalToConeLocal k σ P
      (algebraMap (AffineRing k σ) (Localization.AtPrime P) f)) =
      algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (LaurentPolynomial.C f) := by
    change e (e.symm (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P))
        (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))) = _
    rw [e.apply_symm_apply]
    exact (IsScalarTower.algebraMap_apply (AffineRing k σ) (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) f).symm.trans
        (IsScalarTower.algebraMap_apply (AffineRing k σ) (LaurentChart k σ)
          (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) f)
  apply e.injective
  rw [e.map_mul, e.map_pow, ha]
  change conePrimeLocalizationEquiv k σ P
    (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
      (PiExponentJets.W22.homogenize f)) =
    algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (LaurentPolynomial.C f) *
    conePrimeLocalizationEquiv k σ P
      (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
        (MvPolynomial.X none)) ^ f.totalDegree
  rw [conePrimeLocalizationEquiv_algebraMap, conePrimeLocalizationEquiv_algebraMap,
    coneToLaurent_homogenize, coneToLaurent_X_none, map_mul, map_pow]

theorem affineLocalToConeLocal_faithfullyFlat :
    letI := affineLocalConeAlgebra k σ P
    Module.FaithfullyFlat (Localization.AtPrime P)
      (Localization.AtPrime (conePrime k σ P)) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_flat k σ P
  let : IsLocalHom (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (conePrime k σ P))) :=
    ((IsLocalRing.local_hom_TFAE _).out 1 3).mpr
      (affineLocalToConeLocal_map_maximalIdeal k σ P).le
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem homogenized_list_regular_at_cone (fs : List (AffineRing k σ))
    (hreg : IsRegular (Localization.AtPrime P)
      (fs.map (algebraMap (AffineRing k σ) (Localization.AtPrime P)))) :
    IsRegular (Localization.AtPrime (conePrime k σ P))
      ((fs.map PiExponentJets.W22.homogenize).map
        (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)))) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_faithfullyFlat k σ P
  have hbase : IsRegular (Localization.AtPrime (conePrime k σ P))
      (fs.map (fun f => affineLocalToConeLocal k σ P
        (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))) := by
    have hb := hreg.of_faithfullyFlat (S := Localization.AtPrime (conePrime k σ P))
    change IsRegular (Localization.AtPrime (conePrime k σ P))
      ((fs.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))).map
        (affineLocalToConeLocal k σ P)) at hb
    simpa only [List.map_map, Function.comp_def] using hb
  have hscaled := isRegular_map_mul_units fs
    (fun f => affineLocalToConeLocal k σ P
      (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))
    (fun f => coneLocalCoordinate k σ P ^ f.totalDegree)
    (fun f => (coneLocalCoordinate_isUnit k σ P).pow f.totalDegree) hbase
  simpa only [List.map_map, Function.comp_def,
    homogenized_local_eq_affine_mul_coordinate] using hscaled

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
