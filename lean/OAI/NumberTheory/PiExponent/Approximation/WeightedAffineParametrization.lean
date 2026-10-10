import OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective

universe u
variable {R ι σ : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem imageEvaluation_gradedImageMap (a : σ → ι →₀ ℕ) (p : MvPolynomial σ R) :
    imageEvaluation (R := R) a (gradedImageMap (R := R) a p) = affineMonomialMap (R := R) a p := by
  have h : (imageEvaluation (R := R) a).comp (gradedImageMap (R := R) a).toRingHom =
      affineMonomialMap (R := R) a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, affineMonomialMap, eval₂Hom_C]
      change (eval₂Hom (RingHom.id (MvPolynomial ι R)) (fun _ : Unit => 1))
        (homogeneousMonomialMap a (C r)) = C r
      simp [homogeneousMonomialMap]
    · intro s
      simp only [RingHom.comp_apply, affineMonomialMap, eval₂Hom_X']
      change imageEvaluation (R := R) a (imageCoordinate (R := R) a s) = monomial (a s) 1
      exact imageEvaluation_coordinate a s
  exact RingHom.congr_fun h p

theorem chartEvaluation_map_coordinate (a : σ → ι →₀ ℕ) (z s : σ) (hz : a z = 0) :
    chartEvaluation (R := R) a z hz
      (Away.map (gradedImageMap (R := R) a) (X z) (chartCoordinate z s)) = monomial (a s) 1 := by
  rw [chartCoordinate, Away.map_mk]
  erw [chartEvaluation_mk]
  rw [imageEvaluation_gradedImageMap]
  simp [affineMonomialMap]

theorem chartEvaluation_comp_awayMap (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    (chartEvaluation (R := R) a z hz).comp (Away.map (gradedImageMap (R := R) a) (X z)) =
      evalAway (affineMonomialMap (R := R) a) (X z)
        (by simp [affineMonomialMap, hz]) := by
  apply RingHom.ext
  intro q
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective (PolyGrade R σ) (poly_X_mem z) q
  change chartEvaluation (R := R) a z hz
    (Away.map (gradedImageMap (R := R) a) (X z) (Away.mk _ (poly_X_mem z) n p hp)) = _
  rw [Away.map_mk (gradedImageMap (R := R) a) (X z) (poly_X_mem z) n p hp]
  erw [chartEvaluation_mk]
  rw [imageEvaluation_gradedImageMap]
  have h := evalAway_mk_clear (affineMonomialMap (R := R) a) (poly_X_mem z)
    (show IsUnit (affineMonomialMap (R := R) a (X z)) from by
      simp [affineMonomialMap, hz]) n p hp
  simpa [affineMonomialMap, hz] using h.symm


theorem affineChartMap_comp_projectiveMonomialMap
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := R) a z hz coordinate hcoordinate ≫ projectiveMonomialMap a =
      fromUnitCoordinate (affineMonomialMap (R := R) a) (by decide) (poly_X_mem z)
        (by simp [affineMonomialMap, hz]) := by
  have hchart : affineChartMap (R := R) a z hz coordinate hcoordinate =
      Spec.map (CommRingCat.ofHom (chartEvaluation (R := R) a z hz)) ≫
        Proj.awayι (imageGrade (R := R) a) (imageCoordinate (R := R) a z) (imageCoordinate_mem a z) (by decide) := by
    rfl
  rw [hchart, Category.assoc]
  have hmap := Proj.awayι_comp_map (gradedImageMap (R := R) a)
    (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))
    (by decide : 0 < (1 : ℕ)) (X z) (poly_X_mem z)
  change Spec.map (CommRingCat.ofHom (chartEvaluation (R := R) a z hz)) ≫
    (Proj.awayι (imageGrade (R := R) a) ((gradedImageMap (R := R) a) (X z))
      ((gradedImageMap (R := R) a).map_mem (poly_X_mem z)) (by decide) ≫
        Proj.map (gradedImageMap (R := R) a) _) = _
  erw [hmap]
  erw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    chartEvaluation_comp_awayMap]
  rfl

theorem projective_range_eq_closure_monomial [IsDomain R]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Set.range (projectiveMonomialMap (R := R) a) =
      closure (Set.range (fromUnitCoordinate (affineMonomialMap (R := R) a) (by decide) (poly_X_mem z)
        (by simp [affineMonomialMap, hz]))) := by
  rw [projective_range_eq_closure_affine a z hz coordinate hcoordinate,
    affineChartMap_comp_projectiveMonomialMap]

end PiExponent.WeightedCompactification

end

end OAI
