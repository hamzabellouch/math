import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_cross_ratio_full (i j : σ)
    (b : Finset (ChartVariables j))
    (hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i)) (l : σ) :
    overlapToFull j b (coordinateFiniteRingEquiv M s k hc f hf j b
      (coordinateRatioOn (s i) (s l) hi)) =
      AddMonoidAlgebra.single (standardExponent l 1 - standardExponent i 1) 1 := by
  let r := coordinateFiniteRingEquiv M s k hc f hf j b
  let hj : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) := inf_le_left
  have hinv : r (coordinateRatioOn (s j) (s i) hj) *
      r (coordinateRatioOn (s i) (s j) hi) = 1 := by
    rw [← map_mul, coordinateRatioOn_reciprocal, map_one]
  calc
    _ = overlapToFull j b
        (r (coordinateRatioOn (s j) (s l) hj) * r (coordinateRatioOn (s i) (s j) hi)) := by
      rw [coordinateRatioOn_change (s j) (s i) (s l) hj hi, map_mul, mul_comm]
    _ = _ := overlapToFull_ratio i j l b _ _ _
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b l)
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) hinv

lemma coordinateNegativeFrameFactor_full (n : ℕ) (i j : σ)
    (b : Finset (ChartVariables j))
    (hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i)) :
    overlapToFull j b
      ((coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s j) hi)) ^ n) =
      AddMonoidAlgebra.single
        (standardExponent i (-(n : ℤ)) - standardExponent j (-(n : ℤ))) 1 := by
  classical
  rw [map_pow, coordinateFiniteRingEquiv_cross_ratio_full,
    AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  funext a
  simp only [Pi.smul_apply, Pi.sub_apply, standardExponent]
  split_ifs <;> simp

lemma coordinateNegativeLaurent_change (n : ℕ) (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : Localization.Away (chartProduct (R := K) i a)) :
    overlapLaurent j (-(n : ℤ)) b
      ((coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s j) (h.trans inf_le_left))) ^ n *
        coordinateFiniteTransition M s k hc f hf i j a b h z) =
      overlapLaurent i (-(n : ℤ)) a z :=
  overlapLaurent_change_pivot i j (-(n : ℤ)) a b
    (coordinateFiniteTransition M s k hc f hf i j a b h)
    (coordinateFiniteTransition_full M s k hc f hf i j a b h) _
    (coordinateNegativeFrameFactor_full M s k hc f hf n i j b (h.trans inf_le_left)) z

end
end PiExponentSeshadri.Projective

end OAI
