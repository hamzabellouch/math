import OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Projective
open PiExponentSeshadri.LineBundleGluing

variable {R σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev projectiveSpace (R σ : Type) [CommRing R] := Proj (PolyGrade R σ)
abbrev coordinateOpen (i : σ) : (projectiveSpace R σ).Opens :=
  Proj.basicOpen (PolyGrade R σ) (X i)

def coordinateRatio (i j : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) : Γ(projectiveSpace R σ, W) :=
  ⟨fun x => HomogeneousLocalization.mk
    ⟨1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩,
   fun x => ⟨W, x.2, 𝟙 _, 1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩,
     (fun y => hi y.2), (fun _ => rfl)⟩⟩

theorem coordinateRatio_restrict (i j : σ) {V W : (projectiveSpace R σ).Opens}
    (h : V ≤ W) (hi : W ≤ coordinateOpen i) :
    (projectiveSpace R σ).presheaf.map (homOfLE h).op (coordinateRatio i j W hi) =
      coordinateRatio i j V (h.trans hi) := by
  apply Subtype.ext
  funext x
  rfl

theorem coordinateRatio_self (i : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) : coordinateRatio i i W hi = 1 := by
  apply Subtype.ext
  funext x
  let : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mk ⟨1, ⟨X i, poly_X_mem i⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩).val = (1 : HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)

theorem coordinateRatio_mul (i j k : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) (hj : W ≤ coordinateOpen j) :
    coordinateRatio i j W hi * coordinateRatio j k W hj = coordinateRatio i k W hi := by
  apply Subtype.ext
  funext x
  let : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  apply HomogeneousLocalization.val_injective
  change ((HomogeneousLocalization.mk ⟨1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal) *
    (HomogeneousLocalization.mk ⟨1, ⟨X k, poly_X_mem k⟩, ⟨X j, poly_X_mem j⟩, hj x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal)).val =
    (HomogeneousLocalization.mk ⟨1, ⟨X k, poly_X_mem k⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (X j) (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) *
    Localization.mk (X k) (⟨X j, hj x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
    Localization.mk (X k) (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

def ratioUnit (i j : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) (hj : W ≤ coordinateOpen j) : Γ(projectiveSpace R σ, W)ˣ where
  val := coordinateRatio i j W hi
  inv := coordinateRatio j i W hj
  val_inv := (coordinateRatio_mul i j i W hi hj).trans (coordinateRatio_self i W hi)
  inv_val := (coordinateRatio_mul j i j W hj hi).trans (coordinateRatio_self j W hj)

def coordinateCocycle : Cocycle (coordinateOpen (R := R) (σ := σ)) where
  transition := ratioUnit
  restriction := fun i j {_ _} h hi _ => coordinateRatio_restrict i j h hi
  identity i W hi := Units.ext (coordinateRatio_self i W hi)
  cocycle i j k W hi hj _ := Units.ext (coordinateRatio_mul i j k W hi hj)

def lineBundle : PiExponentSeshadri.Geometry.LineBundle (projectiveSpace R σ) :=
  PiExponentSeshadri.LineBundleGluing.lineBundle coordinateCocycle
    (by rw [show (⨆ i : σ, coordinateOpen (R := R) i) = ⊤ from standardChart_cover])

end PiExponent.ProjectiveO1

end

end OAI
