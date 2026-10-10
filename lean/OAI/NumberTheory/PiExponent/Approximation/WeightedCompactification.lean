import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates
import OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory

variable {R ι σ : Type*} [CommRing R]

abbrev constantChart (a : σ → ι →₀ ℕ) (z : σ) :=
  HomogeneousLocalization.Away (imageGrade (R := R) a) (imageCoordinate a z)

def chartEvaluation (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    constantChart (R := R) a z →+* MvPolynomial ι R :=
  evalAway (imageEvaluation a) (imageCoordinate a z)
    (by simp [hz])

@[simp]
theorem chartEvaluation_mk (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (n : ℕ) (p : monomialImage (R := R) a) (hp : p ∈ imageGrade a (n • 1)) :
    chartEvaluation a z hz (Away.mk _ (imageCoordinate_mem a z) n p hp) =
      imageEvaluation a p := by
  have h := evalAway_mk_clear (imageEvaluation a) (imageCoordinate_mem a z)
    (show IsUnit (imageEvaluation a (imageCoordinate a z)) by simp [hz]) n p hp
  simpa [chartEvaluation, hz] using h

theorem chartEvaluation_injective (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    Function.Injective (chartEvaluation (R := R) a z hz) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (imageCoordinate_mem a z) x
  rw [chartEvaluation_mk] at hx
  have hpzero := imageEvaluation_homogeneous_eq_zero a hp hx
  subst p
  apply HomogeneousLocalization.val_injective
  simp [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

def affineChartCoordinate (a : σ → ι →₀ ℕ) (z s : σ) : constantChart (R := R) a z :=
  Away.mk _ (imageCoordinate_mem a z) 1 (imageCoordinate a s)
    (by simpa using imageCoordinate_mem (R := R) a s)

@[simp]
theorem chartEvaluation_coordinate (a : σ → ι →₀ ℕ) (z s : σ) (hz : a z = 0) :
    chartEvaluation (R := R) a z hz (affineChartCoordinate a z s) =
      monomial (a s) 1 := by
  rw [affineChartCoordinate, chartEvaluation_mk, imageEvaluation_coordinate]

def imageConstant (a : σ → ι →₀ ℕ) (r : R) : monomialImage (R := R) a :=
  ⟨homogeneousMonomialMap a (C r), ⟨C r, rfl⟩⟩

theorem imageConstant_mem (a : σ → ι →₀ ℕ) (r : R) :
    imageConstant a r ∈ imageGrade a 0 :=
  homogeneousMonomialMap_homogeneous a (isHomogeneous_C σ r)

def affineChartConstant (a : σ → ι →₀ ℕ) (z : σ) (r : R) : constantChart (R := R) a z :=
  Away.mk _ (imageCoordinate_mem a z) 0 (imageConstant a r)
    (show imageConstant a r ∈ imageGrade a (0 • 1) from imageConstant_mem a r)

@[simp]
theorem chartEvaluation_constant (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) (r : R) :
    chartEvaluation a z hz (affineChartConstant a z r) = C r := by
  rw [affineChartConstant, chartEvaluation_mk]
  simp [imageEvaluation, imageConstant, homogeneousMonomialMap]

theorem chartEvaluation_surjective (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Function.Surjective (chartEvaluation (R := R) a z hz) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨affineChartConstant a z r, chartEvaluation_constant a z hz r⟩
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨x, rfl⟩ := hp
    refine ⟨x * affineChartCoordinate a z (coordinate i), ?_⟩
    rw [map_mul, chartEvaluation_coordinate, hcoordinate]
    rfl

def constantChartEquiv (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    constantChart (R := R) a z ≃+* MvPolynomial ι R :=
  RingEquiv.ofBijective (chartEvaluation a z hz)
    ⟨chartEvaluation_injective a z hz, chartEvaluation_surjective a z hz coordinate hcoordinate⟩

def constantProjectiveChartIso (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    (Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial ι R)) := by
  let e : CommRingCat.of (constantChart (R := R) a z) ≅
      CommRingCat.of (MvPolynomial ι R) :=
    (constantChartEquiv (R := R) a z hz coordinate hcoordinate).toCommRingCatIso
  exact Proj.basicOpenIsoSpec _ _ (imageCoordinate_mem a z) (by decide) ≪≫
    Scheme.Spec.mapIso e.symm.op

def constantChartSectionRingEquiv (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Γ(Proj (imageGrade (R := R) a), Proj.basicOpen (imageGrade a) (imageCoordinate a z)) ≃+*
      MvPolynomial ι R :=
  ((Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z)).topIso.symm ≪≫
    Scheme.Γ.mapIso (constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate).symm.op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).commRingCatIsoToRingEquiv

abbrev finiteMonomialClosure (S : Finset (ι →₀ ℕ)) :=
  Proj (imageGrade (R := R) (fun s : S => s.1))

def finiteMonomialChartEquiv (S : Finset (ι →₀ ℕ)) (hzero : 0 ∈ S)
    (hcoordinate : ∀ i, Finsupp.single i 1 ∈ S) :
    constantChart (R := R) (fun s : S => s.1) ⟨0, hzero⟩ ≃+* MvPolynomial ι R :=
  constantChartEquiv (R := R) (fun s : S => s.1) ⟨0, hzero⟩ rfl
    (fun i => ⟨Finsupp.single i 1, hcoordinate i⟩) (fun _ => rfl)

def finiteMonomialProjectiveChartIso (S : Finset (ι →₀ ℕ)) (hzero : 0 ∈ S)
    (hcoordinate : ∀ i, Finsupp.single i 1 ∈ S) :
    (Proj.basicOpen (imageGrade (R := R) (fun s : S => s.1))
      (imageCoordinate (fun s : S => s.1) ⟨0, hzero⟩)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial ι R)) :=
  constantProjectiveChartIso (R := R) (fun s : S => s.1) ⟨0, hzero⟩ rfl
    (fun i => ⟨Finsupp.single i 1, hcoordinate i⟩) (fun _ => rfl)

end PiExponent.WeightedCompactification

end

end OAI
