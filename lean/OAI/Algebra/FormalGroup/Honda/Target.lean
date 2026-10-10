import Mathlib

namespace OAI

noncomputable section

namespace HeightThree.HondaTarget

universe u

abbrev Base (K : Type*) [CommRing K] := MvPowerSeries (Fin 2) K

def variablePoint {R : Type*} [CommRing R] (F : FormalGroup R) : F.Point Unit :=
  ⟨PowerSeries.X, PowerSeries.HasSubst.X'⟩

def multiplicationSeries {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries R := (n • variablePoint F).val

structure CoordinateIso {R : Type*} [CommRing R] (F G : FormalGroup R) where
  series : PowerSeries R
  inverse : PowerSeries R
  zero_series : series.constantCoeff = 0
  zero_inverse : inverse.constantCoeff = 0
  left_inv : series.subst inverse = PowerSeries.X
  right_inv : inverse.subst series = PowerSeries.X
  preserves_addition :
    series.subst F.toPowerSeries =
      G.toPowerSeries.subst
        ![series.subst (MvPowerSeries.X 0), series.subst (MvPowerSeries.X 1)]

def FramedEquivalent {K R : Type*} [CommRing K] [CommRing R]
    (ρ : R →+* K) (F G : FormalGroup R) : Prop :=
  ∃ e : CoordinateIso F G, PowerSeries.map ρ e.series = PowerSeries.X

def HeightCoordinates {K : Type*} [CommRing K] (p : ℕ)
    (G : FormalGroup (Base K)) : Prop :=
  (∀ j < p, (multiplicationSeries G p).coeff j = 0) ∧
  (multiplicationSeries G p).coeff p = MvPowerSeries.X 0 ∧
  (∀ j < p^2, (multiplicationSeries G p).coeff j ∈
    Ideal.span ({MvPowerSeries.X 0} : Set (Base K))) ∧
  (multiplicationSeries G p).coeff (p^2) - MvPowerSeries.X 1 ∈
    Ideal.span ({MvPowerSeries.X 0} : Set (Base K))

def IsUniversal {K : Type u} [Field K] (Γ : FormalGroup K)
    (G : FormalGroup (Base K)) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra K R] [IsLocalRing R]
    [FiniteDimensional K R] (ρ : R →ₐ[K] K) (F : FormalGroup R),
    F.IsComm → F.map ρ.toRingHom = Γ →
    ∃! f : Base K →ₐ[K] R,
      ρ.toRingHom.comp f.toRingHom = MvPowerSeries.constantCoeff ∧
      FramedEquivalent ρ.toRingHom (G.map f.toRingHom) F

def HasUniversalHeightCoordinates {K : Type u} [Field K] (p : ℕ)
    (Γ : FormalGroup K) : Prop :=
  ∃ G : FormalGroup (Base K),
    G.IsComm ∧ G.map MvPowerSeries.constantCoeff = Γ ∧
    IsUniversal Γ G ∧ HeightCoordinates p G

end HeightThree.HondaTarget

end

end OAI
