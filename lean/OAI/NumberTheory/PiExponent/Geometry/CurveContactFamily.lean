import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
import OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact

namespace OAI

noncomputable section
namespace PiExponent.CurveContactFamily

open CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] {m K : ℕ}

def fullCenter (c : Fin m → ℂ) : Fin (m+1) → ℂ := Fin.cases 1 c

def fibre (x : Fin m → E) : Fin (m+1) → E := Fin.cases 1 x

@[simp] theorem fullCenter_zero (c : Fin m → ℂ) : fullCenter c 0 = 1 := rfl
@[simp] theorem fullCenter_succ (c : Fin m → ℂ) (i : Fin m) : fullCenter c i.succ = c i := rfl
@[simp] theorem fibre_zero (x : Fin m → E) : fibre x 0 = 1 := rfl
@[simp] theorem fibre_succ (x : Fin m → E) (i : Fin m) : fibre x i.succ = x i := rfl

variable [Algebra ℂ E]

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (fun j => fullCenter (c j)) hz hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (p : NormalizedPlace ℂ E) :
    p ∈ places hfinite z c hz ↔ ∃ j : Fin K, Centered z (fullCenter (c j)) p := by
  exact mem_centerPlaces z (fun j => fullCenter (c j)) hz hfinite p

def center
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) : Fin K :=
  Classical.choose ((mem_places hfinite z c hz p).mp hp)

theorem centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    Centered z (fullCenter (c (center hfinite z c hz p hp))) p :=
  Classical.choose_spec ((mem_places hfinite z c hz p).mp hp)

theorem nonconstant (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ i, z i ≠ algebraMap ℂ E ((fullCenter c) i) :=
  Centered.exists_nonzero_difference z (fullCenter c) hz

def contact
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ)
    (p : NormalizedPlace ℂ E) : ℚ := by
  classical
  letI := hres p
  exact if hp : p ∈ places hfinite z c hz then
    PlaceCenteredBranch.logContact p z (c (center hfinite z c hz p hp))
      (centered hfinite z c hz p hp) (nonconstant z _ hz) v
  else 0

theorem contact_pos
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    0 < contact hres hfinite z c hz v p := by
  let := hres p
  simpa only [contact, dite_eq_left hp] using
    PlaceCenteredBranch.logContact_pos p z (c (center hfinite z c hz p hp))
      (centered hfinite z c hz p hp) (nonconstant z _ hz) v hv

theorem contact_nonneg
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) : 0 ≤ contact hres hfinite z c hz v p := by
  by_cases hp : p ∈ places hfinite z c hz
  · exact (contact_pos hres hfinite z c hz v hv p hp).le
  · simp only [contact, dite_eq_right hp, le_refl]

theorem logWord_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : PiExponentApprox.FramePolynomial m)
    (hF : ∀ j, FormalLogJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word F) ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    contact hres hfinite z c hz v p * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word F)) : ℚ) := by
  let := hres p
  have h := PlaceCenteredBranch.logWord_field_order_lower p z
    (c (center hfinite z c hz p hp)) (centered hfinite z c hz p hp)
    (nonconstant z _ hz) v hv H F (hF _) word hne
  simpa only [contact, dite_eq_left hp] using h

theorem contact_one
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre x) i))
    (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∈ places hfinite (fibre x) c hz) :
    letI := hres p
    contact hres hfinite (fibre x) c hz v p =
      PlaceCenteredBranch.ordinaryContact p x
        (c (center hfinite (fibre x) c hz p hp))
        (fun i => centered hfinite (fibre x) c hz p hp i.succ)
        (PlaceCenteredBranch.fibre_nonconstant x _ (nonconstant _ _ hz))
        (fun i => v i.succ) := by
  let := hres p
  dsimp only [contact]
  rw [dite_eq_left hp]
  exact PlaceCenteredBranch.logContact_one p x _
      (centered hfinite (fibre x) c hz p hp) (nonconstant _ _ hz) v

theorem ordinaryWord_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre x) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : MvPolynomial (Fin m) ℂ)
    (hF : ∀ j, OrdinaryAuxiliaryJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal (fun i => v i.succ)
        (fun i => (hv i.succ).le) H)
    (word : List (Fin m))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word m word F) ≠ 0)
    (p : NormalizedPlace ℂ E)
    (hp : p ∈ places hfinite (fibre x) c hz) :
    contact hres hfinite (fibre x) c hz v p *
        (H - (word.map (fun i => v i.succ)).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval x (OrdinaryDerivatives.word m word F)) : ℚ) := by
  let := hres p
  rw [contact_one hres hfinite x c hz v p hp]
  exact PlaceCenteredBranch.ordinaryWord_field_order_lower p x _
    (fun i => centered hfinite (fibre x) c hz p hp i.succ)
    (PlaceCenteredBranch.fibre_nonconstant x _ (nonconstant _ _ hz))
    (fun i => v i.succ) (fun i => hv i.succ) H F (hF _) word hne

end PiExponent.CurveContactFamily
end

end OAI
