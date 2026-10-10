import OAI.NumberTheory.PiExponent.Geometry.CurveCenters
import OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing
import OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet
import OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

def lift (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : ring p :=
  ⟨z i, hc.coordinate_nonneg i⟩

@[simp] theorem lift_coe (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : (lift p z c hc i : E) = z i := rfl

theorem lift_nonconstant (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i)) :
    ∃ i, lift p z c hc i ≠ algebraMap ℂ (ring p) (c i) := by
  obtain ⟨i,hi⟩ := hnc
  refine ⟨i,?_⟩
  intro he
  exact hi (congrArg (fun a : ring p => (a : E)) he)

theorem lift_eq_algebraMap_iff (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) (a : ℂ) :
    lift p z c hc i = algebraMap ℂ (ring p) a ↔ z i = algebraMap ℂ E a := by
  constructor
  · exact congrArg (fun b : ring p => (b : E))
  · intro h
    exact Subtype.ext h

theorem lift_aeval (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (f : MvPolynomial ι ℂ) :
    algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f) =
      MvPolynomial.aeval z f := by
  exact MvPolynomial.comp_aeval_apply (f := lift p z c hc)
    (IsScalarTower.toAlgHom ℂ (ring p) E) f

theorem coordinateOrder_aeval_eq_length
    (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ) (hc : Centered z c p)
    (f : MvPolynomial ι ℂ) (hne : MvPolynomial.aeval z f ≠ 0) :
    coordinateOrder p.valuation (MvPolynomial.aeval z f) =
      ((Module.length (ring p) ((ring p) ⧸
        Ideal.span {MvPolynomial.aeval (lift p z c hc) f})).toNat : ℤ) := by
  have hn : MvPolynomial.aeval (lift p z c hc) f ≠ 0 := by
    intro h
    apply hne
    rw [← lift_aeval p z c hc f, h, map_zero]
  rw [coordinateOrder, dite_eq_right hne, valuation_eq_fractionAddValuation p]
  have hu : Units.mk0 (MvPolynomial.aeval z f) hne =
      Units.mk0 (algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f))
        ((map_ne_zero_iff _ (IsFractionRing.injective (ring p) E)).mpr hn) := by
    apply Units.ext
    exact (lift_aeval p z c hc f).symm
  rw [hu]
  exact CurveLocalOrder.integerOrder_field_image_eq_length hn

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem lift_residue (z : ι → E) (c : ι → ℂ) (hc : Centered z c p) (i : ι) :
    CurveLocalOrder.residueAugmentation ℂ (ring p) (lift p z c hc i) = c i := by
  have hm : lift p z c hc i - algebraMap ℂ (ring p) (c i) ∈
      IsLocalRing.maximalIdeal (ring p) := by
    apply p.valuation.toValuation.mem_maximalIdeal_iff.mpr
    exact hc i
  have hz : CurveLocalOrder.residueAugmentation ℂ (ring p)
      (lift p z c hc i - algebraMap ℂ (ring p) (c i)) = 0 := by
    change (CurveLocalOrder.residueCoefficientEquiv ℂ (ring p)).symm
      (IsLocalRing.residue (ring p) _) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hm, map_zero]
  rw [map_sub, CurveLocalOrder.residueAugmentation_algebraMap, sub_eq_zero] at hz
  exact hz

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem logLift_nonconstant {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
    lift p z (Fin.cases 1 c) hc 0 ≠ 1 ∨
      ∃ i, lift p z (Fin.cases 1 c) hc i.succ ≠ algebraMap ℂ (ring p) (c i) := by
  obtain ⟨i,hi⟩ := lift_nonconstant p z (Fin.cases 1 c) hc hnc
  cases i using Fin.cases with
  | zero => exact Or.inl (by simpa using hi)
  | succ i => exact Or.inr ⟨i,hi⟩

def logContact {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) : ℚ :=
  DVRBranchJet.contact v c (lift p z (Fin.cases 1 c) hc 0)
    (fun i => lift p z (Fin.cases 1 c) hc i.succ) (logLift_nonconstant p z c hc hnc)

theorem logContact_pos {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) : 0 < logContact p z c hc hnc v := by
  exact DVRBranchJet.contact_pos v hv c _ _
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ) _

def ordinaryContact {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) : ℚ :=
  OrdinaryDVRBranchJet.contact v c (lift p z c hc) (lift_nonconstant p z c hc hnc)

theorem ordinaryContact_pos {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) : 0 < ordinaryContact p z c hc hnc v :=
  OrdinaryDVRBranchJet.contact_pos v hv c _ (lift_residue p z c hc) _

theorem logWord_field_order_lower {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : PiExponentApprox.FramePolynomial m)
    (hf : FormalLogJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f) ≠ 0) :
    logContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation
        (MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f)) : ℚ) := by
  let x := lift p z (Fin.cases 1 c) hc
  have he : (fun i => Fin.cases (x 0) (fun j => x j.succ) i) = x := by
    funext i
    cases i using Fin.cases <;> rfl
  have hn : MvPolynomial.aeval x (PiExponentApprox.polynomialFrameWord m word f) ≠ 0 := by
    intro hz
    apply hne
    rw [← lift_aeval p z (Fin.cases 1 c) hc, hz, map_zero]
  have hb := DVRBranchJet.frameWord_colength_lower v hv H c (x 0) (fun i => x i.succ)
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ)
    (logLift_nonconstant p z c hc hnc) f hf word (he.symm ▸ hn)
  have heval := congrArg (fun u : Fin (m+1) → ring p =>
    MvPolynomial.aeval u (PiExponentApprox.polynomialFrameWord m word f)) he
  rw [heval] at hb
  rw [coordinateOrder_aeval_eq_length p z (Fin.cases 1 c) hc _ hne]
  simpa only [Int.cast_natCast, logContact, x] using hb

theorem ordinaryWord_field_order_lower {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : MvPolynomial (Fin n) ℂ)
    (hf : OrdinaryAuxiliaryJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval z (OrdinaryDerivatives.word n word f) ≠ 0) :
    ordinaryContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval z (OrdinaryDerivatives.word n word f)) : ℚ) := by
  have hn : MvPolynomial.aeval (lift p z c hc) (OrdinaryDerivatives.word n word f) ≠ 0 := by
    intro hz
    apply hne
    rw [← lift_aeval p z c hc, hz, map_zero]
  rw [coordinateOrder_aeval_eq_length p z c hc _ hne]
  simpa only [Int.cast_natCast, ordinaryContact] using
    OrdinaryDVRBranchJet.ordinaryWord_colength_lower v hv H c (lift p z c hc)
      (lift_residue p z c hc) (lift_nonconstant p z c hc hnc) f hf word hn

theorem fibre_nonconstant {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
    ∃ i, x i ≠ algebraMap ℂ E (c i) := by
  obtain ⟨i,hi⟩ := hnc
  cases i using Fin.cases with
  | zero => simp at hi
  | succ i => exact ⟨i,hi⟩

theorem logContact_one {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) p)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) :
    logContact p (Fin.cases (1 : E) x) c hc hnc v =
      ordinaryContact p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc)
        (fun i => v i.succ) := by
  have hy : lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc 0 = 1 :=
    Subtype.ext rfl
  have hx : (fun i => lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc i.succ) =
      lift p x c (fun i => hc i.succ) := rfl
  simpa only [logContact, ordinaryContact, hy, hx] using
    FibreContact.logarithmic_contact_eq_ordinary v c (lift p x c (fun i => hc i.succ))
      (lift_nonconstant p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc))

end PiExponent.PlaceCenteredBranch

end

end OAI
