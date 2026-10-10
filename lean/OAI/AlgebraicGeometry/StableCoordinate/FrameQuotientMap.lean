import OAI.AlgebraicGeometry.StableCoordinate.FrameLiftUniqueness
import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import OAI.AlgebraicGeometry.StableCoordinate.BundleCharts

namespace OAI

/-!
# Actual determinant-quotient maps from frames

A determinant frame in a commutative `k`-algebra, together with an image of
`u`, gives an actual algebra homomorphism from the exact source ring
`k[a,d,b,c,u]/(ac-bd-1)`.  This is the quotient-map construction needed when a
normalized polynomial frame is turned into a lifted additive action.
-/

noncomputable section

namespace StableCoordinate.FrameLift

open MvPolynomial

variable {k S T : Type*} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

/-- Evaluation on the five independent determinant-presentation variables. -/
def Frame.polynomialMap (F : Frame S) (u : S) : Obstruction.P k 5 →ₐ[k] S :=
  MvPolynomial.aeval ![F.a, F.d, F.b, F.c, u]

/-- Every determinant frame satisfies the exact source relation. -/
theorem Frame.polynomialMap_relation (F : Frame S) (u : S) :
    F.polynomialMap (k := k) u (Obstruction.determinantRelation k) = 0 := by
  simpa [Frame.polynomialMap, Obstruction.determinantRelation] using
    sub_eq_zero.mpr F.determinant

/-- The determinant relation generates an ideal in the kernel of evaluation. -/
theorem Frame.ideal_le_ker_polynomialMap (F : Frame S) (u : S) :
    Obstruction.idealC k ≤ RingHom.ker (F.polynomialMap (k := k) u).toRingHom := by
  rw [Obstruction.idealC, Ideal.span_singleton_le_iff_mem]
  exact F.polynomialMap_relation u

/-- The actual map out of the source determinant quotient induced by a frame.
The image of the fifth coordinate `u` is arbitrary and independently specified. -/
def Frame.quotientMap (F : Frame S) (u : S) : Obstruction.C k →ₐ[k] S :=
  Ideal.Quotient.liftₐ (Obstruction.idealC k) (F.polynomialMap u)
    (fun _ hp => F.ideal_le_ker_polynomialMap u hp)

@[simp] theorem Frame.quotientMap_cX (F : Frame S) (u : S) (i : Fin 5) :
    F.quotientMap (k := k) u (Obstruction.cX k i) = ![F.a, F.d, F.b, F.c, u] i := by
  change F.polynomialMap u (X i) = _
  simp [Frame.polynomialMap]

@[simp] theorem Frame.quotientMap_a (F : Frame S) (u : S) :
    F.quotientMap (k := k) u (Obstruction.cX k 0) = F.a := by simp

@[simp] theorem Frame.quotientMap_d (F : Frame S) (u : S) :
    F.quotientMap (k := k) u (Obstruction.cX k 1) = F.d := by simp

@[simp] theorem Frame.quotientMap_b (F : Frame S) (u : S) :
    F.quotientMap (k := k) u (Obstruction.cX k 2) = F.b := by simp

@[simp] theorem Frame.quotientMap_c (F : Frame S) (u : S) :
    F.quotientMap (k := k) u (Obstruction.cX k 3) = F.c := by simp

@[simp] theorem Frame.quotientMap_u (F : Frame S) (u : S) :
    F.quotientMap (k := k) u (Obstruction.cX k 4) = u := by simp

/-- Maps from the concrete determinant quotient are determined by all five
coordinate images. -/
theorem determinant_algHom_ext {φ ψ : Obstruction.C k →ₐ[k] S}
    (h : ∀ i : Fin 5, φ (Obstruction.cX k i) = ψ (Obstruction.cX k i)) : φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

/-- The canonical determinant frame in the exact quotient. -/
def sourceFrame (k : Type*) [CommRing k] : Frame (Obstruction.C k) where
  a := Obstruction.cX k 0
  d := Obstruction.cX k 1
  b := Obstruction.cX k 2
  c := Obstruction.cX k 3
  determinant := sub_eq_zero.mp (Obstruction.c_relation k)

/-- Each algebra map gives its frame of coordinate images. -/
def frameOfHom (φ : Obstruction.C k →ₐ[k] S) : Frame S :=
  (sourceFrame k).map φ.toRingHom

@[simp] theorem frameOfHom_a (φ : Obstruction.C k →ₐ[k] S) :
    (frameOfHom φ).a = φ (Obstruction.cX k 0) := rfl
@[simp] theorem frameOfHom_d (φ : Obstruction.C k →ₐ[k] S) :
    (frameOfHom φ).d = φ (Obstruction.cX k 1) := rfl
@[simp] theorem frameOfHom_b (φ : Obstruction.C k →ₐ[k] S) :
    (frameOfHom φ).b = φ (Obstruction.cX k 2) := rfl
@[simp] theorem frameOfHom_c (φ : Obstruction.C k →ₐ[k] S) :
    (frameOfHom φ).c = φ (Obstruction.cX k 3) := rfl

@[simp] theorem quotientMap_sourceFrame :
    (sourceFrame k).quotientMap (Obstruction.cX k 4) = AlgHom.id k (Obstruction.C k) := by
  apply determinant_algHom_ext
  intro i
  fin_cases i <;> simp [sourceFrame]

/-- Naturality of the quotient-map construction under a target algebra map. -/
theorem Frame.quotientMap_natural (F : Frame S) (u : S) (φ : S →ₐ[k] T) :
    φ.comp (F.quotientMap u) = (F.map φ.toRingHom).quotientMap (φ u) := by
  apply determinant_algHom_ext
  intro i
  fin_cases i <;> simp [Frame.map]

@[simp] theorem quotientMap_frameOfHom (φ : Obstruction.C k →ₐ[k] S) :
    (frameOfHom φ).quotientMap (φ (Obstruction.cX k 4)) = φ := by
  apply determinant_algHom_ext
  intro i
  fin_cases i <;> simp

/-- Equality of the determinant frame and the fifth-coordinate image gives
actual equality of quotient algebra homomorphisms. -/
theorem determinant_algHom_ext_frame {φ ψ : Obstruction.C k →ₐ[k] S}
    (hF : frameOfHom φ = frameOfHom ψ)
    (hu : φ (Obstruction.cX k 4) = ψ (Obstruction.cX k 4)) : φ = ψ := by
  rw [← quotientMap_frameOfHom φ, ← quotientMap_frameOfHom ψ, hF, hu]

/-- Algebra maps from the quadric quotient are determined by its four generators. -/
theorem quadric_algHom_ext {φ ψ : Obstruction.B k →ₐ[k] S}
    (h : ∀ i : Fin 4, φ (Obstruction.bX k i) = ψ (Obstruction.bX k i)) : φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

/-- The existing bundle base map with the canonical source quotient aliases. -/
def sourceBaseMap (k : Type*) [CommRing k] : Obstruction.B k →ₐ[k] Obstruction.C k :=
  BundleCharts.baseMap k

/-- The already-constructed base map, expressed in the canonical source names. -/
@[simp] theorem baseMap_bX (i : Fin 4) :
    sourceBaseMap k (Obstruction.bX k i) =
      ![Obstruction.cX k 0 * Obstruction.cX k 2,
        Obstruction.cX k 1 * Obstruction.cX k 3,
        Obstruction.cX k 1 * Obstruction.cX k 2, Obstruction.cX k 4] i :=
  BundleCharts.baseMap_qgen k i

/-- A frame lying over the four images of a base map gives an actual extension
of that base map to the determinant quotient. -/
theorem Frame.quotientMap_comp_baseMap (F : Frame S) (u : S)
    (φ : Obstruction.B k →ₐ[k] S)
    (hx : F.a * F.b = φ (Obstruction.bX k 0))
    (hy : F.d * F.c = φ (Obstruction.bX k 1))
    (hz : F.d * F.b = φ (Obstruction.bX k 2))
    (hu : u = φ (Obstruction.bX k 3)) :
    (F.quotientMap u).comp (sourceBaseMap k) = φ := by
  apply quadric_algHom_ext
  intro i
  fin_cases i
  · simpa [AlgHom.comp_apply, baseMap_bX] using hx
  · simpa [AlgHom.comp_apply, baseMap_bX] using hy
  · simpa [AlgHom.comp_apply, baseMap_bX] using hz
  · simpa [AlgHom.comp_apply, baseMap_bX] using hu

/-- Restriction to the source base records exactly the three frame products
and the independent coordinate `u`. -/
theorem comp_baseMap_eq_iff {φ ψ : Obstruction.C k →ₐ[k] S} :
    φ.comp (sourceBaseMap k) = ψ.comp (sourceBaseMap k) ↔
      SameBase (frameOfHom φ) (frameOfHom ψ) ∧
      φ (Obstruction.cX k 4) = ψ (Obstruction.cX k 4) := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simpa [AlgHom.comp_apply, baseMap_bX] using AlgHom.congr_fun h (Obstruction.bX k 0)
    · simpa [AlgHom.comp_apply, baseMap_bX] using AlgHom.congr_fun h (Obstruction.bX k 1)
    · simpa [AlgHom.comp_apply, baseMap_bX] using AlgHom.congr_fun h (Obstruction.bX k 2)
    · simpa [AlgHom.comp_apply, baseMap_bX] using AlgHom.congr_fun h (Obstruction.bX k 3)
  · rintro ⟨⟨hx, hy, hz⟩, hu⟩
    apply quadric_algHom_ext
    intro i
    fin_cases i
    · simpa [AlgHom.comp_apply, baseMap_bX] using hx
    · simpa [AlgHom.comp_apply, baseMap_bX] using hy
    · simpa [AlgHom.comp_apply, baseMap_bX] using hz
    · simpa [AlgHom.comp_apply, baseMap_bX] using hu

/-- Normalized polynomial maps of the determinant quotient are unique over
the same base map.  This is an actual equality of algebra homomorphisms. -/
theorem normalized_quotientMap_unique {R σ : Type*} [CommRing R] [Algebra k R]
    [IsReduced R] {φ ψ : Obstruction.C k →ₐ[k] MvPolynomial σ R}
    (hbase : φ.comp (sourceBaseMap k) = ψ.comp (sourceBaseMap k))
    (hzero : (frameOfHom φ).map MvPolynomial.constantCoeff =
      (frameOfHom ψ).map MvPolynomial.constantCoeff) : φ = ψ := by
  obtain ⟨hF, hu⟩ := comp_baseMap_eq_iff.mp hbase
  exact determinant_algHom_ext_frame (normalized_polynomial_unique hF hzero) hu

end StableCoordinate.FrameLift

end

end OAI
