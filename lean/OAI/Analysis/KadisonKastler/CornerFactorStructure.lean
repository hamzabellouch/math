import OAI.Analysis.KadisonKastler.CanonicalAmplificationCorner
import OAI.Analysis.KadisonKastler.PublishedTypeIIIProjection

namespace OAI

/-! # Factor and finite-isometry structure of represented corners

Countable full matrix units identify the original algebra with the actual
amplification of its first corner. A central corner operator therefore
inflates to a central ambient operator. Finiteness of the first projection
also passes directly to the represented corner by extension by zero.
No trace or semifinite decomposition is assumed in these arguments.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- Common full matrix units recover an algebra from its actual first corner. -/
theorem amplified_representedCorner_eq (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) :
    F.amplifiedAlgebra (representedCorner E M (F.zero_zero ▸ hF 0 0)) = M := by
  apply VonNeumannAlgebra.ext
  intro T
  rw [F.mem_amplifiedAlgebra_iff]
  constructor
  · intro h
    exact F.mem_of_matrixEntries M hF T h
  · intro h i j
    rw [mem_representedCorner, F.extension_matrixEntry]
    exact M.mul_mem (M.mul_mem (hF 0 i) h) (hF j 0)

theorem inflateHom_injective : Function.Injective F.inflateHom := by
  intro T S h
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun A : H →L[ℂ] H => A (F.column 0 x)) h
  rw [F.inflateHom_column, F.inflateHom_column] at he
  exact (F.column 0).injective he

/-- Scalar center descends through the concrete matrix-corner decomposition. -/
theorem scalarCenter_representedCorner (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) (hM : ScalarCenter M) :
    ScalarCenter (representedCorner E M (F.zero_zero ▸ hF 0 0)) := by
  intro T hT hcomm
  let P := representedCorner E M (F.zero_zero ▸ hF 0 0)
  have hPT : T ∈ P := hT
  have hI : F.inflateHom T ∈ M := by
    rw [← F.amplified_representedCorner_eq M hF]
    exact F.inflate_mem_amplifiedAlgebra P hPT
  have hc : ∀ S ∈ M, S * F.inflateHom T = F.inflateHom T * S := by
    intro S hS
    apply F.ext_matrixEntry
    intro i j
    rw [F.matrixEntry_mul_inflate, F.matrixEntry_inflate_mul]
    apply hcomm
    rw [mem_representedCorner, F.extension_matrixEntry]
    exact M.mul_mem (M.mul_mem (hF 0 i) hS) (hF j 0)
  obtain ⟨z, hz⟩ := hM (F.inflateHom T) hI hc
  refine ⟨z, F.inflateHom_injective ?_⟩
  simpa only [map_smul, map_one] using hz

end FullMatrixCorner

omit [CompleteSpace H] in
/-- Extension by zero is faithful, even when the original representation is
not the standard tracial representation. -/
theorem cornerExtension_injective : Function.Injective (cornerExtension E) := by
  intro T S h
  have he := congrArg (cornerCompression E) h
  simpa only [cornerCompression_extension] using he

/-- A finite ambient projection makes the represented corner a finite algebra. -/
theorem finite_representedCorner_of_finite_projection (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M)
    (hfinite : FiniteProjectionIn M ⟨E.starProjection, hE⟩) :
    ∀ v : Algebra (representedCorner E M hE),
      star v * v = 1 → v * star v = 1 := by
  intro v hv
  let w : Algebra M := ⟨cornerExtension E (v : E →L[ℂ] E), v.property⟩
  have hv' : star (v : E →L[ℂ] E) * (v : E →L[ℂ] E) = 1 :=
    congrArg Subtype.val hv
  have hi : star w * w = (⟨E.starProjection, hE⟩ : Algebra M) := by
    apply Subtype.ext
    change star (cornerExtension E (v : E →L[ℂ] E)) *
      cornerExtension E (v : E →L[ℂ] E) = E.starProjection
    rw [← cornerExtension_star, ← cornerExtension_mul, hv', cornerExtension_one]
  have hs : (⟨E.starProjection, hE⟩ : Algebra M) * w = w := by
    apply Subtype.ext
    exact starProjection_mul_cornerExtension E (v : E →L[ℂ] E)
  have ho := congrArg Subtype.val (hfinite w hi hs)
  apply Subtype.ext
  apply cornerExtension_injective
  change cornerExtension E ((v : E →L[ℂ] E) * star (v : E →L[ℂ] E)) =
    cornerExtension E (1 : E →L[ℂ] E)
  rw [cornerExtension_mul, cornerExtension_star, cornerExtension_one]
  exact ho

omit [CompleteSpace H] in
/-- A nonzero corner projection gives a nonzero represented identity. -/
theorem representedCorner_nonzero_of_projection_ne_zero
    (hE : E.starProjection ≠ (0 : H →L[ℂ] H)) : (0 : E →L[ℂ] E) ≠ 1 := by
  intro h
  have he := congrArg (cornerExtension E) h
  exact hE (by simpa only [map_zero, cornerExtension_one] using he.symm)

/-- Proper projection splittings remain proper after compression to a larger
projection. Thus diffuseness passes to every represented corner. -/
theorem diffuse_representedCorner (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M)
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    ∀ p : Algebra (representedCorner E M hE), IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra (representedCorner E M hE), IsStarProjection q ∧ q ≠ 0 ∧
        q ≠ p ∧ p * q = q ∧ q * p = q := by
  intro p hp hp0
  let a : Algebra M := ⟨cornerExtension E (p : E →L[ℂ] E), p.property⟩
  have ha : IsStarProjection a := by
    constructor
    · apply Subtype.ext
      change cornerExtension E (p : E →L[ℂ] E) *
        cornerExtension E (p : E →L[ℂ] E) = cornerExtension E (p : E →L[ℂ] E)
      rw [← cornerExtension_mul]
      exact congrArg (cornerExtension E) (congrArg Subtype.val hp.isIdempotentElem.eq)
    · apply Subtype.ext
      change star (cornerExtension E (p : E →L[ℂ] E)) =
        cornerExtension E (p : E →L[ℂ] E)
      rw [← cornerExtension_star]
      exact congrArg (cornerExtension E) (congrArg Subtype.val hp.isSelfAdjoint.star_eq)
  have ha0 : a ≠ 0 := by
    intro hz
    apply hp0
    apply Subtype.ext
    apply cornerExtension_injective
    have hh := congrArg Subtype.val hz
    change cornerExtension E (p : E →L[ℂ] E) = 0 at hh
    simpa only [ZeroMemClass.coe_zero, map_zero] using hh
  obtain ⟨q, hq, hq0, hqa, haq, hqa'⟩ := hdiff a ha ha0
  have hl : E.starProjection * (q : H →L[ℂ] H) = q := by
    have he : cornerExtension E (p : E →L[ℂ] E) * (q : H →L[ℂ] H) = q :=
      congrArg Subtype.val haq
    calc
      _ = E.starProjection * (cornerExtension E (p : E →L[ℂ] E) * q.val) := by rw [he]
      _ = (E.starProjection * cornerExtension E (p : E →L[ℂ] E)) * q.val :=
        (mul_assoc _ _ _).symm
      _ = q := by rw [starProjection_mul_cornerExtension, he]
  have hr : (q : H →L[ℂ] H) * E.starProjection = q := by
    have he : (q : H →L[ℂ] H) * cornerExtension E (p : E →L[ℂ] E) = q :=
      congrArg Subtype.val hqa'
    calc
      _ = (q.val * cornerExtension E (p : E →L[ℂ] E)) * E.starProjection := by rw [he]
      _ = q.val * (cornerExtension E (p : E →L[ℂ] E) * E.starProjection) :=
        mul_assoc _ _ _
      _ = q := by rw [cornerExtension_mul_starProjection, he]
  let b : Algebra (representedCorner E M hE) :=
    ⟨cornerCompression E (q : H →L[ℂ] H), cornerCompression_mem E hE q.property⟩
  have hb : cornerExtension E (b : E →L[ℂ] E) = (q : H →L[ℂ] H) := by
    change cornerExtension E (cornerCompression E q.val) = q.val
    rw [cornerExtension_compression, hl, hr]
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · apply Subtype.ext
      apply cornerExtension_injective
      change cornerExtension E ((b : E →L[ℂ] E) * b.val) = cornerExtension E b.val
      rw [cornerExtension_mul, hb]
      exact congrArg Subtype.val hq.isIdempotentElem.eq
    · apply Subtype.ext
      apply cornerExtension_injective
      change cornerExtension E (star (b : E →L[ℂ] E)) = cornerExtension E b.val
      rw [cornerExtension_star, hb]
      exact congrArg Subtype.val hq.isSelfAdjoint.star_eq
  · intro hz
    apply hq0
    apply Subtype.ext
    rw [← hb]
    have he := congrArg (fun t : Algebra (representedCorner E M hE) =>
      cornerExtension E (t : E →L[ℂ] E)) hz
    simpa only [ZeroMemClass.coe_zero, map_zero] using he
  · intro hbp
    apply hqa
    apply Subtype.ext
    rw [← hb]
    exact congrArg (fun t : Algebra (representedCorner E M hE) =>
      cornerExtension E (t : E →L[ℂ] E)) hbp
  · apply Subtype.ext
    apply cornerExtension_injective
    change cornerExtension E ((p : E →L[ℂ] E) * b.val) = cornerExtension E b.val
    rw [cornerExtension_mul, hb]
    exact congrArg Subtype.val haq
  · apply Subtype.ext
    apply cornerExtension_injective
    change cornerExtension E ((b : E →L[ℂ] E) * p.val) = cornerExtension E b.val
    rw [cornerExtension_mul, hb]
    exact congrArg Subtype.val hqa'

/-- The finite nonzero first corner of a diffuse scalar-center algebra is an
actual II₁ factor. All projection and finiteness hypotheses are geometric. -/
theorem FullMatrixCorner.representedCorner_isII1 (F : FullMatrixCorner E)
    (M : VonNeumannAlgebra H) (hF : ∀ i j, F.entry i j ∈ M)
    (hM : ScalarCenter M) (hE0 : E.starProjection ≠ (0 : H →L[ℂ] H))
    (hfinite : FiniteProjectionIn M ⟨E.starProjection, F.zero_zero ▸ hF 0 0⟩)
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    Generator.IsII1Factor
      (representedCorner E M (F.zero_zero ▸ hF 0 0)).toStarSubalgebra := by
  refine {
    nonzero := representedCorner_nonzero_of_projection_ne_zero hE0
    weaklyClosed := representedCornerAlgebra_wotClosed E M (F.zero_zero ▸ hF 0 0)
    factor := ?_
    finite := finite_representedCorner_of_finite_projection M (F.zero_zero ▸ hF 0 0) hfinite
    diffuse := diffuse_representedCorner M (F.zero_zero ▸ hF 0 0) hdiff }
  intro x hx
  obtain ⟨z, hz⟩ := F.scalarCenter_representedCorner M hF hM x.val x.property
    (fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩))
  refine ⟨z, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  exact hz

end

end KadisonKastler

end OAI
