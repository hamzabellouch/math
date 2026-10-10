import OAI.Analysis.KadisonKastler.CanonicalMatrixCorner
import OAI.Analysis.KadisonKastler.AmplifiedAlgebra
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # Spatial transport and the canonical infinite amplification

Transport into the initial coordinate preserves the unit balls and their
Hausdorff distance. The abstract diagonal action obtained from the matrix
units is exactly the coordinatewise action on the Hilbert direct sum.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem centralizer_image_spatial (e : H ≃ₗᵢ[ℂ] K) (S : Set (H →L[ℂ] H)) :
    Set.centralizer (e.conjStarAlgEquiv '' S) =
      e.conjStarAlgEquiv '' Set.centralizer S := by
  ext x
  constructor
  · intro hx
    refine ⟨e.conjStarAlgEquiv.symm x, ?_, e.conjStarAlgEquiv.apply_symm_apply x⟩
    intro y hy
    apply e.conjStarAlgEquiv.injective
    rw [map_mul, map_mul]
    change e.conjStarAlgEquiv y * e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm x) =
      e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm x) * e.conjStarAlgEquiv y
    rw [e.conjStarAlgEquiv.apply_symm_apply]
    exact hx (e.conjStarAlgEquiv y) ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg e.conjStarAlgEquiv (hy w hw)

/-- The concrete algebra transported by a Hilbert-space isometry. -/
def spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra K where
  toStarSubalgebra := M.toStarSubalgebra.map e.conjStarAlgEquiv.toStarAlgHom
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)))) =
      e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))
    rw [centralizer_image_spatial, centralizer_image_spatial, M.centralizer_centralizer]

theorem mem_spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (T : K →L[ℂ] K) :
    T ∈ spatialTransportAlgebra e M ↔ e.conjStarAlgEquiv.symm T ∈ M := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    change e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv S) ∈ M
    rw [StarAlgEquiv.symm_apply_apply]
    exact hS
  · intro hT
    exact ⟨e.conjStarAlgEquiv.symm T, hT, e.conjStarAlgEquiv.apply_symm_apply T⟩

theorem norm_spatialConjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map e.conjStarAlgEquiv e.conjStarAlgEquiv.injective T

theorem unitBall_spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    unitBall (spatialTransportAlgebra e M) = e.conjStarAlgEquiv '' unitBall M := by
  ext T
  constructor
  · rintro ⟨⟨S, hS, rfl⟩, hn⟩
    change ‖e.conjStarAlgEquiv S‖ ≤ 1 at hn
    exact ⟨S, ⟨hS, by simpa only [norm_spatialConjugate] using hn⟩, rfl⟩
  · rintro ⟨S, ⟨hS, hn⟩, rfl⟩
    exact ⟨⟨S, hS, rfl⟩, by simpa only [norm_spatialConjugate] using hn⟩

/-- Hilbert-space transport does not change the ordinary operator gap. -/
theorem kkDistance_spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K)
    (M N : VonNeumannAlgebra H) :
    kkDistance (spatialTransportAlgebra e M) (spatialTransportAlgebra e N) =
      kkDistance M N := by
  unfold kkDistance
  rw [unitBall_spatialTransportAlgebra, unitBall_spatialTransportAlgebra]
  exact Metric.hausdorffDist_image
    (NonUnitalStarAlgHom.isometry e.conjStarAlgEquiv e.conjStarAlgEquiv.injective)

def spatialTransportHom (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] Algebra (spatialTransportAlgebra e M) :=
  (e.conjStarAlgEquiv.toStarAlgHom.comp M.toStarSubalgebra.subtype).codRestrict
    (spatialTransportAlgebra e M).toStarSubalgebra (fun x => ⟨x.val, x.property, rfl⟩)

theorem spatialTransportHom_bijective (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    Function.Bijective (spatialTransportHom e M) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply e.conjStarAlgEquiv.injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx, hxy⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

def spatialTransportEquiv (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (spatialTransportAlgebra e M) :=
  StarAlgEquiv.ofBijective (spatialTransportHom e M) (spatialTransportHom_bijective e M)

@[simp] theorem spatialTransportEquiv_apply (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) (x : Algebra M) :
    (spatialTransportEquiv e M x : K →L[ℂ] K) = e.conjStarAlgEquiv x := rfl

theorem spatialTransportAlgebra_isII1 (e : H ≃ₗᵢ[ℂ] K) {M : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    Generator.IsII1Factor (spatialTransportAlgebra e M).toStarSubalgebra :=
  Generator.isII1Factor_of_starAlgEquiv (spatialTransportEquiv e M) hM
    (Generator.Tracial.vonNeumann_wotClosed (spatialTransportAlgebra e M))

variable (H)

/-- The original algebra in the first coordinate of its countable sum. -/
def canonicalCornerAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (canonicalInitialSpace H) :=
  spatialTransportAlgebra (canonicalInitialEquiv H) M

/-- The countable amplification formed from the actual coordinate matrix units. -/
def canonicalAmplifiedAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (CountableHilbertSum H) :=
  (canonicalMatrixCorner H).amplifiedAlgebra (canonicalCornerAlgebra H M)

theorem canonicalMatrixCorner_inflate (T : H →L[ℂ] H) :
    (canonicalMatrixCorner H).inflateHom ((canonicalInitialEquiv H).conjStarAlgEquiv T) =
      l2Diagonal T := by
  apply (canonicalMatrixCorner H).ext_on_columns
  intro i x
  obtain ⟨y, rfl⟩ := (canonicalInitialEquiv H).surjective x
  rw [(canonicalMatrixCorner H).inflateHom_column]
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, canonicalMatrixCorner_column, l2Diagonal_single]

theorem l2DiagonalHom_injective : Function.Injective (l2DiagonalHom (E := H)) := by
  intro T S h
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun R : CountableHilbertSum H →L[ℂ] CountableHilbertSum H =>
    R (lp.single 2 0 x) 0) h
  change l2Diagonal T (lp.single 2 0 x) 0 = l2Diagonal S (lp.single 2 0 x) 0 at he
  simpa only [l2Diagonal_apply, lp.single_apply, Pi.single_eq_same] using he

theorem norm_l2Diagonal (T : H →L[ℂ] H) : ‖l2Diagonal T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map (l2DiagonalHom (E := H)) (l2DiagonalHom_injective H) T

/-- Every original operator acts coordinatewise in the canonical amplification. -/
theorem l2Diagonal_mem_canonicalAmplifiedAlgebra {M : VonNeumannAlgebra H}
    {T : H →L[ℂ] H} (hT : T ∈ M) : l2Diagonal T ∈ canonicalAmplifiedAlgebra H M := by
  rw [← canonicalMatrixCorner_inflate]
  apply (canonicalMatrixCorner H).inflate_mem_amplifiedAlgebra
  exact ⟨T, hT, rfl⟩

theorem canonicalMatrixUnit_mem_canonicalAmplifiedAlgebra
    (M : VonNeumannAlgebra H) (i j : ℕ) :
    canonicalMatrixUnit H i j ∈ canonicalAmplifiedAlgebra H M :=
  (canonicalMatrixCorner H).entry_mem_amplifiedAlgebra (canonicalCornerAlgebra H M) i j

theorem kkDistance_canonicalCornerAlgebra (M N : VonNeumannAlgebra H) :
    kkDistance (canonicalCornerAlgebra H M) (canonicalCornerAlgebra H N) = kkDistance M N :=
  kkDistance_spatialTransportAlgebra (canonicalInitialEquiv H) M N

end

end KadisonKastler

end OAI
