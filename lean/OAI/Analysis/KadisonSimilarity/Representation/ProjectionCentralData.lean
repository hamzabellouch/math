import OAI.Analysis.KadisonSimilarity.Representation.ProjectionFieldClosure
import OAI.Analysis.KadisonSimilarity.Representation.ConullRepresentationExtension
import OAI.Analysis.KadisonSimilarity.Representation.CompressedFieldNorm
import OAI.Analysis.KadisonSimilarity.Representation.SupportedFiberAlgebra
import OAI.Analysis.KadisonSimilarity.Representation.CentralDecompositionTests

namespace OAI

/-! # Central-decomposition data from actual projection fields

The construction uses the original measure space. On the null complement
of the genuine unitized representations, the original algebra acts by
zero and its unit range is the zero Hilbert space. Algebraic laws, norm
formulas, von Neumann membership and countable contraction tests are all
derived from the actual L² action identities.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

universe u

variable {Ω F H : Type u} [MeasurableSpace Ω]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine old-unit range at every base point, including zero fibers
on the null complement of the original representations. -/
abbrev conullProjectionFiber {A : Type u} [CStarAlgebra A]
    (s : Set Ω) (ρ : ∀ _x : s, Unitization ℂ A →⋆ₐ[ℂ] (F →L[ℂ] F)) (x : Ω) : Type u :=
  projectionFiber (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
    (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))

omit [MeasurableSpace Ω] in
private theorem conull_projection_membership {A : Type u} [CStarAlgebra A]
    (s : Set Ω) (ρ : ∀ _x : s, Unitization ℂ A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (x : s) (Q : F →L[ℂ] F)
    (hQ : projectionFiberCompression (unitizationProjection (ρ x))
      (unitizationProjection_isStarProjection (ρ x)) Q ∈
        representationVonNeumannAlgebra (unitizationRangeRepresentation (ρ x))) :
    projectionFiberCompression
      (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))
      Q ∈ representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  classical
  have hmap : zeroExtendNonunitalRepresentation s ρ x =
      (ρ x).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A) := by
    unfold zeroExtendNonunitalRepresentation
    exact dite_eq_left x.property
  let membership : (A →⋆ₙₐ[ℂ] (F →L[ℂ] F)) → Prop := fun τ =>
    projectionFiberCompression (nonunitalUnitProjection τ)
      (nonunitalUnitProjection_isStarProjection τ) Q ∈
        representationVonNeumannAlgebra (nonunitalRangeRepresentation τ)
  change membership (zeroExtendNonunitalRepresentation s ρ x)
  rw [hmap]
  exact hQ

variable (μ : Measure Ω) [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace F]

omit [CompleteSpace F] in
private theorem fields_eq_of_same_action
    (T : Lp F 2 μ →L[ℂ] Lp F 2 μ) (R Q : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, T f x = R x (f x))
    (hQ : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, T f x = Q x (f x)) :
    ∀ᵐ x ∂μ, R x = Q x := by
  apply ae_operator_eq_of_forall_vectors
  intro v
  filter_upwards [pointwise_action_column μ T R hR v,
    pointwise_action_column μ T Q hQ v] with x hr hq
  exact hr.symm.trans hq

private theorem isometric_raw_field_sub
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (R : M → Ω → F →L[ℂ] F)
    (hR : ∀ T : M, ∀ f : Lp F 2 μ,
      ∀ᵐ x ∂μ, isometricExtension J (T : H →L[ℂ] H) f x = R T x (f x))
    (T U : M) : ∀ᵐ x ∂μ, R (T - U) x = R T x - R U x := by
  apply ae_operator_eq_of_forall_vectors
  intro v
  have ht := pointwise_action_column μ _ _ (hR T) v
  have hu := pointwise_action_column μ _ _ (hR U) v
  have htu := pointwise_action_column μ _ _ (hR (T - U)) v
  change ∀ᵐ x ∂μ, isometricExtension J
    ((T : H →L[ℂ] H) - (U : H →L[ℂ] H)) (Lp.const 2 μ v) x = R (T - U) x v at htu
  rw [isometricExtension_sub] at htu
  filter_upwards [ht, hu, htu,
    Lp.coeFn_sub (isometricExtension J T (Lp.const 2 μ v))
      (isometricExtension J U (Lp.const 2 μ v))] with x ht hu htu hs
  simpa only [sub_apply, hs, Pi.sub_apply, ht, hu] using htu.symm

private theorem isometric_raw_field_mul
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (R : M → Ω → F →L[ℂ] F)
    (hR : ∀ T : M, ∀ f : Lp F 2 μ,
      ∀ᵐ x ∂μ, isometricExtension J (T : H →L[ℂ] H) f x = R T x (f x))
    (T U : M) : ∀ᵐ x ∂μ, R (T * U) x = R T x * R U x := by
  apply pointwise_field_mul μ _ _ _ _ _ (hR T) (hR U)
  have h := hR (T * U)
  change ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
    isometricExtension J ((T : H →L[ℂ] H) * (U : H →L[ℂ] H)) f x = R (T * U) x (f x) at h
  simpa only [isometricExtension_mul] using h

variable [TopologicalSpace.SeparableSpace H]

/-- A represented bicommutant member has its actual global field in the
bicommutant of the old-unit range representation almost everywhere.
This transports the conull membership statement without choosing arbitrary
representations on the null complement. -/
theorem ae_global_projection_mem_of_isometric_closure
    {A : Type u} [CStarAlgebra A]
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : ∀ _x : s, Unitization ℂ A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ a : A, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ a) f x = ρ x (Unitization.inr a) (f x))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x)) :
    ∀ᵐ x ∂μ, projectionFiberCompression
      (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))
      (R x) ∈ representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  have hR' : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J T f x = R x (f x) :=
    fun f => (ae_restrict_iff_subtype hs).mp (ae_restrict_of_ae (hR f))
  have hm := ae_projection_field_mem_of_isometric_closure μ s hs hnull J σ ρ hρ T hT
    (fun x => R x) hR'
  have hm' := hm.mono fun x hx => conull_projection_membership s ρ x (R x) hx
  have hr := (ae_restrict_iff_subtype (μ := μ)
    (p := fun x => projectionFiberCompression
      (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))
      (R x) ∈ representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x))) hs).mpr hm'
  have hs' : ∀ᵐ x ∂μ, x ∈ s := mem_ae_iff.mpr hnull
  filter_upwards [hs', ae_imp_of_ae_restrict hr] with x hx h
  exact h hx

/-- Construct all the direct-integral data needed for the separable
commutator estimate, before the separate factor-fiber theorem. The only
geometric inputs are genuine conull representations and actual L² action
identities for the isometric extension. -/
def projectionCentralData
    (P : VonNeumannAlgebra H)
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace B]
    (hB : B ≤ P.toStarSubalgebra)
    (hgen : representationVonNeumannAlgebra B.subtype = P)
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (b : H →L[ℂ] H) f x = ρ x (Unitization.inr b) (f x))
    (R : (vonNeumannCenter P).commutant.toStarSubalgebra → Ω → F →L[ℂ] F)
    (hR : ∀ T : (vonNeumannCenter P).commutant.toStarSubalgebra,
      ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
        isometricExtension J (T : H →L[ℂ] H) f x = R T x (f x)) :
    CentralDecompositionData μ (conullProjectionFiber s ρ) P := by
  classical
  let τ := zeroExtendNonunitalRepresentation s ρ
  let p : Ω → F →L[ℂ] F := fun x => nonunitalUnitProjection (τ x)
  let hp : ∀ x, IsStarProjection (p x) := fun x => nonunitalUnitProjection_isStarProjection (τ x)
  let σf : ∀ x, B →⋆ₐ[ℂ] (conullProjectionFiber s ρ x →L[ℂ] conullProjectionFiber s ρ x) :=
    fun x => nonunitalRangeRepresentation (τ x)
  let algebra : ∀ x, VonNeumannAlgebra (conullProjectionFiber s ρ x) :=
    fun x => representationVonNeumannAlgebra (σf x)
  let fiber : (vonNeumannCenter P).commutant.toStarSubalgebra →
      ∀ x, conullProjectionFiber s ρ x →L[ℂ] conullProjectionFiber s ρ x :=
    fun T x => projectionFiberCompression (p x) (hp x) (R T x)
  have hτ (b : B) : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J (b : H →L[ℂ] H) f x = τ x b (f x) := by
    intro f
    simpa only [τ, zeroExtendNonunitalRepresentation_apply] using
      zeroExtendOperatorField_action μ s hs hnull _ _ (hρ b) f
  have hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J 1 f x = p x (f x) := by
    simpa only [OneMemClass.coe_one, p, nonunitalUnitProjection] using hτ (1 : B)
  have hsub : ∀ T U, ∀ᵐ x ∂μ, fiber (T - U) x = fiber T x - fiber U x := by
    intro T U
    filter_upwards [isometric_raw_field_sub μ J _ R hR T U] with x hx
    dsimp only [fiber]
    rw [hx, projectionFiberCompression_sub]
  have hmul : ∀ T U, ∀ᵐ x ∂μ, fiber (T * U) x = fiber T x * fiber U x := by
    intro T U
    filter_upwards [isometric_raw_field_mul μ J _ R hR T U,
      ae_isometric_field_left_support μ J p hP U (R U) (hR U)] with x hx hu
    dsimp only [fiber]
    rw [hx, projectionFiberCompression_mul (p x) (hp x) (R T x) (R U x) hu]
  have hmem : ∀ T : P.toStarSubalgebra, ∀ᵐ x ∂μ,
      fiber (centerCommutantInclusion P T) x ∈ algebra x := by
    intro T
    have hTin : (T : H →L[ℂ] H) ∈ representationVonNeumannAlgebra B.subtype := by
      rw [hgen]
      exact T.property
    exact ae_global_projection_mem_of_isometric_closure μ s hs hnull J B.subtype ρ hρ
      T hTin (R (centerCommutantInclusion P T)) (hR (centerCommutantInclusion P T))
  have hnorm : ∀ (T : (vonNeumannCenter P).commutant.toStarSubalgebra) c, 0 ≤ c →
      (‖(T : H →L[ℂ] H)‖ ≤ c ↔ ∀ᵐ x ∂μ, ‖fiber T x‖ ≤ c) := by
    intro T c hc
    exact norm_le_iff_compressed_field μ J p hp hP T (R T) (hR T) c hc
  have hmatrix : ∀ n (X : Matrix (Fin n) (Fin n)
      (vonNeumannCenter P).commutant.toStarSubalgebra) c, 0 ≤ c →
      (‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖ ≤ c ↔
        ∀ᵐ x ∂μ, ‖matrixOperator (fun i j => fiber (X i j) x)‖ ≤ c) := by
    intro n X c hc
    exact matrix_norm_le_iff_compressed_field μ J p hp hP
      (fun i j => (X i j : H →L[ℂ] H)) (fun i j => R (X i j))
      (fun i j => hR (X i j)) c hc
  have hagrees : ∀ b : B, ∀ᵐ x ∂μ,
      fiber (centerCommutantInclusion P ⟨b.val, hB b.property⟩) x = σf x b := by
    intro b
    have heq := fields_eq_of_same_action μ (isometricExtension J (b : H →L[ℂ] H))
      (R (centerCommutantInclusion P ⟨b.val, hB b.property⟩)) (fun x => τ x b)
      (hR (centerCommutantInclusion P ⟨b.val, hB b.property⟩)) (hτ b)
    filter_upwards [heq] with x hx
    dsimp only [fiber, σf]
    rw [hx]
    exact (projectionFiberAction_eq_compression _ _ _
      (nonunitalUnitProjection_commutes (τ x) b)).symm
  have htests := exists_central_decomposition_tests μ
    (conullProjectionFiber s ρ) P B hB algebra fiber σf hagrees
    (Filter.Eventually.of_forall fun _ => rfl)
  let test := Classical.choose htests
  have htest := (Classical.choose_spec htests).1
  have hdense := (Classical.choose_spec htests).2
  exact {
    algebra := algebra
    fiber := fiber
    map_sub := hsub
    map_mul := hmul
    mem := hmem
    norm_le_iff := hnorm
    matrix_norm_le_iff := hmatrix
    test := test
    test_norm := htest
    test_dense := hdense }

end KadisonSimilarity

end

end OAI
