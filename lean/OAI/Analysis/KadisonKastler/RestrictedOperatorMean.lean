import OAI.Analysis.KadisonKastler.OperatorMeanEquivariance
import OAI.Analysis.KadisonKastler.OperatorFieldValues

namespace OAI

/-! # Equivariant averaging within a von Neumann algebra

The constant-commutant description of the field algebra is invariant under
boundary pullback. Restricting the constructed mean therefore keeps both
the cocycle and its correction in the prescribed von Neumann algebra.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace NonsingularAction

variable (α : NonsingularAction G D μ) (M : VonNeumannAlgebra H)

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
/-- Boundary pullback preserves the algebra of fields with values in M. -/
theorem operatorAction_mem (g : G) (q : WeakOperatorField (H := H) μ)
    (hq : q ∈ operatorFieldAlgebra (μ := μ) M) :
    α.operatorAction (H := H) g q ∈ operatorFieldAlgebra (μ := μ) M := by
  apply (mem_operatorFieldAlgebra_iff M _).mpr
  intro T hT
  have he := congrArg (α.operatorAction (H := H) g)
    ((mem_operatorFieldAlgebra_iff M q).mp hq T hT)
  simpa only [map_mul, α.operatorAction_constant] using he

/-- The boundary automorphism restricted to the M-valued field algebra. -/
def restrictedOperatorEquiv (g : G) :
    operatorFieldAlgebra (μ := μ) M ≃⋆ₐ[ℂ] operatorFieldAlgebra (μ := μ) M where
  toFun q := ⟨α.operatorAction (H := H) g q.val, α.operatorAction_mem M g q.val q.property⟩
  invFun q := ⟨α.operatorAction (H := H) g⁻¹ q.val,
    α.operatorAction_mem M g⁻¹ q.val q.property⟩
  left_inv q := by
    apply Subtype.ext
    change (α.operatorAction (H := H) g⁻¹) ((α.operatorAction (H := H) g) q.val) = q.val
    rw [← StarAlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, StarAlgEquiv.one_apply]
  right_inv q := by
    apply Subtype.ext
    change (α.operatorAction (H := H) g) ((α.operatorAction (H := H) g⁻¹) q.val) = q.val
    rw [← StarAlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, StarAlgEquiv.one_apply]
  map_mul' q r := Subtype.ext ((α.operatorAction (H := H) g).map_mul q.val r.val)
  map_add' q r := Subtype.ext ((α.operatorAction (H := H) g).map_add q.val r.val)
  map_smul' c q := Subtype.ext (map_smul (α.operatorAction (H := H) g) c q.val)
  map_star' q := Subtype.ext (map_star (α.operatorAction (H := H) g) q.val)

/-- The restricted automorphisms form a group action. -/
def restrictedOperatorAction :
    G →* (operatorFieldAlgebra (μ := μ) M ≃⋆ₐ[ℂ] operatorFieldAlgebra (μ := μ) M) where
  toFun := α.restrictedOperatorEquiv M
  map_one' := by
    apply StarAlgEquiv.ext
    intro q
    apply Subtype.ext
    exact congrArg (fun e : WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ]
      WeakOperatorField (H := H) μ => e q.val) (α.operatorAction (H := H)).map_one
  map_mul' g h := by
    apply StarAlgEquiv.ext
    intro q
    apply Subtype.ext
    exact congrArg (fun e : WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ]
      WeakOperatorField (H := H) μ => e q.val) ((α.operatorAction (H := H)).map_mul g h)

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem restrictedOperatorAction_coe (g : G) (q : operatorFieldAlgebra (μ := μ) M) :
    (α.restrictedOperatorAction M g q : WeakOperatorField (H := H) μ) =
      α.operatorAction (H := H) g (q : WeakOperatorField (H := H) μ) := rfl

end NonsingularAction

variable (M : VonNeumannAlgebra H)

instance restrictedOperatorFamilyCStar :
    CStarAlgebra (G →ᵇ operatorFieldAlgebra (μ := μ) M) where

/-- The inclusion of bounded M-valued field families into all field families. -/
def operatorFieldFamilyInclusion : (G →ᵇ operatorFieldAlgebra (μ := μ) M) →⋆ₐ[ℂ]
    (G →ᵇ WeakOperatorField (H := H) μ) where
  toFun F := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => (F g : WeakOperatorField (H := H) μ)) ‖F‖ (fun g => F.norm_coe_le_norm g)
  map_one' := by ext g; rfl
  map_mul' F K := by ext g; rfl
  map_zero' := by ext g; rfl
  map_add' F K := by ext g; rfl
  commutes' c := by ext g; rfl
  map_star' F := by ext g; rfl

omit [Group G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem operatorFieldFamilyInclusion_apply (F : G →ᵇ operatorFieldAlgebra (μ := μ) M)
    (g : G) : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F g = (F g : WeakOperatorField (H := H) μ) := rfl

omit [Group G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem norm_operatorFieldFamilyInclusion_le (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    ‖operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr (fun g => F.norm_coe_le_norm g)

omit [Group G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem operatorFieldFamilyInclusion_constant (q : operatorFieldAlgebra (μ := μ) M) :
    operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryConstant (G := G) q) =
      boundaryConstant (G := G) (q : WeakOperatorField (H := H) μ) := by
  ext g
  rfl

namespace ScalarBoundaryMean

variable {M} {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
  (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))

/-- The restricted mean value, with its range proof separated from linearity. -/
def restrictedOperatorMeanValue (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) : operatorFieldAlgebra (μ := μ) M :=
  ⟨m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F),
    m.operatorMean_mem (H := H) hTom M
      (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) (fun g => (F g).property)⟩

@[simp]
theorem restrictedOperatorMeanValue_coe (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    (m.restrictedOperatorMeanValue hTom M F : WeakOperatorField (H := H) μ) =
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := rfl

private theorem restrictedOperatorMeanValue_add (M : VonNeumannAlgebra H)
    (F K : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMeanValue hTom M (F + K) =
      m.restrictedOperatorMeanValue hTom M F + m.restrictedOperatorMeanValue hTom M K := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (F + K)) =
    m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) +
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M K)
  calc
    _ = m.operatorMean (H := H)
        (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F +
          operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M K) :=
      congrArg (m.operatorMean (H := H))
        ((operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M).map_add F K)
    _ = _ := (m.operatorMean (H := H)).map_add _ _

private theorem restrictedOperatorMeanValue_smul (M : VonNeumannAlgebra H)
    (c : ℂ) (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMeanValue hTom M (c • F) =
      c • m.restrictedOperatorMeanValue hTom M F := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (c • F)) =
    c • m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F)
  calc
    _ = m.operatorMean (H := H) (c • operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) :=
      congrArg (m.operatorMean (H := H))
        (map_smul (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M) c F)
    _ = _ := map_smul (m.operatorMean (H := H)) c _

theorem norm_restrictedOperatorMeanValue_le (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    ‖m.restrictedOperatorMeanValue hTom M F‖ ≤ ‖F‖ :=
  (m.norm_operatorMeanValue_le (H := H) _).trans
    (norm_operatorFieldFamilyInclusion_le (G := G) M F)

/-- Restrict the scalar-coefficient operator mean to M-valued fields. -/
def restrictedOperatorMean (M : VonNeumannAlgebra H) :
    (G →ᵇ operatorFieldAlgebra (μ := μ) M) →L[ℂ] operatorFieldAlgebra (μ := μ) M :=
  LinearMap.mkContinuous
    { toFun := m.restrictedOperatorMeanValue hTom M
      map_add' := m.restrictedOperatorMeanValue_add hTom M
      map_smul' := m.restrictedOperatorMeanValue_smul hTom M }
    1 (fun F => by
      change ‖m.restrictedOperatorMeanValue hTom M F‖ ≤ 1 * ‖F‖
      exact (m.norm_restrictedOperatorMeanValue_le hTom M F).trans_eq (one_mul ‖F‖).symm)

@[simp]
theorem restrictedOperatorMean_coe (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    (m.restrictedOperatorMean hTom M F : WeakOperatorField (H := H) μ) =
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := rfl

theorem norm_restrictedOperatorMean_le (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    ‖m.restrictedOperatorMean hTom M F‖ ≤ ‖F‖ :=
  m.norm_restrictedOperatorMeanValue_le hTom M F

private theorem restrictedOperatorMean_one (M : VonNeumannAlgebra H) :
    m.restrictedOperatorMean hTom M 1 = 1 := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M 1) = 1
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M 1 = 1 := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    (m.operatorMean_fixed (H := H) 1)

private theorem restrictedOperatorMean_star (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (star F) = star (m.restrictedOperatorMean hTom M F) := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (star F)) =
    star (m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F))
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (star F) =
      star (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    (m.operatorMean_star (H := H) _)

private theorem restrictedOperatorMean_left (M : VonNeumannAlgebra H)
    (q : operatorFieldAlgebra (μ := μ) M) (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (boundaryConstant q * F) =
      q * m.restrictedOperatorMean hTom M F := by
  apply Subtype.ext
  change m.operatorMean (H := H)
      (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryConstant q * F)) =
    (q : WeakOperatorField (H := H) μ) *
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F)
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryConstant q * F) =
      boundaryConstant (G := G) (q : WeakOperatorField (H := H) μ) *
        operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    ((hTom (m.operatorMean (H := H)) (m.norm_operatorMeanValue_le (H := H))
      (m.operatorMean_fixed (H := H))).1 _ _)

private theorem restrictedOperatorMean_right (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) (q : operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (F * boundaryConstant q) =
      m.restrictedOperatorMean hTom M F * q := by
  apply Subtype.ext
  change m.operatorMean (H := H)
      (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (F * boundaryConstant q)) =
    m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) *
      (q : WeakOperatorField (H := H) μ)
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (F * boundaryConstant q) =
      operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F *
        boundaryConstant (G := G) (q : WeakOperatorField (H := H) μ) := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    ((hTom (m.operatorMean (H := H)) (m.norm_operatorMeanValue_le (H := H))
      (m.operatorMean_fixed (H := H))).2 _ _)

/-- The restricted mean retains the two module identities. -/
def restrictedOperatorBimoduleMean (M : VonNeumannAlgebra H) :
    BimoduleMean (boundaryConstant (G := G) (B := operatorFieldAlgebra (μ := μ) M)) where
  toCLM := m.restrictedOperatorMean hTom M
  map_one := m.restrictedOperatorMean_one hTom M
  map_star := m.restrictedOperatorMean_star hTom M
  norm_le := m.norm_restrictedOperatorMean_le hTom M
  map_left := m.restrictedOperatorMean_left hTom M
  map_right := m.restrictedOperatorMean_right hTom M

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem operatorFieldFamilyInclusion_translate (M : VonNeumannAlgebra H) (g : G)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryTranslate (α.restrictedOperatorAction M) g F) =
      boundaryTranslate (α.operatorAction (H := H)) g (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := by
  ext t
  rfl

theorem restrictedOperatorMean_equivariant (M : VonNeumannAlgebra H) (g : G)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (boundaryTranslate (α.restrictedOperatorAction M) g F) =
      α.restrictedOperatorAction M g (m.restrictedOperatorMean hTom M F) := by
  apply Subtype.ext
  change m.operatorMean (H := H)
      (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryTranslate (α.restrictedOperatorAction M) g F)) =
    α.operatorAction (H := H) g (m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F))
  exact (congrArg (m.operatorMean (H := H))
    (operatorFieldFamilyInclusion_translate (G := G) (D := D) (H := H) (μ := μ) M g F)).trans
      (m.operatorMean_equivariant (H := H) g (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F))

include m hTom in
/-- The exact cocycle correction remains in the prescribed field algebra. -/
theorem exists_restricted_operator_cocycle (M : VonNeumannAlgebra H)
    (V : unitary (G →ᵇ operatorFieldAlgebra (μ := μ) M))
    (hV : unitaryCocycleDefect (α.restrictedOperatorAction M) V ≤ 1 / 64) :
    ∃ W : unitary (G →ᵇ operatorFieldAlgebra (μ := μ) M),
      (∀ g h, W.val g * α.restrictedOperatorAction M g (W.val h) = W.val (g * h)) ∧
      dist V W ≤ 2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V :=
  exists_bounded_cocycle_of_equivariant_mean (α.restrictedOperatorAction M)
    (m.restrictedOperatorBimoduleMean hTom M) (m.restrictedOperatorMean_equivariant hTom M) V hV

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
