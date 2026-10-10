import OAI.Analysis.KadisonKastler.CocycleMetric

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedCStar : CStarAlgebra (G →ᵇ B) where
local instance boundaryBoundedComplete : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
local instance boundaryBoundedOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryBoundedStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- Fields independent of the averaged group coordinate. -/
def boundaryConstant : B →⋆ₐ[ℂ] (G →ᵇ B) where
  toFun := BoundedContinuousFunction.const G
  map_one' := by ext t; rfl
  map_mul' _ _ := by ext t; rfl
  map_zero' := by ext t; rfl
  map_add' _ _ := by ext t; rfl
  commutes' _ := by ext t; rfl
  map_star' _ := by ext t; rfl

omit [Group G] [DiscreteTopology G] in
@[simp]
theorem boundaryConstant_apply (b : B) (t : G) :
    boundaryConstant (G := G) b t = b := rfl

/-- Transport combines left translation of the group coordinate and the
original action on the value algebra. -/
def boundaryTranslate (α : G →* (B ≃⋆ₐ[ℂ] B)) (g : G) :
    (G →ᵇ B) ≃⋆ₐ[ℂ] (G →ᵇ B) where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => α g (f (g⁻¹ * t))) ‖f‖ (fun t => by
      rw [StarAlgEquiv.norm_map]
      exact f.norm_coe_le_norm _)
  invFun f := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => (α g).symm (f (g * t))) ‖f‖ (fun t => by
      rw [StarAlgEquiv.norm_map]
      exact f.norm_coe_le_norm _)
  left_inv f := by
    ext t
    change (α g).symm (α g (f (g⁻¹ * (g * t)))) = f t
    simp only [inv_mul_cancel_left, StarAlgEquiv.symm_apply_apply]
  right_inv f := by
    ext t
    change α g ((α g).symm (f (g * (g⁻¹ * t)))) = f t
    simp only [mul_inv_cancel_left, StarAlgEquiv.apply_symm_apply]
  map_mul' f h := by
    ext t
    exact map_mul (α g) _ _
  map_add' f h := by
    ext t
    exact map_add (α g) _ _
  map_smul' c f := by
    ext t
    exact map_smul (α g) c _
  map_star' f := by
    ext t
    exact map_star (α g) _

@[simp]
theorem boundaryTranslate_apply (α : G →* (B ≃⋆ₐ[ℂ] B)) (g : G)
    (f : G →ᵇ B) (t : G) : boundaryTranslate α g f t = α g (f (g⁻¹ * t)) := rfl

/-- The translation action agrees with the original action on constant fields. -/
theorem boundaryTranslate_constant (α : G →* (B ≃⋆ₐ[ℂ] B)) (g : G) (b : B) :
    boundaryTranslate α g (boundaryConstant (G := G) b) =
      boundaryConstant (G := G) (α g b) := by
  ext t
  rfl

/-- The induced translations themselves form a group action. -/
def boundaryTranslationAction (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    G →* ((G →ᵇ B) ≃⋆ₐ[ℂ] (G →ᵇ B)) where
  toFun := boundaryTranslate α
  map_one' := by
    ext f t
    simp only [boundaryTranslate_apply, inv_one, one_mul, map_one, StarAlgEquiv.one_apply]
  map_mul' g h := by
    ext f t
    simp only [boundaryTranslate_apply, StarAlgEquiv.mul_apply, map_mul,
      mul_inv_rev, mul_assoc]

/-- Any family of unitaries is uniformly bounded, hence defines an actual
unitary of the bounded-function C-star algebra. -/
def boundedUnitaryFamily (V : G → unitary B) : unitary (G →ᵇ B) :=
  let f : G →ᵇ B := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => (V g : B)) 1 (fun g => norm_unitary_le_one (V g))
  ⟨f, by
    constructor
    · ext g
      exact Unitary.star_mul_self_of_mem (V g).property
    · ext g
      exact Unitary.mul_star_self_of_mem (V g).property⟩

omit [Group G] in
@[simp]
theorem boundedUnitaryFamily_apply (V : G → unitary B) (g : G) :
    (boundedUnitaryFamily V).val g = (V g : B) := rfl

/-- The exact transport field, bundled as a bounded unitary family. -/
def boundedBoundaryTransport (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g : G) : unitary (G →ᵇ B) :=
  boundedUnitaryFamily (fun t =>
    ⟨boundaryTransport α (unitaryFamilyEval V) g t,
      boundaryTransport_mem_unitary α (unitaryFamilyEval V) g t⟩)

@[simp]
theorem boundedBoundaryTransport_apply (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g t : G) :
    (boundedBoundaryTransport α V g).val t =
      V.val t * α g (star (V.val (g⁻¹ * t))) := rfl

/-- The exact pointwise transport factorization holds in the bounded algebra. -/
theorem boundedBoundaryTransport_factor (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g h : G) :
    (boundedBoundaryTransport α V (g * h) : G →ᵇ B) =
      (boundedBoundaryTransport α V g : G →ᵇ B) *
        boundaryTranslate α g (boundedBoundaryTransport α V h : G →ᵇ B) := by
  ext t
  exact boundaryTransport_factor α (unitaryFamilyEval V) g h t

/-- Each pointwise defect is bounded by its actual uniform norm. -/
theorem norm_unitaryCocycleError_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g h : G) :
    ‖V.val g * α g (V.val h) - V.val (g * h)‖ ≤ unitaryCocycleDefect α V :=
  (unitaryCocycleError α V).norm_coe_le_norm (g, h)

/-- The transport family is uniformly within the actual cocycle defect of
its constant value at the given group element. -/
theorem norm_boundedBoundaryTransport_sub_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g : G) :
    ‖(boundedBoundaryTransport α V g : G →ᵇ B) -
      boundaryConstant (G := G) (V.val g)‖ ≤ unitaryCocycleDefect α V := by
  apply (BoundedContinuousFunction.norm_le (unitaryCocycleDefect_nonneg α V)).mpr
  intro t
  exact norm_boundaryTransport_sub_le α (unitaryFamilyEval V)
    (norm_unitaryCocycleError_le α V) g t

/-- An equivariant bimodule mean gives the actual metric-space refinement,
with the precise defect and displacement constants. -/
theorem exists_bounded_cocycle_improvement
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (V : unitary (G →ᵇ B)) (hV : unitaryCocycleDefect α V < 1) :
    ∃ W : unitary (G →ᵇ B),
      unitaryCocycleDefect α W ≤ 16 * (unitaryCocycleDefect α V) ^ 2 ∧
      dist V W ≤ unitaryCocycleDefect α V + 4 * (unitaryCocycleDefect α V) ^ 2 := by
  obtain ⟨W, hclose, hnew⟩ := m.exists_quadratic_improvement
    (fun g => α g) (boundaryTranslate α) hm (boundaryTranslate_constant α)
    (boundedBoundaryTransport α V) (unitaryFamilyEval V)
    (boundedBoundaryTransport_factor α V) (unitaryCocycleDefect_nonneg α V) hV
    (norm_boundedBoundaryTransport_sub_le α V)
  refine ⟨boundedUnitaryFamily W, ?_, ?_⟩
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    rintro ⟨g, h⟩
    exact hnew g h
  · simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖V.val - (boundedUnitaryFamily W).val‖ ≤ _
    apply (BoundedContinuousFunction.norm_le
      (add_nonneg (unitaryCocycleDefect_nonneg α V) (by positivity))).mpr
    intro g
    have hc := hclose g
    change ‖(W g : B) - V.val g‖ ≤ _ at hc
    simpa only [BoundedContinuousFunction.sub_apply, boundedUnitaryFamily_apply,
      norm_sub_rev] using hc

/-- Iterating the actual bounded-family step gives an exact cocycle.
The sole averaging premise is the explicitly supplied equivariant mean. -/
theorem exists_bounded_cocycle_of_equivariant_mean
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (V : unitary (G →ᵇ B)) (hV : unitaryCocycleDefect α V ≤ 1 / 64) :
    ∃ W : unitary (G →ᵇ B),
      (∀ g h, W.val g * α g (W.val h) = W.val (g * h)) ∧
      dist V W ≤ 2 * unitaryCocycleDefect α V := by
  obtain ⟨W, hzero, hdist⟩ := exists_zero_of_quadratic_improvement
    (unitaryCocycleDefect α) (continuous_unitaryCocycleDefect α)
    (unitaryCocycleDefect_nonneg α)
    (fun Z hZ => exists_bounded_cocycle_improvement α m hm Z (by linarith)) V hV
  exact ⟨W, (unitaryCocycleDefect_eq_zero_iff α W).mp hzero, hdist⟩

end

end KadisonKastler

end OAI
