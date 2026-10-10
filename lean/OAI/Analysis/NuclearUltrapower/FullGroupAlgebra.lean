import Mathlib

namespace OAI

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.GroupStarAlgebra
variable {Γ : Type*} [Group Γ]

/-- Algebraic involution on the complex group ring: conjugate coefficients and
invert group elements. This is not the pointwise star on coefficient functions. -/
def involutionAdd : ℂ[Γ] →+ ℂ[Γ] :=
  MonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapDomain.addMonoidHom (Inv.inv : Γ → Γ)).comp
      ((Finsupp.mapRange.addMonoidHom (starAddEquiv : ℂ ≃+ ℂ).toAddMonoidHom).comp
        MonoidAlgebra.coeffAddEquiv.toAddMonoidHom))

instance : Star ℂ[Γ] := ⟨involutionAdd⟩

@[simp] theorem star_single (g : Γ) (c : ℂ) :
    star (MonoidAlgebra.single g c) = MonoidAlgebra.single g⁻¹ (star c) := by
  change involutionAdd _ = _
  simp [involutionAdd]

theorem star_add' (x y : ℂ[Γ]) : star (x+y) = star x + star y :=
  involutionAdd.map_add x y

theorem star_zero' : star (0 : ℂ[Γ]) = 0 := involutionAdd.map_zero

instance : InvolutiveStar ℂ[Γ] where
  star_involutive x := by
    have h : (involutionAdd (Γ := Γ)).comp involutionAdd = AddMonoidHom.id _ := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro g c
      change star (star (MonoidAlgebra.single g c)) = MonoidAlgebra.single g c
      simp only [star_single, inv_inv, star_star]
    exact congrArg (fun f : ℂ[Γ] →+ ℂ[Γ] => f x) h

instance : StarAddMonoid ℂ[Γ] where
  star_add := star_add'

instance : StarModule ℂ ℂ[Γ] where
  star_smul c x := by
    let f : ℂ[Γ] →+ ℂ[Γ] := (involutionAdd (Γ := Γ)).comp
      (DistribSMul.toAddMonoidHom ℂ[Γ] c)
    let g : ℂ[Γ] →+ ℂ[Γ] := (DistribSMul.toAddMonoidHom ℂ[Γ] (star c)).comp involutionAdd
    have h : f = g := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro a b
      change star (c • MonoidAlgebra.single a b) = star c • star (MonoidAlgebra.single a b)
      simp only [MonoidAlgebra.smul_single, star_single, star_mul, smul_eq_mul, mul_comm]
    exact congrArg (fun f : ℂ[Γ] →+ ℂ[Γ] => f x) h

instance : StarRing ℂ[Γ] where
  star_add := star_add'
  star_mul x y := by
    induction x using MonoidAlgebra.induction_on with
    | of a =>
      induction y using MonoidAlgebra.induction_on with
      | of b => simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          one_mul, star_single, star_one, mul_inv_rev]
      | add y z hy hz => simp only [mul_add, star_add, hy, hz, add_mul]
      | smul c y hy => simp only [mul_smul_comm, star_smul, hy, smul_mul_assoc]
    | add x z hx hz => simp only [add_mul, star_add, hx, hz, mul_add]
    | smul c x hx => simp only [smul_mul_assoc, star_smul, hx, mul_smul_comm]

variable {D : Type*} [CStarAlgebra D]

/-- A unitary group representation evaluates finite linear combinations. -/
def evaluate (ρ : Γ →* unitary D) : ℂ[Γ] →⋆ₐ[ℂ] D where
  __ := MonoidAlgebra.lift ℂ D Γ ((unitary D).subtype.comp ρ)
  map_star' x := by
    change (MonoidAlgebra.lift ℂ D Γ ((unitary D).subtype.comp ρ)) (star x) =
      star ((MonoidAlgebra.lift ℂ D Γ ((unitary D).subtype.comp ρ)) x)
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      simp only [MonoidAlgebra.of_apply, star_single, star_one, MonoidAlgebra.lift_single,
        one_smul, MonoidHom.comp_apply, Submonoid.subtype_apply, ρ.map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
    | add x y hx hy => simp only [star_add, map_add, hx, hy]
    | smul c x hx => simp only [star_smul, map_smul, hx]

@[simp] theorem evaluate_single (ρ : Γ →* unitary D) (g : Γ) (c : ℂ) :
    evaluate ρ (MonoidAlgebra.single g c) = c • (ρ g : D) :=
  MonoidAlgebra.lift_single _ _ _

end NuclearUltrapower.GroupStarAlgebra

namespace NuclearUltrapower.GroupStarAlgebra
open scoped MonoidAlgebra
variable {Γ : Type} [Group Γ]

/-- The possible operator norms in all unital C*-models of the group. -/
def modelNormSet (x : ℂ[Γ]) : Set ℝ :=
  {t | ∃ (D : Type) (_ : CStarAlgebra D) (ρ : Γ →* unitary D), t = ‖evaluate ρ x‖}

theorem modelNormSet_nonempty (x : ℂ[Γ]) : (modelNormSet x).Nonempty := by
  exact ⟨‖evaluate (1 : Γ →* unitary ℂ) x‖, ℂ, inferInstance, 1, rfl⟩

/-- Every finite group-ring expression is bounded uniformly over ALL models. -/
theorem models_bounded (x : ℂ[Γ]) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (D : Type) [CStarAlgebra D] (ρ : Γ →* unitary D), ‖evaluate ρ x‖ ≤ M := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨1, zero_le_one, ?_⟩
    intro D _ ρ
    simp only [MonoidAlgebra.of_apply, evaluate_single, one_smul]
    cases subsingleton_or_nontrivial D with
    | inl h => simp [Subsingleton.elim (ρ g : D) 0]
    | inr h => exact (CStarRing.norm_coe_unitary (ρ g)).le
  | add x y hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M+N, add_nonneg hM hN, ?_⟩
    intro D _ ρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hx D ρ) (hy D ρ))
  | smul c x hx =>
    obtain ⟨M, hM, hx⟩ := hx
    refine ⟨‖c‖*M, mul_nonneg (norm_nonneg _) hM, ?_⟩
    intro D _ ρ
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hx D ρ) (norm_nonneg _)

theorem modelNormSet_bdd (x : ℂ[Γ]) : BddAbove (modelNormSet x) := by
  obtain ⟨M, _, hx⟩ := models_bounded x
  refine ⟨M, ?_⟩
  rintro r ⟨D, inst, ρ, rfl⟩
  exact hx D ρ

/-- The full, not the reduced, universal C*-seminorm. -/
def universalNorm (x : ℂ[Γ]) : ℝ := sSup (modelNormSet x)

theorem model_norm_le (x : ℂ[Γ]) (D : Type) [CStarAlgebra D] (ρ : Γ →* unitary D) :
    ‖evaluate ρ x‖ ≤ universalNorm x :=
  le_csSup (modelNormSet_bdd x) ⟨D, inferInstance, ρ, rfl⟩

theorem universalNorm_le {x : ℂ[Γ]} {M : ℝ}
    (h : ∀ (D : Type) [CStarAlgebra D] (ρ : Γ →* unitary D), ‖evaluate ρ x‖ ≤ M) :
    universalNorm x ≤ M := by
  apply csSup_le (modelNormSet_nonempty x)
  rintro r ⟨D, inst, ρ, rfl⟩
  exact h D ρ

theorem universalNorm_nonneg (x : ℂ[Γ]) : 0 ≤ universalNorm x :=
  (norm_nonneg _).trans (model_norm_le x ℂ 1)

@[simp] theorem universalNorm_zero : universalNorm (0 : ℂ[Γ]) = 0 := by
  apply le_antisymm _ (universalNorm_nonneg _)
  apply universalNorm_le
  intro D _ ρ
  simp

/-- The universal model supremum is a submultiplicative seminorm. -/
def universalSeminorm : RingSeminorm ℂ[Γ] where
  toFun := universalNorm
  map_zero' := universalNorm_zero
  add_le' x y := by
    apply universalNorm_le
    intro D _ ρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (model_norm_le x D ρ) (model_norm_le y D ρ))
  neg' x := by
    apply le_antisymm
    · apply universalNorm_le
      intro D _ ρ
      simpa only [map_neg, norm_neg] using model_norm_le x D ρ
    · have h : universalNorm x ≤ universalNorm (-x) := by
        apply universalNorm_le
        intro D _ ρ
        have := model_norm_le (-x) D ρ
        simpa only [map_neg, norm_neg] using this
      exact h
  mul_le' x y := by
    apply universalNorm_le
    intro D _ ρ
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (model_norm_le x D ρ) (model_norm_le y D ρ)
      (norm_nonneg _) (universalNorm_nonneg _))

instance : SeminormedRing ℂ[Γ] := universalSeminorm.toSeminormedRing

@[simp] theorem norm_eq_universalNorm (x : ℂ[Γ]) : ‖x‖ = universalNorm x := rfl

instance : NormedStarGroup ℂ[Γ] where
  norm_star_le x := by
    apply universalNorm_le
    intro D _ ρ
    simpa only [map_star, norm_star, norm_eq_universalNorm] using model_norm_le x D ρ

instance : NormedAlgebra ℂ ℂ[Γ] where
  norm_smul_le c x := by
    apply universalNorm_le
    intro D _ ρ
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (model_norm_le x D ρ) (norm_nonneg _)

/-- C*-identity at the seminorm level, which survives separated completion. -/
theorem norm_mul_self_le (x : ℂ[Γ]) : ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  have h : ‖x‖ ≤ Real.sqrt ‖star x * x‖ := by
    apply universalNorm_le
    intro D _ ρ
    apply (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mpr
    have hm := model_norm_le (star x*x) D ρ
    simpa only [map_mul, map_star, CStarRing.norm_star_mul_self, pow_two, norm_eq_universalNorm] using hm
  nlinarith [Real.sq_sqrt (norm_nonneg (star x*x)), norm_nonneg x]

/-- Every model evaluation is contractive for the universal seminorm. -/
theorem evaluate_continuous {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) :
    Continuous (evaluate ρ) := by
  apply (evaluate ρ).toLinearMap.mkContinuous 1 ?_ |>.continuous
  intro x
  change ‖evaluate ρ x‖ ≤ 1 * universalNorm x
  simpa only [one_mul] using model_norm_le x D ρ

end NuclearUltrapower.GroupStarAlgebra

noncomputable section
open UniformSpace
namespace NuclearUltrapower.UniversalCompletion

variable {R : Type*} [SeminormedRing R] [StarRing R] [NormedStarGroup R]

instance completionStar : Star (Completion R) := ⟨Completion.map star⟩

@[simp] theorem star_coe (x : R) : star (x : Completion R) = (star x : R) :=
  Completion.map_coe (by exact star_isometry.uniformContinuous) x

instance completionContinuousStar : ContinuousStar (Completion R) where
  continuous_star := Completion.continuous_map

instance completionInvolutiveStar : InvolutiveStar (Completion R) where
  star_involutive x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

instance completionStarRing : StarRing (Completion R) where
  star_mul x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_mul, star_coe, star_mul]
  star_add x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_add, star_coe, star_add]

instance completionNormedStar : NormedStarGroup (Completion R) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) continuous_norm
    | ih x => simp

variable [NormedAlgebra ℂ R] [StarModule ℂ R]

instance completionNormedAlgebra : NormedAlgebra ℂ (Completion R) where
  norm_smul_le := norm_smul_le

instance completionStarModule : StarModule ℂ (Completion R) where
  star_smul c x := by
    induction x using Completion.induction_on with
    | hp =>
      apply isClosed_eq
      · exact continuous_star.comp (continuous_id.const_smul c)
      · exact continuous_star.const_smul (star c)
    | ih x => simp only [← Completion.coe_smul, star_coe, star_smul]

/-- The separated completion of a C*-seminormed star algebra is a C*-algebra. -/
@[instance_reducible] def cstarAlgebra (hc : ∀ x : R, ‖x‖ * ‖x‖ ≤ ‖star x * x‖) : CStarAlgebra (Completion R) where
  norm_mul_self_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [star_coe, ← Completion.coe_mul, Completion.norm_coe] using hc x

/-- The canonical, dense star algebra map to the universal completion. -/
def inclusion : R →⋆ₐ[ℂ] Completion R where
  __ := Completion.coeRingHom
  commutes' c := by
    change ((algebraMap ℂ R c : R) : Completion R) = algebraMap ℂ (Completion R) c
    exact (Completion.algebraMap_def R ℂ c).symm
  map_star' x := by
    change ((star x : R) : Completion R) = star (x : Completion R)
    exact (star_coe x).symm

/-- Any continuous model map extends uniquely over the completed algebra. -/
def extend {D : Type*} [CStarAlgebra D] (f : R →⋆ₐ[ℂ] D) (hf : Continuous f) :
    Completion R →⋆ₐ[ℂ] D where
  __ := Completion.extensionHom f.toRingHom hf
  commutes' c := by
    change Completion.extensionHom f.toRingHom hf (algebraMap ℂ (Completion R) c) = _
    rw [Completion.algebraMap_def, Completion.extensionHom_coe]
    exact f.commutes c
  map_star' x := by
    change Completion.extensionHom f.toRingHom hf (star x) =
      star (Completion.extensionHom f.toRingHom hf x)
    have hc : Continuous (Completion.extensionHom f.toRingHom hf) :=
      Completion.continuous_extension
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (hc.comp continuous_star) (continuous_star.comp hc)
    | ih x =>
      simp only [star_coe, Completion.extensionHom_coe]
      exact map_star f x

omit [StarModule ℂ R] in
@[simp] theorem extend_coe {D : Type*} [CStarAlgebra D]
    (f : R →⋆ₐ[ℂ] D) (hf : Continuous f) (x : R) : extend f hf (x : Completion R) = f x :=
  Completion.extensionHom_coe f.toRingHom hf x

end NuclearUltrapower.UniversalCompletion

namespace NuclearUltrapower.FullGroupModel
open UniformSpace
open scoped MonoidAlgebra CStarAlgebra
open GroupStarAlgebra
variable (Γ : Type) [Group Γ]

/-- A separated completion in the supremum over all unitary models. -/
def Full := Completion ℂ[Γ]

instance : CStarAlgebra (Full Γ) :=
  UniversalCompletion.cstarAlgebra GroupStarAlgebra.norm_mul_self_le

def algebraicInclusion : ℂ[Γ] →⋆ₐ[ℂ] Full Γ := UniversalCompletion.inclusion

/-- The canonical group generators are unitaries in the full completion. -/
def generator (g : Γ) : unitary (Full Γ) :=
  ⟨algebraicInclusion Γ (MonoidAlgebra.single g 1), by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star, ← map_mul, GroupStarAlgebra.star_single]
      simp only [star_one, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
        ← MonoidAlgebra.one_def, map_one]
    · rw [← map_star, ← map_mul, GroupStarAlgebra.star_single]
      simp only [star_one, MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul,
        ← MonoidAlgebra.one_def, map_one]⟩

def inclusion : Γ →* unitary (Full Γ) where
  toFun := generator Γ
  map_one' := by
    apply Subtype.ext
    change algebraicInclusion Γ (MonoidAlgebra.single 1 1) = 1
    exact map_one _
  map_mul' g h := by
    apply Subtype.ext
    change algebraicInclusion Γ (MonoidAlgebra.single (g*h) 1) =
      algebraicInclusion Γ (MonoidAlgebra.single g 1) * algebraicInclusion Γ (MonoidAlgebra.single h 1)
    rw [← map_mul, MonoidAlgebra.single_mul_single, one_mul]

@[simp] theorem inclusion_coe (g : Γ) :
    (inclusion Γ g : Full Γ) = algebraicInclusion Γ (MonoidAlgebra.single g 1) := rfl

/-- Extension to every model, not merely to Hilbert-space models. -/
def modelMap {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) : Full Γ →⋆ₐ[ℂ] D :=
  UniversalCompletion.extend (evaluate ρ) (evaluate_continuous ρ)

@[simp] theorem modelMap_coe {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) (x : ℂ[Γ]) :
    modelMap Γ ρ (algebraicInclusion Γ x) = evaluate ρ x :=
  UniversalCompletion.extend_coe _ _ _

@[simp] theorem modelMap_generator {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) (g : Γ) :
    modelMap Γ ρ (inclusion Γ g) = (ρ g : D) := by
  rw [inclusion_coe, modelMap_coe, evaluate_single, one_smul]

instance : Nontrivial (Full Γ) := by
  apply nontrivial_of_ne (0 : Full Γ) 1
  intro h
  have := congrArg (modelMap Γ (1 : Γ →* unitary ℂ)) h
  exact zero_ne_one (by simpa only [map_zero, map_one] using this)

/-- The linear span, not just the algebra generated by the generators, is dense. -/
theorem dense_span : Dense (Submodule.span ℂ (Set.range (fun g => (inclusion Γ g : Full Γ))) : Set (Full Γ)) := by
  apply Completion.denseRange_coe.mono
  rintro _ ⟨x, rfl⟩
  have hin (y : ℂ[Γ]) : algebraicInclusion Γ y ∈
      Submodule.span ℂ (Set.range (fun g => (inclusion Γ g : Full Γ))) := by
    induction y using MonoidAlgebra.induction_on with
    | of g => exact Submodule.subset_span ⟨g, rfl⟩
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul c x hx => simpa only [map_smul] using Submodule.smul_mem _ c hx
  exact hin x

/-- Uniqueness is proved from continuity and dense generation. -/
theorem modelMap_unique {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D)
    (φ : Full Γ →⋆ₐ[ℂ] D) (hφ : ∀ g, φ (inclusion Γ g) = (ρ g : D)) :
    φ = modelMap Γ ρ := by
  have he (x : ℂ[Γ]) : φ (algebraicInclusion Γ x) = modelMap Γ ρ (algebraicInclusion Γ x) := by
    induction x using MonoidAlgebra.induction_on with
    | of g => exact (hφ g).trans (modelMap_generator Γ ρ g).symm
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul c x hx => simp only [map_smul, hx]
  have hc : Continuous (φ : Full Γ → D) :=
    AddMonoidHomClass.continuous_of_bound φ 1 (by
      intro x
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ x)
  have hd : Continuous (modelMap Γ ρ : Full Γ → D) :=
    AddMonoidHomClass.continuous_of_bound (modelMap Γ ρ) 1 (by
      intro x
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (modelMap Γ ρ) x)
  apply DFunLike.ext'
  exact Completion.denseRange_coe.equalizer hc hd (funext he)

/-- Countability of the group gives the standing separability conclusion. -/
instance [Countable Γ] : TopologicalSpace.SeparableSpace (Full Γ) := by
  have hs : TopologicalSpace.IsSeparable (Set.range (fun g => (inclusion Γ g : Full Γ))) :=
    (Set.countable_range _).isSeparable
  have ht := hs.span (R := ℂ)
  have hc := ht.closure
  rw [(dense_span Γ).closure_eq] at hc
  exact TopologicalSpace.isSeparable_univ_iff.mp hc

end NuclearUltrapower.FullGroupModel
end
end
end

end OAI
