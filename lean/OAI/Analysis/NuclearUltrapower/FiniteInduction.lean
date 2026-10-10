import OAI.Analysis.NuclearUltrapower.HilbertInduction
import OAI.Analysis.NuclearUltrapower.Schur
import OAI.Analysis.NuclearUltrapower.HilbertTensor

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ENNReal
namespace NuclearUltrapower
universe u

instance lp_finiteDimensional {ι V : Type u} [Finite ι]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (lp (fun _ : ι => V) 2) := by
  let := Fintype.ofFinite ι
  let f : lp (fun _ : ι => V) 2 →ₗ[ℂ] (ι → V) := {
    toFun x := x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact FiniteDimensional.of_injective f (fun _ _ h => lp.ext h)

section FiniteInduction
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Finite (Γ ⧸ H)]
    (α : FiniteUnitaryRep.{u,u} H)

instance induced_nontrivial : Nontrivial (lp (fun _ : Γ ⧸ H => α) 2) :=
  (inductionInclusion H (V := α)).injective.nontrivial

/-- Finite-index unitary induction, using the exact coset cocycle. -/
def finiteInduced : FiniteUnitaryRep.{u,u} Γ where
  carrier := lp (fun _ : Γ ⧸ H => α) 2
  action := inducedUnitary H α.action

/-- Restriction changes only the action, not the Hilbert carrier. -/
def restrictSubgroup (σ : FiniteUnitaryRep.{u,u} Γ) : FiniteUnitaryRep.{u,u} H :=
  { σ with action := σ.action.comp H.subtype }

/-- Identity-coordinate projection on the induced Hilbert space. -/
def identityCoordinate : finiteInduced H α →L[ℂ] α :=
  lp.evalCLM ℂ (fun _ : Γ ⧸ H => α) 2 (QuotientGroup.mk 1)

@[simp] theorem identityCoordinate_apply (x : finiteInduced H α) :
    identityCoordinate H α x = Subtype.val x (QuotientGroup.mk 1) := rfl

theorem identityCoordinate_intertwines (h : H) (x : finiteInduced H α) :
    identityCoordinate H α ((finiteInduced H α).action h x) =
      α.action h (identityCoordinate H α x) :=
  induced_identity_coordinate H α.action h x

/-- Every nonzero subrepresentation of a finite induction has a nonzero
identity-coordinate map. This is the all-constituent point in Frobenius reciprocity. -/
theorem identityCoordinate_nonzero {σ : FiniteUnitaryRep.{u,u} Γ}
    (U : σ →ₗᵢ[ℂ] finiteInduced H α)
    (hU : ∀ g x, U (σ.action g x) = (finiteInduced H α).action g (U x)) :
    (identityCoordinate H α).comp U.toContinuousLinearMap ≠ 0 := by
  intro hz
  obtain ⟨w,hw⟩ := exists_ne (0 : σ)
  have hUw : U w ≠ 0 := by simpa only [← map_zero U] using U.injective.ne hw
  have hex : ∃ i : Γ ⧸ H, Subtype.val (U w) i ≠ 0 := by
    by_contra! hn
    exact hUw (lp.ext (funext hn))
  obtain ⟨i,hi⟩ := hex
  have h := congrArg (fun T : σ →L[ℂ] α => T (σ.action (cosetRep H i)⁻¹ w)) hz
  change identityCoordinate H α (U (σ.action (cosetRep H i)⁻¹ w)) = 0 at h
  rw [hU] at h
  exact hi ((induced_translate_coordinate H α.action i (U w)).symm.trans h)

theorem frobenius_all_constituents (hα : α.Irreducible)
    {σ : FiniteUnitaryRep.{u,u} Γ} (hσ : σ.Embeds (finiteInduced H α)) :
    α.Embeds (restrictSubgroup H σ) := by
  obtain ⟨U,hU⟩ := hσ
  let F : σ →L[ℂ] α := (identityCoordinate H α).comp U.toContinuousLinearMap
  have hF0 : F ≠ 0 := identityCoordinate_nonzero H α U hU
  have hF (g : H) (x : σ) : F (σ.action g x) = α.action g (F x) := by
    dsimp only [F, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [hU, identityCoordinate_intertwines]
  have hstar : F.adjoint ≠ 0 := by
    intro h
    apply hF0
    have hh := congrArg ContinuousLinearMap.adjoint h
    simpa only [ContinuousLinearMap.adjoint_adjoint, map_zero] using hh
  apply FiniteUnitaryRep.isometry_of_intertwiner hα (restrictSubgroup H σ).action F.adjoint hstar
  intro g x
  change F.adjoint (α.action g x) = σ.action g (F.adjoint x)
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨z,rfl⟩ := (σ.action g).surjective y
  rw [hF, (α.action g).inner_map_map, (σ.action g).inner_map_map,
    ContinuousLinearMap.adjoint_inner_right]

end FiniteInduction
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
section Functor
variable {E E' E'' F F' F'' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup E''] [InnerProductSpace ℂ E'']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
  [NormedAddCommGroup F''] [InnerProductSpace ℂ F'']

/-- Heterogeneous completion of the Hilbert tensor functor. -/
def tensorMapBetween (U : E →L[ℂ] E') (V : F →L[ℂ] F') :
    TensorHilbert E F →L[ℂ] TensorHilbert E' F' := (TensorProduct.mapL U V).completion

@[simp] theorem tensorMapBetween_coe (U : E →L[ℂ] E') (V : F →L[ℂ] F')
    (z : E ⊗[ℂ] F) : tensorMapBetween U V z =
      (TensorProduct.mapL U V z : TensorHilbert E' F') :=
  ContinuousLinearMap.completion_apply_coe _ _

@[simp] theorem tensorMapBetween_comp (U : E →L[ℂ] E') (U' : E' →L[ℂ] E'')
    (V : F →L[ℂ] F') (V' : F' →L[ℂ] F'') :
    tensorMapBetween (U'.comp U) (V'.comp V) =
      (tensorMapBetween U' V').comp (tensorMapBetween U V) := by
  simp only [tensorMapBetween, TensorProduct.mapL_comp, completed_comp]

@[simp] theorem tensorMapBetween_one :
    tensorMapBetween (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := completedTensorMap_one

@[simp] theorem tensorMapBetween_add_right (U : E →L[ℂ] E') (V W : F →L[ℂ] F') :
    tensorMapBetween U (V+W) = tensorMapBetween U V + tensorMapBetween U W := by
  simp only [tensorMapBetween, TensorProduct.mapL_add_right, completed_add]

@[simp] theorem tensorMapBetween_zero_right (U : E →L[ℂ] E') :
    tensorMapBetween U (0 : F →L[ℂ] F') = 0 := by
  simp only [tensorMapBetween, TensorProduct.mapL_zero_right, completed_zero]

/-- Isometries remain isometries upon completion, proved using density. -/
def tensorIsometry (U : E →ₗᵢ[ℂ] E') (V : F →ₗᵢ[ℂ] F') :
    TensorHilbert E F →ₗᵢ[ℂ] TensorHilbert E' F' where
  toLinearMap := (tensorMapBetween U.toContinuousLinearMap V.toContinuousLinearMap).toLinearMap
  norm_map' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_norm
    | ih x =>
      change ‖tensorMapBetween U.toContinuousLinearMap V.toContinuousLinearMap (x : TensorHilbert E F)‖ = ‖(x : TensorHilbert E F)‖
      rw [tensorMapBetween_coe, UniformSpace.Completion.norm_coe,
        UniformSpace.Completion.norm_coe]
      rw [← TensorProduct.toContinuousLinearMap_mapIsometry]
      exact (TensorProduct.mapIsometry U V).norm_map x

@[simp] theorem tensorIsometry_toCLM (U : E →ₗᵢ[ℂ] E') (V : F →ₗᵢ[ℂ] F') :
    (tensorIsometry U V).toContinuousLinearMap =
      tensorMapBetween U.toContinuousLinearMap V.toContinuousLinearMap := rfl

@[simp] theorem tensorMapBetween_adjoint [CompleteSpace E] [CompleteSpace E']
    [CompleteSpace F] [CompleteSpace F'] (U : E →L[ℂ] E') (V : F →L[ℂ] F') :
    tensorMapBetween U.adjoint V.adjoint = (tensorMapBetween U V).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      simp only [tensorMapBetween_coe, UniformSpace.Completion.inner_coe]
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']
      | tmul a b =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
        | tmul a' b' =>
          simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
          rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

end Functor
section Projection
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (W : Submodule ℂ F) [CompleteSpace W]

def tensorInclusion : TensorHilbert E W →ₗᵢ[ℂ] TensorHilbert E F :=
  tensorIsometry (LinearIsometry.id) W.subtypeₗᵢ

def tensorProjection : TensorHilbert E F →L[ℂ] TensorHilbert E W :=
  tensorMapBetween (1 : E →L[ℂ] E) W.orthogonalProjectionOnto

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem tensorInclusion_projection :
    (tensorInclusion (E := E) W).toContinuousLinearMap.comp (tensorProjection (E := E) W) =
      completedTensorMap (1 : E →L[ℂ] E) W.starProjection := by
  rw [tensorProjection, tensorInclusion, tensorIsometry_toCLM, ← tensorMapBetween_comp]
  rfl

theorem tensorProjection_norm_sq (x : TensorHilbert E F) :
    ‖x‖^2 = ‖tensorProjection (E := E) W x‖^2 +
      ‖tensorProjection (E := E) Wᗮ x‖^2 := by
  let P := completedTensorMap (1 : E →L[ℂ] E) W.starProjection
  let Q := completedTensorMap (1 : E →L[ℂ] E) Wᗮ.starProjection
  have hsum : P + Q = 1 := by
    rw [← completedTensorMap_add_right]
    have h : W.starProjection + Wᗮ.starProjection = 1 := by
      ext x
      exact Submodule.starProjection_add_starProjection_orthogonal x
    rw [h,completedTensorMap_one]
  have hPQ : P*Q = 0 := by
    dsimp only [P,Q]
    rw [← completedTensorMap_mul, one_mul]
    have h : W.starProjection * Wᗮ.starProjection = 0 := by
      rw [Submodule.starProjection_orthogonal', mul_sub, mul_one]
      rw [W.isIdempotentElem_starProjection.eq]
      exact sub_self _
    rw [h]
    simp [completedTensorMap]
  have hPstar : star P = P := by
    dsimp only [P]
    rw [← completedTensorMap_star, star_one]
    congr 1
    exact isSelfAdjoint_starProjection W
  have hi : inner ℂ (P x) (Q x) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x ((star P * Q) x) = 0
    rw [hPstar,hPQ]
    simp
  have hp : ‖P x‖ = ‖tensorProjection (E := E) W x‖ := by
    dsimp only [P]
    rw [← tensorInclusion_projection]
    exact (tensorInclusion (E := E) W).norm_map _
  have hq : ‖Q x‖ = ‖tensorProjection (E := E) Wᗮ x‖ := by
    dsimp only [Q]
    rw [← tensorInclusion_projection]
    exact (tensorInclusion (E := E) Wᗮ).norm_map _
  have hs : P x + Q x = x := by
    change (P+Q) x = x
    rw [hsum]
    rfl
  rw [← hp,← hq, sq, sq, sq, ← norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (Q x) hi, hs]

end Projection
end NuclearUltrapower
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped InnerProductSpace ENNReal
namespace NuclearUltrapower
universe u v
section Coordinates
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ)
  {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

def coordinateInclusion (i : Γ ⧸ H) : V →ₗᵢ[ℂ] lp (fun _ : Γ ⧸ H => V) 2 := by
  classical
  refine { toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : Γ ⧸ H => V) 2 i, norm_map' := ?_ }
  intro v
  exact lp.norm_single (E := fun _ : Γ ⧸ H => V) (p := 2) (by norm_num) i v

@[simp] theorem coordinateInclusion_apply (i j : Γ ⧸ H) (v : V) :
    coordinateInclusion H i v j = Pi.single (M := fun _ : Γ ⧸ H => V) i v j := rfl

@[simp] theorem coordinateInclusion_identity :
    coordinateInclusion H (QuotientGroup.mk 1) = inductionInclusion H (V := V) := rfl

theorem coordinateInclusion_action (g : Γ) (i : Γ ⧸ H) (v : V) :
    inducedUnitary H α g (coordinateInclusion H i v) =
      coordinateInclusion H (g • i) (α (cosetCocycle H g i) v) := by
  classical
  ext j
  rw [inducedUnitary_apply, coordinateInclusion_apply, coordinateInclusion_apply]
  by_cases hj : j = g • i
  · subst j
    simp
  · have hh : g⁻¹ • j ≠ i := by
      intro he
      exact hj (by simpa only [smul_inv_smul] using congrArg (fun k : Γ ⧸ H => g • k) he)
    simp only [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hh, map_zero]

theorem cosetCocycle_factor (g : Γ) (i : Γ ⧸ H) :
    g * cosetRep H i = cosetRep H (g • i) * (cosetCocycle H g i : Γ) := by
  simp only [cosetCocycle]
  group

end Coordinates
section FiniteCoordinates
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Finite (Γ ⧸ H)]
  (α : FiniteUnitaryRep.{u,u} H)

@[simp] theorem identityCoordinate_inclusion (i : Γ ⧸ H) (v : α) :
    identityCoordinate H α (coordinateInclusion H i v) =
      if i = QuotientGroup.mk 1 then v else 0 := by
  classical
  change Pi.single (M := fun _ : Γ ⧸ H => α) i v (QuotientGroup.mk 1) = _
  split_ifs with hi
  · simp [hi]
  · exact Pi.single_eq_of_ne (M := fun _ : Γ ⧸ H => α) (Ne.symm hi) v

theorem identityCoordinate_norm_le : ‖identityCoordinate H α‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖Subtype.val (x : lp (fun _ : Γ ⧸ H => α) 2) (QuotientGroup.mk 1)‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x (QuotientGroup.mk 1)

end FiniteCoordinates
end NuclearUltrapower
end
end

end OAI
