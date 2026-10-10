import Mathlib.LinearAlgebra.TensorProduct.Associator
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Algebra.EvaluationMatrix
import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Construction.NodeEmbedding
import OAI.Computability.PerfectCompleteness.Foundations.PartitionsLemmas

namespace OAI


namespace PerfectCompleteness.TensorBucketEvaluation

open scoped BigOperators TensorProduct Classical

noncomputable section

abbrev F2 := BucketSampler.F2

variable {ℓ : Nat} {Ω H : Type*} [AddCommGroup H] [Module F2 H]

def tensorOutputLinear (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) : (W ⊗[F2] H) →ₗ[F2] (Fin ℓ → F2) :=
  W.subtype.comp
    ((TensorProduct.rid F2 W).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : W →ₗ[F2] W) q))

def tensorOutput (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (X : W ⊗[F2] H) : Fin ℓ → F2 :=
  tensorOutputLinear W q X

@[simp] theorem tensorOutput_tmul (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (w : W) (h : H) :
    tensorOutput W q (w ⊗ₜ[F2] h) = q h • w.val := by
  simp [tensorOutput, tensorOutputLinear]

@[simp] theorem tensorOutput_zero (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) : tensorOutput W q 0 = 0 :=
  (tensorOutputLinear W q).map_zero

@[simp] theorem tensorOutput_add (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (X Y : W ⊗[F2] H) :
    tensorOutput W q (X + Y) = tensorOutput W q X + tensorOutput W q Y :=
  (tensorOutputLinear W q).map_add X Y

theorem tensorOutput_hiddenSum (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H)
    (ω : HiddenBucketBias.HiddenTape W Ω) :
    tensorOutput W q (HiddenBucketBias.hiddenSum W eval ω) =
      ∑ v : HiddenBucketBias.HiddenDirection W, q (eval (ω v)) • v.val.val := by
  change tensorOutputLinear W q
    (∑ v : HiddenBucketBias.HiddenDirection W,
      HiddenBucketBias.directionIn W v ⊗ₜ[F2] eval (ω v)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact tensorOutput_tmul W q (HiddenBucketBias.directionIn W v) (eval (ω v))

def visibleOutput (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H)
    (ω : HiddenBucketBias.VisibleTape W Ω) : Fin ℓ → F2 :=
  ∑ v : HiddenBucketBias.VisibleDirection W, q (eval (ω v)) • v.val.val

theorem evaluate_eq_direction_sum (q : Module.Dual F2 H)
    (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      ∑ v : BucketSampler.Direction ℓ, q (eval (t v)) • v.val := by
  funext i
  rw [BucketSampler.linearMap_evaluate]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_comm _ _

theorem evaluate_split (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      visibleOutput W q eval (fun v => t v.val) +
        tensorOutput W q
          (HiddenBucketBias.hiddenSum W eval (fun v => t v.val)) := by
  rw [evaluate_eq_direction_sum, tensorOutput_hiddenSum]
  exact (Fintype.sum_subtype_add_sum_subtype
    (fun v : BucketSampler.Direction ℓ => v.val ∈ W)
    (fun v => q (eval (t v)) • v.val)).symm.trans (add_comm _ _)

theorem evaluate_splitTape (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      visibleOutput W q eval (HiddenBucketBias.splitTape W Ω t).2 +
        tensorOutput W q
          (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω t).1) :=
  evaluate_split W q eval t

theorem evaluate_apply_split {A : Type*}
    (W : Submodule F2 (Fin ℓ → F2)) (V : Submodule F2 (A → F2))
    (eval : Ω → V) (t : BucketSampler.Tape ℓ Ω) (a : A) :
    (fun i => (BucketSampler.evaluate ℓ eval t i).val a) =
      visibleOutput W (EvaluationMatrix.evaluation V a) eval
        (HiddenBucketBias.splitTape W Ω t).2 +
      tensorOutput W (EvaluationMatrix.evaluation V a)
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω t).1) :=
  evaluate_splitTape W (EvaluationMatrix.evaluation V a) eval t

end

end PerfectCompleteness.TensorBucketEvaluation



namespace PerfectCompleteness.TensorProjectedSlice

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K H H' : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H']
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)

def totalMatrix (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    Module.Dual F2 H →ₗ[F2] K :=
  X₀ + W.subtype.comp ((TensorRestriction.tensorEquivHom T).comp i.dualMap)

@[simp] theorem totalMatrix_apply (X₀ : Module.Dual F2 H →ₗ[F2] K)
    (T : W ⊗[F2] H') (z : Module.Dual F2 H) :
    totalMatrix i W X₀ T z =
      X₀ z + (TensorRestriction.tensorEquivHom T (i.dualMap z) : K) := rfl

variable (Z : Submodule F2 (Module.Dual F2 H))

def Compatible (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (T : W ⊗[F2] H') : Prop :=
  (totalMatrix i W X₀ T).domRestrict Z = v

def targetAt (T₀ : W ⊗[F2] H') :
    ProjectedColumnSlice.projectedColumns i Z →ₗ[F2] W :=
  TensorRestriction.restrictionMap (ProjectedColumnSlice.projectedColumns i Z) T₀

theorem compatible_iff_restrictionMap_eq
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (T₀ : W ⊗[F2] H') (h₀ : Compatible i W Z X₀ v T₀)
    (T : W ⊗[F2] H') :
    Compatible i W Z X₀ v T ↔
      TensorRestriction.restrictionMap (ProjectedColumnSlice.projectedColumns i Z) T =
        targetAt i W Z T₀ := by
  constructor
  · intro hT
    apply LinearMap.ext
    intro q
    obtain ⟨z, rfl⟩ := ProjectedColumnSlice.restrictionZ_surjective i Z q
    apply Subtype.ext
    have hTz := LinearMap.congr_fun hT z
    have h₀z := LinearMap.congr_fun h₀ z
    change X₀ z.val + (TensorRestriction.tensorEquivHom T (i.dualMap z.val) : K) =
      v z at hTz
    change X₀ z.val + (TensorRestriction.tensorEquivHom T₀ (i.dualMap z.val) : K) =
      v z at h₀z
    exact add_left_cancel (hTz.trans h₀z.symm)
  · intro hT
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hT (ProjectedColumnSlice.restrictionZ i Z z)
    change TensorRestriction.tensorEquivHom T (i.dualMap z.val) =
      TensorRestriction.tensorEquivHom T₀ (i.dualMap z.val) at hz
    change X₀ z.val + (TensorRestriction.tensorEquivHom T (i.dualMap z.val) : K) = v z
    rw [hz]
    exact LinearMap.congr_fun h₀ z

theorem targetAt_comp_restrictionZ
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (T₀ : W ⊗[F2] H') (h₀ : Compatible i W Z X₀ v T₀) :
    W.subtype.comp ((targetAt i W Z T₀).comp
      (ProjectedColumnSlice.restrictionZ i Z)) = v - X₀.domRestrict Z := by
  apply LinearMap.ext
  intro z
  have h₀z := LinearMap.congr_fun h₀ z
  change X₀ z.val + (TensorRestriction.tensorEquivHom T₀ (i.dualMap z.val) : K) =
    v z at h₀z
  change (TensorRestriction.tensorEquivHom T₀ (i.dualMap z.val) : K) = v z - X₀ z.val
  rw [← h₀z, add_sub_cancel_left]

theorem targetAt_independent
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (T₀ T₁ : W ⊗[F2] H')
    (h₀ : Compatible i W Z X₀ v T₀) (h₁ : Compatible i W Z X₀ v T₁) :
    targetAt i W Z T₀ = targetAt i W Z T₁ :=
  (compatible_iff_restrictionMap_eq i W Z X₀ v T₁ h₁ T₀).mp h₀

def inducedTarget (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (hne : ∃ T : W ⊗[F2] H', Compatible i W Z X₀ v T) :
    ProjectedColumnSlice.projectedColumns i Z →ₗ[F2] W :=
  targetAt i W Z (Classical.choose hne)

theorem inducedTarget_eq_targetAt
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (hne : ∃ T : W ⊗[F2] H', Compatible i W Z X₀ v T)
    (T₀ : W ⊗[F2] H') (h₀ : Compatible i W Z X₀ v T₀) :
    inducedTarget i W Z X₀ v hne = targetAt i W Z T₀ :=
  targetAt_independent i W Z X₀ v (Classical.choose hne) T₀
    (Classical.choose_spec hne) h₀

theorem inducedTarget_comp_restrictionZ
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (hne : ∃ T : W ⊗[F2] H', Compatible i W Z X₀ v T) :
    W.subtype.comp ((inducedTarget i W Z X₀ v hne).comp
      (ProjectedColumnSlice.restrictionZ i Z)) = v - X₀.domRestrict Z :=
  targetAt_comp_restrictionZ i W Z X₀ v (Classical.choose hne) (Classical.choose_spec hne)

theorem columnEquations_iff_inducedTarget
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (hne : ∃ T : W ⊗[F2] H', Compatible i W Z X₀ v T)
    (T : W ⊗[F2] H') :
    (totalMatrix i W X₀ T).domRestrict Z = v ↔
      TensorRestriction.restrictionMap (ProjectedColumnSlice.projectedColumns i Z) T =
        inducedTarget i W Z X₀ v hne :=
  compatible_iff_restrictionMap_eq i W Z X₀ v
    (Classical.choose hne) (Classical.choose_spec hne) T

def sliceEquiv (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (hne : ∃ T : W ⊗[F2] H', Compatible i W Z X₀ v T) :
    {T : W ⊗[F2] H' // (totalMatrix i W X₀ T).domRestrict Z = v} ≃
      {T : W ⊗[F2] H' //
        TensorRestriction.restrictionMap (ProjectedColumnSlice.projectedColumns i Z) T =
          inducedTarget i W Z X₀ v hne} where
  toFun T := ⟨T.val, (columnEquations_iff_inducedTarget i W Z X₀ v hne T.val).mp T.property⟩
  invFun T := ⟨T.val, (columnEquations_iff_inducedTarget i W Z X₀ v hne T.val).mpr T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional F2 H'] in
theorem finrank_projectedColumns_le [FiniteDimensional F2 Z] :
    Module.finrank F2 (ProjectedColumnSlice.projectedColumns i Z) ≤ Module.finrank F2 Z :=
  ProjectedColumnSlice.finrank_projectedColumns_le i Z


variable {ℓ : Nat} (R : Submodule F2 (Fin ℓ → F2))

theorem includedEvaluation_eq_tensorOutputLinear (q : Module.Dual F2 H') :
    R.subtype.comp ((LinearMap.applyₗ (R := F2) q).comp
      (TensorRestriction.tensorEquivHom (W := R) (H := H')).toLinearMap) =
      TensorBucketEvaluation.tensorOutputLinear R q := by
  apply TensorProduct.ext'
  intro w h
  change (TensorRestriction.tensorEquivHom (w ⊗ₜ[F2] h) q : Fin ℓ → F2) =
    TensorBucketEvaluation.tensorOutput R q (w ⊗ₜ[F2] h)
  rw [TensorRestriction.tensorEquivHom_tmul, TensorBucketEvaluation.tensorOutput_tmul]
  rfl

theorem includedEvaluation_eq_tensorOutput (q : Module.Dual F2 H')
    (T : R ⊗[F2] H') :
    (TensorRestriction.tensorEquivHom T q : Fin ℓ → F2) =
      TensorBucketEvaluation.tensorOutput R q T :=
  LinearMap.congr_fun (includedEvaluation_eq_tensorOutputLinear R q) T

theorem prediction_eq_visible_add_tensorOutput
    (X₀ : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2))
    (T : R ⊗[F2] H') (z : Module.Dual F2 H) (u : Fin ℓ → F2) :
    totalMatrix i R X₀ T z + u =
      (X₀ z + u) + TensorBucketEvaluation.tensorOutput R (i.dualMap z) T := by
  rw [totalMatrix_apply, includedEvaluation_eq_tensorOutput]
  exact add_right_comm _ _ _

end
end PerfectCompleteness.TensorProjectedSlice



namespace PerfectCompleteness.HierarchicalTensorMatrix

noncomputable section

open scoped BigOperators TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (W : Submodule F2 (Block rows upper))

def visibleMatrix
    (known : HiddenBucketBias.VisibleDirection W → NodeEmbedding.NodeH slots upper) :
    Module.Dual F2 (NodeEmbedding.RowSpace slots upper) →ₗ[F2] Block rows upper :=
  ∑ v : HiddenBucketBias.VisibleDirection W,
    (Module.Dual.eval F2 (NodeEmbedding.RowSpace slots upper)
      (NodeEmbedding.embed slots upper (known v))).smulRight v.val.val

theorem visibleMatrix_apply
    (known : HiddenBucketBias.VisibleDirection W → NodeEmbedding.NodeH slots upper)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    visibleMatrix slots upper W known q =
      ∑ v : HiddenBucketBias.VisibleDirection W,
        (q.comp (NodeEmbedding.embed slots upper)) (known v) • v.val.val := by
  simp only [visibleMatrix, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rfl

variable {Ω : Type*} (eval : Ω → NodeEmbedding.NodeH slots upper)
  (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)

theorem matrix_eq_totalMatrix (arrays : Arrays slots rows)
    (hrows : BucketSampler.evaluate (rows (Nodes.height upper)) eval tape = arrays upper) :
    NodeEmbedding.matrix arrays upper =
      TensorProjectedSlice.totalMatrix (NodeEmbedding.embed slots upper) W
        (visibleMatrix slots upper W
          (fun v => eval ((HiddenBucketBias.splitTape W Ω tape).2 v)))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) := by
  apply LinearMap.ext
  intro q
  calc
    NodeEmbedding.matrix arrays upper q =
        (fun i => (q.comp (NodeEmbedding.embed slots upper)) (arrays upper i)) := rfl
    _ = (fun i => (q.comp (NodeEmbedding.embed slots upper))
        (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape i)) := by rw [hrows]
    _ = TensorBucketEvaluation.visibleOutput W (q.comp (NodeEmbedding.embed slots upper))
          eval (HiddenBucketBias.splitTape W Ω tape).2 +
        TensorBucketEvaluation.tensorOutput W (q.comp (NodeEmbedding.embed slots upper))
          (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) :=
      TensorBucketEvaluation.evaluate_splitTape W (q.comp (NodeEmbedding.embed slots upper)) eval tape
    _ = _ := by
      rw [TensorProjectedSlice.totalMatrix_apply,
        TensorProjectedSlice.includedEvaluation_eq_tensorOutput, visibleMatrix_apply]
      rfl

theorem prediction_eq_visible_add_tensorOutput (arrays : Arrays slots rows)
    (hrows : BucketSampler.evaluate (rows (Nodes.height upper)) eval tape = arrays upper)
    (z : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) (u : Block rows upper) :
    NodeEmbedding.matrix arrays upper z + u =
      (visibleMatrix slots upper W
        (fun v => eval ((HiddenBucketBias.splitTape W Ω tape).2 v)) z + u) +
      TensorBucketEvaluation.tensorOutput W
        (z.comp (NodeEmbedding.embed slots upper))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) := by
  rw [matrix_eq_totalMatrix slots upper W eval tape arrays hrows]
  exact TensorProjectedSlice.prediction_eq_visible_add_tensorOutput
    (NodeEmbedding.embed slots upper) W _ _ z u

end
end PerfectCompleteness.HierarchicalTensorMatrix



namespace PerfectCompleteness.TensorTargetCharacter

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open TensorCosetEvaluation (pureFrequency)

variable {ℓ : Nat} {H : Type*} [AddCommGroup H] [Module F2 H]

theorem comp_tensorOutputLinear (W : Submodule F2 (Fin ℓ → F2))
    (σ : Module.Dual F2 (Fin ℓ → F2)) (z : Module.Dual F2 H) :
    σ.comp (TensorBucketEvaluation.tensorOutputLinear W z) =
      pureFrequency (σ.comp W.subtype) z := by
  apply TensorProduct.ext'
  intro w h
  change σ (TensorBucketEvaluation.tensorOutput W z (w ⊗ₜ[F2] h)) =
    pureFrequency (σ.comp W.subtype) z (w ⊗ₜ[F2] h)
  rw [TensorBucketEvaluation.tensorOutput_tmul,
    TensorCosetEvaluation.pureFrequency_tmul, map_smul]
  change z h * σ w.val = σ w.val * z h
  exact mul_comm _ _

theorem apply_tensorOutput (W : Submodule F2 (Fin ℓ → F2))
    (σ : Module.Dual F2 (Fin ℓ → F2)) (z : Module.Dual F2 H)
    (X : W ⊗[F2] H) :
    σ (TensorBucketEvaluation.tensorOutput W z X) =
      pureFrequency (σ.comp W.subtype) z X :=
  LinearMap.congr_fun (comp_tensorOutputLinear W σ z) X

theorem character_affine_tensorOutput (W : Submodule F2 (Fin ℓ → F2))
    (χ : AddChar F2 ℝ) (σ : Module.Dual F2 (Fin ℓ → F2))
    (z : Module.Dual F2 H) (offset : Fin ℓ → F2) (X : W ⊗[F2] H) :
    χ (σ (offset + TensorBucketEvaluation.tensorOutput W z X)) =
      χ (σ offset) * χ (pureFrequency (σ.comp W.subtype) z X) := by
  rw [map_add, apply_tensorOutput, χ.map_add_eq_mul]

theorem sign_affine_tensorOutput (W : Submodule F2 (Fin ℓ → F2))
    (σ : Module.Dual F2 (Fin ℓ → F2)) (z : Module.Dual F2 H)
    (offset : Fin ℓ → F2) (X : W ⊗[F2] H) :
    HiddenBucketBias.signCharacter
        (σ (offset + TensorBucketEvaluation.tensorOutput W z X)) =
      HiddenBucketBias.signCharacter (σ offset) *
        HiddenBucketBias.signCharacter (pureFrequency (σ.comp W.subtype) z X) :=
  character_affine_tensorOutput W HiddenBucketBias.signCharacter σ z offset X

end
end PerfectCompleteness.TensorTargetCharacter

end OAI
