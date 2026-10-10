import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions
import Mathlib.Analysis.InnerProductSpace.TensorProduct

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped InnerProductSpace TensorProduct ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def elementary (f : HilbertSum G ℂ) (v : H) : HilbertSum G H :=
  lp.mapCLM 2 (fun _ => (1 : ℂ →L[ℂ] ℂ).smulRight v) (norm_nonneg v)
    (fun _ => by simp [ContinuousLinearMap.norm_smulRight_apply]) f

@[simp] lemma elementary_apply (f : HilbertSum G ℂ) (v : H) (g : G) :
    elementary f v g = (f g) • v := rfl

lemma elementary_inner (f f' : HilbertSum G ℂ) (v v' : H) :
    inner ℂ (elementary f v) (elementary f' v') = inner ℂ f f' * inner ℂ v v' := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum,← tsum_mul_right]
  apply tsum_congr; intro g
  simp [inner_smul_left,inner_smul_right,RCLike.inner_apply,mul_comm,mul_left_comm]

def elementaryBilinear : HilbertSum G ℂ →ₗ[ℂ] H →ₗ[ℂ] HilbertSum G H where
  toFun f := {
    toFun := elementary f
    map_add' v w := by ext; simp [smul_add]
    map_smul' c v := by ext g; exact smul_comm (f g) c v }
  map_add' f h := by ext; simp [add_smul]
  map_smul' c f := by ext; simp [mul_smul]

def tensorToSum : (HilbertSum G ℂ ⊗[ℂ] H) →ₗ[ℂ] HilbertSum G H :=
  TensorProduct.lift elementaryBilinear
@[simp] lemma tensorToSum_tmul (f : HilbertSum G ℂ) (v : H) :
    tensorToSum (f ⊗ₜ[ℂ] v) = elementary f v := rfl

lemma tensorToSum_inner (x y : HilbertSum G ℂ ⊗[ℂ] H) :
    inner ℂ (tensorToSum x) (tensorToSum y) = inner ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul f v =>
    induction y using TensorProduct.inductionOn with
    | tmul g w => simpa using elementary_inner f g v w
    | add y z hy hz => simp only [map_add,inner_add_right]; rw [hy,hz]
  | add x z hx hz => simp only [map_add,inner_add_left]; rw [hx,hz]

def tensorToSumIsometry : (HilbertSum G ℂ ⊗[ℂ] H) →ₗᵢ[ℂ] HilbertSum G H :=
  { tensorToSum with
    norm_map' := fun x => by
      have h := tensorToSum_inner x x
      have hh := congrArg Complex.re h
      change RCLike.re (inner ℂ (tensorToSum x) (tensorToSum x)) = RCLike.re (inner ℂ x x) at hh
      rw [inner_self_eq_norm_sq (tensorToSum x),inner_self_eq_norm_sq (𝕜:=ℂ) x] at hh
      nlinarith [norm_nonneg (tensorToSum x),norm_nonneg x] }

lemma elementary_delta (g : G) (v : H) : elementary (lp.single 2 g (1:ℂ)) v = lp.single (E:=fun _ : G => H) 2 g v := by
  classical
  ext k
  by_cases hg : k=g
  · subst k; simp [lp.single_apply]
  · simp [lp.single_apply,hg]

lemma tensorToSum_dense : DenseRange (tensorToSumIsometry (G:=G) (H:=H)) := by
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ g ∈ s, (lp.single 2 g (1:ℂ)) ⊗ₜ[ℂ] (x g),?_⟩
  simp only [map_sum]
  apply Finset.sum_congr rfl; intro g _
  exact elementary_delta g (x g)

abbrev HilbertTensor := UniformSpace.Completion (HilbertSum G ℂ ⊗[ℂ] H)

variable [CompleteSpace H]

def tensorCompletionMap : HilbertTensor (G:=G) (H:=H) →L[ℂ] HilbertSum G H :=
  tensorToSumIsometry.toContinuousLinearMap.extend UniformSpace.Completion.toComplL

@[simp] lemma tensorCompletionMap_coe (x : HilbertSum G ℂ ⊗[ℂ] H) :
    tensorCompletionMap (x : HilbertTensor (G:=G) (H:=H)) = tensorToSum x := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) x

def tensorCompletionIsometry : HilbertTensor (G:=G) (H:=H) →ₗᵢ[ℂ] HilbertSum G H :=
  { tensorCompletionMap.toLinearMap with
    norm_map' := fun x => by
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (continuous_norm.comp tensorCompletionMap.continuous) continuous_norm
      | ih x =>
          change ‖tensorCompletionMap (x : HilbertTensor (G:=G) (H:=H))‖ = _
          rw [tensorCompletionMap_coe,UniformSpace.Completion.norm_coe]
          exact tensorToSumIsometry.norm_map x }

lemma tensorCompletionIsometry_surjective : Function.Surjective (tensorCompletionIsometry (G:=G) (H:=H)) := by
  intro x
  have hc := (tensorCompletionIsometry (G:=G) (H:=H)).isometry.isClosedEmbedding.isClosed_range
  have hs : Set.range (tensorToSumIsometry (G:=G) (H:=H)) ⊆ Set.range tensorCompletionIsometry := by
    rintro _ ⟨y,rfl⟩
    exact ⟨(y : HilbertTensor (G:=G) (H:=H)),tensorCompletionMap_coe y⟩
  exact (closure_minimal hs hc) (tensorToSum_dense x)

def tensorHilbertEquiv : HilbertTensor (G:=G) (H:=H) ≃ₗᵢ[ℂ] HilbertSum G H :=
  LinearIsometryEquiv.ofSurjective tensorCompletionIsometry tensorCompletionIsometry_surjective

@[simp] lemma tensorHilbertEquiv_tmul (f : HilbertSum G ℂ) (v : H) :
    tensorHilbertEquiv ((f ⊗ₜ[ℂ] v) : HilbertTensor (G:=G) (H:=H)) = elementary f v :=
  tensorCompletionMap_coe _

omit [CompleteSpace H] in
lemma diagonal_elementary (T : H →L[ℂ] H) (f : HilbertSum G ℂ) (v : H) :
    diagonal T (elementary f v) = elementary f (T v) := by
  ext g
  exact T.map_smul (f g) v

omit [CompleteSpace H] in
lemma left_elementary [Group G] (g : G) (f : HilbertSum G ℂ) (v : H) :
    left g (elementary f v) = elementary (left g f) v := by ext; rfl


end KaplanskyConsequences.Regular

end

end OAI
