import OAI.Analysis.KadisonSimilarity.Representation.DenseStarRepresentation
import Mathlib.SetTheory.Cardinal.Free

namespace OAI

/-! # Operators from dense additive column data

Bounded additive data on a dense subgroup extends by uniform continuity.
Compatibility with multiplication by `i` makes the extension complex linear.
Only a countable dense subgroup is needed for the later AE construction.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology Pointwise NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace F] in
private theorem denseAdditive_uniformContinuous (S : AddSubgroup E)
    (f : S →+ F) (C : ℝ≥0) (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) :
    UniformContinuous f :=
  (AddMonoidHomClass.lipschitz_of_bound f C hnorm).uniformContinuous

/-- The additive extension of bounded data from a dense subgroup. -/
def denseAdditiveExtension (S : AddSubgroup E) (hdense : Dense (S : Set E))
    (f : S →+ F) (C : ℝ≥0) (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) : E →+ F where
  toFun := (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing
    hdense.denseRange_val).extend f
  map_zero' := by
    convert! IsDenseInducing.extend_eq
      (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing hdense.denseRange_val)
      (denseAdditive_uniformContinuous S f C hnorm).continuous (0 : S) using 1
    exact f.map_zero.symm
  map_add' := by
    have hc := (uniformContinuous_uniformly_extend
      isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
      (denseAdditive_uniformContinuous S f C hnorm)).continuous
    refine fun x y => hdense.denseRange_val.induction_on₂ ?_ (fun a b => ?_) x y
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [← AddSubgroup.coe_add]
      simp only [IsDenseInducing.extend_eq _
        (denseAdditive_uniformContinuous S f C hnorm).continuous, map_add]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
theorem denseAdditiveExtension_continuous (S : AddSubgroup E)
    (hdense : Dense (S : Set E)) (f : S →+ F) (C : ℝ≥0)
    (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) :
    Continuous (denseAdditiveExtension S hdense f C hnorm) :=
  (uniformContinuous_uniformly_extend
    isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
    (denseAdditive_uniformContinuous S f C hnorm)).continuous

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
@[simp] theorem denseAdditiveExtension_apply (S : AddSubgroup E)
    (hdense : Dense (S : Set E)) (f : S →+ F) (C : ℝ≥0)
    (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) (x : S) :
    denseAdditiveExtension S hdense f C hnorm x = f x :=
  IsDenseInducing.extend_eq
    (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing hdense.denseRange_val)
    (denseAdditive_uniformContinuous S f C hnorm).continuous x

omit [CompleteSpace F] in
/-- A continuous additive map that commutes with `i` is complex linear. -/
def continuousAdditiveToComplexLinear (f : E →+ F) (hf : Continuous f)
    (hI : ∀ x, f (Complex.I • x) = Complex.I • f x) : E →L[ℂ] F where
  toFun := f
  map_add' := f.map_add
  map_smul' z x := by
    change f (z • x) = z • f x
    have hr (r : ℝ) (y : E) : f ((r : ℂ) • y) = (r : ℂ) • f y := by
      calc
        f ((r : ℂ) • y) = f (r • y) :=
          congrArg f (RCLike.real_smul_eq_coe_smul (K := ℂ) r y).symm
        _ = r • f y := map_real_smul f hf r y
        _ = (r : ℂ) • f y := RCLike.real_smul_eq_coe_smul (K := ℂ) r (f y)
    rw [← Complex.re_add_im z]
    simp only [add_smul, map_add, mul_smul, hr, hI]
  cont := hf

/-- The bounded dense-subgroup data gives an operator of the same norm bound. -/
theorem exists_operator_of_dense_additive
    (S : AddSubgroup E) (hdense : Dense (S : Set E))
    (hIS : ∀ x ∈ S, Complex.I • x ∈ S) (f : S →+ F) (C : ℝ≥0)
    (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖)
    (hI : ∀ x : S, f ⟨Complex.I • x.val, hIS x.val x.property⟩ = Complex.I • f x) :
    ∃ T : E →L[ℂ] F, ‖T‖ ≤ C ∧ ∀ x : S, T x = f x := by
  let g := denseAdditiveExtension S hdense f C hnorm
  have hg : Continuous g := denseAdditiveExtension_continuous S hdense f C hnorm
  have hext : ∀ x : S, g x = f x := denseAdditiveExtension_apply S hdense f C hnorm
  have hgI : ∀ x, g (Complex.I • x) = Complex.I • g x := by
    intro x
    refine hdense.denseRange_val.induction_on
      (p := fun y => g (Complex.I • y) = Complex.I • g y) x
      (isClosed_eq (hg.comp (continuous_const.smul continuous_id))
        (continuous_const.smul hg)) ?_
    intro y
    calc
      g (Complex.I • (y : E)) = f ⟨Complex.I • y.val, hIS y.val y.property⟩ :=
        hext ⟨Complex.I • y.val, hIS y.val y.property⟩
      _ = Complex.I • f y := hI y
      _ = Complex.I • g (y : E) := congrArg (Complex.I • ·) (hext y).symm
  let T := continuousAdditiveToComplexLinear g hg hgI
  refine ⟨T, ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg ?_, hext⟩
  intro x
  refine hdense.denseRange_val.induction_on
    (p := fun y => ‖T y‖ ≤ C * ‖y‖) x
    (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro y
  change ‖g (y : E)‖ ≤ C * ‖(y : E)‖
  rw [hext y]
  exact hnorm y

theorem countable_addSubgroupClosure {G : Type*} [AddCommGroup G] {s : Set G}
    (hs : s.Countable) : (AddSubgroup.closure s : Set G).Countable := by
  let : Countable s := hs.to_subtype
  let f : FreeAbelianGroup s →+ G := FreeAbelianGroup.lift (fun x : s => (x : G))
  have hle : AddSubgroup.closure s ≤ f.range := (AddSubgroup.closure_le f.range).2 fun x hx => by
    exact ⟨FreeAbelianGroup.of ⟨x, hx⟩, FreeAbelianGroup.lift_apply_of _ _⟩
  exact (Set.countable_range f).mono hle

/-- A separable complex normed space has a countable dense additive subgroup
that is stable under multiplication by `i`. -/
theorem exists_countable_dense_complex_addSubgroup
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ S : AddSubgroup E, (S : Set E).Countable ∧ Dense (S : Set E) ∧
      ∀ x ∈ S, Complex.I • x ∈ S := by
  let s := Set.range (TopologicalSpace.denseSeq E)
  let t := s ∪ (fun x : E => Complex.I • x) '' s
  let S := AddSubgroup.closure t
  have hs : s.Countable := Set.countable_range _
  refine ⟨S, countable_addSubgroupClosure (hs.union (hs.image _)), ?_, ?_⟩
  · exact (TopologicalSpace.denseRange_denseSeq E).mono fun x hx =>
      AddSubgroup.subset_closure (Or.inl hx)
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact AddSubgroup.subset_closure (Or.inr ⟨x, hx, rfl⟩)
        · simpa only [smul_smul, Complex.I_mul_I, neg_one_smul] using
            (AddSubgroup.closure t).neg_mem (AddSubgroup.subset_closure (Or.inl hy))
    | zero => simpa only [smul_zero] using S.zero_mem
    | add x y _ _ hx hy => simpa only [smul_add] using S.add_mem hx hy
    | neg x _ hx => simpa only [smul_neg] using S.neg_mem hx

end KadisonSimilarity

end

end OAI
