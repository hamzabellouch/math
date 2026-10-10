import OAI.Probability.SwitchChain.SliceProjectionComparison

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

def pullback {q : ℕ} (e : Ω ≃ State V q) :
    Space V q ≃ₗᵢ[ℝ] EuclideanSpace ℝ Ω :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

include sectionDecidableEqV in
@[simp] theorem pullback_apply {q : ℕ} (e : Ω ≃ State V q)
    (f : Space V q) (ω : Ω) : pullback e f ω = f (e ω) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def reindexedRaw {q : ℕ} (e : Ω ≃ State V q) (i j : V) :
    EuclideanSpace ℝ Ω := pullback e (raw q i j)

@[simp] theorem reindexedRaw_apply {q : ℕ} (e : Ω ≃ State V q)
    (i j : V) (ω : Ω) :
    reindexedRaw e i j ω = if i = j then 0 else
      SliceMoments.centeredEqual Finset.univ q i j (e ω).val := rfl

def reindexedMove {q : ℕ} (e : Ω ≃ State V q) (i j : V)
    (f : EuclideanSpace ℝ Ω) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun ω => f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω))))

include sectionFintypeΩ in
@[simp] theorem reindexedMove_apply {q : ℕ} (e : Ω ≃ State V q)
    (i j : V) (f : EuclideanSpace ℝ Ω) (ω : Ω) :
    reindexedMove e i j f ω =
      f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω))) := by
  have retainedsectionFintypeΩ := sectionFintypeΩ
  exact rfl

 theorem pullback_move {q : ℕ} (e : Ω ≃ State V q) (i j : V) (f : Space V q) :
    pullback e (SliceEuclideanGenerator.moveOperator q i j f) =
      reindexedMove e i j (pullback e f) := by
  ext ω
  simp

include sectionDecidableEqV in
 theorem norm_projection_pullback {q : ℕ} (e : Ω ≃ State V q)
    (z f : Space V q) :
    ‖(ℝ ∙ pullback e z).starProjection (pullback e f)‖ =
      ‖(ℝ ∙ z).starProjection f‖ := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  rw [Submodule.starProjection_singleton, Submodule.starProjection_singleton]
  simp only [norm_smul, (pullback e).inner_map_map, (pullback e).norm_map]

 theorem reindexed_projection_energy_le_swap_energy {q : ℕ}
    (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V) (f : EuclideanSpace ℝ Ω) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j, ‖f - reindexedMove e i j f‖ ^ 2 := by
  let g : Space V q := (pullback e).symm f
  have hfg : pullback e g = f := (pullback e).apply_symm_apply f
  have hp (i j : V) : ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 =
      ‖(ℝ ∙ raw q i j).starProjection g‖ ^ 2 := by
    rw [← hfg]
    exact congrArg (fun t : ℝ => t^2) (norm_projection_pullback e (raw q i j) g)
  have hm (i j : V) : ‖f - reindexedMove e i j f‖ ^ 2 =
      ‖g - SliceEuclideanGenerator.moveOperator q i j g‖ ^ 2 := by
    rw [← hfg, ← pullback_move, ← map_sub, (pullback e).norm_map]
  simp_rw [hp, hm]
  exact projection_energy_le_swap_energy q hq g

 theorem reindexed_projection_energy_le_swap_sum {q : ℕ}
    (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V) (f : EuclideanSpace ℝ Ω) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j, ∑ ω : Ω,
        (f ω - f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω)))) ^ 2 := by
  have h := reindexed_projection_energy_le_swap_energy e hq f
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, reindexedMove_apply] using h

end Problem315.SliceNormalized

end

end OAI
