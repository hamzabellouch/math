import OAI.Probability.DilutedSpin.RootMultileafMatrix
import OAI.Probability.DilutedSpin.TargetScheduleContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- Bounded products are Lipschitz in the actual normalized spatial norm,
including the empty spatial dimension convention. -/
lemma spatialSq_product_difference_le (X Y : ι → Fin N → ℝ)
    (hX : ∀ j i, |X j i|≤1) (hY : ∀ j i, |Y j i|≤1) :
    spatialSq (fun i => (∏ j, X j i)-(∏ j, Y j i)) ≤
      (Fintype.card ι:ℝ)*∑ j, spatialSq (fun i => X j i-Y j i) := by
  unfold spatialSq
  calc
    _ ≤ (∑ i, (Fintype.card ι:ℝ)*∑ j, (X j i-Y j i)^2)/(N:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ =>
        bounded_product_difference_sq (fun j => X j i) (fun j => Y j i)
          (fun j => hX j i) (fun j => hY j i))) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      rw [mul_div_assoc,Finset.sum_div]

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- Exact proper-child factorization of the conditional first-split mean;
the unary child transition is retained, not erased. -/
lemma tailMean_node_product (k : ℕ+) (C : Fin k → PrescribedTree n) (p : ℕ)
    (T : KernelTower Ω (n+1+p)) (f : FinitePath Ω (n+1+p) → ℝ)
    (x : FinitePath Ω (n+1+p)) :
    tailMean (.node k C) p T f x=∏ j, tailMean (unary (C j)) p T f x := by
  induction p with
  | zero => simp only [tailMean,treeMean,treeMean_unary]
  | succ p ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) x.2

/-- The projector used in the signed multileaf matrix identity is literally
the product of proper-child conditional means on the SAME sampled prefix. -/
lemma splitProjector_node_product (k : ℕ+) (C : Fin k → PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → ℝ)
    (x : FinitePath Ω (n+1+r+1+d)) :
    splitProjector (.node k C) r d T f x=∏ j, splitProjector (unary (C j)) r d T f x := by
  induction d with
  | zero => exact tailMean_node_product k C (r+1) T f x
  | succ d ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) x.2

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance properChildSchedulePropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]

omit [NeZero L] in
lemma tailScheduleChange_nonneg (H d p : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (q : S.Vertex → Fin L) :
    0≤tailScheduleChange H d p S s T f q :=
  FiniteLaw.expect_nonneg _ (fun _ => FiniteLaw.spatialSq_nonneg _)

/-- Product of the actual proper-child schedule projectors, restricted from
the parent depth-assignment cube. Coordinates may be independently translated.
No independent sampling of aligned copies occurs in this definition. -/
noncomputable def childScheduleProjection (H d p : ℕ) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (s : (j : ι) → (C j).Vertex → Bool)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ)
    (q : α → Fin L) (x : FinitePath Ω (H+p)) (i : Fin N) : ℝ :=
  ∏ j, scheduledTailProjection H d p (C j)
    (fun v => DepthAverage.shiftPerm (s j v) (τ j v (q (e j v)))) T f x i

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma childScheduleProjection_bound (H d p : ℕ) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (s : (j : ι) → (C j).Vertex → Bool)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (q : α → Fin L) (x : FinitePath Ω (H+p)) (i : Fin N) :
    |childScheduleProjection H d p C e τ s T f q x i|≤1 := by
  unfold childScheduleProjection
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j _ =>
    scheduledTailProjection_bound H d p (C j) _ T f hf x i)

 
theorem averaged_childScheduleProjection_change_le (H d p : ℕ) (hheight : d+H=L)
    (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (he : ∀ j, Function.Injective (e j))
    (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : (j : ι) → (C j).Vertex → Bool)
    (D : (α → Fin L) → Prop)
    (hD : ∀ q, D q → ∀ j, Admissible (C j) (fun v => (τ j v (q (e j v))).val) d L ∧
      DepthAverage.Regular η (DepthAverage.coordinateProjection (e j) (τ j) q))
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun q => (KernelTower.law (H+p) T).expect (fun x =>
      FiniteLaw.spatialSq (fun i => childScheduleProjection H d p C e τ (fun _ _ => false) T f q x i-
        childScheduleProjection H d p C e τ s T f q x i))) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  have hp (q : α → Fin L) : (KernelTower.law (H+p) T).expect (fun x =>
      FiniteLaw.spatialSq (fun i => childScheduleProjection H d p C e τ (fun _ _ => false) T f q x i-
        childScheduleProjection H d p C e τ s T f q x i)) ≤
        (Fintype.card ι:ℝ)*∑ j, tailScheduleChange H d p (C j) (s j) T f
          (DepthAverage.coordinateProjection (e j) (τ j) q) := by
    have hh := (KernelTower.law (H+p) T).expect_mono (fun x =>
      FiniteLaw.spatialSq_product_difference_le
        (fun j => scheduledTailProjection H d p (C j) (fun v => τ j v (q (e j v))) T f x)
        (fun j => scheduledTailProjection H d p (C j) (fun v => DepthAverage.shiftPerm (s j v) (τ j v (q (e j v)))) T f x)
        (fun j => scheduledTailProjection_bound H d p (C j) _ T f hf x)
        (fun j => scheduledTailProjection_bound H d p (C j) _ T f hf x))
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at hh
    exact hh
  calc
    _ ≤ DepthAverage.average D (fun q => (Fintype.card ι:ℝ)*∑ j,
        tailScheduleChange H d p (C j) (s j) T f (DepthAverage.coordinateProjection (e j) (τ j) q)) :=
      DepthAverage.average_mono_on _ _ _ (fun q _ => hp q)
    _ = (Fintype.card ι:ℝ)*∑ j, DepthAverage.average D (fun q =>
        tailScheduleChange H d p (C j) (s j) T f (DepthAverage.coordinateProjection (e j) (τ j) q)) := by
      rw [DepthAverage.average_mul_left,DepthAverage.average_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      let E := fun y : (C j).Vertex → Fin L => Admissible (C j) (fun v => (y v).val) d L ∧
        DepthAverage.Regular η y
      exact (DepthAverage.fiber_bound (e j) (he j) (τ j) D E (fun q hq => hD q hq j)
        (tailScheduleChange H d p (C j) (s j) T f)
        (tailScheduleChange_nonneg H d p (C j) (s j) T f)).trans
          (averaged_tailScheduleChange_le H d p hheight (C j) η hlarge (s j) E
            (fun _ h => h) T f hf)

/-- Both target vectors may come from any joint history marginal on the
parent assignment cube. The bound is the same single-copy proper-child cost. -/
theorem averaged_childSchedule_target_change_le (H d p : ℕ) (hheight : d+H=L)
    (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (he : ∀ j, Function.Injective (e j))
    (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : (j : ι) → (C j).Vertex → Bool)
    (D : (α → Fin L) → Prop)
    (hD : ∀ q, D q → ∀ j, Admissible (C j) (fun v => (τ j v (q (e j v))).val) d L ∧
      DepthAverage.Regular η (DepthAverage.coordinateProjection (e j) (τ j) q))
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (Target : (α → Fin L) → PrescribedTree (H+p))
    (a b : (q : α → Fin L) → (Target q).Leaf) :
    DepthAverage.average D (fun q => PrescribedTree.targetContractionChangeSq (Target q) T (a q) (b q)
      (childScheduleProjection H d p C e τ (fun _ _ => false) T f q)
      (childScheduleProjection H d p C e τ s T f q)) ≤
      4*((Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ)) := by
  calc
    _ ≤ DepthAverage.average D (fun q => 4*(KernelTower.law (H+p) T).expect (fun x =>
        FiniteLaw.spatialSq (fun i => childScheduleProjection H d p C e τ (fun _ _ => false) T f q x i-
          childScheduleProjection H d p C e τ s T f q x i))) := by
      apply DepthAverage.average_mono_on
      intro q _
      exact PrescribedTree.targetContractionChangeSq_le (Target q) T (a q) (b q) _ _
        (childScheduleProjection_bound H d p C e τ _ T f hf q)
        (childScheduleProjection_bound H d p C e τ s T f hf q)
    _ = 4*DepthAverage.average D (fun q => (KernelTower.law (H+p) T).expect (fun x =>
        FiniteLaw.spatialSq (fun i => childScheduleProjection H d p C e τ (fun _ _ => false) T f q x i-
          childScheduleProjection H d p C e τ s T f q x i))) := DepthAverage.average_mul_left _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (averaged_childScheduleProjection_change_le H d p hheight C e he τ η hlarge s D hD T f hf)
      (by norm_num)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
