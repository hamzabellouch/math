import OAI.Probability.DilutedSpin.ConditionalScheduledMean
import OAI.Probability.DilutedSpin.FirstSplitSchedule

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Single-copy spatial squared distance of two actual conditional means. -/
noncomputable def projectorChangeSq {M : ℕ} (T : KernelTower Ω M)
    (X Y : FinitePath Ω M → Fin N → ℝ) : ℝ :=
  (KernelTower.law M T).expect (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))

lemma projectorChangeSq_nonneg {M : ℕ} (T : KernelTower Ω M)
    (X Y : FinitePath Ω M → Fin N → ℝ) : 0≤projectorChangeSq T X Y :=
  FiniteLaw.expect_nonneg _ (fun _ => FiniteLaw.spatialSq_nonneg _)

lemma projectorChangeSq_symm {M : ℕ} (T : KernelTower Ω M)
    (X Y : FinitePath Ω M → Fin N → ℝ) : projectorChangeSq T X Y=projectorChangeSq T Y X := by
  unfold projectorChangeSq FiniteLaw.spatialSq
  simp_rw [sub_sq_comm]

lemma projectorChangeSq_triangle {M : ℕ} (T : KernelTower Ω M)
    (X Y Z : FinitePath Ω M → Fin N → ℝ) :
    projectorChangeSq T X Z≤2*(projectorChangeSq T X Y+projectorChangeSq T Y Z) := by
  have h := (KernelTower.law M T).expect_mono (fun x => show
      FiniteLaw.spatialSq (fun i => X x i-Z x i)≤
      2*(FiniteLaw.spatialSq (fun i => X x i-Y x i)+FiniteLaw.spatialSq (fun i => Y x i-Z x i)) from by
    unfold FiniteLaw.spatialSq
    calc
      _ ≤ (∑ i, 2*((X x i-Y x i)^2+(Y x i-Z x i)^2))/(N:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (X x i-2*Y x i+Z x i)]
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; ring)
  simpa only [FiniteLaw.expect_mul_left,FiniteLaw.expect_add,projectorChangeSq] using h

variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

/-- Fixed-prefix simultaneous child-shift continuity, stated on the actual
full-horizon conditional products. The horizon equality is a reindexing only. -/
theorem averaged_conditional_schedule_change_le (M H p : ℕ) (htotal : M=H+p)
    (hheight : p+H=L) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (he : ∀ j, Function.Injective (e j))
    (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : (j : ι) → (C j).Vertex → Bool)
    (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (τ j v (Q (e j v))).val) p L ∧
      DepthAverage.Regular η (DepthAverage.coordinateProjection (e j) (τ j) Q))
    (T : KernelTower Ω M) (f : FinitePath Ω M → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct M 0 p C (fun j v => (τ j v (Q (e j v))).val) T f)
      (conditionalScheduledProduct M 0 p C
        (fun j v => (DepthAverage.shiftPerm (s j v) (τ j v (Q (e j v)))).val) T f)) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  subst M
  have hu (Q : α → Fin L) :
      conditionalScheduledProduct (H+p) 0 p C (fun j v => (τ j v (Q (e j v))).val) T f=
      childScheduleProjection H p p C e τ (fun _ _ => false) T f Q := by
    simpa only [DepthAverage.shiftPerm,Bool.false_eq_true,ite_false,Equiv.refl_apply] using
      conditionalScheduledProduct_eq_childSchedule H p C e τ (fun _ _ => false) Q T f
  simp_rw [hu,conditionalScheduledProduct_eq_childSchedule]
  exact averaged_childScheduleProjection_change_le H p p hheight C e he τ η hlarge s D hD T f hf

omit [NeZero L] in
/-- Full-horizon evaluation martingale energy before the first child split,
in the actual single-copy spatial norm, with arbitrary retained subdomain. -/
theorem conditional_evaluation_sum_le (M n r : ℕ) (htotal : M=n+r)
    (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r≤q j v) (U : Finset (Fin r))
    (T : KernelTower Ω M) (f : FinitePath Ω M → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    (∑ t ∈ U, projectorChangeSq T
      (conditionalScheduledProduct M 0 (t.val+1) C q T f)
      (conditionalScheduledProduct M 0 t.val C q T f))/(L:ℝ) ≤ (Fintype.card ι:ℝ)^2/(L:ℝ) := by
  subst M
  have hq' : ∀ j v, 0+r≤q j v := by simpa only [Nat.zero_add] using hq
  have hs (t : Fin r) : conditionalScheduledProduct (n+r) 0 (t.val+1) C q T f=
      PrescribedTree.productStemMeanAt (fun j => realize n r (C j) (q j)) r t.succ T f := by
    have h := (conditionalScheduledProduct_eq_prefix n r 0 C q t.succ T f).trans
      (scheduledProductMean_eq n r 0 C q hq' t.succ T f)
    simpa only [Nat.zero_add,Fin.val_succ] using h
  have hb (t : Fin r) : conditionalScheduledProduct (n+r) 0 t.val C q T f=
      PrescribedTree.productStemMeanAt (fun j => realize n r (C j) (q j)) r t.castSucc T f := by
    have h := (conditionalScheduledProduct_eq_prefix n r 0 C q t.castSucc T f).trans
      (scheduledProductMean_eq n r 0 C q hq' t.castSucc T f)
    simpa only [Nat.zero_add,Fin.val_castSucc] using h
  simp_rw [hs,hb]
  unfold projectorChangeSq
  simp_rw [PrescribedTree.productStemMeanAt_spatial_increment]
  exact PrescribedTree.averaged_productStemIncrement_spatial_le
    (fun j => realize n r (C j) (q j)) r L U T f hf

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
