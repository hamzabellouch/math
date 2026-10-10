import OAI.Probability.DilutedSpin.SimultaneousShift

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance spatialScheduledContinuityDepthDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_div (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ) :
    average D (fun q => F q/c)=average D F/c := by
  unfold average
  rw [← FiniteLaw.expect_div]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

lemma average_sum {ι : Type*} [Fintype ι] (D : (α → Fin L) → Prop)
    (F : ι → (α → Fin L) → ℝ) :
    average D (fun q => ∑ i, F i q)=∑ i, average D (F i) := by
  unfold average
  rw [← FiniteLaw.expect_fintype_sum]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
noncomputable local instance spatialScheduledContinuityReducedDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {L N : ℕ} [NeZero L]

/-- Actual normalized spatial squared norm of the conditional-mean change.
Both schedules use the same ancestral kernel and spin function. -/
noncomputable def spatialScheduleChange (H d : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (q : S.Vertex → Fin L) : ℝ :=
  (∑ i : Fin N,
    (PrescribedTree.treeMean (realize H d S (fun v => (q v).val)) T (fun x => f x i)-
     PrescribedTree.treeMean (realize H d S
       (fun v => (DepthAverage.shiftPerm (s v) (q v)).val)) T (fun x => f x i))^2)/(N:ℝ)

omit [NeZero L] in
lemma spatialScheduleChange_nonneg (H d : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (q : S.Vertex → Fin L) :
    0 ≤ spatialScheduleChange H d S s T f q := by
  unfold spatialScheduleChange
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-- Full vector-valued branching-depth part of decor:depth-continuity.
The constant b*sum(arity²) is independent of N, all transition kernels and
the spin function. N=0 obeys the same inequality without an extra hypothesis. -/
theorem averaged_spatialScheduleChange_le (H d : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (spatialScheduleChange H d S s T f) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  classical
  unfold spatialScheduleChange
  rw [DepthAverage.average_div,DepthAverage.average_sum]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    averaged_simultaneous_shift_le H d hheight S η hlarge s D hD T (fun x => f x i) (fun x => hf x i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,div_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (Nat.cast_nonneg _)
  · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    nlinarith [hh]

/-- Uniformity survives the ACTUAL law of any already sampled ancestral
prefix; it can even have prefix-dependent finite alphabets. -/
theorem prefix_averaged_spatialScheduleChange_le {Z : Type} [Fintype Z] (P : FiniteLaw Z)
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (H d : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : (z : Z) → KernelTower (Ω z) H) (f : (z : Z) → FinitePath (Ω z) H → Fin N → ℝ)
    (hf : ∀ z x i, |f z x i|≤1) :
    P.expect (fun z => DepthAverage.average D (spatialScheduleChange H d S s (T z) (f z))) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  calc
    _ ≤ P.expect (fun _ => (Fintype.card S.Vertex:ℝ)*
        (∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ)) :=
      P.expect_mono (fun z => averaged_spatialScheduleChange_le H d hheight S η hlarge s D hD
        (T z) (f z) (hf z))
    _ = _ := P.expect_const _

/-- The same estimate after arbitrary probability root averaging. Only
ordinary integrability is requested; the bounded error is computed from
literal trees, not introduced as an abstract error variable. -/
theorem root_averaged_spatialScheduleChange_le {Z : Type} [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Z) [MeasureTheory.IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (H d : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : (z : Z) → KernelTower (Ω z) H) (f : (z : Z) → FinitePath (Ω z) H → Fin N → ℝ)
    (hf : ∀ z x i, |f z x i|≤1)
    (hI : MeasureTheory.Integrable
      (fun z => DepthAverage.average D (spatialScheduleChange H d S s (T z) (f z))) μ) :
    (∫ z, DepthAverage.average D (spatialScheduleChange H d S s (T z) (f z)) ∂μ) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  calc
    _ ≤ ∫ _ : Z, (Fintype.card S.Vertex:ℝ)*
        (∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) ∂μ :=
      MeasureTheory.integral_mono hI (MeasureTheory.integrable_const _) (fun z =>
        averaged_spatialScheduleChange_le H d hheight S η hlarge s D hD (T z) (f z) (hf z))
    _ = _ := by simp

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
