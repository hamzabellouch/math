import OAI.Probability.DilutedSpin.FirstSplitSchedule
import OAI.Probability.DilutedSpin.ProjectionShiftError
import OAI.Probability.DilutedSpin.RootMultileafMatrix

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω α I : Type} [Fintype Ω] [Fintype α] [DecidableEq α]
  [Fintype I] [DecidableEq I] {N : ℕ}

/-- The actual delayed target's own projection is the shifted scheduled
proper-child product. No identification of independent pairs of assignments. -/
lemma delayed_target_projector (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r+d+1≤q j v)
    (T : KernelTower Ω (H+1+r+1+d))
    (f : FinitePath Ω (H+1+r+1+d) → Fin N → ℝ) :
    (fun x i => PrescribedTree.splitProjector
      (.node k (fun j => realize H (r+1+d+1) (C j) (fun v => q j v+1)))
      r d T (fun y => f y i) x)=
    conditionalScheduledProduct (H+1+r+1+d) 0 (r+1+d) C (fun j v => q j v+1) T f := by
  have h := scheduled_splitProjector_product H r d k hk C (fun j v => q j v+1)
    (fun j v => by have := hq j v; omega) T f
  simpa only [realize,rootSchedule,lt_self_iff_false,ite_false] using h

omit [Fintype α] [DecidableEq α] in
/-- Bound the literal target error in the signed matrix identity by proper
children and the ONE extension-uniform h_N on the SAME full depth cube.
Target leaf labels may be any bijective spatial-multioverlap enumeration. -/
theorem delayed_target_projection_le (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+r+1+d)) (ha : (Q a).val=r+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (T : KernelTower Ω (H+1+r+1+d))
    (f : FinitePath Ω (H+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    let Child := fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let S := PrescribedTree.node k Child
    let Target := PrescribedTree.splitFrame S r d
    ∀ (b : S.Leaf) (q : I → Target.Leaf), Function.Bijective q →
      ∀ (u v : I), q u=PrescribedTree.splitFrameLeaf S r d 0 b →
        q v=PrescribedTree.splitFrameLeaf S r d 1 b →
    PrescribedTree.matrixProjectionError Target q T u v
      (PrescribedTree.spatialProduct (fun _ : I => f))
      (conditionalScheduledProduct (H+1+r+1+d) 0 (Q a).val C
        (fun j w => (Q (e j w)).val) T f) ≤
      2*Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (PrescribedTree.descendantEnergyAt (Child j) r d T f))+
        projectionShiftError a C e T f Q := by
  dsimp only
  intro b q hq u v hu hv
  let Child := fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let S := PrescribedTree.node k Child
  let Target := PrescribedTree.splitFrame S r d
  have hp := delayed_target_projector H r d k hk C (fun j w => (Q (e j w)).val)
    (fun j w => by rw [← ha]; exact hQ j w) T f
  have hown := PrescribedTree.matrixProjectionError_prefixed_le k Child b r d q hq T u v hu hv f hf
  change (fun x i => PrescribedTree.splitProjector S r d T (fun y => f y i) x)=_ at hp
  rw [hp] at hown
  have hdepth : r+1+d=(Q a).val+1 := by omega
  rw [hdepth] at hown
  let : NeZero (H+1+r+1+d) := ⟨by omega⟩
  exact (matrixProjectionError_shift_le a C e T f hf Q Target q u v
    (PrescribedTree.spatialProduct (fun _ : I => f))).trans (add_le_add hown le_rfl)

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass.DepthAverage
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
noncomputable local instance rootProjectionShiftErrorDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_le_sqrt_average_sq (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (hF : ∀ Q, D Q → 0≤F Q) : average D F≤Real.sqrt (average D (fun Q => (F Q)^2)) := by
  have h := FiniteLaw.expect_sqrt_le (depthLaw α L)
    (fun Q => if D Q then (F Q)^2 else 0) (fun Q => by split_ifs <;> positivity)
  have he : (fun Q => Real.sqrt (if D Q then (F Q)^2 else 0))=(fun Q => if D Q then F Q else 0) := by
    funext Q
    split_ifs with hQ
    · exact Real.sqrt_sq (hF Q hQ)
    · exact Real.sqrt_zero
  rw [he] at h
  exact h

lemma integrable_average {Z : Type} [MeasurableSpace Z] {μ : Measure Z}
    (D : (α → Fin L) → Prop) (F : Z → (α → Fin L) → ℝ)
    (hF : ∀ Q, Integrable (fun z => F z Q) μ) : Integrable (fun z => average D (F z)) μ := by
  unfold average FiniteLaw.expect
  apply integrable_finsetSum
  intro Q _
  by_cases hQ : D Q
  · simpa only [ite_eq_left hQ] using (hF Q).const_mul ((depthLaw α L).weight Q)
  · simp only [ite_eq_right hQ,mul_zero]
    exact integrable_zero Z ℝ μ

lemma integral_average {Z : Type} [MeasurableSpace Z] {μ : Measure Z}
    (D : (α → Fin L) → Prop) (F : Z → (α → Fin L) → ℝ)
    (hF : ∀ Q, Integrable (fun z => F z Q) μ) :
    (∫ z, average D (F z) ∂μ)=average D (fun Q => ∫ z, F z Q ∂μ) := by
  have hG (Q : α → Fin L) : Integrable (fun z => if D Q then F z Q else 0) μ := by
    by_cases hQ : D Q
    · simpa only [ite_eq_left hQ] using hF Q
    · simp only [ite_eq_right hQ]; exact integrable_zero Z ℝ μ
  unfold average FiniteLaw.expect
  rw [integral_finsetSum Finset.univ (fun Q _ => (hG Q).const_mul _)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hQ : D Q <;> simp only [hQ,ite_true,ite_false,integral_zero]

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] {L N : ℕ} [NeZero L]

theorem averaged_projectionShiftError_le {Ω : Type} [Fintype Ω]
    (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (projectionShiftError a C e T f) ≤
      Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(Fintype.card ι:ℝ)^2)/(L:ℝ)) :=
  (DepthAverage.average_le_sqrt_average_sq D _ (fun Q _ => projectionShiftError_nonneg a C e T f Q)).trans
    (Real.sqrt_le_sqrt (averaged_projectionShiftError_sq_le a C e he η hlarge D hD T f hf))

/-- The SAME normalized-cube estimate survives genuine physical-root
averaging with no uniformity loss. The root law may have a variable finite
alphabet. Only ordinary Bochner integrability is required. -/
theorem root_averaged_projectionShiftError_le {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : (z : Z) → KernelTower (Ω z) L)
    (f : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hf : ∀ z x i, |f z x i|≤1)
    (hI : ∀ Q, Integrable (fun z => projectionShiftError a C e (T z) (f z) Q) μ) :
    DepthAverage.average D (fun Q => ∫ z, projectionShiftError a C e (T z) (f z) Q ∂μ) ≤
      Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(Fintype.card ι:ℝ)^2)/(L:ℝ)) := by
  rw [← DepthAverage.integral_average D _ hI]
  have h := integral_mono (DepthAverage.integrable_average D _ hI) (integrable_const _) (fun z =>
    averaged_projectionShiftError_le a C e he η hlarge D hD (T z) (f z) (hf z))
  simpa only [integral_const,probReal_univ,one_smul] using h

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
