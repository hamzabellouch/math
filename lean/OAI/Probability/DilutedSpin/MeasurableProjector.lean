import OAI.Probability.DilutedSpin.ProjectionShiftError
import OAI.Probability.DilutedSpin.TreeMeasurable

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z]

omit [Fintype Ω] in
lemma measurable_leafProduct {n : ℕ} (S : PrescribedTree n)
    {g : Z → FinitePath Ω n → ℝ} (hg : ∀ y, Measurable (fun z => g z y))
    (a : S.Sample Ω) : Measurable (fun z => leafProduct S (g z) a) := by
  simp_rw [leafProduct_eq_prod]
  exact Finset.measurable_prod _ (fun b _ => hg _)

lemma measurable_treeMean_tilt {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {f g : Z → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y)) :
    Measurable (fun z => treeMean S (KernelTower.tilt n T m (f z)) (g z)) := by
  simp_rw [treeMean_eq_expect]
  exact measurable_tilt_sample_expect S T m hf (measurable_leafProduct S hg)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma measurable_conditionalScheduledMean_tilt (H d e : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f g : Z → FinitePath Ω H → ℝ} (hf : ∀ y, Measurable (fun z => f z y))
    (hg : ∀ y, Measurable (fun z => g z y)) (x : FinitePath Ω H) :
    Measurable (fun z => conditionalScheduledMean H d e S q (KernelTower.tilt H T m (f z)) (g z) x) := by
  induction H generalizing d e with
  | zero => exact hg ()
  | succ H ih =>
    cases e with
    | zero => exact PrescribedTree.measurable_treeMean_tilt _ T m hf hg
    | succ e =>
        exact ih (d+1) e (T.2 x.1) (fun j => m j.succ)
          (fun y => hf (x.1,y)) (fun y => hg (x.1,y)) x.2

lemma measurable_conditionalScheduledProduct_tilt {ι : Type} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f : Z → FinitePath Ω H → ℝ} {g : Z → FinitePath Ω H → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y i, Measurable (fun z => g z y i))
    (x : FinitePath Ω H) (i : Fin N) :
    Measurable (fun z => conditionalScheduledProduct H d e C q (KernelTower.tilt H T m (f z)) (g z) x i) := by
  unfold conditionalScheduledProduct
  exact Finset.measurable_prod _ (fun j _ =>
    measurable_conditionalScheduledMean_tilt H d e (C j) (q j) T m hf (fun y => hg y i) x)

lemma measurable_projectorChangeSq_tilt (H : ℕ) (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f : Z → FinitePath Ω H → ℝ} {X Y : Z → FinitePath Ω H → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i))
    (hY : ∀ y i, Measurable (fun z => Y z y i)) :
    Measurable (fun z => projectorChangeSq (KernelTower.tilt H T m (f z)) (X z) (Y z)) := by
  apply KernelTower.measurable_path_expect H T m hf
  intro y
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => ((hX y i).sub (hY y i)).pow_const 2)

lemma projectorChangeSq_le_four {H : ℕ} (T : KernelTower Ω H)
    (X Y : FinitePath Ω H → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) (hY : ∀ y i, |Y y i|≤1) : projectorChangeSq T X Y≤4 := by
  apply ((KernelTower.law H T).expect_mono (fun y => show FiniteLaw.spatialSq (fun i => X y i-Y y i)≤4 from ?_)).trans_eq
    ((KernelTower.law H T).expect_const 4)
  by_cases hN : N=0
  · simp [FiniteLaw.spatialSq,hN]
  · unfold FiniteLaw.spatialSq
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    calc
      _ ≤ ∑ _ : Fin N, (4:ℝ) := Finset.sum_le_sum (fun i _ => by
        have hx := abs_le.mp (hX y i)
        have hy := abs_le.mp (hY y i)
        nlinarith [sq_nonneg (2-(X y i-Y y i)),sq_nonneg (2+(X y i-Y y i)),
          mul_nonneg (show 0≤2-(X y i-Y y i) by linarith) (show 0≤2+(X y i-Y y i) by linarith)])
      _ = _ := by simp; ring

variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] {L : ℕ} [NeZero L]

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma measurable_projectionShiftError_tilt (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f : Z → FinitePath Ω L → ℝ} {g : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y i, Measurable (fun z => g z y i))
    (Q : α → Fin L) :
    Measurable (fun z => projectionShiftError a C e (KernelTower.tilt L T m (f z)) (g z) Q) := by
  unfold projectionShiftError
  apply Measurable.const_mul
  apply Measurable.sqrt
  exact measurable_projectorChangeSq_tilt L T m hf
    (measurable_conditionalScheduledProduct_tilt L 0 _ C _ T m hf hg)
    (measurable_conditionalScheduledProduct_tilt L 0 _ C _ T m hf hg)

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_le_four (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ)
    (hf : ∀ y i, |f y i|≤1) (Q : α → Fin L) : projectionShiftError a C e T f Q≤4 := by
  have h := projectorChangeSq_le_four T _ _
    (conditionalScheduledProduct_bound L 0 ((Q a).val+1) C
      (fun j v => (Q (e j v)).val+1) T f hf)
    (conditionalScheduledProduct_bound L 0 (Q a).val C
      (fun j v => (Q (e j v)).val) T f hf)
  have h' := Real.sqrt_le_sqrt h
  norm_num at h'
  unfold projectionShiftError
  linarith

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
