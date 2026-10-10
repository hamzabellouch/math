import OAI.NumberTheory.Ostmann.Tree.CoordinateAverages

namespace OAI

/-! # Bounded measurable bulk integrands, including sharp gates

The sharp terminal windows need not be continuous. This small function space
retains their actual values while providing the finite-measure operations used
in the bulk comparison.
-/

namespace Ostmann
open MeasureTheory
open scoped Classical

structure BulkIntegrand (σ : Type*) where
  toFun : (σ → ℝ) → ℂ
  measurable : Measurable toFun
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖toFun x‖ ≤ C

instance {σ : Type*} : CoeFun (BulkIntegrand σ) (fun _ => (σ → ℝ) → ℂ) := ⟨BulkIntegrand.toFun⟩

@[ext] theorem BulkIntegrand.ext {σ : Type*} {f g : BulkIntegrand σ}
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  have he := funext h
  cases he
  rfl

noncomputable def BulkIntegrand.sub {σ : Type*} (f g : BulkIntegrand σ) : BulkIntegrand σ where
  toFun x := f x - g x
  measurable := f.measurable.sub g.measurable
  bounded := by
    obtain ⟨A, hA, hf⟩ := f.bounded
    obtain ⟨B, hB, hg⟩ := g.bounded
    exact ⟨A + B, add_nonneg hA hB, fun x => (norm_sub_le _ _).trans (add_le_add (hf x) (hg x))⟩

theorem BulkIntegrand.integrable {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (μ : Measure (σ → ℝ)) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C, _, hC⟩ := f.bounded
  exact ⟨f.measurable.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩

theorem BulkIntegrand.slice_integrable {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (x : σ → ℝ) :
    Integrable (fun t => f (Function.update x i t)) μ := by
  obtain ⟨C, _, hC⟩ := f.bounded
  exact ⟨(f.measurable.comp (continuous_const.update i continuous_id).measurable).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun t => hC _)⟩

noncomputable def BulkIntegrand.average {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (f : BulkIntegrand σ) : BulkIntegrand σ where
  toFun x := ∫ t, f (Function.update x i t) ∂μ
  measurable := by
    have hj : Measurable (fun z : (σ → ℝ) × ℝ => f (Function.update z.1 i z.2)) :=
      f.measurable.comp (continuous_update i).measurable
    exact hj.stronglyMeasurable.integral_prod_right'.measurable
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    refine ⟨C * μ.real Set.univ, mul_nonneg hC measureReal_nonneg, fun x => ?_⟩
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun _t => hf _)

theorem BulkIntegrand.average_bound {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (f : BulkIntegrand σ)
    (C : ℝ) (hf : ∀ x, ‖f x‖ ≤ C) (x : σ → ℝ) :
    ‖f.average μ i x‖ ≤ C * μ.real Set.univ :=
  norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun _t => hf _)

theorem BulkIntegrand.average_sub {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (f g : BulkIntegrand σ) :
    (f.sub g).average μ i = (f.average μ i).sub (g.average μ i) := by
  ext x
  exact integral_sub (f.slice_integrable μ i x) (g.slice_integrable μ i x)

theorem BulkIntegrand.average_commute {σ : Type*} [Fintype σ]
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (i j : σ) (hij : i ≠ j) (f : BulkIntegrand σ) :
    (f.average ν j).average μ i = (f.average μ i).average ν j := by
  ext x
  obtain ⟨C, _, hC⟩ := f.bounded
  have hj : Measurable (fun z : ℝ × ℝ => f (Function.update (Function.update x i z.1) j z.2)) :=
    f.measurable.comp (((show Continuous (fun _ : ℝ × ℝ => x) from continuous_const).update i
      continuous_fst).update j continuous_snd).measurable
  have hg : Integrable (fun z : ℝ × ℝ => f (Function.update (Function.update x i z.1) j z.2))
      (μ.prod ν) := ⟨hj.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun z => hC _)⟩
  have he := integral_integral_swap (μ := μ) (ν := ν)
    (f := fun t s => f (Function.update (Function.update x i t) j s)) hg
  change (∫ t, ∫ s, f (Function.update (Function.update x i t) j s) ∂ν ∂μ) = _
  rw [he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => integral_congr_ae
    (Filter.Eventually.of_forall fun t => by dsimp only; rw [Function.update_comm hij])

noncomputable def BulkIntegrand.averages {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] : List σ → BulkIntegrand σ → BulkIntegrand σ
  | [], f => f
  | i :: l, f => (f.averages μ l).average (μ i) i

theorem BulkIntegrand.averages_sub {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (l : List σ) (f g : BulkIntegrand σ) :
    (f.sub g).averages μ l = (f.averages μ l).sub (g.averages μ l) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [averages, ih, average_sub]

theorem BulkIntegrand.averages_bound {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (l : List σ)
    (hμ : ∀ i ∈ l, (μ i).real Set.univ ≤ 2) (f : BulkIntegrand σ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) :
    ∀ x, ‖f.averages μ l x‖ ≤ 2 ^ l.length * C := by
  induction l with
  | nil => simpa only [averages, List.length_nil, pow_zero, one_mul] using hf
  | cons i l ih =>
    intro x
    have ht := ih (fun j hj => hμ j (by simp [hj]))
    calc
      _ ≤ (2 ^ l.length * C) * (μ i).real Set.univ := average_bound _ _ _ _ ht x
      _ ≤ (2 ^ l.length * C) * 2 := mul_le_mul_of_nonneg_left (hμ i (by simp)) (by positivity)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

theorem BulkIntegrand.averages_commute {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (ν : Measure ℝ) [IsFiniteMeasure ν]
    (l : List σ) (i : σ) (hi : i ∉ l) (f : BulkIntegrand σ) :
    (f.averages μ l).average ν i = (f.average ν i).averages μ l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (by simp [h])
    simp only [averages, average_commute ν (μ j) i j hij, ih hil]

/-- Pointwise product comparison, valid also for the original sharp windows. -/
theorem BulkIntegrand.averages_comparison {σ : Type*} [Fintype σ] (μ ν : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (l : List σ) (hl : l.Nodup)
    (hμ : ∀ i ∈ l, (μ i).real Set.univ ≤ 2) (hν : ∀ i ∈ l, (ν i).real Set.univ ≤ 2)
    (f : BulkIntegrand σ) (ε : σ → ℝ) (hε : ∀ i ∈ l, 0 ≤ ε i)
    (herr : ∀ i ∈ l, ∀ x, ‖f.average (μ i) i x - f.average (ν i) i x‖ ≤ ε i) :
    ∀ x, ‖f.averages μ l x - f.averages ν l x‖ ≤ 2 ^ l.length * (l.map ε).sum := by
  induction l with
  | nil => simp [averages]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    have hμl : ∀ j ∈ l, (μ j).real Set.univ ≤ 2 := fun j hj => hμ j (by simp [hj])
    have hνl : ∀ j ∈ l, (ν j).real Set.univ ≤ 2 := fun j hj => hν j (by simp [hj])
    have he0 := hε i (by simp)
    have heSum : 0 ≤ (l.map ε).sum := List.sum_nonneg (by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact hε j (by simp [hj]))
    have htail := ih hl hμl hνl (fun j hj => hε j (by simp [hj]))
      (fun j hj => herr j (by simp [hj]))
    have hfirst (x : σ → ℝ) :
        ‖(f.averages ν l).average (μ i) i x - (f.averages ν l).average (ν i) i x‖ ≤
          2 ^ l.length * ε i := by
      rw [averages_commute ν (μ i) l i hi, averages_commute ν (ν i) l i hi]
      have hb := averages_bound ν l hνl ((f.average (μ i) i).sub (f.average (ν i) i))
        (ε i) he0 (herr i (by simp)) x
      rw [averages_sub] at hb
      exact hb
    intro x
    change ‖(f.averages μ l).average (μ i) i x - (f.averages ν l).average (ν i) i x‖ ≤ _
    calc
      _ ≤ ‖(f.averages μ l).average (μ i) i x - (f.averages ν l).average (μ i) i x‖ +
          ‖(f.averages ν l).average (μ i) i x - (f.averages ν l).average (ν i) i x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (2 ^ l.length * (l.map ε).sum) + 2 ^ l.length * ε i := by
        apply add_le_add _ (hfirst x)
        have ha := average_bound (μ i) i ((f.averages μ l).sub (f.averages ν l))
          (2 ^ l.length * (l.map ε).sum) htail x
        rw [average_sub] at ha
        apply ha.trans
        calc
          _ ≤ (2 ^ l.length * (l.map ε).sum) * 2 :=
            mul_le_mul_of_nonneg_left (hμ i (by simp)) (mul_nonneg (by positivity) heSum)
          _ = _ := by ring
      _ ≤ _ := by
        simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) l.length]

end Ostmann

end OAI
