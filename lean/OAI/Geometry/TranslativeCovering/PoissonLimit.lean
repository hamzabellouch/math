import OAI.Geometry.TranslativeCovering.PoissonCells

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace PoissonLimit
open Set MeasureTheory ProbabilityTheory PoissonConfig PoissonMeasureCells CellMatching PoissonDiagrams
open scoped Classical BigOperators ENNReal
variable {Ω : Type u_1} {A : Type u_2} [MeasurableSpace Ω] [Fintype A] [Nonempty A]
variable {I : A → Type u_3} [∀ a, Fintype (I a)] [∀ a, Nonempty (I a)]

omit [Nonempty A] [∀ a, Nonempty (I a)] in
lemma exists_partition_sequence [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (E : ∀ a, I a → Set Ω) (hE : ∀ a i, MeasurableSet (E a i)) :
    ∃ s : ℕ → Finset (Set Ω), ∃ P : ∀ k, Partition Ω ↥(s k),
      (∀ k a i, Respects (P k) (E a i)) ∧
      (∀ k c, μ.real ((P k).cell c) ≤ 1 / ((k : ℝ) + 1)) := by
  have hs (k : ℕ) := PoissonCells.exists_fine_partition μ
    (fun j : Σ a, I a => E j.1 j.2) (fun j => hE j.1 j.2)
    (δ := ENNReal.ofReal (1 / ((k : ℝ) + 1))) (by positivity)
  choose s hm hd hc hr using hs
  let P (k : ℕ) : Partition Ω ↥(s k) := {
    cell := fun c => c.val
    measurable := fun c => (hm k c c.property).1
    disjoint := fun c d hcd => hd k c.property d.property (fun h => hcd (Subtype.ext h))
    cover := by
      ext x
      simpa only [mem_iUnion, Subtype.exists, exists_prop] using
        (iff_of_eq (congrArg (fun S : Set Ω => x ∈ S) (hc k))) }
  refine ⟨s,P, ?_, ?_⟩
  · intro k a i c
    exact hr k ⟨a,i⟩ c c.property
  · intro k c
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm k c c.property).2.le).trans_eq
      (ENNReal.toReal_ofReal (by positivity))

theorem lower_tail [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (P : Measure (Config Ω)) [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
    (E : ∀ a, I a → Set Ω) (hE : ∀ a i, MeasurableSet (E a i))
    (hpos : ∀ a i, 0 < μ.real (E a i)) :
    (0 < ∑ a, ∑ b, diagram μ (E a) (E b)) ∧
    P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
      (-(∑ a, ∏ i, μ.real (E a i))^2 /
        (2 * (∑ a, ∑ b, diagram μ (E a) (E b)))) := by
  obtain ⟨s,cells,hr,hd⟩ := exists_partition_sequence μ E hE
  let m (k : ℕ) := ∑ a, Q μ (cells k) (E a)
  let d (k : ℕ) := ∑ a, ∑ b, ∑ M : Matching (I a) (I b),
    if M.val.Nonempty then Q μ (cells k) (classSet M (E a) (E b)) else 0
  let ν := ∑ a, ∏ i, μ.real (E a i)
  let D := ∑ a, ∑ b, diagram μ (E a) (E b)
  have hν : 0 < ν := Finset.sum_pos (fun a _ => Finset.prod_pos (fun i _ => hpos a i))
    Finset.univ_nonempty
  have hm : Filter.Tendsto m Filter.atTop (nhds ν) := by
    apply tendsto_finsetSum
    intro a _
    exact Q_tendsto μ (fun k => ↥(s k)) cells (E a) (hE a) (fun k => hr k a)
      (fun k => by positivity) hd tendsto_one_div_add_atTop_nhds_zero_nat
  have hDform : D = ∑ a, ∑ b, ∑ M : Matching (I a) (I b),
      if M.val.Nonempty then ∏ v, μ.real (classSet M (E a) (E b) v) else 0 := by
    dsimp only [D]
    simp_rw [diagram_eq_classSet_sum μ _ _ (fun i => ne_of_gt (hpos _ i))
      (fun i => ne_of_gt (hpos _ i))]
  have hdt : Filter.Tendsto d Filter.atTop (nhds D) := by
    rw [hDform]
    apply tendsto_finsetSum
    intro a _
    apply tendsto_finsetSum
    intro b _
    apply tendsto_finsetSum
    intro M _
    by_cases hM : M.val.Nonempty
    · simp only [ite_eq_left hM]
      exact Q_tendsto μ (fun k => ↥(s k)) cells (classSet M (E a) (E b))
        (classSet_measurable M (E a) (E b) (hE a) (hE b))
        (fun k => classSet_respects (cells k) M (E a) (E b) (hr k a) (hr k b))
        (fun k => by positivity) hd tendsto_one_div_add_atTop_nhds_zero_nat
    · simp only [ite_eq_right hM]
      exact tendsto_const_nhds
  have hevent : ∀ᶠ k in Filter.atTop, 0 < m k := hm.eventually (eventually_gt_nhds hν)
  have hbd : ∀ᶠ k in Filter.atTop, m k ≤ d k ∧
      P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp (-(m k)^2 / (2 * d k)) := by
    filter_upwards [hevent] with k hk
    exact PoissonFinite.finite_cell_bound μ P hP (cells k) E hk
  have hνD : ν ≤ D := le_of_tendsto_of_tendsto hm hdt (hbd.mono fun _ h => h.1)
  have hD : 0 < D := hν.trans_le hνD
  refine ⟨hD, ?_⟩
  have hexp : Filter.Tendsto (fun k => Real.exp (-(m k)^2 / (2*d k))) Filter.atTop
      (nhds (Real.exp (-ν^2/(2*D)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      ((hm.pow 2).neg.div (tendsto_const_nhds.mul hdt) (ne_of_gt (mul_pos (by norm_num) hD)))
  exact ge_of_tendsto hexp (hbd.mono fun _ h => h.2)

end PoissonLimit

end OAI
