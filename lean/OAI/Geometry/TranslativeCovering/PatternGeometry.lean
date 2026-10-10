import OAI.Geometry.TranslativeCovering.RandomBody

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PatternGeometry
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set Metric MeasureTheory SphericalLaw PoissonConfig LocalizationRounding
open scoped BigOperators ENNReal Classical

noncomputable def relevant {n : ℕ} {I : Type u_1} [Fintype I] (p : I → Space n)
    (L : ℝ) (y : Space n) : Finset I := Finset.univ.filter (fun i => ‖y-p i‖ ≤ L)

noncomputable def roundedGood {n : ℕ} {I : Type u_2} [Fintype I] (p : I → Space n)
    (a D r L C : ℝ) : Set (Space n) :=
  {y | y ∈ closedBall 0 D ∧ (∀ i,r ≤ ‖y-p i‖) ∧
    ((relevant p L y).card:ℝ) ≤ C ∧
    ∑ i ∈ relevant p L y,weight n a ‖y-p i‖ ≤ C}

lemma measurable_roundedGood {n : ℕ} {I : Type u_3} [Fintype I] (p : I → Space n)
    (a D r L C : ℝ) : MeasurableSet (roundedGood p a D r L C) := by
  have hi (i : I) : MeasurableSet {y : Space n | ‖y-p i‖ ≤ L} :=
    measurableSet_le ((continuous_id.sub continuous_const).norm.measurable) measurable_const
  have hc : Measurable (fun y : Space n => ((relevant p L y).card:ℝ)) := by
    simp only [relevant,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    exact Finset.measurable_sum _ fun i _ => Measurable.ite (hi i) measurable_const measurable_const
  have hw : Measurable (fun y : Space n => ∑ i ∈ relevant p L y,weight n a ‖y-p i‖) := by
    simp only [relevant,Finset.sum_filter]
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite (hi i) _ measurable_const
    exact (continuous_const.add (continuous_const.mul
      ((continuous_const.sub (((continuous_id.sub continuous_const).norm.pow 2).div_const (a^2))).max continuous_const))).measurable
  have hall : MeasurableSet {y : Space n | ∀ i,r ≤ ‖y-p i‖} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (by fun_prop)
  exact measurableSet_closedBall.inter (hall.inter
    ((measurableSet_le hc measurable_const).inter (measurableSet_le hw measurable_const)))

lemma budgets {n : ℕ} {I : Type u_4} [Fintype I] (p : I → Space n)
    {a D r L C : ℝ} {y : Space n} (hy : y ∈ roundedGood p a D r L C) :
    (∀ i : relevant p L y,r ≤ ‖y-p i‖ ∧ ‖y-p i‖ ≤ L) ∧
    (Fintype.card (relevant p L y):ℝ)+(∑ i : relevant p L y,weight n a ‖y-p i‖) ≤ 2*C := by
  refine ⟨fun i => ⟨hy.2.1 i, (Finset.mem_filter.mp i.property).2⟩,?_⟩
  have he := Finset.sum_coe_sort (relevant p L y) (fun i => weight n a ‖y-p i‖)
  rw [Fintype.card_coe,he]
  linarith only [hy.2.2.1,hy.2.2.2]

lemma cover_measurable {n : ℕ} {I : Type u_5} [Fintype I] (p : I → Space n) (b t D : ℝ) :
    MeasurableSet {U : Config (Sphere n) | ∀ y ∈ closedBall (0 : Space n) D,
      ∃ i,y-p i ∈ RandomBody.body b t U} := by
  apply measurableSet_sigma
  intro k
  have hc : IsClosed {U : {f : Fin k → Sphere n // Function.Injective f} |
      ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-p i ∈ RandomBody.body b t ⟨k,U⟩} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    simp only [ofPred_exists]
    apply isClosed_iUnion_of_finite
    intro i
    simp only [RandomBody.body,mem_inter_iff,mem_closedBall_zero_iff,mem_iInter]
    change IsClosed {U : {f : Fin k → Sphere n // Function.Injective f} |
      ‖y-p i‖ ≤ b ∧ ∀ j,|inner ℝ (U.val j).val (y-p i)| ≤ t}
    apply (isClosed_const : IsClosed {U : {f : Fin k → Sphere n // Function.Injective f} | ‖y-p i‖ ≤ b}).inter
    have hj (j : Fin k) : IsClosed {U : {f : Fin k → Sphere n // Function.Injective f} |
        |inner ℝ (U.val j).val (y-p i)| ≤ t} :=
      isClosed_le ((((continuous_apply j).comp continuous_subtype_val).subtype_val.inner continuous_const).abs) continuous_const
    change IsClosed {U : {f : Fin k → Sphere n // Function.Injective f} |
      ∀ j,|inner ℝ (U.val j).val (y-p i)| ≤ t}
    simpa only [Set.ofPred_forall] using isClosed_iInter hj
  exact hc.measurableSet

lemma witness_hole {n : ℕ} {J : Type u_6} [Fintype J] (p : J → Space n)
    (y : Space n) (L t : ℝ)
    (P : Finpartition (Finset.univ : Finset (relevant p L y)))
    (E : Finset (relevant p L y) → Set (Sphere n))
    (hE : ∀ S ∈ P.parts,E S ⊆ ⋂ i ∈ S,cap (y-p i) t)
    (U : Config (Sphere n)) (hw : 0 < witnessCount (fun S : P.parts => E S) U) :
    ∀ j,y-p j ∉ RandomBody.body L t U := by
  obtain ⟨f,hf⟩ := Finset.card_pos.mp hw
  have hf' : ∀ S : P.parts,U.2.val (f S) ∈ E S := (Finset.mem_filter.mp hf).2
  intro j hj
  have hjL : ‖y-p j‖ ≤ L := mem_closedBall_zero_iff.mp hj.1
  let i : relevant p L y := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjL⟩⟩
  obtain ⟨S,hS,hi⟩ := P.exists_mem (Finset.mem_univ i)
  have hcut := mem_iInter₂.mp (hE S hS (hf' ⟨S,hS⟩)) i hi
  change t < |inner ℝ (U.2.val (f ⟨S,hS⟩)).val (y-p j)| at hcut
  have hbound : |inner ℝ (U.2.val (f ⟨S,hS⟩)).val (y-p j)| ≤ t := mem_iInter.mp hj.2 (f ⟨S,hS⟩)
  exact (not_lt_of_ge hbound) hcut

lemma rounding_cover {n : ℕ} {I : Type u_7} [Fintype I] (p : I → Space n) {h : ℝ}
    (hh : 0 < h) (U : Config (Sphere n)) (b t D : ℝ)
    (hc : ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-p i ∈ RandomBody.body b t U) :
    ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-rounded h (p i) ∈
      RandomBody.body (b+Real.sqrt n*h/2) (t+Real.sqrt n*h/2) U := by
  intro y hy
  obtain ⟨i,hi⟩ := hc y hy
  refine ⟨i,mem_closedBall_zero_iff.mpr (norm_buffer hh (p i) y (mem_closedBall_zero_iff.mp hi.1)),?_⟩
  apply mem_iInter.mpr
  intro j
  exact slab_buffer hh (p i) y (U.2.val j).val (mem_sphere_zero_iff_norm.mp (U.2.val j).property)
    (mem_iInter.mp hi.2 j)

end PatternGeometry

end OAI
