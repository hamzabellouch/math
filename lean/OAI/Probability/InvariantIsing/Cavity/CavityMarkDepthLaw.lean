import OAI.Probability.InvariantIsing.Cavity.CavityInnovationPrefix
import OAI.Probability.IsingPerceptron.SamplingIndependent

namespace OAI

/-! Common depth of atomless marked cascade leaves, without identifying
different branches from a possibly degenerate projected coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavityCommonMarkDepth_labeled {d : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d)) (hg : Function.Injective g)
    (v w : LabeledLeaf n) :
    cavityCommonMarkDepth n
      (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) v)
      (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) w) =
        labeledCommonDepth n v w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hroot : g (v.1.1, v.1.2, none) = g (w.1.1, w.1.2, none) ↔ v.1 = w.1 := by
      rw [hg.eq_iff]
      constructor
      · intro h
        exact Prod.ext (congrArg (fun x : ForestVertex (n + 1) => x.1) h)
          (congrArg (fun x : ForestVertex (n + 1) => x.2.1) h)
      · intro h
        rw [show v.1.1 = w.1.1 from congrArg Prod.fst h,
          show v.1.2 = w.1.2 from congrArg Prod.snd h]
    simp only [labeledNoiseLeaf, markForestOfCoords, cavityCommonMarkDepth, labeledCommonDepth,
      hroot]
    split_ifs with h
    · have hsub : Function.Injective (fun a : ForestVertex n => g (v.1.1, v.1.2, some a)) := by
        intro a b hab
        exact Option.some.inj (congrArg (fun x => x.2.2) (hg hab))
      have hw₁ : w.1.1 = v.1.1 := (congrArg Prod.fst h).symm
      have hw₂ : w.1.2 = v.1.2 := (congrArg Prod.snd h).symm
      rw [hw₁, hw₂, ih _ _ hsub]
    · rfl

lemma cavityForestVertexDepth_lt (n : ℕ) (v : ForestVertex n) :
    forestVertexDepth n v < n := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
    rcases v with ⟨a, b, v⟩
    cases v with
    | none => exact Nat.zero_lt_succ n
    | some v => exact Nat.succ_lt_succ (ih v)

lemma cavity_atomless_marks_injective {d : ℕ} (n : ℕ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hμ : ∀ i < n, NullSingletonClass (μ i : Measure (EuclideanSpace ℝ (Fin d)))) :
    ∀ᵐ g ∂Measure.infinitePi
      (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure (EuclideanSpace ℝ (Fin d)))), Function.Injective g := by
  let P := fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure (EuclideanSpace ℝ (Fin d)))
  have (v : ForestVertex n) : NullSingletonClass (P v) :=
    hμ (forestVertexDepth n v) (cavityForestVertexDepth_lt n v)
  change ∀ᵐ g ∂Measure.infinitePi P, ∀ i j, g i = g j → i = j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · subst j
    exact ae_of_all _ fun _ _ => rfl
  have hp : MeasurePreserving (fun g : ForestVertex n → EuclideanSpace ℝ (Fin d) => (g i, g j))
      (Measure.infinitePi P) ((P i).prod (P j)) :=
    ⟨by fun_prop, Measure.infinitePi_map_eval_prod hij⟩
  have ha : ∀ᵐ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)
      ∂(P i).prod (P j), p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact ae_of_all _ fun x => by simp only [ae_iff]; simp
  filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually ha] with g hg
  exact fun h => (hg h).elim

theorem cavity_marked_common_depth_integral {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hμ : ∀ i < n, NullSingletonClass (μ i : Measure (EuclideanSpace ℝ (Fin d)))) (a : ℕ → ℝ) :
    (∫ σ, a (cavityCommonMarkDepth n (σ 0) (σ 1)) ∂markedReplicaLaw n b μ) =
      ∫ α, a (labeledCommonDepth n (α 0) (α 1)) ∂cascadeReplicaLaw n b := by
  let Q := Measure.infinitePi
    (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure (EuclideanSpace ℝ (Fin d))))
  let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod Q
  let κ := probabilityReplicaKernel (labeledLeafLaw n) (measurable_labeledLeafLaw n)
  let J := P ⊗ₘ κ.comap Prod.fst measurable_fst
  let ψ := fun p : (LabeledTree n × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (ℕ → LabeledLeaf n) => fun i =>
        labeledNoiseLeaf _ n (p.1.1, markForestOfCoords _ n p.1.2) (p.2 i)
  have hψ : Measurable ψ := by
    have hm : Measurable (fun p :
        (LabeledTree n × (ForestVertex n → EuclideanSpace ℝ (Fin d))) × LabeledLeaf n =>
        labeledNoiseLeaf _ n (p.1.1, markForestOfCoords _ n p.1.2) p.2) := by
      apply measurable_from_prod_countable_left
      intro α
      exact (measurable_labeledNoiseLeaf _ n α).comp (by fun_prop)
    apply Measurable.of_eval
    intro i
    exact hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hJ : J.map ψ = markedReplicaLaw n b μ := labeled_marked_replica_law n b hb μ
  have hf : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      a (cavityCommonMarkDepth n (σ 0) (σ 1))) :=
    by
      have hp : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
          (σ 0, σ 1)) := by fun_prop
      exact (measurable_of_countable a).comp ((cavityCommonMarkDepth_measurable n).comp hp)
  have hPg : ∀ᵐ p ∂P, Function.Injective p.2 :=
    (measurePreserving_snd (μ := (labeledCascadeLaw n b : Measure (LabeledTree n))) (ν := Q)).quasiMeasurePreserving.tendsto_ae.eventually (cavity_atomless_marks_injective n μ hμ)
  have hJg : ∀ᵐ p ∂J, Function.Injective p.1.2 :=
    (show MeasurePreserving Prod.fst J P from ⟨measurable_fst, Measure.fst_compProd _ _⟩).quasiMeasurePreserving.tendsto_ae.eventually hPg
  rw [← hJ, integral_map hψ.aemeasurable hf.aestronglyMeasurable]
  have he : (∫ p, a (cavityCommonMarkDepth n (ψ p 0) (ψ p 1)) ∂J) =
      ∫ p, a (labeledCommonDepth n (p.2 0) (p.2 1)) ∂J := by
    apply integral_congr_ae
    filter_upwards [hJg] with p hp
    rw [show cavityCommonMarkDepth n (ψ p 0) (ψ p 1) =
      labeledCommonDepth n (p.2 0) (p.2 1) from cavityCommonMarkDepth_labeled n _ _ hp _ _]
  rw [he]
  have hT : J.map (fun p => (p.2, p.1.2)) = (cascadeReplicaLaw n b).prod Q :=
    independent_marks_sampling (labeledCascadeLaw n b : Measure (LabeledTree n)) Q κ
  have htest : Measurable (fun p : (ℕ → LabeledLeaf n) ×
      (ForestVertex n → EuclideanSpace ℝ (Fin d)) =>
        a (labeledCommonDepth n (p.1 0) (p.1 1))) :=
    by
      have hp : Measurable (fun p : (ℕ → LabeledLeaf n) ×
          (ForestVertex n → EuclideanSpace ℝ (Fin d)) => (p.1 0, p.1 1)) := by fun_prop
      exact (measurable_of_countable (fun p : LabeledLeaf n × LabeledLeaf n =>
        a (labeledCommonDepth n p.1 p.2))).comp hp

  have hmap : Measurable (fun p :
      (LabeledTree n × (ForestVertex n → EuclideanSpace ℝ (Fin d))) × (ℕ → LabeledLeaf n) =>
        (p.2, p.1.2)) := by fun_prop
  have hi := integral_map (μ := J) hmap.aemeasurable htest.aestronglyMeasurable
  change (∫ p, a (labeledCommonDepth n (p.2 0) (p.2 1)) ∂J) = _
  rw [← hi, hT]
  simpa only [probReal_univ, one_smul] using
    (integral_fun_fst (μ := cascadeReplicaLaw n b) (ν := Q)
      (fun α => a (labeledCommonDepth n (α 0) (α 1))))

end InvariantIsing

end

end OAI
