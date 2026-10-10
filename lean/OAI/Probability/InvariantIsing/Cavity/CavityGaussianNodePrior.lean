import OAI.Probability.InvariantIsing.Cavity.CavityGaussianForestLaw

namespace OAI

/-! Reindexing the actual shared Gaussian root, independent forest, and
replica-specific ordinary residuals as one independent node family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

private theorem cavity_infinitePi_sum_join {I J E : Type*} [MeasurableSpace E]
    (μ : I → Measure E) (ν : J → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (I → E) × (J → E) => Sum.elim p.1 p.2) =
        Measure.infinitePi (Sum.elim μ ν) := by
  classical
  have hm : Measurable (fun p : (I → E) × (J → E) => Sum.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro a
    cases a <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  let : ∀ a : I ⊕ J, IsProbabilityMeasure (Sum.elim μ ν a) := by
    intro a
    cases a <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (.pi s.countable_toSet (fun a _ => ht a))]
  have he : (fun p : (I → E) × (J → E) => Sum.elim p.1 p.2) ⁻¹'
      ((s : Set (I ⊕ J)).pi t) =
      ((s.toLeft : Set I).pi (fun i => t (.inl i))) ×ˢ
        ((s.toRight : Set J).pi (fun j => t (.inr j))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe,
      Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h (.inl i) hi, fun j hj => h (.inr j) hj⟩
    · rintro ⟨hI, hJ⟩ a ha
      cases a with
      | inl i => exact hI i ha
      | inr j => exact hJ j ha
  rw [he, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun i _ => ht (.inl i)),
    Measure.infinitePi_pi _ (fun j _ => ht (.inr j)),
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  rfl

abbrev CavityReplicaNode (n r : ℕ) := Option (ForestVertex n) ⊕ Fin r

def cavityReplicaNodeCovariance {d : ℕ} (n r : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    CavityReplicaNode n r → Matrix (Fin d) (Fin d) ℝ :=
  Sum.elim (fun a => a.elim S₀ (fun v => S (forestVertexDepth n v))) (fun _ => R)

def cavityReplicaNodeJoin {d : ℕ} (n r : ℕ)
    (p : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    CavityReplicaNode n r → EuclideanSpace ℝ (Fin d) :=
  Sum.elim (fun a => a.elim p.1.1 p.1.2) p.2

lemma measurable_cavityReplicaNodeJoin {d : ℕ} (n r : ℕ) :
    Measurable (cavityReplicaNodeJoin (d := d) n r) := by
  unfold cavityReplicaNodeJoin
  apply Measurable.of_eval
  intro a
  cases a with
  | inl a =>
    cases a <;> dsimp only [Sum.elim_inl, Option.elim_none, Option.elim_some] <;> fun_prop
  | inr a => dsimp only [Sum.elim_inr]; fun_prop

theorem cavity_replica_node_prior_law {d : ℕ} (n r : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) R))).map (cavityReplicaNodeJoin n r) =
      Measure.infinitePi (fun a : CavityReplicaNode n r => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (cavityReplicaNodeCovariance n r S₀ R S a)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let μ := fun a : Option (ForestVertex n) =>
    a.elim (multivariateGaussian (0 : E) S₀)
      (fun v => multivariateGaussian (0 : E) (S (forestVertexDepth n v)))
  let : ∀ a, IsProbabilityMeasure (μ a) := by
    intro a
    cases a <;> dsimp only [μ, Option.elim_none, Option.elim_some] <;> infer_instance
  let ν := fun _ : Fin r => multivariateGaussian (0 : E) R
  let F : E × (ForestVertex n → E) → (Option (ForestVertex n) → E) :=
    fun p a => a.elim p.1 p.2
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro a
    cases a <;> dsimp only [F, Option.elim_none, Option.elim_some] <;> fun_prop
  have hbase : ((multivariateGaussian (0 : E) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n =>
        multivariateGaussian (0 : E) (S (forestVertexDepth n v))))).map F =
      Measure.infinitePi μ := by
    simpa only [F, μ] using infinitePi_option_join
      (multivariateGaussian (0 : E) S₀)
      (fun v : ForestVertex n => multivariateGaussian (0 : E) (S (forestVertexDepth n v)))
  have hm : Measurable (fun p : (Option (ForestVertex n) → E) × (Fin r → E) =>
      Sum.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro a
    cases a <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  have hC : (fun a : CavityReplicaNode n r => multivariateGaussian
      (0 : E) (cavityReplicaNodeCovariance n r S₀ R S a)) = Sum.elim μ ν := by
    funext a
    cases a with
    | inl a => cases a <;> rfl
    | inr a => rfl
  rw [hC]
  rw [show cavityReplicaNodeJoin (d := d) n r =
      (fun p : (Option (ForestVertex n) → E) × (Fin r → E) => Sum.elim p.1 p.2) ∘
        Prod.map F id from rfl,
    ← Measure.map_map hm (hF.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hF measurable_id, hbase, Measure.map_id,
    ← Measure.infinitePi_eq_pi]
  exact cavity_infinitePi_sum_join μ ν

end InvariantIsing

end

end OAI
