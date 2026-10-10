import Mathlib
import OAI.Probability.LogConcave.Sampling.UnitUniform
import OAI.Probability.LogConcave.Sampling.StateLaw

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling

lemma probability_measure_eq_of_subsingleton {X : Type*} [MeasurableSpace X] [Subsingleton X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s hs
  by_cases h : s.Nonempty
  · have he : s = Set.univ := Set.eq_univ_of_forall (fun x => by
      obtain ⟨y,hy⟩ := h
      simpa only [Subsingleton.elim x y] using hy)
    simp [he]
  · simp [Set.not_nonempty_iff_eq_empty.mp h]

end LogConcaveSampling

namespace LogConcaveSampling

def tapeSnocEquiv {R : Type*} [MeasurableSpace R] (n : ℕ) :
    (Fin n → R) × R ≃ᵐ (Fin (n+1) → R) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => R) (Fin.last n)).symm

@[simp] lemma tapeSnocEquiv_apply {R : Type*} [MeasurableSpace R] (n : ℕ)
    (p : (Fin n → R) × R) :
    tapeSnocEquiv n p = Fin.snoc (α := fun _ : Fin (n+1) => R) p.1 p.2 := by
  exact Fin.insertNth_last' p.2 p.1

def seedTapeSnoc {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R] (n : ℕ) :
    ((Ω × (Fin n → R)) × R) ≃ᵐ Ω × (Fin (n+1) → R) :=
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl Ω).prodCongr (tapeSnocEquiv n))

@[simp] lemma seedTapeSnoc_apply {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    (n : ℕ) (p : (Ω × (Fin n → R)) × R) :
    seedTapeSnoc n p = (p.1.1, Fin.snoc (α := fun _ : Fin (n+1) => R) p.1.2 p.2) := by
  change (p.1.1, tapeSnocEquiv n (p.1.2,p.2)) = _
  rw [tapeSnocEquiv_apply]

lemma seedTapeSnoc_law {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    (μ : Measure Ω) (γ : Measure R) [SFinite μ] [SigmaFinite γ] (n : ℕ) :
    (((μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ).map (seedTapeSnoc n)) =
      μ.prod (Measure.pi (fun _ : Fin (n+1) => γ)) := by
  change ((μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ).map
    (((MeasurableEquiv.refl Ω).prodCongr (tapeSnocEquiv n)) ∘ MeasurableEquiv.prodAssoc) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.prodAssoc_prod]
  have h := Measure.map_prod_map μ ((Measure.pi (fun _ : Fin n => γ)).prod γ)
    measurable_id (tapeSnocEquiv n).measurable
  rw [Measure.map_id] at h
  change (μ.prod ((Measure.pi (fun _ : Fin n => γ)).prod γ)).map (Prod.map id (tapeSnocEquiv n)) = _
  rw [← h]
  have ht : (tapeSnocEquiv (R := R) n : (Fin n → R) × R → _) =
    fun p => Fin.snoc (α := fun _ : Fin (n+1) => R) p.1 p.2 := by funext p; exact tapeSnocEquiv_apply n p
  rw [ht, pi_snoc_law]

section Run
variable {S : ℕ → Type*} {Ω R : Type*}
  [∀ n, MeasurableSpace (S n)] [MeasurableSpace Ω] [MeasurableSpace R]

def stateRun (init : Ω → S 0) (step : (n : ℕ) → S n × R → S (n+1)) :
    (n : ℕ) → Ω × (Fin n → R) → S n
  | 0, p => init p.1
  | n+1, p => step n (stateRun init step n (p.1,Fin.init p.2),p.2 (Fin.last n))

omit [∀ n, MeasurableSpace (S n)] in
@[simp] lemma stateRun_snoc (init : Ω → S 0) (step : (n : ℕ) → S n × R → S (n+1))
    (n : ℕ) (p : (Ω × (Fin n → R)) × R) :
    stateRun init step (n+1) (seedTapeSnoc n p) =
      step n (stateRun init step n p.1,p.2) := by
  simp [stateRun, Fin.init_snoc]

lemma measurable_stateRun (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n)) (n : ℕ) :
    Measurable (stateRun init step n) := by
  induction n with
  | zero => exact hi.comp measurable_fst
  | succ n ih =>
    apply (hs n).comp
    exact (ih.comp (measurable_fst.prodMk (Measurable.of_eval
      (fun index => (measurable_pi_apply index.castSucc).comp measurable_snd)))).prodMk
        (by fun_prop)

lemma stateRun_law (μ : Measure Ω) (γ : Measure R) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n)) (n : ℕ) :
    (μ.prod (Measure.pi (fun _ : Fin n => γ))).map (stateRun init step n) =
      stateLaw (μ.map init) γ step n := by
  induction n with
  | zero =>
    change (μ.prod (Measure.pi (fun _ : Fin 0 => γ))).map (init ∘ Prod.fst) = μ.map init
    rw [← Measure.map_map hi measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  | succ n ih =>
    rw [← seedTapeSnoc_law μ γ n, Measure.map_map (measurable_stateRun init hi step hs (n+1))
      (seedTapeSnoc n).measurable]
    change _ = (((stateLaw (μ.map init) γ step n).prod γ).map (step n))
    rw [← ih]
    have h := Measure.map_prod_map (μ.prod (Measure.pi (fun _ : Fin n => γ))) γ
      (measurable_stateRun init hi step hs n) measurable_id
    rw [Measure.map_id] at h
    rw [h, Measure.map_map (hs n) ((measurable_stateRun init hi step hs n).prodMap measurable_id)]
    congr 1
    funext p
    exact stateRun_snoc init step n p

lemma stateRun_ae_invariant (μ : Measure Ω) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n))
    (P : (n : ℕ) → S n → Prop) (N : ℕ)
    (good : (n : ℕ) → S n × R → Prop)
    (hgood : ∀ n, MeasurableSet {z | good n z})
    (hgood_ae : ∀ n < N, ∀ s, ∀ᵐ r ∂γ, good n (s,r))
    (h0 : ∀ ω, P 0 (init ω))
    (hstep : ∀ n < N, ∀ s r, P n s → good n (s,r) → P (n+1) (step n (s,r))) :
    ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin N => γ)), P N (stateRun init step N p) := by
  have h : ∀ n ≤ N, ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin n => γ)),
      P n (stateRun init step n p) := by
    intro n hn
    induction n with
    | zero => exact Filter.Eventually.of_forall (fun p => h0 p.1)
    | succ n ih =>
      rw [← seedTapeSnoc_law μ γ n, (seedTapeSnoc n).measurableEmbedding.ae_map_iff]
      simp only [stateRun_snoc]
      have hg : ∀ᵐ p ∂(μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ,
          good n (stateRun init step n p.1,p.2) := by
        apply (Measure.ae_prod_iff_ae_ae ((hgood n).preimage
          ((measurable_stateRun init hi step hs n).prodMap measurable_id))).mpr
        exact Filter.Eventually.of_forall (fun p => hgood_ae n (by omega) _)
      filter_upwards [hg, Measure.quasiMeasurePreserving_fst.ae (ih (by omega))] with p hp hP
      exact hstep n (by omega) _ _ hP hp
  exact h N le_rfl

end Run
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
