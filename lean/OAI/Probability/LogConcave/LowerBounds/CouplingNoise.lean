import Mathlib
import OAI.Probability.LogConcave.LowerBounds.LinearHistory

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

namespace LogConcaveSampling.LowerBound

abbrev CouplingNoise (Ω : Type*) (d q : ℕ) :=
  ((Ω × (Fin q → RoundRandom d)) × Point d) × Rotations d

def couplingLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d q : ℕ) :
    Measure (CouplingNoise Ω d q) :=
  ((μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d))).prod
    (stdGaussian (Point d))).prod (remainingHaar (prefixSpace d (2*q+1)))

instance couplingLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d q : ℕ) :
    IsProbabilityMeasure (couplingLaw μ d q) := by unfold couplingLaw; infer_instance

def couplingState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (p : CouplingNoise Ω d q) : (RevealState Ω d q q × Point d) × Rotations d :=
  ((stateRun initialRevealState (revealStep A Λ hd) q p.1.1,p.1.2),p.2)

lemma measurable_couplingState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    Measurable (couplingState A Λ hd) := by
  exact (((measurable_stateRun initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q).comp
    measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd

lemma couplingState_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    (couplingLaw μ d q).map (couplingState A Λ hd) =
      ((stateLaw (μ.map initialRevealState) (roundRandomLaw d)
        (revealStep A Λ hd) q).prod (stdGaussian (Point d))).prod
        (remainingHaar (prefixSpace d (2*q+1))) := by
  rw [← stateRun_law μ (roundRandomLaw d) initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q]
  have hr := measurable_stateRun initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q
  simp only [couplingLaw]
  rw [← Measure.map_id (μ := stdGaussian (Point d)),
    Measure.map_prod_map _ _ hr measurable_id,
    ← Measure.map_id (μ := remainingHaar (prefixSpace d (2*q+1))),
    Measure.map_prod_map _ _ (hr.prodMap measurable_id) measurable_id]
  simp only [Measure.map_id]
  rfl

theorem coupling_complete_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    (couplingLaw μ d q).map (finishComplete A (by omega) ∘ couplingState A Λ hd) =
      μ.prod (rotationHaar d) := by
  rw [← Measure.map_map (measurable_finishComplete A (by omega)) (measurable_couplingState A Λ hd),
    couplingState_law]
  have : IsProbabilityMeasure
      (μ.map (initialRevealState (Ω := Ω) (d := d) (q := q))) := inferInstance
  have := stateLaw_probability (μ.map initialRevealState) (roundRandomLaw d)
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q
  rw [finishComplete_law, revealState_completion_law μ A Λ hd]

lemma revealRun_tape {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (p : Ω × (Fin n → RoundRandom d)) :
    (stateRun initialRevealState (revealStep A Λ hd) n p).2.2.2 =
      fun i => ((p.2 i).1,(p.2 i).2.1) := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have ht : (stateRun initialRevealState (revealStep A Λ hd) (n+1) p).2.2.2 =
        Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d)
          (stateRun initialRevealState (revealStep A Λ hd) n (p.1,Fin.init p.2)).2.2.2
          ((p.2 (Fin.last n)).1,(p.2 (Fin.last n)).2.1) := by
      simp only [stateRun,revealStep]
      split_ifs <;> rfl
    rw [ht,ih]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.init]

def couplingColumns {Ω : Type*} {d q : ℕ} (p : CouplingNoise Ω d q) : Fin (q+q+1) → Point d :=
  Fin.snoc (α := fun _ : Fin (q+q+1) => Point d)
    (Fin.append (fun i => (p.1.1.2 i).1) (fun i => (p.1.1.2 i).2.1)) p.1.2

lemma measurable_couplingColumns {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ} :
    Measurable (couplingColumns (Ω := Ω) (d := d) (q := q)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [couplingColumns,Fin.snoc_last] using measurable_fst.snd
  · simp only [couplingColumns,Fin.snoc_castSucc]
    exact Fin.addCases (fun j => by fun_prop) (fun j => by fun_prop) j

lemma tapeHull_le_couplingColumns {Ω : Type*} {d q : ℕ} (p : CouplingNoise Ω d q) :
    tapeHull (fun i => ((p.1.1.2 i).1,(p.1.1.2 i).2.1)) ⊔ ℝ ∙ p.1.2 ≤
      Submodule.span ℝ (Set.range (couplingColumns p)) := by
  apply sup_le
  · apply Submodule.span_le.mpr
    rintro v (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · apply Submodule.subset_span
      exact ⟨(Fin.castAdd q i).castSucc, by simp only [couplingColumns,Fin.snoc_castSucc,Fin.append_left]⟩
    · apply Submodule.subset_span
      exact ⟨(Fin.natAdd q i).castSucc, by simp only [couplingColumns,Fin.snoc_castSucc,Fin.append_right]⟩
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    apply Submodule.subset_span
    exact ⟨Fin.last (q+q), by simp [couplingColumns]⟩

theorem coupling_output_span {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ∀ᵐ p ∂couplingLaw μ d q,
      finishCoordinate A (by omega) (couplingState A Λ hd p).1 ∈
        orbitHull Λ.toLinearMap (q+q) (couplingColumns p) := by
  let ν := μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d))
  let f := stateRun initialRevealState (revealStep A Λ hd) q
  have hf : Measurable f := measurable_stateRun initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q
  have hg : ∀ᵐ p ∂ν.prod (stdGaussian (Point d)),
      (prefixSpace d (2*q))ᗮ.orthogonalProjectionOnto (rotationIsometry (f p.1).2.1.2⁻¹ p.2) ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_singleton 0).compl.preimage
      ((measurable_frameProjection d (2*q)).comp
        (f := fun p => ((f p.1).2.1.2,p.2))
        ((hf.comp measurable_fst).snd.fst.snd.prodMk measurable_snd)))).mpr
    exact Filter.Eventually.of_forall (fun p => ae_frameGaussian_nonzero (by omega) (f p).2.1.2)
  have hs := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := stdGaussian (Point d))).ae
    (revealRun_spanConsistent μ A Λ hd)
  have hboth : ∀ᵐ p ∂ν.prod (stdGaussian (Point d)),
      finishCoordinate A (by omega) (f p.1,p.2) ∈
        powerHull Λ.toLinearMap q (tapeHull (fun i => ((p.1.2 i).1,(p.1.2 i).2.1))) ⊔ ℝ ∙ p.2 := by
    filter_upwards [hg,hs] with p hp hsp
    have h := finishCoordinate_mem A (by omega) (f p.1,p.2) hp
    have hh := sup_le_sup hsp (le_refl (ℝ ∙ p.2)) h
    simpa only [revealRun_tape] using hh
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := ν.prod (stdGaussian (Point d)))
    (ν := remainingHaar (prefixSpace d (2*q+1)))).ae hboth] with p hp
  have hbase := tapeHull_le_couplingColumns p
  have hpow := (powerHull_le_orbitHull Λ.toLinearMap q (couplingColumns p)
    (le_sup_left.trans hbase)).trans (orbitHull_mono Λ.toLinearMap (show q ≤ q+q by omega) _)
  have hlast : ℝ ∙ p.1.2 ≤ orbitHull Λ.toLinearMap (q+q) (couplingColumns p) :=
    (le_sup_right.trans hbase).trans (span_range_le_orbitHull _ _ _)
  exact sup_le hpow hlast hp

theorem coupling_output_correct {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ∀ᵐ p ∂couplingLaw μ d q,
      finishCoordinate A (by omega) (couplingState A Λ hd p).1 =
      (rotationIsometry (finishComplete A (by omega) (couplingState A Λ hd p)).2).symm
        (A.output ((finishComplete A (by omega) (couplingState A Λ hd p)).1,
          linearHistory A Λ (finishComplete A (by omega) (couplingState A Λ hd p)).2
            (finishComplete A (by omega) (couplingState A Λ hd p)).1 q)) := by
  filter_upwards [(Measure.quasiMeasurePreserving_snd
    (μ := (μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d))).prod (stdGaussian (Point d)))
    (ν := remainingHaar (prefixSpace d (2*q+1)))).ae
    (remainingHaar_fixes (prefixSpace d (2*q+1)))] with p hp
  exact finishCoordinate_correct A Λ (by omega) _ _
    (revealRun_historyConsistent A Λ hd q le_rfl p.1.1) hp

end LogConcaveSampling.LowerBound

open WithLp

end LowerProof
end
end
end

end OAI
