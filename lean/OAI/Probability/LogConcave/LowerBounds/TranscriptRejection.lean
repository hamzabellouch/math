import Mathlib
import OAI.Probability.LogConcave.Analysis.GaussianProposalPotential

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling

def transcriptRejection {d : ℕ} : (q : ℕ) →
    ((Fin q → Point d × ℝ) × (Fin q → ℝ)) → Point d
  | 0, _ => 0
  | n+1, p =>
      if (p.1 (Fin.last n)).2 ≤ Real.exp (-(p.2 (Fin.last n))+
          gaussianProposalPotential d (p.1 (Fin.last n)).1) then (p.1 (Fin.last n)).1
      else transcriptRejection n (fun i => p.1 i.castSucc,fun i => p.2 i.castSucc)

@[fun_prop] lemma measurable_transcriptRejection (d q : ℕ) :
    Measurable (transcriptRejection (d := d) q) := by
  induction q with
  | zero => exact measurable_const
  | succ n ih =>
      apply Measurable.ite
      · apply measurableSet_le
        · fun_prop
        · exact Real.measurable_exp.comp (((measurable_pi_apply (Fin.last n)).comp measurable_snd).neg.add
            ((gaussianProposalPotential_admissible d).smooth.continuous.measurable.comp
            (((measurable_pi_apply (Fin.last n)).comp measurable_fst).fst)))
      · fun_prop
      · exact ih.comp ((Measurable.of_eval fun index =>
          (measurable_pi_apply index.castSucc).comp measurable_fst).prodMk
          (Measurable.of_eval fun index => (measurable_pi_apply index.castSucc).comp measurable_snd))

lemma transcriptRejection_eq {d : ℕ} (V : Point d → ℝ) (q : ℕ) (tape : Fin q → Point d × ℝ) :
    transcriptRejection q (tape,fun i => V (tape i).1) =
      rejectionPick (gaussianAcceptance V) 0 q tape := by
  induction q with
  | zero => rfl
  | succ n ih =>
      simp only [transcriptRejection,rejectionPick,gaussianAcceptance]
      congr 1
      exact ih _

def finiteRejectionAlgorithm (d q : ℕ) : OracleAlgorithm (Fin q → Point d × ℝ) d q where
  query i p := (p.1 i).1
  query_measurable _ := by fun_prop
  output p := transcriptRejection q (p.1,fun i => (p.2 i).1)
  output_measurable := (measurable_transcriptRejection d q).comp (measurable_fst.prodMk
    (Measurable.of_eval fun _ => by fun_prop))

lemma finiteRejection_history {d q : ℕ} (V : Point d → ℝ) (tape : Fin q → Point d × ℝ)
    (n : ℕ) (i : Fin q) (hi : i.val < n) :
    (finiteRejectionAlgorithm d q).history V tape n i = firstOrderReply V (tape i).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [OracleAlgorithm.history]
      split_ifs with hn
      · by_cases he : i = ⟨n,hn⟩
        · subst i
          simp [finiteRejectionAlgorithm]
        · rw [Function.update_of_ne he]
          exact ih (by have hne : i.val ≠ n := fun h => he (Fin.ext h); omega)
      · apply ih
        omega

lemma finiteRejection_run {d q : ℕ} (V : Point d → ℝ) (tape : Fin q → Point d × ℝ) :
    (finiteRejectionAlgorithm d q).run V tape = rejectionPick (gaussianAcceptance V) 0 q tape := by
  change transcriptRejection q (tape,_) = _
  have hh : (fun i => ((finiteRejectionAlgorithm d q).history V tape q i).1) =
      fun i => V (tape i).1 := by
    funext i
    rw [finiteRejection_history V tape q i i.isLt]
    rfl
  rw [hh,transcriptRejection_eq]

lemma rejection_failure_bound {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1-p)^n * (1+(n:ℝ)*p) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,Nat.cast_add,Nat.cast_one]
      have hnon : 0 ≤ (1-p)^n := pow_nonneg (sub_nonneg.mpr hp1) _
      have hs : (1-p)*(1+((n:ℝ)+1)*p) ≤ 1+(n:ℝ)*p := by
        have hh : 0 ≤ ((n:ℝ)+1)*p^2 := by positivity
        nlinarith
      have h := mul_le_mul_of_nonneg_left hs hnon
      nlinarith

theorem finite_dimension_sampler (d : ℕ) : CanSample d (10*2^d) := by
  let q := 10*2^d
  let ν := gibbs (gaussianProposalPotential d)
  have hB := gaussianProposalPotential_admissible d
  have := hB.isProbabilityMeasure_gibbs
  refine ⟨Fin q → Point d × ℝ,inferInstance,
    Measure.pi (fun _ : Fin q => ν.prod unitUniform),inferInstance,finiteRejectionAlgorithm d q,?_⟩
  intro V hV
  refine ⟨(finiteRejectionAlgorithm d q).measurable_run hV,?_⟩
  have := hV.isProbabilityMeasure_gibbs
  let p := (partition V).toReal/(partition (gaussianProposalPotential d)).toReal
  have hZ : 0 < (partition (gaussianProposalPotential d)).toReal :=
    ENNReal.toReal_pos hB.partition_pos.ne' hB.partition_ne_top
  have hp0 : 0 ≤ p := div_nonneg ENNReal.toReal_nonneg hZ.le
  have hp1 : p ≤ 1 := (div_le_one hZ).mpr (partition_comparison hV).2
  have hpl : (2:ℝ)^(-(d:ℤ)) ≤ p := (le_div_iff₀ hZ).mpr (partition_comparison hV).1
  have hq : (10:ℝ) ≤ (q:ℝ)*p := by
    have hh := mul_le_mul_of_nonneg_left hpl (show (0:ℝ) ≤ (q:ℝ) by positivity)
    dsimp [q] at hh ⊢
    norm_num only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,zpow_neg,zpow_natCast] at hh ⊢
    have hpow : (2:ℝ)^d ≠ 0 := by positivity
    field_simp at hh
    nlinarith
  have hfail : (1-p)^q ≤ 1/10 := by
    have h := rejection_failure_bound hp0 hp1 q
    have hnon : 0 ≤ (1-p)^q := pow_nonneg (sub_nonneg.mpr hp1) q
    nlinarith
  have htv := capped_rejection_tv ν (gibbs V) (measurable_gaussianAcceptance hV)
    hp0 hp1 (gaussian_accepted_measure hV) 0 q
  have he : (finiteRejectionAlgorithm d q).run V = rejectionPick (gaussianAcceptance V) 0 q :=
    funext (finiteRejection_run V)
  rw [he]
  exact fun s hs => (htv s hs).trans hfail

end LogConcaveSampling

end UpperProof
section LowerProof

open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound

abbrev Rotations (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ

theorem orthogonal_entry_bound {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M ∈ Matrix.orthogonalGroup (Fin d) ℝ) (i j : Fin d) : |M i j| ≤ 1 := by
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i i)
    ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hM)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have ht : (M i j)^2 ≤ ∑ k, M i k * M i k := by
    simpa only [pow_two] using
      (Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) => mul_self_nonneg (M i k))
        (Finset.mem_univ j))
  rw [h] at ht
  nlinarith [sq_abs (M i j), abs_nonneg (M i j)]

theorem orthogonal_group_isCompact (d : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin d) ℝ : Set (Matrix (Fin d) (Fin d) ℝ)) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_unitary (R := Matrix (Fin d) (Fin d) ℝ)
  · apply (Metric.isBounded_iff_subset_closedBall (0 : Matrix (Fin d) (Fin d) ℝ)).mpr
    refine ⟨1,?_⟩
    intro M hM
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (Matrix.norm_le_iff (by norm_num)).mpr
    intro i j
    exact orthogonal_entry_bound hM i j

instance rotations_compactSpace (d : ℕ) : CompactSpace (Rotations d) :=
  isCompact_iff_compactSpace.mp (orthogonal_group_isCompact d)

instance rotations_measurableSpace (d : ℕ) : MeasurableSpace (Rotations d) := borel _
instance rotations_borelSpace (d : ℕ) : BorelSpace (Rotations d) := ⟨rfl⟩

instance rotations_secondCountable (d : ℕ) : SecondCountableTopology (Rotations d) := by
  let : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  exact (Topology.IsEmbedding.subtypeVal (p := fun M : Matrix (Fin d) (Fin d) ℝ =>
    M ∈ Matrix.orthogonalGroup (Fin d) ℝ)).isInducing.secondCountableTopology

instance rotations_measurableMul (d : ℕ) : MeasurableMul₂ (Rotations d) :=
  ⟨continuous_mul.measurable⟩

def rotationHaar (d : ℕ) : Measure (Rotations d) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (Rotations d))

instance rotationHaar_probability (d : ℕ) : IsProbabilityMeasure (rotationHaar d) := by
  constructor
  exact Measure.haarMeasure_self

instance rotationHaar_isHaar (d : ℕ) : (rotationHaar d).IsHaarMeasure := by
  unfold rotationHaar
  infer_instance

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
