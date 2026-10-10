import OAI.MathematicalPhysics.Boltzmann.Branching.CompactParameterConvergence
import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Sequences

namespace OAI

section

/-! # Countably many compact smooth cutoffs covering an open spacetime region -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

theorem exists_spacetime_cutoff_cover {U : Set Published.SpaceTime}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ χ : ℕ → Published.SpaceTime → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n, tsupport (χ n) ⊆ U) ∧ (∀ x ∈ U, ∃ n, χ n x ≠ 0) := by
  let ι := {f : Published.SpaceTime → ℝ // tsupport f ⊆ U ∧ HasCompactSupport f ∧
    ContDiff ℝ (⊤ : ℕ∞) f}
  have hcover : (⋃ f : ι, Function.support (f : Published.SpaceTime → ℝ)) = U := by
    apply Subset.antisymm
    · exact iUnion_subset (fun f => (subset_tsupport f.1).trans f.2.1)
    · intro x hx
      obtain ⟨f,hfs,hfc,hfd,_hfR,hfx⟩ :=
        exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
      let b : ι := ⟨f,hfs,hfc,hfd⟩
      exact mem_iUnion_of_mem b (by simp only [b,Function.mem_support,hfx,ne_eq,one_ne_zero,not_false_eq_true])
  obtain ⟨S,hSc,hS⟩ : ∃ S : Set ι, S.Countable ∧
      (⋃ f ∈ S, Function.support (f : Published.SpaceTime → ℝ)) = U := by
    obtain ⟨S,hSc,hS⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun f : ι => Function.support f.1)
      (fun f : ι => f.2.2.2.continuous.isOpen_support)
    exact ⟨S,hSc,hS.trans hcover⟩
  have hSne : S.Nonempty := by
    by_contra he
    have hse : S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    simp only [hse,mem_empty_iff_false,iUnion_of_empty,iUnion_empty] at hS
    exact hne.ne_empty hS.symm
  obtain ⟨a,ha⟩ := Set.Countable.exists_eq_range hSc hSne
  refine ⟨fun n => (a n).1,fun n => (a n).2.2.2,fun n => (a n).2.2.1,
    fun n => (a n).2.1,?_⟩
  intro x hx
  rw [← hS,ha] at hx
  obtain ⟨f,hf,hfx⟩ := mem_iUnion₂.mp hx
  obtain ⟨n,rfl⟩ := hf
  exact ⟨n,hfx⟩

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # A countable smooth compact family determining integrable velocity densities -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

private abbrev SupportedTest (n : ℕ) :=
  {f : C(Velocity,ℝ) // ContDiff ℝ (⊤ : ℕ∞) (f : Velocity → ℝ) ∧
    tsupport (f : Velocity → ℝ) ⊆ Metric.closedBall 0 (n+1 : ℝ)}

private instance (n : ℕ) : Nonempty (SupportedTest n) :=
  ⟨⟨0,contDiff_const,by simp⟩⟩

private instance (n : ℕ) : SecondCountableTopology (SupportedTest n) :=
  TopologicalSpace.Subtype.secondCountableTopology _

private def supportedSeq (n m : ℕ) : SupportedTest n :=
  TopologicalSpace.denseSeq (SupportedTest n) m

private def supportedFn (n m : ℕ) : C(Velocity,ℝ) := (supportedSeq n m).1

private def smoothTest (j : ℕ) : Velocity → ℝ :=
  supportedFn (Nat.unpair j).1 (Nat.unpair j).2

private theorem smoothTest_smooth (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smoothTest j) :=
  (supportedSeq (Nat.unpair j).1 (Nat.unpair j).2).2.1

private theorem smoothTest_compact (j : ℕ) : HasCompactSupport (smoothTest j) :=
  (isCompact_closedBall (0 : Velocity) ((Nat.unpair j).1+1 : ℝ)).of_isClosed_subset
    (isClosed_tsupport _) (supportedSeq (Nat.unpair j).1 (Nat.unpair j).2).2.2

theorem exists_countable_smooth_determining_tests :
    ∃ ψ : ℕ → Velocity → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) ∧
      (∀ j, HasCompactSupport (ψ j)) ∧
      ∀ u : Velocity → ℝ, Integrable u →
        (∀ j, ∫ v, ψ j v*u v = 0) → u =ᵐ[volume] 0 := by
  refine ⟨smoothTest,smoothTest_smooth,smoothTest_compact,?_⟩
  intro u hu hzero
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable
  intro ψ hψ hψc
  obtain ⟨R,_hR,hball⟩ := hψc.isBounded.subset_ball_lt 0 (0 : Velocity)
  obtain ⟨n,hn⟩ := exists_nat_gt R
  have hsupp : tsupport ψ ⊆ Metric.closedBall (0 : Velocity) (n+1 : ℝ) := by
    intro v hv
    have hvr : ‖v‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hball hv
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  let t : SupportedTest n := ⟨⟨ψ,hψ.continuous⟩,hψ,hsupp⟩
  have hd : DenseRange (supportedSeq n) := TopologicalSpace.denseRange_denseSeq (SupportedTest n)
  obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp (hd t)
  choose b hb using ha
  have hat' : Tendsto (fun m => (supportedSeq n (b m)).1) atTop (𝓝 t.1) := by
    have he : (fun m => supportedSeq n (b m)) = a := funext hb
    have hat0 : Tendsto (fun m => supportedSeq n (b m)) atTop (𝓝 t) := by
      rw [he]
      exact hat
    exact continuous_subtype_val.continuousAt.tendsto.comp hat0
  have ht := tendsto_integral_mul_common_support hu
    (isCompact_closedBall (0 : Velocity) (n+1 : ℝ))
    (fun m => (supportedSeq n (b m)).2.2) hsupp hat'
  have hz (m) : (∫ v, (supportedSeq n (b m)).1 v*u v) = 0 := by
    have hz := hzero (Nat.pair n (b m))
    unfold smoothTest at hz
    rw [Nat.unpair_pair] at hz
    exact hz
  simp_rw [hz] at ht
  have hlim : (0 : ℝ) = ∫ v, ψ v*u v := tendsto_nhds_unique tendsto_const_nhds ht
  simpa only [smul_eq_mul] using hlim.symm

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
