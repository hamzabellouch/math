import OAI.Analysis.CircleDomains.Rigidity.CountableTraceEnumeration
import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonRadii
import OAI.Analysis.CircleDomains.Topology.ShrinkingBallNeighborhoods

namespace OAI

/-! Actual intervals for the matched disks. Their lengths are square
summable and their centers represent values of the closed correspondence.
Unused natural codes are harmless shrinking intervals at one fixed fiber. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

 theorem MatchedRoundDisks.source_center_mem (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    (E.sourceCenter j : Sphere) ∈ j.val.1 := by
  rw [E.source_eq]
  exact mem_image_of_mem _ (mem_closedBall_self (E.source_nonneg j))

 theorem MatchedRoundDisks.target_center_mem (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    (E.targetCenter j : Sphere) ∈ j.val.2 := by
  rw [E.target_eq]
  exact mem_image_of_mem _ (mem_closedBall_self (E.target_nonneg j))

 theorem MatchedRoundDisks.centers_related (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    D.componentRelation (E.sourceCenter j : Sphere) (E.targetCenter j : Sphere) := by
  change (E.targetCenter j : Sphere) ∈ D.targetFiber (E.sourceCenter j : Sphere)
  rw [j.property.1.2.2 _ (E.source_center_mem j)]
  exact E.target_center_mem j

 theorem MatchedRoundDisks.scalar_fiber_bound (E : D.MatchedRoundDisks)
    {φ : Sphere → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (j : D.IndexedMatchedPair) {q p : Sphere} (hq : q ∈ j.val.1)
    (hp : D.componentRelation q p) : |φ p-φ (E.targetCenter j : Sphere)| ≤ L*E.targetRadius j := by
  have hp' : p ∈ j.val.2 := by
    rw [← j.property.1.2.2 q hq]
    exact hp
  rw [E.target_eq] at hp'
  obtain ⟨z,hz,rfl⟩ := hp'
  exact (hL.dist_le_mul z (E.targetCenter j)).trans
    (mul_le_mul_of_nonneg_left hz L.coe_nonneg)

variable [Encodable D.IndexedMatchedPair]

 def MatchedRoundDisks.traceCenter (E : D.MatchedRoundDisks) : ℕ → ℂ :=
  traceEnumeration E.sourceCenter 0

 def MatchedRoundDisks.traceRadius (E : D.MatchedRoundDisks) : ℕ → ℝ :=
  traceEnumeration E.sourceRadius 0

 def MatchedRoundDisks.traceTargetRadius (E : D.MatchedRoundDisks) : ℕ → ℝ :=
  traceEnumeration E.targetRadius 0

 def MatchedRoundDisks.traceScalarCenter (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) : ℕ → ℝ :=
  traceEnumeration (fun j => φ (E.targetCenter j : Sphere))
    (φ (D.selectedTarget hG hf (0 : ℂ)))

 def MatchedRoundDisks.traceWidth (E : D.MatchedRoundDisks) (L : ℝ≥0) (n : ℕ) : ℝ :=
  L*E.traceTargetRadius n+traceExtraRadius n

 def MatchedRoundDisks.traceInterval (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ)
    (L : ℝ≥0) (n : ℕ) : Set ℝ :=
  Ioo (E.traceScalarCenter hG hf φ n-E.traceWidth L n)
      (E.traceScalarCenter hG hf φ n+E.traceWidth L n)

 theorem MatchedRoundDisks.traceWidth_pos (E : D.MatchedRoundDisks) (L : ℝ≥0) (n : ℕ) :
    0 < E.traceWidth L n :=
  add_pos_of_nonneg_of_pos (mul_nonneg L.coe_nonneg
    (traceEnumeration_nonneg E.target_nonneg n)) (traceExtraRadius_pos n)

 theorem MatchedRoundDisks.traceWidth_summable_sq (E : D.MatchedRoundDisks) (L : ℝ≥0) :
    Summable (fun n => E.traceWidth L n^2) := by
  have hs := (traceEnumeration_summable_sq E.target_summable).mul_left (2*(L:ℝ)^2)
  apply (hs.add (traceExtraRadius_summable_sq.mul_left 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro n
  dsimp only [traceWidth,traceTargetRadius]
  nlinarith [sq_nonneg ((L:ℝ)*traceEnumeration E.targetRadius 0 n-traceExtraRadius n)]

 theorem MatchedRoundDisks.traceWidth_tendsto (E : D.MatchedRoundDisks) (L : ℝ≥0) :
    Tendsto (E.traceWidth L) atTop (𝓝 0) :=
  nonnegative_square_summable_tendsto_zero (fun n => (E.traceWidth_pos L n).le)
    (E.traceWidth_summable_sq L)

 theorem MatchedRoundDisks.traceInterval_length (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ)
    (L : ℝ≥0) (n : ℕ) :
    volume.real (E.traceInterval hG hf φ L n) = 2*E.traceWidth L n := by
  rw [traceInterval,Real.volume_real_Ioo_of_le (by linarith [E.traceWidth_pos L n])]
  ring

 theorem MatchedRoundDisks.traceInterval_summable_sq (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) (L : ℝ≥0) :
    Summable (fun n => volume.real (E.traceInterval hG hf φ L n)^2) := by
  simpa only [E.traceInterval_length,mul_pow,show (2:ℝ)^2=4 by norm_num] using
    (E.traceWidth_summable_sq L).mul_left 4

 theorem MatchedRoundDisks.traceInterval_represents (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ)
    (L : ℝ≥0) (n : ℕ) (t : ℝ) (ht : t ∈ E.traceInterval hG hf φ L n) :
    ∃ p : Sphere, D.componentRelation (E.traceCenter n : Sphere) p ∧
      |t-φ p| ≤ E.traceWidth L n := by
  have ht' : |t-E.traceScalarCenter hG hf φ n| ≤ E.traceWidth L n := by
    apply abs_le.mpr
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
  · obtain ⟨j,rfl⟩ := hn
    refine ⟨(E.targetCenter j : Sphere),?_,?_⟩
    · simpa only [traceCenter,traceEnumeration_encode] using E.centers_related j
    · simpa only [traceScalarCenter,traceEnumeration_encode] using ht'
  · refine ⟨D.selectedTarget hG hf (0 : ℂ),?_,?_⟩
    · simpa only [traceCenter,traceEnumeration_missing _ _ hn] using
        D.selectedTarget_mem hG hf (0 : ℂ)
    · simpa only [traceScalarCenter,traceEnumeration_missing _ _ hn] using ht'

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
