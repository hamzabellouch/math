import OAI.Analysis.CircleDomains.Probability.HitFusionLaw
import OAI.Analysis.CircleDomains.Probability.ContinuousLawMeasurable
import OAI.Analysis.CircleDomains.Modulus.ConfigurationNorm

namespace OAI

/-! Fusion of a nonsmall closed family of path laws into a law with finite
point-hit square norm. All finite splitting and branch laws are constructed. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MetricSpace Z] [SecondCountableTopology Z] [CompleteSpace Z]
  {law : Z → ProbabilityMeasure C(PathTime, X)} {C : ℝ}

namespace HitFusionData

variable (T : HitFusionData (law := law) (C := C)) (hlaw : Continuous law)

def fusedLaw : ProbabilityMeasure C(PathTime, X) :=
  probabilityMixture T.addressLaw (law ∘ T.endpoint) (measurable_of_continuous_probability (hlaw.comp T.continuous_endpoint))

omit [CompactSpace X] [SecondCountableTopology X] [BorelSpace X]
    [SecondCountableTopology Z] in
theorem weighted_fusedLaw {n : ℕ} {r : ℝ} (p : HitConfiguration X n r) :
    weightedConfigurationHits (fun _ : Unit => T.fusedLaw hlaw) () p =
      ∫ x, weightedConfigurationHits law (T.endpoint x) p
        ∂(T.addressLaw : Measure (ℕ → ℕ)) := by
  unfold weightedConfigurationHits
  simp_rw [fusedLaw, pathHitReal_mixture]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (integral_const_mul _ _).symm
  · intro i _
    exact (integrable_pathHitReal T.addressLaw
      (measurable_of_continuous_probability (hlaw.comp T.continuous_endpoint)) (p.val.1 i)).const_mul _

omit [CompactSpace X] [SecondCountableTopology Z] in
theorem fusedLaw_configuration_bound (d : ℕ)
    (p : HitConfiguration X (T.sizes d) (T.separations d)) :
    weightedConfigurationHits (fun _ : Unit => T.fusedLaw hlaw) () p ≤ C + T.error := by
  rw [T.weighted_fusedLaw hlaw p]
  exact T.integral_endpoint_hits_le hlaw d p

end HitFusionData


def standardHitFusion (hlaw : Continuous law) (hC : 0 ≤ C)
    (root : ClosedHitCandidate law C) (ε : ℝ) (hε : 0 < ε) :
    HitFusionData (law := law) (C := C) where
  sizes d := (Nat.unpair d).1
  separations d := 1 / (((Nat.unpair d).2 : ℝ) + 1)
  error := ε
  initial := root
  split d A := Classical.choice (nonempty_hitFusionSplit hlaw hC A (Nat.unpair d).1
    (by positivity) hε (by positivity))

theorem standardHitFusion_norm_bound (hlaw : Continuous law) (hC : 0 ≤ C)
    (root : ClosedHitCandidate law C) {ε : ℝ} (hε : 0 < ε) :
    HasHitNormBound ((standardHitFusion hlaw hC root ε hε).fusedLaw hlaw) (C + ε) := by
  apply hasHitNormBound_of_configuration_bounds _ ?_ (by positivity)
  intro n m
  have hb := (standardHitFusion hlaw hC root ε hε).fusedLaw_configuration_bound hlaw
    (Nat.pair n m)
  have hs : (standardHitFusion hlaw hC root ε hε).sizes (Nat.pair n m) = n := by
    change (Nat.unpair (Nat.pair n m)).1 = n
    rw [Nat.unpair_pair]
  have hr : (standardHitFusion hlaw hC root ε hε).separations (Nat.pair n m) =
      1 / ((m : ℝ) + 1) := by
    change 1 / (((Nat.unpair (Nat.pair n m)).2 : ℝ) + 1) = _
    rw [Nat.unpair_pair]
  rw [hs, hr] at hb
  exact hb

/-- The fused law is supported on original candidates, not merely limits of
arbitrary probability laws. Its positive point-hit support is countable. -/
theorem exists_hit_norm_mixture_of_nonsmall (hlaw : Continuous law) (hC : 0 ≤ C)
    {A : Set Z} (hAclosed : IsClosed A) (hA : ¬HitTestSmall law C A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ProbabilityMeasure (ℕ → ℕ)) (e : C(ℕ → ℕ, Z)),
      (∀ x, e x ∈ A) ∧
      HasHitNormBound (probabilityMixture P (law ∘ e) (measurable_of_continuous_probability (hlaw.comp e.continuous)))
        (C + ε) := by
  let root : ClosedHitCandidate law C := ⟨A, hAclosed, hA⟩
  let T := standardHitFusion hlaw hC root ε hε
  refine ⟨T.addressLaw, ⟨T.endpoint, T.continuous_endpoint⟩, ?_, ?_⟩
  · intro x
    exact T.endpoint_mem x 0
  · exact standardHitFusion_norm_bound hlaw hC root hε

/-- The original countable and atomless tests supply the nonsmall root of the
constructed fusion tree. -/
theorem exists_hit_norm_mixture_of_countable_tests
    (hlaw : Continuous law) (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ∃ z, PassesHitTests C (law z) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ProbabilityMeasure (ℕ → ℕ)) (e : C(ℕ → ℕ, Z)),
      HasHitNormBound (probabilityMixture P (law ∘ e)
        (measurable_of_continuous_probability (hlaw.comp e.continuous))) (C + ε) := by
  obtain ⟨P, e, _, hb⟩ := exists_hit_norm_mixture_of_nonsmall hlaw hC isClosed_univ
    (not_hitTestSmall_univ htest) hε
  exact ⟨P, e, hb⟩

end CircleDomainRigidity

end

end OAI
