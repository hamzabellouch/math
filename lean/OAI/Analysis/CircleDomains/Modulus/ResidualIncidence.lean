import OAI.Analysis.CircleDomains.Topology.PathTags

namespace OAI

/-! Borel residual incidences after finite point deletions. Compact time
projection proves these directly, including the prior-path and level tests. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

def separatedResidualIncidence (B : Set X) (I : Set PathTime)
    (R : Set (Y × X)) (P : Set X) (r : ℝ) : Set (TaggedPath X × Y) :=
  {q | ∃ t ∈ residualTimes B q.1, t ∈ I ∧ (q.2, q.1.1 t) ∈ R ∧
    ∀ p ∈ P, r ≤ dist (q.1.1 t) p}

theorem isClosed_separatedResidualIncidence {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    (P : Set X) (r : ℝ) : IsClosed (separatedResidualIncidence B I R P r) := by
  let H : Set ((TaggedPath X × Y) × PathTime) :=
    {q | q.2 ∈ residualTimes B q.1.1 ∧ q.2 ∈ I ∧ (q.1.2, q.1.1.1 q.2) ∈ R ∧
      ∀ p ∈ P, r ≤ dist (q.1.1.1 q.2) p}
  have he : Continuous (fun q : (TaggedPath X × Y) × PathTime => q.1.1.1 q.2) :=
    continuous_eval.comp (continuous_fst.fst.fst.prodMk continuous_snd)
  have hH : IsClosed H := by
    refine ((isClosed_residualTimeGraph hB).preimage
      (continuous_fst.fst.prodMk continuous_snd)).inter ?_
    refine (hI.preimage continuous_snd).inter ?_
    refine (hR.preimage (continuous_fst.snd.prodMk he)).inter ?_
    change IsClosed {q : (TaggedPath X × Y) × PathTime |
      ∀ p ∈ P, r ≤ dist (q.1.1.1 q.2) p}
    simp only [ofPred_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ =>
      isClosed_le continuous_const (he.dist continuous_const)
  have hproj : Prod.fst '' H = separatedResidualIncidence B I R P r := by
    ext q
    constructor
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(q, t), ht, rfl⟩
  rw [← hproj]
  exact isClosedMap_fst_of_compactSpace H hH

def residualIncidence (B : Set X) (I : Set PathTime) (R : Set (Y × X))
    (P : Set X) : Set (TaggedPath X × Y) :=
  {q | ∃ t ∈ residualTimes B q.1, t ∈ I ∧ (q.2, q.1.1 t) ∈ R ∧ q.1.1 t ∉ P}

omit [TopologicalSpace Y] in
theorem residualIncidence_eq_iUnion (B : Set X) (I : Set PathTime)
    (R : Set (Y × X)) {P : Set X} (hP : IsClosed P) :
    residualIncidence B I R P =
      ⋃ n : ℕ, separatedResidualIncidence B I R P (1 / ((n : ℝ) + 1)) := by
  ext q
  constructor
  · rintro ⟨t, ht, hI, hR, hnot⟩
    obtain ⟨ε, hε, hball⟩ := isOpen_iff.mp hP.isOpen_compl (q.1.1 t) hnot
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine mem_iUnion.mpr ⟨n, t, ht, hI, hR, fun p hp => hn.le.trans ?_⟩
    by_contra h
    have hd : dist p (q.1.1 t) < ε := by simpa only [dist_comm] using not_le.mp h
    exact hball hd hp
  · intro h
    obtain ⟨n, t, ht, hI, hR, hsep⟩ := mem_iUnion.mp h
    refine ⟨t, ht, hI, hR, ?_⟩
    intro hp
    have h := hsep _ hp
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

variable [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_residualIncidence {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    {P : Set X} (hP : P.Finite) : MeasurableSet (residualIncidence B I R P) := by
  rw [residualIncidence_eq_iUnion B I R hP.isClosed]
  exact MeasurableSet.iUnion fun n =>
    (isClosed_separatedResidualIncidence hB hI hR P (1 / ((n : ℝ) + 1))).measurableSet

end CircleDomainRigidity

end

end OAI
