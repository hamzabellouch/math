import OAI.Analysis.CircleDomains.Modulus.ResidualIncidence

namespace OAI

/-! Compact residual images and their Borel incidence masses. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def residualImage (B : Set X) (Γ : TaggedPath X) : Set X :=
  Γ.1 '' residualTimes B Γ

theorem isCompact_residualImage {B : Set X} (hB : IsClosed B) (Γ : TaggedPath X) :
    IsCompact (residualImage B Γ) :=
  (isCompact_residualTimes hB Γ).image Γ.1.continuous

theorem residualImage_subset (B : Set X) (Γ : TaggedPath X) : residualImage B Γ ⊆ B := by
  rintro x ⟨t, ht, rfl⟩
  exact ht.1

def residualImageGraph (B : Set X) : Set (TaggedPath X × X) :=
  {q | q.2 ∈ residualImage B q.1}

theorem isClosed_residualImageGraph {B : Set X} (hB : IsClosed B) :
    IsClosed (residualImageGraph B) := by
  let H : Set ((TaggedPath X × X) × PathTime) :=
    {q | (q.1.1, q.2) ∈ residualTimeGraph B ∧ q.1.1.1 q.2 = q.1.2}
  have hH : IsClosed H :=
    ((isClosed_residualTimeGraph hB).preimage
      (continuous_fst.fst.prodMk continuous_snd)).inter
        (isClosed_eq (continuous_eval.comp
          (continuous_fst.fst.fst.prodMk continuous_snd)) continuous_fst.snd)
  have heq : Prod.fst '' H = residualImageGraph B := by
    ext q
    constructor
    · rintro ⟨⟨p, t⟩, ⟨ht, heq⟩, rfl⟩
      exact ⟨t, ht, heq⟩
    · rintro ⟨t, ht, heq⟩
      exact ⟨(q, t), ⟨ht, heq⟩, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace H hH

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_residualImageMass {B : Set X} (hB : IsClosed B)
    (ν : Measure X) [SFinite ν] :
    Measurable (fun Γ : TaggedPath X => ν (residualImage B Γ)) :=
  measurable_measure_prodMk_left (isClosed_residualImageGraph hB).measurableSet

theorem measurableSet_residualImageMass_zero {B : Set X} (hB : IsClosed B)
    (ν : Measure X) [SFinite ν] :
    MeasurableSet {Γ : TaggedPath X | ν (residualImage B Γ) = 0} :=
  (measurable_residualImageMass hB ν) (measurableSet_singleton 0)

variable {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem measurable_residualIncidenceMass {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    {P : Set X} (hP : P.Finite) (ν : Measure Y) [SFinite ν] :
    Measurable (fun Γ : TaggedPath X =>
      ν {y | (Γ, y) ∈ residualIncidence B I R P}) :=
  measurable_measure_prodMk_left (measurableSet_residualIncidence hB hI hR hP)

end CircleDomainRigidity

end

end OAI
