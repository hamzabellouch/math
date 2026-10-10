import Mathlib
import OAI.NumberTheory.PrimePackets.PacketMoments

namespace OAI

noncomputable section
open scoped Topology Pointwise ENNReal
open Module Filter Set MeasureTheory
namespace PrimeDegreePackets.Adelic

 

structure PacketTorusParametrization {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (Q : Type*) [CommGroup Q] [TopologicalSpace Q]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) where
  point : Q → X (d+1)
  continuous_point : Continuous point
  liftFlow : LogCoordinates d → Q
  continuous_liftFlow : Continuous liftFlow
  flow_eq : ∀ q u, point (q * liftFlow u) = orbitMap (point q) u
  fibers_mul : ∀ {s t}, point s = point t → ∀ q, point (q*s) = point (q*t)
  range_eq : Set.range point = packetSupport M σ

namespace PacketTorusParametrization
variable {d : ℕ} {K Q : Type*} [Field K] [NumberField K]
  [CommGroup Q] [TopologicalSpace Q] {M : FullLattice (d+1) K}
  {σ : OrderedEmbeddings (d+1) K} (P : PacketTorusParametrization Q M σ)
include P

lemma period_eq (q s : Q) : periodGroup (P.point q) = periodGroup (P.point s) := by
  ext u
  change orbitMap (P.point q) u = P.point q ↔ orbitMap (P.point s) u = P.point s
  rw [← P.flow_eq,← P.flow_eq]
  constructor
  · intro h
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using P.fibers_mul h (s*q⁻¹)
  · intro h
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using P.fibers_mul h (q*s⁻¹)

lemma exists_basepoint_lift (O : packetOrbits M σ) : ∃ q, P.point q = orbitBasepoint O := by
  apply Set.mem_range.mp
  rw [P.range_eq]
  refine Set.mem_iUnion.mpr ⟨O,?_⟩
  rw [← orbitBasepoint_spec O]
  exact mem_diagonalOrbit_self _

def select (O : packetOrbits M σ) : Q := (P.exists_basepoint_lift O).choose

lemma select_eq (O : packetOrbits M σ) : P.point (P.select O) = orbitBasepoint O :=
  (P.exists_basepoint_lift O).choose_spec

lemma point_orbit_mem (q : Q) : diagonalOrbit (P.point q) ∈ packetOrbits M σ := by
  have hx : P.point q ∈ packetSupport M σ := by rw [← P.range_eq]; exact ⟨q,rfl⟩
  obtain ⟨O,hO⟩ := Set.mem_iUnion.mp hx
  rw [← orbitBasepoint_spec O] at hO
  obtain ⟨u,hu⟩ := hO
  rw [← hu,diagonalOrbit_orbitMap,orbitBasepoint_spec]
  exact O.property

def orbitTranslate (q : Q) (O : packetOrbits M σ) : packetOrbits M σ :=
  ⟨diagonalOrbit (P.point (q*P.select O)),P.point_orbit_mem _⟩

lemma orbitTranslate_injective (q : Q) : Function.Injective (P.orbitTranslate q) := by
  intro O O' h
  have he : diagonalOrbit (P.point (q*P.select O)) = diagonalOrbit (P.point (q*P.select O')) :=
    congrArg Subtype.val h
  have hx := mem_diagonalOrbit_self (P.point (q*P.select O))
  rw [he] at hx
  obtain ⟨u,hu⟩ := hx
  rw [← P.flow_eq] at hu
  have H := P.fibers_mul hu q⁻¹
  simp only [mul_assoc,inv_mul_cancel_left] at H
  rw [P.flow_eq,P.select_eq,P.select_eq] at H
  apply Subtype.ext
  rw [← orbitBasepoint_spec O,← orbitBasepoint_spec O',← H,diagonalOrbit_orbitMap]

lemma basepoint_period_eq (O O' : packetOrbits M σ) :
    periodGroup (orbitBasepoint O) = periodGroup (orbitBasepoint O') := by
  rw [← P.select_eq O,← P.select_eq O']
  exact P.period_eq _ _

lemma basepoint_volume_eq (O O' : packetOrbits M σ) :
    orbitVolume (orbitBasepoint O) = orbitVolume (orbitBasepoint O') := by
  unfold orbitVolume
  rw [P.basepoint_period_eq O O']

lemma point_period_eq_basepoint (q : Q) (O : packetOrbits M σ) :
    periodGroup (P.point q) = periodGroup (orbitBasepoint O) := by
  rw [← P.select_eq O]
  exact P.period_eq _ _

lemma packetMeasure_eq_uniform [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (hodd : Odd (d+1)) [Fintype (packetOrbits M σ)]
    (O₀ : packetOrbits M σ) :
    packetMeasure M σ = (Fintype.card (packetOrbits M σ) : ℝ≥0∞)⁻¹ •
      ∑ O : packetOrbits M σ, orbitProbability (orbitBasepoint O) := by
  have hv := packetBasepoint_volume_pos_finite hn hodd O₀
  have hvol : ∀ O : packetOrbits M σ, orbitVolume (orbitBasepoint O) = orbitVolume (orbitBasepoint O₀) :=
    fun O => P.basepoint_volume_eq O O₀
  rw [packetMeasure,tsum_fintype,Measure.sum_fintype]
  simp only [hvol,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.smul_sum]
  rw [smul_smul,ENNReal.mul_inv (Or.inr hv.2) (Or.inr hv.1),mul_assoc,ENNReal.inv_mul_cancel hv.1 hv.2,mul_one]

lemma sum_translated_orbitProbabilities [Fintype (packetOrbits M σ)] (q : Q) :
    ∑ O : packetOrbits M σ, orbitProbability (P.point (q * P.select O)) =
      ∑ O : packetOrbits M σ, orbitProbability (orbitBasepoint O) := by
  have he (O : packetOrbits M σ) :
      orbitProbability (P.point (q*P.select O)) = orbitProbability (orbitBasepoint (P.orbitTranslate q O)) := by
    apply orbitProbability_eq_of_diagonalOrbit_eq
    exact (orbitBasepoint_spec (P.orbitTranslate q O)).symm
  simp_rw [he]
  exact Fintype.sum_bijective _ ⟨P.orbitTranslate_injective q,Finite.surjective_of_injective (P.orbitTranslate_injective q)⟩ _ _ (fun _ => rfl)

 

lemma exists_common_average [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    ∃ θ : Measure (LogCoordinates d), IsProbabilityMeasure θ ∧ ∀ q : Q,
      Measure.map (orbitMap (P.point q)) θ = orbitProbability (P.point q) := by
  obtain ⟨O,hO⟩ := packetOrbits_nonempty M σ
  let O₀ : packetOrbits M σ := ⟨O,hO⟩
  let := packetBasepoint_period_isZLattice hn hodd O₀
  have : Countable (periodGroup (orbitBasepoint O₀)) := countable_of_Lindelof_of_discrete
  obtain ⟨s,hs⟩ := (periodGroup_hasFundamentalDomain (orbitBasepoint O₀)).ExistsIsAddFundamentalDomain
  have hv : volume s ≠ 0 ∧ volume s ≠ ⊤ := by
    rw [← hs.covolume_eq_volume volume]
    exact orbitVolume_ne_zero_ne_top (orbitBasepoint O₀)
  refine ⟨(volume s)⁻¹ • volume.restrict s,?_,?_⟩
  · constructor
    rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv.1 hv.2
  · intro q
    have he := P.point_period_eq_basepoint q O₀
    have : IsZLattice ℝ (periodGroup (P.point q)).toIntSubmodule := by
      simpa only [he] using (inferInstance : IsZLattice ℝ (periodGroup (orbitBasepoint O₀)).toIntSubmodule)
    rw [Measure.map_smul _ (continuous_orbitMap _).measurable.aemeasurable]
    symm
    apply orbitProbability_eq_normalized_map_sublattice (P.point q)
      (periodGroup (orbitBasepoint O₀)).toIntSubmodule
    · rw [he]
    · exact hs

end PacketTorusParametrization
end PrimeDegreePackets.Adelic

end

end OAI
