import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalBranchEstimates

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable

structure PhysicalScaleBounds (m : ℕ) (t r R C S s₀ h : ℝ) (u : Time) : Prop where
  mesh_pos : 0  <  m
  time_pos : 0  <  t
  radius_pos : 0  <  r
  radius_le : r ≤ 1
  R_nonneg : 0 ≤ R
  C_nonneg : 0 ≤ C
  window_pos : 0  <  h
  prefix_eq : (u:ℝ)=h/(2*t)
  small : r*R ≤ 1
  separation : r+2*S ≤ s₀
  mesh_radius : (2*t)/(m:ℝ) ≤ r^2
  mesh_scale : (m:ℝ)*r^2 ≤ 2*(2*t)
  window : 2*((2*t)/(m:ℝ)) ≤ h
  large : 8*(2*t) ≤ (m:ℝ)*h
  drift : 26/(m:ℝ) ≤ r

variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def PhysicalMomentData {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) (q : ℝ≥0∞)
    (d : PhysicalDatum N K M G L) : Prop :=
  (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ) ≤ 2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
  (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card ≤ M) ∧
  (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
  (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
    physicalCollisionReference hL g m t r R C S u particle d j
      {p | TrialCollision r (projectCurve L f.val) p.val} ≤ q)

omit [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma PhysicalMomentData.accessible {N M G : ℕ} {L : Length} {hL : L.val=(K:ℝ)}
    {g : Fin G} {m : ℕ} {t r R C S : ℝ} {u : Time} {particle : J↪Fin N}
    {ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)} {q : ℝ≥0∞}
    {d : PhysicalDatum N K M G L} (hd : PhysicalMomentData hL g m t r R C S u particle ν q d)
    (hM : 0 < M) :
    ∀ᵐp ∂ν d,∀i : Fin p.val.length,
      (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty := by
  filter_upwards [hd.1] with p hp
  intro i
  apply Finset.card_pos.mp
  have H := hp _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hc : (0:ℝ) < (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).card := by linarith
  exact_mod_cast hc

theorem physical_branch_moment_data {N M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (h50 : 50 < L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (flags : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (t r R C S s₀ h : ℝ) (u : Time) (hs : PhysicalScaleBounds m t r R C S s₀ h u)
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1) :
    ∀ᵐd ∂(physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).restrict E,
      PhysicalMomentData hL g m t r R C S u (branchParticles g a) ν (datumCollisionBound t r h R C) d := by
  filter_upwards [physicalBranchLaw_path_supply hL μ g flags a m r R C S s₀ t u E hE ν hgood,
    ae_restrict_of_ae (physicalBranchLaw_multiplicity hL hK μ g flags a m r R C S s₀ (2*t) u),
    ae_restrict_of_ae (physicalBranchLaw_normalized hL hK h50 μ m r R C S s₀ t u g flags a),
    ae_restrict_of_ae (physicalBranchLaw_collision hL hK h50 hs.mesh_pos μ g flags a t r R C S s₀ h u
      hs.time_pos hs.radius_pos hs.radius_le hs.R_nonneg hs.C_nonneg hs.window_pos hs.prefix_eq
      hs.small hs.separation hs.mesh_radius hs.mesh_scale hs.window hs.large hs.drift)] with d h₁ h₂ h₃ h₄
  exact ⟨h₁,h₂,h₃.2,h₄⟩

end HardSphere.Groups
end
end

end OAI
