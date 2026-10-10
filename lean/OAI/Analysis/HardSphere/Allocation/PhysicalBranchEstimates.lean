import Mathlib
import OAI.Analysis.HardSphere.Conditioning.RouteMatches
import OAI.Analysis.HardSphere.Collisions.PhysicalCollisionReference
import OAI.Analysis.HardSphere.Allocation.PhysicalLabelLaw

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

def branchParticles {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) :
    {i // i∈groupUnion g a}↪Fin N := ⟨Subtype.val,Subtype.val_injective⟩

lemma physicalBranchLaw_primary {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) (v : Fin 3→Fin K) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u,
      IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u (branchParticles g a) v d) := by
  filter_upwards [physicalBranchLaw_normalized hL hK h50 μ m r R C S s₀ t u g b a] with d hd
  change IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u
    (fun i : {i // i∈groupUnion g a} ↦ i.val) v d)
  rw [physicalPrimaryReference_actual]
  have := hd.1
  infer_instance

theorem physicalBranchLaw_collision {N K M G m : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val) (hm : 0 < m)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (t r R C S s₀ h : ℝ) (u : Time)
    (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hR : 0≤R) (hC : 0≤C) (hh : 0<h)
    (hu : (u:ℝ)=h/(2*t)) (hsmall : r*R≤1) (hsep : r + 2*S ≤ s₀)
    (hτr : (2*t)/(m:ℝ)≤r^2) (hmscale : (m:ℝ)*r^2≤2*(2*t))
    (hwindow : 2*((2*t)/(m:ℝ))≤h) (hlarge : 8*(2*t)≤(m:ℝ)*h) (hdrift : 26/(m:ℝ)≤r) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u,
      ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u (branchParticles g a) d (some k),
        physicalCollisionReference hL g m t r R C S u (branchParticles g a) d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤datumCollisionBound t r h R C := by
  filter_upwards [physicalBranchLaw_geometry hL hK μ g b a m r R C S s₀ (2*t) u] with d hd
  apply physicalCollisionReference_collision hL h50 hm g t r R C S h u ht hr hr1 hR hC hh hu
    hsmall hτr hmscale hwindow hlarge hdrift (branchParticles g a) d
    (fun j ↦ (hd j).1) (fun j ↦ (hd j).2.1)
  · intro i j hij
    exact hsep.trans_lt ((hd i).2.2 j.val (fun he ↦ hij (Subtype.ext he.symm))).1
  · intro i j hij
    exact hsep.trans_lt ((hd i).2.2 j.val (fun he ↦ hij (Subtype.ext he.symm))).2

def latticeDatumBad {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (d : PhysicalDatum N K M G L) :
    Finset (DiscreteTorus K) := (datumBad hL g m t r R C S u d).image indexSite
lemma latticeDatumBad_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) :
    Measurable (latticeDatumBad (N:=N) (M:=M) hL g m t r R C S u) :=
  (measurable_of_countable (fun A : Finset (Fin 3→Fin K) ↦ A.image indexSite)).comp
    (datumBad_measurable hL g m t r R C S u)
lemma mem_latticeDatumBad {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (d : PhysicalDatum N K M G L)
    (v : DiscreteTorus K) : v∈latticeDatumBad hL g m t r R C S u d ↔
      siteIndex v∈datumBad hL g m t r R C S u d := by
  change v∈Finset.image _ _ ↔ _
  constructor
  · rintro hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    simpa only [siteIndex_indexSite] using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨siteIndex v,hv,indexSite_siteIndex v⟩

lemma physicalBranchLaw_path_supply {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) {x y : DiscreteTorus K}
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1) :
    ∀ᵐd ∂(physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).restrict E,
      ∀ᵐp ∂ν d,∀v∈departureSites p,
        (M:ℝ)≤2*((branchAccessible hL g m t r R C S u (branchParticles g a) v d).card:ℝ) := by
  filter_upwards [ae_restrict_of_ae (physicalBranchLaw_allocation hL μ g b a m r R C S s₀ (2*t) u),
    ae_restrict_mem hE] with d hd hdE
  have hp : ∀ᵐp ∂ν d,simplePathGood (latticeDatumBad hL g m t r R C S u d) p :=
    (mem_ae_iff_prob_eq_one (Set.to_countable _).measurableSet).mpr (hgood d hdE)
  filter_upwards [hp] with p hp
  intro v hv
  apply branchAccessible_supply hL g a m t r R C S u v d hd
  intro hvb
  exact hp v (List.mem_toFinset.mp (departureSites_subset p hv))
    ((mem_latticeDatumBad hL g m t r R C S u d v).mpr hvb)

end HardSphere.Groups
end
end

end OAI
