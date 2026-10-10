import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral

namespace OAI

/-! The reference-family analyzing coefficients are exactly the
original physical packet integrals. Swapping coordinates and applying
the reference slope shear preserves product Lebesgue measure, including
for the totalized Bochner integral without an integrability premise. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

/-- Reference coordinates are ordered `(transverse, horizontal)`. -/
def sourceReferenceToPhysical (t : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodComm.trans (slopeShear t)

@[simp] theorem sourceReferenceToPhysical_apply (t : ℝ) (z : ℝ × ℝ) :
    sourceReferenceToPhysical t z = (z.2, z.1 + t * z.2) := rfl

theorem sourceReferenceToPhysical_measurePreserving (t : ℝ) :
    MeasurePreserving (sourceReferenceToPhysical t)
      (volume.prod volume) (volume.prod volume) :=
  (slopeShear_measurePreserving t).comp Measure.measurePreserving_swap

theorem integral_sourceReferenceToPhysical (t : ℝ) (F : ℝ × ℝ → ℂ) :
    (∫ z, F (sourceReferenceToPhysical t z) ∂volume.prod volume) =
      ∫ z, F z ∂volume.prod volume :=
  (sourceReferenceToPhysical_measurePreserving t).integral_comp
    (sourceReferenceToPhysical t).measurableEmbedding F

namespace SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

def physicalSelectedWave (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (q : Σ j, ι j) (k : κ) (z : ℝ × ℝ) : ℂ :=
  if v z ≤ d q.1 then P.physicalPacket t q.1 q.2 k z else 0

def physicalCoefficient (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (u : ι j) :
    EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume)
    (fun q : Σ j, ι j => P.length q.1 * P.width)
    (P.physicalSelectedWave t d v) g ⟨j, u⟩

theorem family_selectedWave_physical (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (q : Σ j, ι j) (k : κ) (z : ℝ × ℝ) :
    P.family.selectedWave d (fun w => v (sourceReferenceToPhysical t w)) q k z =
      P.physicalSelectedWave t d v q k (sourceReferenceToPhysical t z) := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f z.2)
    (P.raw_eq_physical_slice 0 q.1 q.2 k z.1 t)
  change P.raw 0 q.1 q.2 k z.1 z.2 =
    P.physicalPacket t q.1 q.2 k (sourceReferenceToPhysical t z) at h
  change (if v (sourceReferenceToPhysical t z) ≤ d q.1 then
      P.raw 0 q.1 q.2 k z.1 z.2 else 0) =
    (if v (sourceReferenceToPhysical t z) ≤ d q.1 then
      P.physicalPacket t q.1 q.2 k (sourceReferenceToPhysical t z) else 0)
  split_ifs
  · exact h
  · rfl

/-- The normalized coefficient is unchanged by passing from the
physical packets to their reference-line family. Both the original
field and the original test function are pulled back by the same map. -/
theorem family_mainCoefficient_physical (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (u : ι j) :
    P.family.mainCoefficient d (fun z => v (sourceReferenceToPhysical t z))
      (fun z => g (sourceReferenceToPhysical t z)) j u =
      P.physicalCoefficient t d v g j u := by
  ext k
  simp only [PlanarPacketFamily.mainCoefficient, physicalCoefficient, analyzingCoefficient,
    WithLp.ofLp_toLp, family_length]
  change ((↑(P.length j * P.width) : ℂ)⁻¹) *
      (∫ z, g (sourceReferenceToPhysical t z) k * conj
        (P.family.selectedWave d (fun w => v (sourceReferenceToPhysical t w)) ⟨j, u⟩ k z)
          ∂volume.prod volume) =
    ((↑(P.length j * P.width) : ℂ)⁻¹) *
      (∫ z, g z k * conj (P.physicalSelectedWave t d v ⟨j, u⟩ k z)
        ∂volume.prod volume)
  congr 1
  simp_rw [P.family_selectedWave_physical]
  exact integral_sourceReferenceToPhysical t
    (fun z => g z k * conj (P.physicalSelectedWave t d v ⟨j, u⟩ k z))

end SourceLatticePacket

end LipschitzHilbert

end

end OAI
