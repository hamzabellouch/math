import OAI.Analysis.LipschitzHilbert.Trees.SourcePackedEnvelopeEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedBoxSeparation
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral

namespace OAI

/-! The weighted envelope estimate in the physical coordinates of an
arbitrary reference slope. The shear preserves product Lebesgue measure. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def shearedTileEnvelope (cx cy ell W t : ℝ) (n : ℕ) (z : ℝ×ℝ) : ℝ :=
  tileEnvelope cx (cy-t*cx) ell W n (z.1,z.2-t*z.1)

def shearedTopReciprocal (a b L W t : ℝ) (z : ℝ×ℝ) : ℝ :=
  topReciprocalWeight a (b-t*a) L W (z.1,z.2-t*z.1)

theorem coordinateBox_shear (cx cy ell W t : ℝ) (z : ℝ×ℝ) :
    z∈coordinateBox cx (cy-t*cx) ell W ↔
      |(slopeShear t z).1-cx|≤ell ∧
      |((slopeShear t z).2-cy)-t*((slopeShear t z).1-cx)|≤W := by
  change (|z.1-cx|≤ell ∧ |z.2-(cy-t*cx)|≤W) ↔
    (|z.1-cx|≤ell ∧ |(z.2+t*z.1-cy)-t*(z.1-cx)|≤W)
  have he : z.2-(cy-t*cx)=(z.2+t*z.1-cy)-t*(z.1-cx) := by ring
  rw [he]

theorem sheared_packed_envelope_energy {ι : Type*}
    (S : Finset ι) (cx cy ell : ι → ℝ) (a b L W t K : ℝ)
    (hL : 0<L) (hW : 0<W) (hell : ∀ i∈S, 0<ell i)
    (hlen : ∀ i∈S, ell i≤L)
    (hcount : ∀ z : ℝ×ℝ, ((S.filter fun i => |z.1-cx i|≤ell i ∧
      |(z.2-cy i)-t*(z.1-cx i)|≤W).card:ℝ)≤K) :
    let H := fun z => shearedTopReciprocal a b L W t z*
      ∑ i∈S, shearedTileEnvelope (cx i) (cy i) (ell i) W t 2 z
    Integrable (fun z => (H z)^2) (volume.prod volume) ∧
      (∫ z, (H z)^2 ∂volume.prod volume)≤(82944*K)^2*1296*Real.pi^2*L*W := by
  have hc (z : ℝ×ℝ) :
      ((S.filter fun i => z∈coordinateBox (cx i) (cy i-t*cx i) (ell i) W).card:ℝ)≤K := by
    simpa only [coordinateBox_shear] using hcount (slopeShear t z)
  have h := packed_envelope_energy S cx (fun i => cy i-t*cx i) ell a (b-t*a) L W K hL hW hell hlen hc
  let F := fun z : ℝ×ℝ =>
    (topReciprocalWeight a (b-t*a) L W z*
      ∑ i∈S, tileEnvelope (cx i) (cy i-t*cx i) (ell i) W 2 z)^2
  have he (z : ℝ×ℝ) :
      (shearedTopReciprocal a b L W t z*
        ∑ i∈S, shearedTileEnvelope (cx i) (cy i) (ell i) W t 2 z)^2=F (slopeShear (-t) z) := by
    have hz : (z.1,z.2-t*z.1)=slopeShear (-t) z := by
      ext <;> simp [slopeShear,sub_eq_add_neg]
    simp only [shearedTopReciprocal,shearedTileEnvelope,hz,F]
  constructor
  · simp_rw [he]
    exact (slopeShear_measurePreserving (-t)).integrable_comp_of_integrable h.1
  · simp_rw [he]
    rw [integral_slopeShear]
    exact h.2

end LipschitzHilbert

end

end OAI
