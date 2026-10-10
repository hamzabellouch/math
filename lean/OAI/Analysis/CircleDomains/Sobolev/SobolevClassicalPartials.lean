import OAI.Analysis.CircleDomains.Sobolev.SobolevCoordinateFTC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

namespace OAI

/-! On almost every coordinate line, the classical derivative of the
continuous Sobolev representative equals its actual weak partial. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma locallyIntegrable_of_intervalIntegrable {G : ℝ → ℝ}
    (hG : ∀ a b, IntervalIntegrable G volume a b) : LocallyIntegrable G volume := by
  intro x
  refine ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (hG (x-1) (x+1)).1.mono_set Ioo_subset_Ioc_self

lemma ae_hasDerivAt_of_integral_increments {u G : ℝ → ℝ}
    (hG : ∀ a b, IntervalIntegrable G volume a b)
    (hinc : ∀ a b, (∫ t in a..b, G t) = u b-u a) :
    ∀ᵐ t ∂volume, HasDerivAt u (G t) t := by
  have hu : u = fun t => u 0 + ∫ s in (0 : ℝ)..t, G s := by
    funext t
    rw [hinc]
    ring
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_of_intervalIntegrable hG)] with t ht
  rw [hu]
  exact (ht 0).const_add _

lemma sobolev_coordinate_ae_hasDerivAt {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ t ∂volume,
      HasDerivAt (fun s => u (physicalCoordinateLine i y s))
        (W.weakGrad (physicalCoordinateLine i y t) i) t := by
  filter_upwards [exact_sobolev_line_payment hu hs W i,
    sobolev_coordinate_fundamentalTheorem hu hs W i] with y hy hftc
  exact ae_hasDerivAt_of_integral_increments (fun a b => (hy a b).1) hftc

end CircleDomainRigidity

end

end OAI
