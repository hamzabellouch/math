import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeOutgoingSpectrum
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace OAI

/-! The zero outgoing count excludes every free zero in angular degree at
least two, including the boundary of the counting half-plane. -/

namespace DefocusingNLS

theorem free_outgoing_nonzero (hR : RectangleRouche) (ell : ℕ) (hell : 2 ≤ ell)
    (b Z : ℝ) (hD : (b,Z) ∈ freeMatchingDisk) (lam : ℂ)
    (hhalf : -(1/32 : ℝ)≤lam.re) : spectralSlowDeterminant ell b Z lam≠0 := by
  have hZ : Z≠0 := by
    have hh := (abs_le.mp (freeMatchingDisk_subset_certificate_box hD).2).1
    intro hz
    norm_num [hz] at hh
  have hc := free_outgoing_count hR ell b Z hD
  have hcount : closedCountingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z)=0 := by
    simpa only [freeOutgoingCount,ite_eq_right (show ell≠0 by omega),
      ite_eq_right (show ell≠1 by omega),Nat.cast_zero] using hc
  let f := fun z : {z : ℂ | -(1/32 : ℝ)≤z.re} =>
    analyticOrderAt (spectralSlowDeterminant ell b Z) z.val
  have hs : Summable f := ⟨_,hasSum_of_isLUB _ (isLUB_sSup (Set.range
    (fun s : Finset {z : ℂ | -(1/32 : ℝ)≤z.re} => ∑ z ∈ s, f z)))⟩
  have ho : analyticOrderAt (spectralSlowDeterminant ell b Z) lam=0 :=
    hs.tsum_eq_zero_iff.mp hcount ⟨lam,hhalf⟩
  exact (analyticAt_spectralSlowDeterminant ell b Z lam hZ hhalf).analyticOrderAt_eq_zero.mp ho

end DefocusingNLS

end OAI
