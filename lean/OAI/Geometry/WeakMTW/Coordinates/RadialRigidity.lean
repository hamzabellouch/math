import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateGeometry

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace RadialRigidity
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry

omit [FiniteDimensional ℝ E] in
 theorem eq_endpoints_of_deriv_zero {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) : f a = f b := by
  obtain ⟨k, hk⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv)
  have hkc : EqOn f (fun _ => k) (Icc a b) :=
    (show EqOn f (fun _ => k) (Ioo a b) from hk).of_subset_closure hc continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  exact (hkc ⟨le_rfl, hab.le⟩).trans (hkc ⟨hab.le, le_rfl⟩).symm

omit [FiniteDimensional ℝ E] in
 theorem radial_linear {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U)
    {ν ν' : ℝ → E} {a : ℝ} (ha : a ∈ U) (hzero : ν a = 0)
    (hd : ∀ t ∈ U, HasDerivAt ν (ν' t) t)
    (hr : ∀ t ∈ U, (t - a) • ν' t = ν t) :
    ∀ t ∈ U, ν t = (t - a) • ν' a := by
  let f := dslope ν a
  have hfc : ContinuousOn f U := (continuousOn_dslope (hU.mem_nhds ha)).mpr
    ⟨fun t ht => (hd t ht).continuousAt.continuousWithinAt, (hd a ha).differentiableAt⟩
  have hfd : ∀ t ∈ U, t ≠ a → HasDerivAt f 0 t := by
    intro t ht hta
    have hne : t - a ≠ 0 := sub_ne_zero.mpr hta
    have hd' := (((hasDerivAt_id t).sub_const a).inv hne).smul ((hd t ht).sub_const (ν a))
    have hh : -(1 / (t - a) ^ 2) • (ν t - ν a) + (t - a)⁻¹ • ν' t = 0 := by
      rw [hzero, sub_zero, ← hr t ht, smul_smul, ← add_smul]
      have he : -(1 / (t - a) ^ 2) * (t - a) + (t - a)⁻¹ = 0 := by field_simp; ring
      rw [he, zero_smul]
    have hg : HasDerivAt (slope ν a) 0 t := by
      convert! hd' using 1
      simpa only [id_eq, Pi.inv_apply, neg_div, add_comm] using hh.symm
    exact hg.congr_of_eventuallyEq (dslope_eventuallyEq_slope_of_ne ν hta)
  intro t ht
  have halte : Icc (min a t) (max a t) ⊆ U := by
    exact hUc.ordConnected.uIcc_subset ha ht
  have hfa : f a = ν' a := (dslope_same ν a).trans (hd a ha).deriv
  have hft : f t = f a := by
    rcases lt_trichotomy a t with hat | hat | hat
    · apply (eq_endpoints_of_deriv_zero hat (hfc.mono (by simpa [min_eq_left hat.le, max_eq_right hat.le] using halte)) ?_).symm
      intro s hs
      exact hfd s (halte (by simpa [min_eq_left hat.le, max_eq_right hat.le] using (show s ∈ Icc _ _ from ⟨hs.1.le, hs.2.le⟩))) (ne_of_gt hs.1)
    · rw [hat]
    · apply eq_endpoints_of_deriv_zero hat (hfc.mono (by simpa [min_eq_right hat.le, max_eq_left hat.le] using halte))
      intro s hs
      exact hfd s (halte (by simpa [min_eq_right hat.le, max_eq_left hat.le] using (show s ∈ Icc _ _ from ⟨hs.1.le, hs.2.le⟩))) (ne_of_lt hs.2)
  rw [← sub_smul_dslope_of_zero hzero t, ← hfa]
  exact congrArg ((t - a) • ·) hft

omit [FiniteDimensional ℝ E] in
 theorem gauss_equality {B₀ B₁ : MetricTensor E} {L : E →L[ℝ] E}
    (hs : ∀ v w, B₁ v w = B₁ w v)
    (hp : ∀ v : E, v ≠ 0 → 0 < B₁ v v)
    (hL : Function.Injective L) {v w : E} {T C θ : ℝ}
    (hg : ∀ u, B₁ (L v) (L u) = T ^ 2 * B₀ v u)
    (hr : T ^ 2 * B₀ v v = C ^ 2 * θ ^ 2)
    (hdr : T ^ 2 * B₀ v w = C ^ 2 * θ)
    (hsp : B₁ (L w) (L w) = C ^ 2) : θ • w = v := by
  have he : B₁ (θ • L w - L v) (θ • L w - L v) = 0 := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [hs (L w) (L v), hg w, hg v, hsp, hdr, hr]
    ring
  have hz : θ • L w - L v = 0 := by
    by_contra hn
    have h := hp _ hn
    rw [he] at h
    exact lt_irrefl _ h
  apply hL
  rw [map_smul]
  exact sub_eq_zero.mp hz
end
end RadialRigidity
end

end WeakMTWGlobalSupport

end OAI
