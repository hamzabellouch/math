import OAI.Analysis.CircleDomains.Uniformization.RiemannDiskSeed
import OAI.Analysis.CircleDomains.Topology.DiskFractionalMap

namespace OAI

/-! A missing disk value gives a genuine holomorphic square-root
competitor; its derivative is computed before the final normalization. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_root_disk_competitor {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) {a : ℂ} {f : ℂ → ℂ}
    (hf : NormalizedDiskEmbedding U a f) {b : ℂ} (hb : ‖b‖<1)
    (hmiss : b ∉ f '' U) :
    ∃ r : ℂ → ℂ, ContinuousOn r U ∧ InjOn r U ∧ MapsTo r U (ball 0 1) ∧
      (∀ z, r z^2=diskFractionalMap b (f z)) ∧
      (∀ z ∈ U, r z ≠ 0) ∧
      (∀ z ∈ U, HasDerivAt r
        (((1-star b*b)/(1-star b*f z)^2*deriv f z)/(2*r z)) z) ∧
      r a^2 = -b := by
  let g := diskFractionalMap b ∘ f
  have hg (z : ℂ) (hz : z ∈ U) : HasDerivAt g
      ((1-star b*b)/(1-star b*f z)^2*deriv f z) z :=
    (diskFractionalMap_hasDerivAt hb (mem_ball_zero_iff.mp (hf.mapsTo hz))).comp z
      ((hf.holomorphic z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hgcont : ContinuousOn g U := fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hgnz (z : ℂ) (hz : z ∈ U) : g z ≠ 0 := by
    intro he
    have hden := diskFractionalMap_denom_ne_zero hb (mem_ball_zero_iff.mp (hf.mapsTo hz))
    have he' : f z-b=0 := (div_eq_zero_iff.mp he).resolve_right hden
    exact hmiss ⟨z,hz,sub_eq_zero.mp he'⟩
  obtain ⟨r,hr,hpow⟩ := Complex.exists_continuousOn_pow_eq hc hU hgcont (by
    rintro ⟨z,hz,he⟩
    exact hgnz z hz he) (by norm_num : (2:ℕ)≠0)
  have hrnz (z : ℂ) (hz : z ∈ U) : r z ≠ 0 := by
    intro he
    have hh := hpow z
    rw [he,zero_pow (by norm_num)] at hh
    exact hgnz z hz hh.symm
  refine ⟨r,hr,?_,?_,hpow,hrnz,?_,?_⟩
  · intro x hx y hy he
    apply hf.injective hx hy
    apply diskFractionalMap_injective hb (hf.mapsTo hx) (hf.mapsTo hy)
    change g x=g y
    rw [← hpow x,← hpow y,he]
  · intro z hz
    apply mem_ball_zero_iff.mpr
    have hh : ‖r z‖^2=‖g z‖ := by rw [← norm_pow,hpow]
    have hlt := diskFractionalMap_mem_ball hb (mem_ball_zero_iff.mp (hf.mapsTo hz))
    change ‖g z‖<1 at hlt
    nlinarith [norm_nonneg (r z)]
  · intro z hz
    have hp : HasDerivAt (fun w : ℂ => w^2) (2*r z) (r z) := by
      simpa using hasDerivAt_pow 2 (r z)
    exact hp.of_comp_left (hr.continuousAt (hU.mem_nhds hz)) (hg z hz)
      (mul_ne_zero (by norm_num) (hrnz z hz)) (Filter.Eventually.of_forall hpow)
  · simpa only [g,Function.comp_apply,hf.at_base,diskFractionalMap_zero] using hpow a

end CircleDomainRigidity

end

end OAI
