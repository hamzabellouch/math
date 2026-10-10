import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSimpleKernelEstimate

namespace OAI

/-! Normalization by a fixed functional converts the complement estimate
into convergence of the perturbed kernel vector. -/

open Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spectral_normalized_kernel_distance
    (K₀ K : E →L[ℂ] E) (L : E →L[ℂ] ℂ) (c : ℝ) (hc : 0 < c)
    (hbase : ∀ w : E, L w=0 → c * ‖w‖ ≤ ‖w-K₀ w‖)
    (hclose : ‖K-K₀‖ ≤ c/2) (u v : E)
    (hu : K₀ u=u) (hv : K v=v) (hL : L v=L u) :
    ‖v-u‖ ≤ (‖K-K₀‖ * ‖u‖)/(c/2) := by
  have hw : L (v-u)=0 := by rw [map_sub,hL,sub_self]
  have hb := kernel_complement_perturbation_estimate K₀ K L c hbase hclose (v-u) hw
  have he : (v-u)-K (v-u)=(K-K₀) u := by
    simp only [map_sub,sub_apply,hu,hv]
    abel
  rw [he] at hb
  apply (le_div_iff₀ (half_pos hc)).mpr
  exact (mul_comm _ _).trans_le (hb.trans ((K-K₀).le_opNorm u))

theorem spectral_normalized_kernel_tendsto
    (K : ℕ → E →L[ℂ] E) (K₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (L : E →L[ℂ] ℂ) (c : ℝ) (hc : 0 < c)
    (hbase : ∀ w : E, L w=0 → c * ‖w‖ ≤ ‖w-K₀ w‖)
    (hclose : ∀ n, ‖K n-K₀‖ ≤ c/2) (u : E) (v : ℕ → E)
    (hu : K₀ u=u) (hv : ∀ n, K n (v n)=v n) (hL : ∀ n, L (v n)=L u) :
    Tendsto v atTop (𝓝 u) := by
  have hn : Tendsto (fun n => ‖K n-K₀‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (hK.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => K₀) atTop (𝓝 K₀))).norm
  have hb : Tendsto (fun n => (‖K n-K₀‖ * ‖u‖)/(c/2)) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_div] using (hn.mul_const ‖u‖).div_const (c/2)
  have ht : Tendsto (fun n => v n-u) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => spectral_normalized_kernel_distance K₀ (K n) L c hc
      hbase (hclose n) u (v n) hu (hv n) (hL n)) hb
  simpa only [sub_add_cancel,zero_add] using ht.add_const u

end DefocusingNLS

end OAI
