import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPerturbedKernelLine
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNonzeroKernelLimit
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

/-! A simple compact limiting kernel bounds all sufficiently late kernel dimensions. -/

open Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spectral_eventually_kernel_line
    (K : ℕ → E →L[ℂ] E) (K₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hcompact : IsCompactOperator K₀)
    (hker : ∀ u₀ : E, u₀ ≠ 0 → K₀ u₀=u₀ →
      ∀ w : E, K₀ w=w → ∃ a : ℂ, w=a • u₀) :
    ∀ᶠ n in atTop, ∀ u v : E, K n u=u → u ≠ 0 → K n v=v → ∃ a : ℂ, v=a • u := by
  classical
  by_contra h
  have hbad : ∃ᶠ n in atTop, ∃ u v : E,
      K n u=u ∧ u ≠ 0 ∧ K n v=v ∧ ¬ ∃ a : ℂ, v=a • u := by
    apply (not_eventually.mp h).mono
    intro n hn
    simpa only [not_forall,not_imp,exists_prop] using hn
  obtain ⟨s,hs,hbad⟩ := exists_seq_forall_of_frequently hbad
  choose u v hu hne hv hnot using hbad
  have hKs := hK.comp hs
  obtain ⟨u₀,hnorm,hfix⟩ := compact_kernel_limit_of_eventually_nonzero
    (fun n => K (s n)) K₀ hKs hcompact u (Eventually.of_forall fun n => ⟨hu n,hne n⟩)
  have hu₀ : u₀ ≠ 0 := by
    intro he
    rw [he,norm_zero] at hnorm
    norm_num at hnorm
  obtain ⟨L,_hLn,hLu⟩ := exists_dual_vector ℂ u₀ (by rw [hnorm]; norm_num)
  have hL₀ : L u₀=1 := by simpa [hnorm] using hLu
  obtain ⟨c,hc,hbase⟩ := compact_simple_kernel_estimate K₀ hcompact u₀ L
    (by rw [hL₀]; norm_num) (hker u₀ hu₀ hfix)
  have hclose := (tendsto_iff_norm_sub_tendsto_zero.mp hKs).eventually
    (gt_mem_nhds (half_pos hc))
  obtain ⟨n,hn⟩ := hclose.exists
  exact hnot n (spectral_kernel_line_of_close K₀ (K (s n)) L c hc hbase hn.le
    (u n) (v n) (hu n) (hne n) (hv n))

end DefocusingNLS

end OAI
