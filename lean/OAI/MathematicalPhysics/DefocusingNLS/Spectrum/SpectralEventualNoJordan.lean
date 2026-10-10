import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSimpleLimitNoJordan

namespace OAI

/-! The compact no-chain limit gives an eventual exclusion of every first chain. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem spectral_eventually_no_jordan
    (F : ℕ → ℂ → E →L[ℂ] E) (f : ℂ → E →L[ℂ] E)
    (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (z : ℂ) (hz : z ∈ U) (hcompact : IsCompactOperator (f z))
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z))
    (hker : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, f z w=w → ∃ a : ℂ, w=a • u₀)
    (hno : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, w-f z w ≠ deriv f z u₀) :
    ∀ᶠ n in atTop, ∀ u v : E, F n (x n) u=u → u ≠ 0 →
      v-F n (x n) v ≠ deriv (F n) (x n) u := by
  classical
  by_contra h
  have hbad : ∃ᶠ n in atTop, ∃ u v : E,
      F n (x n) u=u ∧ u ≠ 0 ∧ v-F n (x n) v=deriv (F n) (x n) u := by
    apply (not_eventually.mp h).mono
    intro n hn
    simpa only [not_forall,not_imp,not_not,exists_prop] using hn
  obtain ⟨s,hs,hbad⟩ := exists_seq_forall_of_frequently hbad
  choose u v hu hne hv using hbad
  have hFs : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop U := by
    intro V hV w hw
    obtain ⟨S,hS,hFS⟩ := hF V hV w hw
    exact ⟨S,hS,hs.eventually hFS⟩
  exact spectral_simple_limit_no_jordan (fun n => F (s n)) f U hU hFs (hs.eventually hd)
    z hz hcompact (fun n => x (s n)) (hx.comp hs) u v
    (Eventually.of_forall (fun n => ⟨hu n,hne n⟩)) (Eventually.of_forall hv) hker hno

end DefocusingNLS

end OAI
