import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreIdentification
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

/-! Uniqueness and subsequence criteria for the C1 core limit. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_derivative_limit_unique (R : ℝ) (hR : 0 < R)
    (A B D E : ℝ → ℝ) (hD : Continuous D) (hE : Continuous E)
    (hAB : EqOn A B (Icc 0 R))
    (hAD : ∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r)
    (hBE : ∀ r ∈ Ioo 0 R, HasDerivAt B (E r) r) : EqOn D E (Icc 0 R) := by
  have hi : Ioo 0 R ⊆ {r | D r=E r} := by
    intro r hr
    have hd : HasDerivAt B (D r) r := (hAD r hr).congr_of_eventuallyEq (by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact (hAB ⟨ht.1.le,ht.2.le⟩).symm)
    exact hd.unique (hBE r hr)
  have hc := closure_minimal hi (isClosed_eq hD hE)
  rw [closure_Ioo hR.ne] at hc
  exact hc

theorem radial_uniform_limit_of_subsequences {ι : Type*} {s : Set ι}
    (H : ℕ → ι → ℝ) (A : ι → ℝ)
    (hs : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, TendstoUniformlyOn (fun n => H (ns (ms n))) A atTop s) :
    TendstoUniformlyOn H A atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hn
  have hf : ∃ᶠ n in atTop, ¬∀ r ∈ s, dist (A r) (H n r) < ε := by
    simpa only [Filter.Frequently,not_not] using hn
  obtain ⟨ns,hns,hbad⟩ := exists_seq_forall_of_frequently hf
  obtain ⟨ms,hms⟩ := hs ns hns
  have hgood := (Metric.tendstoUniformlyOn_iff.mp hms) ε hε
  obtain ⟨n,hn⟩ := hgood.exists
  exact hbad (ms n) hn

end DefocusingNLS

end OAI
