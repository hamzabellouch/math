import OAI.MeasureTheory.Falconer.Recursion.ProfileContactInterval
import OAI.MeasureTheory.Falconer.Recursion.ProfileUniformLimit

namespace OAI

/-! # Fixed contact intervals for profiles with vanishing comparison losses -/

namespace Falconer
open Set Filter
open scoped Topology NNReal

theorem profile_sequence_contact {K : ℝ≥0} (f : ℕ → ℝ → ℝ)
    (hLip : ∀ n, LipschitzOnWith K (f n) (Icc 0 1)) (hzero : ∀ n, f n 0 = 0)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) {q t s : ℝ}
    (hlower : ∀ n, ∀ u ∈ Icc (0:ℝ) 1, s*u-e n ≤ f n u)
    (hqt : q < t) (hts : t < s) :
    ∃ A B : ℝ, ∃ φ : ℕ → ℕ,
      0 < A ∧ A < B ∧ B < 1 ∧ B < 2*A ∧ StrictMono φ ∧
      ∀ η > 0, ∃ N : ℕ, ∀ n ≥ N,
        (∀ w ∈ Icc 0 A, q*w-η ≤ f (φ n) w) ∧
        (∀ w ∈ Icc A B, t*(w-A)-η ≤ f (φ n) w-f (φ n) A) ∧
        (∀ w ∈ Icc B 1, q*(w-B)-η ≤ f (φ n) w-f (φ n) B) := by
  obtain ⟨m,hm,hm0,φ,hφ,hlim⟩ := normalized_real_profile_subsequence f hLip hzero
  have hmlower := uniform_profile_limit_lower hφ he hlower hlim
  obtain ⟨A,B,hA,hAB,hB,hBA,hfirst,hmiddle,hlast⟩ :=
    profile_contact_interval hm hm0 hmlower hqt hts
  refine ⟨A,B,φ,hA,hAB,hB,hBA,hφ,fun η hη => ?_⟩
  obtain ⟨N,hN⟩ := hlim (η/2) (by linarith)
  refine ⟨N,fun n hn => ⟨?_,?_,?_⟩⟩
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1,hw.2.trans (hAB.trans hB).le⟩
    have hc := (abs_lt.mp (hN n hn w hwI)).1
    linarith [hfirst w hw]
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hA.le.trans hw.1,hw.2.trans hB.le⟩
    have hc := (abs_lt.mp (hN n hn w hwI)).1
    have hca := (abs_lt.mp (hN n hn A ⟨hA.le,(hAB.trans hB).le⟩)).2
    linarith [hmiddle w hw]
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨(hA.trans hAB).le.trans hw.1,hw.2⟩
    have hc := (abs_lt.mp (hN n hn w hwI)).1
    have hcb := (abs_lt.mp (hN n hn B ⟨(hA.trans hAB).le,hB.le⟩)).2
    linarith [hlast w hw]

end Falconer

end OAI
