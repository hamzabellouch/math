import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteEntryPhaseBound

namespace OAI

/-! # Simultaneous velocity-tail and near-axis deletion, with bounded retained windows -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selected_window_deletion {K α γ q a T ε R₀ b₀ s₀ η d₀ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (m : ℕ) {f : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, z.1.1 ∈ Icc a T → f n z ≤ B) :
    ∃ (V β : ℝ) (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i)),
      0 < V ∧ 0 < β ∧ S 0 = velocityWindow R₀ b₀ ∧
      (∀ i v, v ∈ S i → ‖v‖ ≤ V ∧ β ≤ ‖transverse v‖) ∧
      ∀ᶠ n in atTop, ∀ (N : ℕ) (z : Published.KineticPhase),
        z.1.1 ∈ Icc a T → z.2 ∈ velocityWindow R₀ b₀ →
        iterate a (selectedFreeKernel (r n) s₀ η K α γ d₀ q N) (f n) m z ≤
          restrictedChain a (selectedFreeKernel (r n) s₀ η K α γ d₀ q N) S hS (f n) 0 m z+
          ((ENNReal.ofReal ε+ENNReal.ofReal ε)*ENNReal.ofReal (T-a))*deletionCoefficient B
            (ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a)*ENNReal.ofReal (T-a)) m := by
  obtain ⟨R,b,hR0,hb0,hR,hb,hsmall⟩ := selected_velocity_windows hK hα hγ hq₁ hq₂ ha hε hR₀ hb₀
    hs₀ hsmax hη hηmax hd₀ hdmax hr hrlim m
  let S := fun i => velocityWindow (R (min i m)) (b (min i m))
  have hS : ∀ i, MeasurableSet (S i) := fun i => velocityWindow_measurable _ _
  obtain ⟨V,β,hV,hβ,hbounds⟩ := finite_velocity_window_bounds R b hR hb m
  have hS0 : S 0 = velocityWindow R₀ b₀ := by simp only [S,Nat.zero_min,hR0,hb0]
  refine ⟨V,β,S,hS,hV,hβ,hS0,hbounds,?_⟩
  filter_upwards [hsmall] with n hn N z hz hzv
  have hmass : ∀ y, y.1.1 ∈ Icc a T →
      selectedFreeKernel (r n) s₀ η K α γ d₀ q N y univ ≤
        ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a) := by
    intro y hy
    apply (selectedFreeKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      N y (ha.trans_le hy.1)).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
      (JetCoreSheet.growthConstant_nonneg hK α γ q) ha hy.1)
  apply restrictedChain_deletion_bound _ S hS hmass (hfm n) (hf n) 0 m ?_ z hz
    (hS0.symm ▸ hzv)
  intro j _ hj y hy hyv
  have hjm : j < m := by simpa only [Nat.zero_add] using hj
  have hjle : j ≤ m := hjm.le
  have hjnext : j+1 ≤ m := Nat.succ_le_of_lt hjm
  have hyv' : y.2 ∈ velocityWindow (R j) (b j) := by
    simpa only [S,Nat.min_eq_left hjle] using hyv
  simpa only [S,Nat.min_eq_left hjnext] using hn j hjm N y hy.1 hyv'

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
