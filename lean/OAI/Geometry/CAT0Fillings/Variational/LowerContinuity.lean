import Mathlib
import OAI.Geometry.CAT0Fillings.Fillings.WeightedCone

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem fillingVolume_le_of_bounded_weak_limit (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hz : ∀ j, boundarySucc (Ts j) = 0)
    (M B : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M) (hB : ∀ j, fillingVolume (Ts j) ≤ B)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    fillingVolume T ≤ B := by
  choose S hS hb hm using fun j => hX.exists_minimal_integral_filling (hTs j) (hz j)
  obtain ⟨ψ,hψ,U,hU,hUm,_,hweak⟩ := exists_integral_weak_subsequence hS B M
    (fun j => by rw [hm]; exact hB j) (fun j => by rw [hb]; exact hM j) hX
  have hboundary : boundarySucc U = T := by
    funext b π
    apply tendsto_nhds_unique (boundarySucc_weak_limit hweak b π)
    simpa only [hb,Function.comp_def] using (hlim b π).comp hψ.tendsto_atTop
  exact (fillingVolume_le hU hboundary).trans hUm

theorem fillingVolume_le_of_eventually_bounded_weak_limit (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hz : ∀ j, boundarySucc (Ts j) = 0)
    (M B : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hB : ∀ᶠ j in atTop, fillingVolume (Ts j) ≤ B)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    fillingVolume T ≤ B := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hB
  exact fillingVolume_le_of_bounded_weak_limit hX (fun j => hTs (j+N))
    (fun j => hz (j+N)) M B (fun j => hM (j+N))
    (fun j => hN (j+N) (Nat.le_add_left N j))
    (fun b π => (hlim b π).comp (tendsto_add_atTop_nat N))

theorem fillingVolume_sub_tendsto_zero (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hz : ∀ j, boundarySucc (Ts j) = 0)
    (M : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hcauchy : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      fillingVolume (Ts i-Ts j) < ε)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hlim : ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π))) :
    Tendsto (fun j => fillingVolume (Ts j-T)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun j => ha.trans_le (fillingVolume_nonneg _)
  · intro ε hε
    obtain ⟨N,hN⟩ := hcauchy (ε/2) (half_pos hε)
    apply eventually_atTop.mpr
    refine ⟨N,fun i hi => ?_⟩
    have hb : fillingVolume (Ts i-T) ≤ ε/2 := by
      apply fillingVolume_le_of_eventually_bounded_weak_limit hX
        (fun j => (hTs i).sub (hTs (ψ j)))
        (fun j => by rw [boundarySucc_sub,hz,hz,sub_self])
        (M+M) (⟨ε/2,(half_pos hε).le⟩ : ℝ≥0)
      · intro j
        exact (mass_sub_le (hTs i).1 (hTs (ψ j)).1).trans (add_le_add (hM i) (hM (ψ j)))
      · filter_upwards [hψ.tendsto_atTop.eventually (eventually_ge_atTop N)] with j hj
        exact (hN i hi (ψ j) hj).le
      · intro b π
        exact tendsto_const_nhds.sub (hlim b π)
    exact hb.trans_lt (half_lt_self hε)

lemma fillingVolume_tendsto_of_sub_tendsto_zero (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hzs : ∀ j, boundarySucc (Ts j) = 0)
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (hlim : Tendsto (fun j => fillingVolume (Ts j-T)) atTop (𝓝 0)) :
    Tendsto (fun j => fillingVolume (Ts j)) atTop (𝓝 (fillingVolume T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by
    simpa only [Real.norm_eq_abs] using abs_fillingVolume_sub_le hX (hTs j) (hzs j) hT hz) hlim

end CAT0Fillings
end

end OAI
