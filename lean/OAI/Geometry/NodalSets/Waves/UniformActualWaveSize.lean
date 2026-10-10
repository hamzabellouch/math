import OAI.Geometry.NodalSets.Coefficients.MetricWaveJets

namespace OAI

namespace Yau.Jets
open Filter Set
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma cutoff_wave_derivative_zero_outside (u : Coord → ℂ) {N : ℝ} (hN : 0 < N)
    (x : Coord) (k : ℕ) (hx : 2*N^(-1/3:ℝ) < ‖x‖) :
    iteratedFDeriv ℝ k (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) x = 0 := by
  have hnear : ∀ᶠ z in 𝓝 x, 2*N^(-1/3:ℝ) < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have he : (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [hnear] with z hz
    have hb : Yau.Waves.scaledCutoff N (0:Coord) z = 0 := by
      by_contra hn
      have hm : z ∈ Function.support (Yau.Waves.scaledCutoff N (0:Coord)) := hn
      rw [Yau.Waves.scaledCutoff_support hN] at hm
      have hlt : ‖z‖ < 2*N^(-1/3:ℝ) := by simpa [Metric.mem_ball,dist_eq_norm] using hm
      linarith
    simp [hb]
  simpa using (he.iteratedFDeriv ℝ k).self_of_nhds

theorem uniform_cutoff_wave_size {s : Set T} (hs : IsCompact s)
    (phi : T → CPoly) (A : ℕ → T → CPoly)
    (hp : ContinuousPolyFamily phi) (hA : ∀ j, ContinuousPolyFamily (A j))
    (J k : ℕ) (S : T → Coord → ℝ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (phi t) x).re-S t x ≤ -c*‖x‖^2) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖iteratedFDeriv ℝ k (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z •
        (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)) x‖ ≤
        C*N^k*Real.exp (N*S t x-c*N*‖x‖^2) := by
  obtain ⟨Ca,hCa,hamp⟩ := finiteAmplitude_all_parameter_derivatives A hA J k s hs 2
  obtain ⟨Cp,hCp,hphase⟩ := (hp.uniformSmoothBounded s hs 2).2 k
  obtain ⟨B,hB,hsize⟩ := cutoff_wave_size k
  let D := max Cp (1+c)
  have hD : 1 ≤ D := (le_add_of_nonneg_right hc.le).trans (le_max_right _ _)
  refine ⟨B*Ca*(k.factorial:ℝ)*D^k,by positivity,?_⟩
  filter_upwards [hgap,eventually_ge_atTop (1:ℝ)] with N hgN hN
  intro t ht x
  by_cases hx : ‖x‖ ≤ 2*N^(-1/3:ℝ)
  · have hx2 : ‖x‖ ≤ 2 := hx.trans (by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos hN (show (-1/3:ℝ) ≤ 0 by norm_num)
      linarith)
    simpa only [sub_zero,mul_assoc] using hsize (reval (phi t))
      (finiteAmplitude (fun j ↦ A j t) J N) (reval_contDiff _) (finiteAmplitude_contDiff _ _ _)
      0 x N Ca D (S t x) c hN hCa.le hD (hamp t ht N hN x hx2)
      (fun j _ hj ↦ (hphase t ht x hx2 j hj).trans (le_max_left _ _))
      (by simpa only [sub_zero] using hgN t ht x hx)
  · rw [cutoff_wave_derivative_zero_outside _ (by linarith) x k (lt_of_not_ge hx),norm_zero]
    positivity

theorem eventually_nat_frequency {P : ℝ → Prop} (h : ∀ᶠ N : ℝ in atTop, P N) :
    ∀ᶠ n : ℕ in atTop, P (n:ℝ) :=
  tendsto_natCast_atTop_atTop.eventually h

end
end Yau.Jets

end OAI
