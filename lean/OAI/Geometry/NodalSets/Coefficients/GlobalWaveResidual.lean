import OAI.Geometry.NodalSets.Coefficients.UniformWaveResidual

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section

lemma cutoff_residual_derivative_zero_outside (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) (lam : ℂ) {N : ℝ} (hN : 0 < N)
    (x : Coord) (k : ℕ) (hx : 2*N^(-1/3:ℝ) < ‖x‖) :
    iteratedFDeriv ℝ k (fun z ↦
      smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w • u w) z +
        lam * (Yau.Waves.scaledCutoff N (0:Coord) z • u z)) x = 0 := by
  have hnear : ∀ᶠ z in 𝓝 x, 2*N^(-1/3:ℝ) < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have hbeta : Yau.Waves.scaledCutoff N (0:Coord) =ᶠ[𝓝 x] fun _ ↦ (0:ℝ) := by
    filter_upwards [hnear] with z hz
    by_contra hn
    have hm : z ∈ Function.support (Yau.Waves.scaledCutoff N (0:Coord)) := hn
    rw [Yau.Waves.scaledCutoff_support hN] at hm
    have hlt : ‖z‖ < 2*N^(-1/3:ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hm
    linarith
  have hprod : (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [hbeta] with z hz
    simp [hz]
  have hpartial (i : Fin 4) : coordPartial i (fun _ : Coord ↦ (0:ℂ)) = fun _ ↦ (0:ℂ) := by
    funext z
    simp [coordPartial]
  have hres : (fun z ↦ smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w • u w) z +
        lam * (Yau.Waves.scaledCutoff N (0:Coord) z • u z)) =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [smoothSecondOrder_eventuallyEq g b hprod, hprod] with z hz hz'
    rw [hz, hz']
    simp only [smoothSecondOrder, hpartial, mul_zero, Finset.sum_const_zero, zero_add]
  have h := (hres.iteratedFDeriv ℝ k).self_of_nhds
  simpa using h

variable {T : Type*} [TopologicalSpace T]
theorem global_uniform_cutoff_wave_residual {s : Set T} (hs : IsCompact s)
    (c : ℝ) (hcpos : 0 < c)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (hg : ∀ i j, UniformSmoothBounded s 2 (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s 2 (fun t ↦ b t i))
    (hsym : ∀ t i j x, g t i j x = g t j i x)
    (phi : T → CPoly) (A : ℕ → T → CPoly)
    (hp : ContinuousPolyFamily phi) (hA : ∀ j, ContinuousPolyFamily (A j))
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J)
    (hE : ∀ t ∈ s, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0)
    (hT0 : ∀ t ∈ s, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
      (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0)
    (hTj : ∀ j, j < J → ∀ t ∈ s, FlatAt m
      (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t)))
        (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
        (reval (A (j+1) t))) 0)
    (S : T → Coord → ℝ)
    (hgap : ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (phi t) x).re-S t x ≤ -c*‖x‖^2) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      DerivativeBound k0 (fun z ↦
        smoothSecondOrder (g t) (b t) (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x
        (C * N ^ (-(K:ℝ)) * Real.exp (N*S t x)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_cutoff_wave_residual_all hs (R := 2) (by norm_num)
    c hcpos g b hg hb hsym phi A hp hA m J K k0 hm hJ hE hT0 hTj
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hgap, eventually_ge_atTop (1:ℝ)] with N hbN hgN hN
  intro t ht x
  by_cases hx : ‖x‖ ≤ 2*N^(-1/3:ℝ)
  · exact hbN t ht x hx (S t x) (hgN t ht x hx)
  · intro j hj
    rw [cutoff_residual_derivative_zero_outside (g t) (b t)
      (fun z ↦ finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)
      ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) (by linarith : 0 < N) x j (lt_of_not_ge hx), norm_zero]
    positivity

end
end Yau.Jets

end OAI
