import OAI.Geometry.NodalSets.Coefficients.UniformResidualCore

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma finiteAmplitude_all_parameter_derivatives (A : ℕ → T → CPoly)
    (hA : ∀ j, ContinuousPolyFamily (A j)) (J k : ℕ)
    (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      DerivativeBound k (finiteAmplitude (fun j ↦ A j t) J N) x C := by
  have h (j : Fin (k+1)) := finiteAmplitude_parameter_uniform_derivative_bound A hA J j.val s hs R
  choose C hC hb using h
  refine ⟨∑ j, C j, ?_, ?_⟩
  · exact (hC ⟨0, by omega⟩).trans_le
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro t ht N hN x hx j hj
    exact (hb ⟨j, by omega⟩ t ht N hN x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

theorem uniform_uncut_wave_residual {s : Set T} (hs : IsCompact s) {R : ℝ} (hR : 0 ≤ R)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
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
        (reval (A (j+1) t))) 0) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) → ∀ S : ℝ, (reval (phi t) x).re ≤ S →
      DerivativeBound k0 (fun z ↦
        smoothSecondOrder (g t) (b t) (fun w ↦
          finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) *
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)) x
        (C * N ^ (-(K:ℝ)) * Real.exp (N*S)) := by
  let E := fun t ↦ smoothEikonal (g t) (reval (phi t))
  let t0 := fun t ↦ smoothTransport (smoothBeamVector (g t) (reval (phi t)))
    (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))
  let tj := fun j t x ↦ smoothTransport (smoothBeamVector (g t) (reval (phi t)))
    (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A (j+1) t)) x +
      smoothSecondOrder (g t) (b t) (reval (A j t)) x
  let L := fun t ↦ smoothSecondOrder (g t) (b t) (reval (A J t))
  have hpB := hp.uniformSmoothBounded s hs R
  have hAB := fun j ↦ (hA j).uniformSmoothBounded s hs R
  have hEB : UniformSmoothBounded s R E := uniformSmoothBounded_eikonal hg hpB
  have ht0B : UniformSmoothBounded s R t0 := by
    have h := (UniformSmoothBounded.sum Finset.univ (fun i _ ↦
      (uniformSmoothBounded_beamVector hg hpB i).mul ((hAB 0).coordPartial i))).add
        ((uniformSmoothBounded_beamScalar hg hb hpB).mul (hAB 0))
    convert h using 1
    funext t x
    simp [t0, smoothTransport]
  have htjB : ∀ j, UniformSmoothBounded s R (tj j) := fun j ↦
    uniformSmoothBounded_transport_defect hg hb hpB (hAB (j+1)) (hAB j)
  have hLB : UniformSmoothBounded s R L := uniformSmoothBounded_secondOrder hg hb (hAB J)
  have htjz : ∀ j, j < J → ∀ t ∈ s, FlatAt m (tj j t) 0 := by
    intro j hj t ht
    convert hTj j hj t ht using 1
    funext x
    simp [tj, smoothTransport]
  obtain ⟨C, hC, hc⟩ := uniform_finiteResidualCore_bound E t0 L tj
    (fun t N ↦ finiteAmplitude (fun j ↦ A j t) J N) hEB ht0B htjB hLB
    (fun t N ↦ finiteAmplitude_contDiff _ J N) m J K k0 hm hJ hR hE hT0 htjz
    (finiteAmplitude_all_parameter_derivatives A hA J k0 s hs R)
  obtain ⟨D, hD, hd⟩ := hpB.2 k0
  refine ⟨2^k0*C*(k0.factorial : ℝ)*(D+1)^k0, by positivity, ?_⟩
  intro t ht N hN x hx S hS
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hxR : ‖x‖ ≤ R := by
    apply hx.trans
    calc
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)) hR
      _ = _ := mul_one R
  let core := finiteResidualCore (E t) (finiteAmplitude (fun j ↦ A j t) J N)
    (t0 t) (fun j ↦ tj j t) (L t) J N
  have hcore : ContDiff ℝ ∞ core := finiteResidualCore_contDiff (hEB.1 t)
    (finiteAmplitude_contDiff _ J N) (ht0B.1 t) (fun j ↦ (htjB j).1 t) (hLB.1 t) J N
  have heq : (fun z ↦ smoothSecondOrder (g t) (b t) (fun w ↦
      finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w) z +
      ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) *
        (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)) =
      fun z ↦ core z * waveExp (reval (phi t)) N z := by
    funext z
    rw [smooth_finite_wave_residual (g t) (b t) (hsym t) _ (reval_contDiff _) _ J hNp.ne' z]
    dsimp [core, finiteResidualCore, E, t0, tj, L]
    ring
  rw [heq]
  exact residual_times_exponential_bound (reval_contDiff _) hcore k0 x hC.le
    (by linarith) hN (hc t ht N hN x hx) ((hd t ht x hxR).enlarge (by linarith)) hS

end
end Yau.Jets

end OAI
