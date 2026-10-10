import OAI.Geometry.NodalSets.Coefficients.CutoffWaveResidual
import OAI.Geometry.NodalSets.Coefficients.UniformUncutResidual

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T]

omit [TopologicalSpace T] in
lemma finite_uniformSmoothBounded_bound {ι : Type*} [Fintype ι]
    {s : Set T} {R : ℝ} (f : ι → T → Coord → ℂ)
    (hf : ∀ i, UniformSmoothBounded s R (f i)) (k : ℕ) :
    ∃ C > 0, ∀ i t, t ∈ s → ∀ x : Coord, ‖x‖ ≤ R → DerivativeBound k (f i t) x C := by
  choose C hC hb using (fun i ↦ (hf i).2 k)
  have hnonneg : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ ↦ (hC i).le)
  refine ⟨1+∑ i, C i, by linarith, ?_⟩
  intro i t ht x hx
  apply (hb i t ht x hx).enlarge
  have := Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ i)
  linarith

lemma uncut_wave_all_gaussian_derivatives {phi a : Coord → ℂ}
    (hp : ContDiff ℝ ∞ phi) (ha : ContDiff ℝ ∞ a) (k : ℕ) (x : Coord)
    {A D N S c r : ℝ} (hA : 0 ≤ A) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hab : DerivativeBound k a x A) (hpb : DerivativeBound k phi x D)
    (hgap : (phi x).re-S ≤ -c*r^2) :
    DerivativeBound k (fun z ↦ a z * waveExp phi N z) x
      ((2^k*A*(k.factorial:ℝ)*D^k)*N^k*Real.exp (N*S-c*N*r^2)) := by
  let Q := (k.factorial:ℝ)*D^k
  have hNp : 0 ≤ N := le_trans zero_le_one hN
  have he (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (waveExp phi N) x‖ ≤ Q*N^j*Real.exp (N*S-c*N*r^2) := by
    apply (waveExp_gaussian_derivative_bound hp j x hD hN
      (fun i _ hi ↦ hpb i (hi.trans hj)) hgap).trans
    have hfact : (j.factorial:ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpow : D^j ≤ D^k := pow_le_pow_right₀ hD hj
    dsimp [Q]
    gcongr
  intro j hj
  have hh := mul_derivative_power_bound ha (waveExp_contDiff hp N) j x hA hNp
    (fun i hi ↦ (hab i (hi.trans hj)).trans
      (le_mul_of_one_le_right hA (one_le_pow₀ hN))) (fun i hi ↦ he i (hi.trans hj))
  apply hh.trans
  have h2 : (2:ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) hj
  have hn : N^j ≤ N^k := pow_le_pow_right₀ hN hj
  dsimp [Q]
  simp only [mul_assoc]
  gcongr

theorem uniform_cutoff_wave_residual {s : Set T} (hs : IsCompact s) {R : ℝ} (hR : 0 ≤ R)
    (c : ℝ) (hcpos : 0 < c)
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
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) → ∀ S : ℝ,
      (reval (phi t) x).re-S ≤ -c*‖x‖^2 →
      ‖iteratedFDeriv ℝ k0 (fun z ↦
        smoothSecondOrder (g t) (b t) (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x‖ ≤
        C * N ^ (-(K:ℝ)) * Real.exp (N*S) := by

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
  obtain ⟨D, hD, hd⟩ := hpB.2 (k0+2)
  obtain ⟨AA, hAA, haa⟩ := finiteAmplitude_all_parameter_derivatives A hA J (k0+2) s hs R
  obtain ⟨G, hG, hGbound⟩ := finite_uniformSmoothBounded_bound
    (fun ij : Fin 4 × Fin 4 ↦ fun t ↦ g t ij.1 ij.2) (fun ij ↦ hg ij.1 ij.2) k0
  obtain ⟨B, hB, hBbound⟩ := finite_uniformSmoothBounded_bound (fun i t ↦ b t i) hb k0
  obtain ⟨Q1, hQ1, Q2, hQ2, hfull⟩ := cutoff_wave_residual_bound k0 c (K:ℝ) (k0+2) hcpos
  let AW := 2^(k0+2)*AA*((k0+2).factorial:ℝ)*(D+1)^(k0+2)
  refine ⟨Q1*C*(k0.factorial:ℝ)*(D+1)^k0 + Q2*(G+B)*AW, by dsimp [AW]; positivity, ?_⟩
  filter_upwards [hfull, eventually_ge_atTop (1:ℝ)] with N hfullN hN
  intro t ht x hx S hgap
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hxR : ‖x‖ ≤ R := by
    apply hx.trans
    calc
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)) hR
      _ = _ := mul_one R
  let u := fun z ↦ finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z
  let core := finiteResidualCore (E t) (finiteAmplitude (fun j ↦ A j t) J N)
    (t0 t) (fun j ↦ tj j t) (L t) J N
  have hcore : ContDiff ℝ ∞ core := finiteResidualCore_contDiff (hEB.1 t)
    (finiteAmplitude_contDiff _ J N) (ht0B.1 t) (fun j ↦ (htjB j).1 t) (hLB.1 t) J N
  have heq (z : Coord) : smoothSecondOrder (g t) (b t) u z +
      ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))*u z = core z * waveExp (reval (phi t)) N z := by
    dsimp [u]
    rw [smooth_finite_wave_residual (g t) (b t) (hsym t) _ (reval_contDiff _) _ J hNp.ne' z]
    dsimp [core, finiteResidualCore, E, t0, tj, L]
    ring
  have hphiB : DerivativeBound (k0+2) (reval (phi t)) x (D+1) :=
    (hd t ht x hxR).enlarge (by linarith)
  have huB := uncut_wave_all_gaussian_derivatives (reval_contDiff (phi t))
    (finiteAmplitude_contDiff (fun j ↦ A j t) J N) (k0+2) x hAA.le
    (by linarith : 1 ≤ D+1) hN (haa t ht N hN x hxR) hphiB hgap
  have hu : ContDiff ℝ ∞ u := (finiteAmplitude_contDiff _ J N).mul (waveExp_contDiff (reval_contDiff _) N)
  have h := hfullN (g t) (b t) u (reval (phi t)) core ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))
    (fun i j ↦ (hg i j).1 t) (fun i ↦ (hb i).1 t) hu (reval_contDiff _) hcore heq
    x 0 C (D+1) (G+B) AW S hC.le (by linarith) (by positivity) (by dsimp [AW]; positivity)
    (hc t ht N hN x hx) (hphiB.mono (by omega))
    (by nlinarith [sq_nonneg ‖x‖])
    (fun i j ↦ (hGbound (i,j) t ht x hxR).enlarge (by linarith))
    (fun i ↦ (hBbound i t ht x hxR).enlarge (by linarith))
    (by
      have hpow : N ^ ((k0:ℝ)+2) = N ^ (k0+2:ℕ) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        rfl
      simpa [u, AW, sub_zero, hpow] using huB)
  simpa [u] using h

theorem uniform_cutoff_wave_residual_all {s : Set T} (hs : IsCompact s) {R : ℝ} (hR : 0 ≤ R)
    (c : ℝ) (hcpos : 0 < c)
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
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) → ∀ S : ℝ,
      (reval (phi t) x).re-S ≤ -c*‖x‖^2 →
      DerivativeBound k0 (fun z ↦
        smoothSecondOrder (g t) (b t) (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x
        (C * N ^ (-(K:ℝ)) * Real.exp (N*S)) := by
  have h (j : Fin (k0+1)) := uniform_cutoff_wave_residual hs hR c hcpos g b hg hb hsym phi A hp hA
    m J K j.val (by omega) (by omega) hE hT0 hTj
  choose C hC hbound using h
  have hnonneg : 0 ≤ ∑ j, C j := Finset.sum_nonneg (fun j _ ↦ (hC j).le)
  refine ⟨1+∑ j, C j, by linarith, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound, eventually_ge_atTop (1:ℝ)] with N hNall hN
  intro t ht x hx S hgap j hj
  have h := hNall ⟨j, by omega⟩ t ht x hx S hgap
  apply h.trans
  have hsum : C ⟨j, by omega⟩ ≤ 1+∑ j, C j := by
    have := Finset.single_le_sum (fun i _ ↦ (hC i).le) (Finset.mem_univ (⟨j, by omega⟩ : Fin (k0+1)))
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (by linarith : 0 ≤ N) _))
    (Real.exp_pos _).le

end
end Yau.Jets

end OAI
