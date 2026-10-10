import OAI.MeasureTheory.Falconer.Fourier.PoleStationarySupport
import OAI.MeasureTheory.Falconer.Geometry.FixedChartBounds
import OAI.MeasureTheory.Falconer.Angular.MixedCapBounds

namespace OAI

/-! # The derivative budget of the actual quadratic amplitude

The fixed pole cutoff and fixed quadratic geometry cost constants depending
only on the dimension and derivative order. The original symbol supplies
the entire scale power.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem mixed_product_uniform_bound_at {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (k : ℕ)
    (hfb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 2^k*A*B := by
  apply (norm_iteratedFDeriv_mul_le_at hf hg k).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb j hjk) (Nat.cast_nonneg _))
        (hgb (k-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by
      have hs : (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)) = (2 : ℝ)^k := by
        simpa only [one_pow,mul_one,one_mul,one_add_one_eq_two] using
          (add_pow (1 : ℝ) 1 k).symm
      rw [← Finset.sum_mul,← Finset.sum_mul,hs]

theorem poleLocalizedAmbient_uniform_budget (d K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere d) (B : Space d → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere d, ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ w : Sphere d,
        ‖iteratedFDeriv ℝ j (poleLocalizedAmbient e B) w‖ ≤ A*C*D^K := by
  choose P hP hPb using fun j => capBump_ambient_derivatives d j
  let Q := ∑ j ∈ Finset.range (K+1), P j*4^j
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
  have hPQ (j : ℕ) (hj : j ≤ K) : P j*4^j ≤ Q := by
    change P j*(4 : ℝ)^j ≤ ∑ i ∈ Finset.range (K+1), P i*4^i
    exact Finset.single_le_sum (fun i _ => mul_nonneg (hP i) (pow_nonneg (by norm_num) i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨2^K*Q,by positivity,?_⟩
  intro e B hB C D hC hD hb j hj w
  have hCD : 0 ≤ C*D^K := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) K)
  have hcut (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun x => (poleCutoff e x : ℂ)) w‖ ≤ Q := by
    have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      ((poleCutoff_contDiff e).contDiffAt (x := (w : Space d)))
      (show (i : ℕ∞ω) ≤ ∞ by simp)
    change ‖iteratedFDeriv ℝ i (Complex.ofRealLI ∘ poleCutoff e) w‖ ≤ Q
    rw [hn]
    apply (hPb i (1/4) (by norm_num) e w).trans
    simpa only [one_div,inv_inv] using hPQ i (hi.trans hj)
  have hBb (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i B w‖ ≤ C*D^K :=
    (hb i (hi.trans hj) w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (hi.trans hj)) hC)
  have hh := mixed_product_uniform_bound_at
    ((Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).contDiffAt)
    hB.contDiffAt hQ hCD j hcut hBb
  apply hh.trans
  calc
    _ ≤ 2^K*Q*(C*D^K) := by gcongr; norm_num
    _ = _ := by ring

theorem quadraticAmplitude_tsupport_half (m : ℕ) (e : Sphere (m+3))
    (B : Space (m+3) → ℂ) :
    tsupport (quadraticAmplitude m
      (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) ⊆
      closedBall (0 : Space (m+2)) (1/2) := by
  apply closure_minimal _ isClosed_closedBall
  intro u hu
  by_contra hout
  have hlarge : 1/2 < ‖u‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hout
  by_cases hunit : ‖u‖ < 1
  · have hz := (rotated_cap_quadratic_support m e
      (fun w => poleLocalizedAmbient e B w) (poleLocalizedAmbient_cap e B)).2.2 u hlarge.le hunit
    have hum : u ∈ ball (0 : Space (m+2)) 1 := by
      simpa only [mem_ball,dist_zero_right] using hunit
    exact hu (by simp only [quadraticAmplitude,indicator_of_mem hum,hz,mul_zero])
  · have hum : u ∉ ball (0 : Space (m+2)) 1 := by
      simpa only [mem_ball,dist_zero_right] using hunit
    exact hu (by simp only [quadraticAmplitude,indicator_of_notMem hum])

theorem quadratic_chart_composition_uniform_budget (n K : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (T : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1))
      (B : Space (n+1) → ℂ), ContDiff ℝ ∞ B → ∀ E : ℝ, 0 ≤ E →
      (∀ j ≤ K, ∀ w : Sphere (n+1), ‖iteratedFDeriv ℝ j B w‖ ≤ E) →
      ∀ j ≤ K, ∀ u : Space n, ‖u‖ ≤ 1 →
        ‖iteratedFDeriv ℝ j (fun y => B (T (quadraticSpherePoint y))) u‖ ≤ H*E := by
  obtain ⟨Q,_C,hQ,_hC,hgeometry⟩ := fixed_quadratic_geometry_bounds n 0 K
  let a : ℕ → ℝ := fun j => mixedCompositionBudget (fun _ => Q) j
  have ha (j : ℕ) : 0 ≤ a j := mixedCompositionBudget_nonneg (fun _ => hQ) j
  let H := ∑ j ∈ Finset.range (K+1), a j
  have hH : 0 ≤ H := Finset.sum_nonneg (fun j _ => ha j)
  have haH (j : ℕ) (hj : j ≤ K) : a j ≤ H :=
    Finset.single_le_sum (fun j _ => ha j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨H,hH,?_⟩
  intro T B hB E hE hb j hj u hu
  have hu2 : ‖u‖ < 2 := by linarith
  have hQu := quadraticSpherePoint_contDiffAt hu2
  let f : Space n → Space (n+1) := fun y => T (quadraticSpherePoint y)
  have hf : ContDiffAt ℝ ∞ f u := T.toContinuousLinearMap.contDiff.contDiffAt.comp u hQu
  let w : Sphere (n+1) := ⟨f u,by
    rw [mem_sphere,dist_zero_right]
    exact (T.norm_map _).trans (quadraticSpherePoint_norm hu2.le)⟩
  have hinner (i : ℕ) (_hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i f u‖ ≤ Q*(1 : ℝ)^i := by
    have he := T.toLinearIsometry.norm_iteratedFDeriv_comp_left hQu
      (show (i : ℕ∞ω) ≤ ∞ by simp)
    change ‖iteratedFDeriv ℝ i (T.toLinearIsometry ∘ quadraticSpherePoint) u‖ ≤ _
    rw [he,one_pow,mul_one]
    exact (hgeometry i (hij.trans hj) u hu).1
  have hh := mixed_composition_derivative_bound hf hB.contDiffAt hE j
    (fun i hi => hb i (hi.trans hj) w) hinner
  change ‖iteratedFDeriv ℝ j (B ∘ f) u‖ ≤ H*E
  apply hh.trans
  simp only [one_pow,mul_one]
  exact mul_le_mul_of_nonneg_right (haH j hj) hE

/-- Uniform global bounds for the actual zero-extended quadratic amplitude.
The scale appears with exactly the highest requested derivative order K. -/
theorem pole_quadratic_amplitude_budget (m K : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ u,
        ‖iteratedFDeriv ℝ j (quadraticAmplitude m
          (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) u‖ ≤
          L*C*D^K := by
  obtain ⟨A,hA,hAb⟩ := poleLocalizedAmbient_uniform_budget (m+3) K
  obtain ⟨H,hH,hHb⟩ := quadratic_chart_composition_uniform_budget (m+2) K
  obtain ⟨_Q,R,_hQ,hR,hgeometry⟩ := fixed_quadratic_geometry_bounds (m+2) m K
  refine ⟨2^K*R*H*A,by positivity,?_⟩
  intro e B hB C D hC hD hder j hj u
  let b := fun w : Sphere (m+3) => poleLocalizedAmbient e B w
  let amp := quadraticAmplitude m (fun w => b (sphereMap (stationaryPoleRotation e) w))
  let T := stationaryPoleRotation e
  let G : Space (m+2) → ℂ := fun y => poleLocalizedAmbient e B (T (quadraticSpherePoint y))
  let F : Space (m+2) → ℂ := fun y => quadraticChartDensity m y * G y
  have hE : 0 ≤ A*C*D^K := by positivity
  have hGb := hHb T (poleLocalizedAmbient e B) (poleLocalizedAmbient_contDiff e hB)
    (A*C*D^K) hE (hAb e B hB C D hC hD hder)
  by_cases hu : ‖u‖ < 1
  · have hu2 : ‖u‖ < 2 := hu.trans (by norm_num)
    have hG : ContDiffAt ℝ ∞ G u :=
      ((poleLocalizedAmbient_contDiff e hB).comp T.toContinuousLinearMap.contDiff).contDiffAt.comp u
        (quadraticSpherePoint_contDiffAt hu2)
    have hbound := mixed_product_uniform_bound_at (quadraticChartDensity_contDiffAt m hu2)
      hG hR (mul_nonneg hH hE) j
      (fun i hi => (hgeometry i (hi.trans hj) u hu.le).2)
      (fun i hi => hGb i (hi.trans hj) u hu.le)
    have he : amp =ᶠ[𝓝 u] F := by
      have hum : u ∈ ball (0 : Space (m+2)) 1 := by simpa only [mem_ball,dist_zero_right] using hu
      filter_upwards [isOpen_ball.mem_nhds hum] with y hy
      have hy1 : ‖y‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hy
      dsimp only [amp,quadraticAmplitude,F,G,b,quadraticChartDensity]
      rw [indicator_of_mem hy]
      change _ * poleLocalizedAmbient e B (T (gnomonicChart (quadraticToGnomonic y))) = _
      rw [gnomonicChart_quadraticToGnomonic hy1]
    change ‖iteratedFDeriv ℝ j amp u‖ ≤ _
    rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
    apply hbound.trans
    calc
      _ ≤ 2^K*R*(H*(A*C*D^K)) := by gcongr; norm_num
      _ = _ := by ring
  · have hn : u ∉ tsupport amp := by
      intro hm
      have hh := quadraticAmplitude_tsupport_half m e B hm
      have huHalf : ‖u‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hh
      linarith
    have he := (notMem_tsupport_iff_eventuallyEq.mp hn).iteratedFDeriv ℝ j
    have hz : iteratedFDeriv ℝ j amp u = 0 := by simpa using he.self_of_nhds
    change ‖iteratedFDeriv ℝ j amp u‖ ≤ _
    rw [hz,norm_zero]
    positivity

/-- Quantitative outgoing stationary phase for the actual ambient symbol.
The Euclidean derivative budget is derived, not assumed. -/
theorem pole_stationary_remainder_of_ambient_bounds
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ ^ (((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) * Complex.exp (-(Complex.I*(Λ : ℂ))) *
          sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w) -
        ∑ j ∈ Finset.range J, ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) *
          actualStationaryCoefficient m j B e‖ ≤
        A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) := by
  obtain ⟨A,hA,hrem⟩ := poleLocalized_stationary_remainder hgnomonic hquadratic m J hJ
  obtain ⟨L,hL,hbudget⟩ := pole_quadratic_amplitude_budget m (2*J+(m+2)+1)
  refine ⟨A*L,by positivity,?_⟩
  intro e B hB C D hC hD hder Λ hΛ
  have hh := hrem e B hB (L*C*D^(2*J+(m+2)+1)) (by positivity)
    (hbudget e B hB C D hC hD hder) Λ hΛ
  exact hh.trans_eq (by ring)

end Falconer

end OAI
