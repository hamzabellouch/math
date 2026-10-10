import Mathlib
import OAI.Geometry.SmoothYau.Estimates.GeneratedCutoffWaveEndpointRatio
import OAI.Geometry.SmoothYau.Smoothness.ContDiffSmoothFiniteWave

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {P E F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma compact_fiber_jet_bound (ψ : P × E → F) (hψ : ContDiff ℝ (∞ : WithTop ℕ∞) ψ)
    {L : Set (P × E)} (hL : IsCompact L) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ w ∈ L, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖ ≤ D := by
  let B := fun w : P × E => ∑ i ∈ Finset.range (m+1),
    ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖
  have hB : Continuous B := continuous_finsetSum _
    (fun i _ => (continuous_parameter_iteratedFDeriv ψ hψ i).norm)
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro w hw i hi
  calc
    _ ≤ B w := Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    _ ≤ ‖B w‖ := le_abs_self _
    _ ≤ C := hC w hw
    _ ≤ max 1 C := le_max_right _ _

theorem compact_fiber_comp_derivative_bound (ψ : P × E → F) (hψ : ContDiff ℝ (∞ : WithTop ℕ∞) ψ)
    {L : Set (P × E)} (hL : IsCompact L) (m : ℕ) :
    ∃ C > 0, ∀ w ∈ L, ∀ f : F → V, ContDiff ℝ (∞ : WithTop ℕ∞) f →
      ∀ n : ℝ, 1 ≤ n → ∀ a : ℝ, 0 ≤ a →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (ψ w)‖ ≤ a*n^i) → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (fun y => f (ψ (w.1,y))) w.2‖ ≤ C*a*n^k := by
  obtain ⟨D,hD,hDb⟩ := compact_fiber_jet_bound ψ hψ hL m
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨(m.factorial : ℝ)*D^m,mul_pos (by positivity) (pow_pos hDp _),?_⟩
  intro w hw f hf n hn a ha hb k hk
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  have hCk : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f (ψ w)‖ ≤ a*n^k := by
    intro i hi
    exact (hb i (hi.trans hk)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn hi) ha)
  have hDk : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖ ≤ D^i := by
    intro i hi hik
    exact (hDb w hw i (hik.trans hk)).trans (by
      simpa only [pow_one] using (pow_le_pow_right₀ hD hi))
  have hbnd := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) hf
    (hψ.comp (contDiff_const.prodMk contDiff_id))
    (show (k : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl k) w.2 hCk hDk
  have hfact : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hk
  have hpow : D^k ≤ D^m := pow_le_pow_right₀ hD hk
  calc
    _ ≤ (k.factorial : ℝ)*(a*n^k)*D^k := hbnd
    _ ≤ (m.factorial : ℝ)*(a*n^k)*D^m := by gcongr
    _ = _ := by ring

end

open Set Filter
open scoped Topology ContDiff
variable {X P E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma uniformJetBounds_fiber_comp (partition : X → P) (hπ : Continuous partition)
    (ψ : P × E → F) (hψ : ContDiff ℝ ∞ ψ)
    (f : X → F → ℂ) (hf : ∀ p, ContDiff ℝ ∞ (f p))
    (hb : UniformJetBounds f univ (ψ '' ((partition '' univ) ×ˢ Metric.closedBall 0 1))) :
    UniformJetBounds (fun p x => f p (ψ (partition p,x))) univ (Metric.closedBall 0 1) := by
  classical
  have hcompact : IsCompact ((partition '' univ) ×ˢ Metric.closedBall (0 : E) 1) :=
    (isCompact_univ.image hπ).prod (isCompact_closedBall 0 1)
  intro k
  obtain ⟨C,hC,hcomp⟩ := compact_fiber_comp_derivative_bound ψ hψ hcompact k (V := ℂ)
  choose A hA hbA using hb
  let a := 1+∑ i ∈ Finset.range (k+1), A i
  have ha : 0 < a := by
    dsimp [a]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hA i).le))
  refine ⟨C*a,mul_pos hC ha,?_⟩
  intro p _ x hx
  have hw : (partition p,x) ∈ (partition '' univ) ×ˢ Metric.closedBall (0 : E) 1 :=
    ⟨mem_image_of_mem partition (mem_univ p),hx⟩
  have hp := hcomp (partition p,x) hw (f p) (hf p) 1 le_rfl a ha.le (fun i hi => ?_) k le_rfl
  · simpa only [one_pow,mul_one] using hp
  · rw [one_pow,mul_one]
    refine (hbA i p (mem_univ _) _ (mem_image_of_mem ψ hw)).trans ?_
    have hs : A i ≤ ∑ j ∈ Finset.range (k+1), A j :=
      Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_range.mpr (by omega))
    exact hs.trans (le_add_of_nonneg_left zero_le_one)

theorem generated_composed_wave_endpoint_ratio
    (partition : X → P) (hπ : Continuous partition)
    (ψ : P × E → (Fin 3 → ℝ)) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ∀ p, ψ (partition p,0) = 0)
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → ComplexPhaseMatrix) (hQ : ∀ i j, Continuous (fun p => Q p i j))
    (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p t => realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)) (ψ (partition p,t))
    let U := fun p n t => canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n (ψ (partition p,t))
    ∃ r₀ > 0, ∃ C > 0, ∀ p (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
      ∀ x y : E, ‖x‖ ≤ r → ‖y‖ ≤ r → n*‖y-x‖ ≤ 1 →
      ∀ L : E →L[ℝ] ℂ, ‖fderiv ℝ (S p) 0-L‖ ≤ δ → C*r+δ ≤ 1/2 →
      ‖U p n y-Complex.exp ((n : ℂ)*L (y-x))*U p n x‖ ≤
        (10*(C*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U p n x‖ := by
  dsimp only
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  let B := ψ '' ((partition '' univ) ×ˢ Metric.closedBall (0 : E) 1)
  have hB : IsCompact B := ((isCompact_univ.image hπ).prod
    (isCompact_closedBall 0 1)).image hψ.continuous
  have hjet := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz
    (fun p => phase_vector_ne_zero _ (hnull p)) Q hQ hsym hnull hQz K J
    (by dsimp [K]; omega) isCompact_univ hB
  have hspec (p) := smoothPhasePolynomial_spec (g p) (hg p) (hg0 p) (hdg0 p)
    (s p) (z p) (Q p) (phase_vector_ne_zero _ (hnull p)) (hsym p) (hnull p) (hQz p)
    (K+J+1) (by dsimp [K,J]; omega)
  have hv0 (p) (j) : realPolyEval (V p j) 0 = if j = 0 then 1 else 0 := by
    rw [realPolyEval_at_zero]
    exact (uniformSmoothWaveAmplitudes_genuine (g p) (b p) (hg p) (hb p) (hg0 p) (S p)
      (z p) (phase_vector_ne_zero _ (hnull p)) (hspec p).2.1 K J (by dsimp [K]; omega)).1 j
  let S' := fun p t => realPolyEval (S p) (ψ (partition p,t))
  let V' := fun p j t => realPolyEval (V p j) (ψ (partition p,t))
  have hS' (p) : ContDiff ℝ ∞ (S' p) :=
    (contDiff_realPolyEval _).comp (hψ.comp (contDiff_const.prodMk contDiff_id))
  have hV' (p j) : ContDiff ℝ ∞ (V' p j) :=
    (contDiff_realPolyEval _).comp (hψ.comp (contDiff_const.prodMk contDiff_id))
  have hV'0 (p j) : V' p j 0 = if j = 0 then 1 else 0 := by simp only [V',hψ0,hv0]
  have hSB := uniformJetBounds_fiber_comp partition hπ ψ hψ (fun p => realPolyEval (S p))
    (fun p => contDiff_realPolyEval _) hjet.1
  have hVB (j) := uniformJetBounds_fiber_comp partition hπ ψ hψ (fun p => realPolyEval (V p j))
    (fun p => contDiff_realPolyEval _) (hjet.2.2.2.2 j)
  obtain ⟨C,hC,hbnd⟩ := finite_wave_endpoint_ratio S' V' hS' hV' hV'0 hSB hVB J
  obtain ⟨R,hR,hcut⟩ := Metric.mem_nhds_iff.mp hζ
  have hψc : Continuous (fun w : X × E => ψ (partition w.1,w.2)) :=
    hψ.continuous.comp ((hπ.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r₁,hr₁,hrcut⟩ := compact_family_positive_radius (E := E) isCompact_univ
    (fun w : X × E => R-‖ψ (partition w.1,w.2)‖) (continuous_const.sub hψc.norm)
    (fun p _ => by simp only [hψ0,norm_zero,sub_zero]; exact hR)
  refine ⟨min r₁ 1,lt_min hr₁ zero_lt_one,C,hC,?_⟩
  intro p n r δ hn hr hrr hδ x y hx hy hsep L hL he
  have hr1 : r ≤ 1 := hrr.le.trans (min_le_right r₁ 1)
  have heq (t : E) (ht : ‖t‖ ≤ r) :
      canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n (ψ (partition p,t)) =
        smoothFiniteWave (S' p) (V' p) J n t := by
    have htball : t ∈ Metric.ball (0 : E) r₁ := by
      simpa only [Metric.mem_ball,dist_zero_right] using ht.trans_lt (hrr.trans_le (min_le_left r₁ 1))
    have hpball : ψ (partition p,t) ∈ Metric.ball (0 : Fin 3 → ℝ) R := by
      simpa only [Metric.mem_ball,dist_zero_right] using sub_pos.mp (hrcut p (mem_univ _) t htball)
    have hζt : ζ (ψ (partition p,t)) = 1 := hcut hpball
    simp only [canonicalCutoffWave,smoothFiniteWave,S',V',S,V,K,J,hζt,one_mul]
  simpa only [heq x hx,heq y hy] using hbnd p n r δ hn hr hr1 hδ x y hx hy hsep L hL he


end YauCounterexamples
end

end OAI
