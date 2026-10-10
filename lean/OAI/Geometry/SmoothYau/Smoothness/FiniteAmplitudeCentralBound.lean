import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CanonicalCutoffWave

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
open Set Filter MvPolynomial
open scoped Topology ContDiff
section FiniteWaveCentre
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma smoothFiniteWave_at_zero (S : E → ℂ) (V : ℕ → E → ℂ)
    (hV : ∀ j, V j 0 = if j = 0 then 1 else 0) (J : ℕ) (n : ℝ) :
    smoothFiniteWave S V J n 0 = Complex.exp ((n : ℂ)*S 0) := by
  simp [smoothFiniteWave,hV]

lemma smoothFiniteWave_central_derivative (S : E → ℂ) (V : ℕ → E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (hV0 : ∀ j, V j 0 = if j = 0 then 1 else 0) (J : ℕ) (n : ℝ) (v : E) :
    waveDeriv v (smoothFiniteWave S V J n) 0 =
      Complex.exp ((n : ℂ)*S 0) * ((n : ℂ)*waveDeriv v S 0 +
        ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * waveDeriv v (V j) 0) := by
  have hA : ContDiff ℝ ∞ (fun x => ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * V j x) :=
    ContDiff.sum (fun j _ => contDiff_const.mul (hV j))
  rw [show smoothFiniteWave S V J n = fun x => Complex.exp ((n : ℂ)*S x) *
      ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * V j x from rfl,
    waveDeriv_mul _ _ _ _ ((contDiff_const.mul hS).cexp.differentiable (by simp) _)
      (hA.differentiable (by simp) _),waveDeriv_exp _ _ _ _ (hS.differentiable (by simp) _)]
  rw [waveDeriv_sum _ _ _ (fun j _ => contDiff_const.mul (hV j))]
  simp only [waveDeriv_const_mul _ _ _ _ ((hV _).differentiable (by simp) _)]
  simp [hV0,mul_add,mul_assoc]

omit [NormedSpace ℝ E] in
lemma smoothFiniteWave_cutoff_germ (S : E → ℂ) (V : ℕ → E → ℂ)
    {ζ : E → ℂ} (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (J : ℕ) (n : ℝ) :
    smoothFiniteWave S (fun j x => ζ x*V j x) J n =ᶠ[𝓝 0] smoothFiniteWave S V J n := by
  rw [smoothFiniteWave_cutoff]
  filter_upwards [hζ] with x hx
  simp [hx]
end FiniteWaveCentre

theorem canonicalCutoffWave_central_jet
    (g : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (s : ℂ) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i*z i = -1)
    (hQz : ∀ k, ∑ i, z i*Q k i = 0)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) (n : ℝ) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := smoothPhasePolynomial g s z Q (K+J+1)
    let V := uniformSmoothWaveAmplitudes g b S z K J
    canonicalCutoffWave g b s z Q ζ m D n 0 = Complex.exp ((n : ℂ)*s) ∧
      ∀ i, waveDeriv (Pi.single i 1) (canonicalCutoffWave g b s z Q ζ m D n) 0 =
        Complex.exp ((n : ℂ)*s) * ((n : ℂ)*z i +
          ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * waveDeriv (Pi.single i 1) (realPolyEval (V j)) 0) := by
  dsimp only [canonicalCutoffWave]
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := smoothPhasePolynomial g s z Q (K+J+1)
  let V := uniformSmoothWaveAmplitudes g b S z K J
  have hs := smoothPhasePolynomial_spec g hg hg0 hdg0 s z Q (phase_vector_ne_zero z hnull)
    hQ hnull hQz (K+J+1) (by dsimp [K,J]; omega)
  have hs0 : realPolyEval S 0 = s := by
    have h := hs.1.constantCoeff_eq_zero (by decide)
    rw [map_sub, sub_eq_zero] at h
    rw [realPolyEval_at_zero]
    exact h.trans (wavePhaseSeed_constantCoeff s z Q)
  have hv := (uniformSmoothWaveAmplitudes_genuine g b hg hb hg0 S z
    (phase_vector_ne_zero z hnull) hs.2.1 K J (by dsimp [K,J]; omega)).1
  have hv0 (j) : realPolyEval (V j) 0 = if j = 0 then 1 else 0 := by
    rw [realPolyEval_at_zero]; exact hv j
  have hge := smoothFiniteWave_cutoff_germ (realPolyEval S) (fun j => realPolyEval (V j)) hζ J n
  constructor
  · rw [hge.self_of_nhds,smoothFiniteWave_at_zero _ _ hv0,hs0]
  · intro i
    change fderiv ℝ _ 0 (Pi.single i 1) = _
    rw [hge.fderiv_eq]
    change waveDeriv _ (smoothFiniteWave _ _ J n) 0 = _
    rw [smoothFiniteWave_central_derivative _ _ (contDiff_realPolyEval S)
      (fun j => contDiff_realPolyEval (V j)) hv0,hs0]
    rw [waveDeriv_realPolyEval_single,realPolyEval_at_zero,hs.2.1]

end

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
open Set Filter MvPolynomial
open scoped Topology ContDiff

lemma finite_amplitude_central_bound {X : Type*}
    (V : X → ℕ → (Fin 3 → ℝ) → ℂ)
    (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    (hB : ∀ j, UniformJetBounds (fun p => V p j) univ {0}) (J : ℕ) :
    ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ i : Fin 3,
      ‖∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * waveDeriv (Pi.single i 1) (V p j) 0‖ ≤ C := by
  choose C hC hb using fun j => hB j 1
  refine ⟨1+∑ j ∈ Finset.range (J+1), C j,
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => (hC j).le)),?_⟩
  intro p n hn i
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hpow (j : ℕ) : ‖((n : ℂ)⁻¹)^j‖ ≤ 1 := by
    rw [norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hnpos]
    exact pow_le_one₀ (inv_nonneg.mpr hnpos.le) ((inv_le_one₀ hnpos).mpr hn)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun j hj => ?_)).trans (le_add_of_nonneg_left zero_le_one)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right (hpow j) (norm_nonneg _)).trans
  rw [one_mul]
  have h := norm_iteratedFDeriv_waveDeriv (hV p j) (Pi.single i 1) 0 (0 : Fin 3 → ℝ)
  simp only [norm_iteratedFDeriv_zero,Pi.norm_single,norm_one,one_mul] at h
  exact h.trans (hb j p (mem_univ _) 0 (mem_singleton 0))

lemma normalize_central_derivative {n : ℝ} (hn : n ≠ 0) (s z R d : ℂ)
    (hd : d = Complex.exp ((n : ℂ)*s) * ((n : ℂ)*z+R)) :
    (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*s))⁻¹*d-z = (n : ℂ)⁻¹*R := by
  rw [hd]
  have he := Complex.exp_ne_zero ((n : ℂ)*s)
  have hn' : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  field_simp
  ring

theorem generated_waves_central_error {X : Type*} [TopologicalSpace X] [CompactSpace X]
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
    ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n →
      ‖fun i => (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*s p))⁻¹*
        waveDeriv (Pi.single i 1) (canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n) 0-z p i‖ ≤ C/n := by
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hjet := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz
    (fun p => phase_vector_ne_zero _ (hnull p)) Q hQ hsym hnull hQz K J
    (by dsimp [K]; omega) isCompact_univ (isCompact_singleton (x := (0 : Fin 3 → ℝ)))
  obtain ⟨C,hC,hbnd⟩ := finite_amplitude_central_bound
    (fun p j => realPolyEval (V p j)) (fun p j => contDiff_realPolyEval _)
    hjet.2.2.2.2 J
  refine ⟨C,hC,?_⟩
  intro p n hn
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hC.le hnpos.le)).mpr
  intro i
  have hj := (canonicalCutoffWave_central_jet (g p) (b p) (hg p) (hb p) (hg0 p)
    (hdg0 p) (s p) (z p) (Q p) (hsym p) (hnull p) (hQz p) ζ hζ m D n).2 i
  change waveDeriv (Pi.single i 1) _ 0 =
    Complex.exp ((n : ℂ)*s p) * ((n : ℂ)*z p i +
      ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * waveDeriv (Pi.single i 1) (realPolyEval (V p j)) 0) at hj
  rw [normalize_central_derivative hnpos.ne' _ _ _ _ hj,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hnpos]
  rw [div_eq_mul_inv,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hbnd p n hn i) (inv_nonneg.mpr hnpos.le)


end YauCounterexamples
end

end OAI
