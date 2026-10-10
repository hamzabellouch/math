import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ComplexPolarWeight
import OAI.Geometry.SmoothYau.Smoothness.PhaseDerivativeLipschitz

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

section Normalize
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_vector_error (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • b‖ ≤ 2*‖a-b‖/‖a‖ := by
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  calc
    _ = ‖‖a‖⁻¹ • (a-b)+(‖a‖⁻¹-‖b‖⁻¹) • b‖ := by congr 1; module
    _ ≤ ‖‖a‖⁻¹ • (a-b)‖+‖(‖a‖⁻¹-‖b‖⁻¹) • b‖ := norm_add_le _ _
    _ = ‖a-b‖/‖a‖+|‖b‖-‖a‖|/‖a‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr han)]
      have he : ‖a‖⁻¹-‖b‖⁻¹ = (‖b‖-‖a‖)/(‖a‖*‖b‖) := by field_simp
      rw [he,abs_div,abs_mul,abs_of_pos han,abs_of_pos hbn]
      field_simp
    _ ≤ ‖a-b‖/‖a‖+‖a-b‖/‖a‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le b a
    _ = _ := by ring

lemma norm_normalize_vector (a : E) (ha : a ≠ 0) : ‖‖a‖⁻¹ • a‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

end Normalize

variable {I : Type*} [Fintype I]

def complexValueVector (z : I → ℂ) : EuclideanSpace ℝ (I ⊕ I) :=
  WithLp.toLp 2 (Sum.elim (fun i => (z i).re) (fun i => (z i).im))

lemma complexValueVector_inner (z w : I → ℂ) :
    ⟪complexValueVector z,complexValueVector w⟫ = ∑ i, ((starRingEnd ℂ (z i))*w i).re := by
  simp only [PiLp.inner_apply,complexValueVector,Fintype.sum_sum_type,
    RCLike.inner_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    neg_mul,sub_neg_eq_add,Finset.sum_add_distrib, Sum.elim_inl, Sum.elim_inr]
  simp only [starRingEnd_apply, star_trivial]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma complexValueVector_norm_sq (z : I → ℂ) :
    ‖complexValueVector z‖^2 = ∑ i, ‖z i‖^2 := by
  rw [←real_inner_self_eq_norm_sq,complexValueVector_inner]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add,
    Complex.sq_norm]
  rw [Complex.normSq_apply]

omit [Fintype I] in
lemma complexValueVector_sub (z w : I → ℂ) :
    complexValueVector (fun i => z i-w i) = complexValueVector z-complexValueVector w := by
  ext i
  cases i <;> rfl

omit [Fintype I] in
lemma complexValueVector_real_smul (a : ℝ) (z : I → ℂ) :
    complexValueVector (fun i => (a : ℂ)*z i) = a • complexValueVector z := by
  ext i
  cases i <;> simp [complexValueVector,Complex.mul_re,Complex.mul_im]

omit [Fintype I] in
lemma complexValueVector_nonzero {z : I → ℂ} (hz : ∃ i, z i ≠ 0) : complexValueVector z ≠ 0 := by
  intro he
  obtain ⟨i,hi⟩ := hz
  apply hi
  apply Complex.ext
  · have hh := congrArg (fun v : EuclideanSpace ℝ (I ⊕ I) => v (.inl i)) he
    exact hh
  · have hh := congrArg (fun v : EuclideanSpace ℝ (I ⊕ I) => v (.inr i)) he
    exact hh

def rotatedWaveValues (z : I → ℂ) (θ : I → ℝ) : I → ℂ :=
  fun i => Complex.exp ((θ i : ℂ)*Complex.I)*z i

lemma complexValueVector_rotated_norm (z : I → ℂ) (θ : I → ℝ) :
    ‖complexValueVector (rotatedWaveValues z θ)‖ = ‖complexValueVector z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [complexValueVector_norm_sq,complexValueVector_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  simp [rotatedWaveValues,Complex.norm_exp]

lemma complexValueVector_rotated_inner (z : I → ℂ) (θ : I → ℝ) :
    ⟪complexValueVector z,complexValueVector (rotatedWaveValues z θ)⟫ =
      ∑ i, ‖z i‖^2*Real.cos (θ i) := by
  rw [complexValueVector_inner]
  apply Finset.sum_congr rfl
  intro i _
  have he : starRingEnd ℂ (z i)*(Complex.exp ((θ i : ℂ)*Complex.I)*z i) =
      (‖z i‖^2 : ℂ)*Complex.exp ((θ i : ℂ)*Complex.I) := by
    rw [show starRingEnd ℂ (z i)*(Complex.exp ((θ i : ℂ)*Complex.I)*z i) =
      (starRingEnd ℂ (z i)*z i)*Complex.exp ((θ i : ℂ)*Complex.I) by ring,
      Complex.conj_mul']
  change (starRingEnd ℂ (z i)*(Complex.exp ((θ i : ℂ)*Complex.I)*z i)).re = _
  rw [he]
  simp [←Complex.ofReal_pow,Complex.mul_re,Complex.exp_re]

end



section
open Set Filter
open scoped Topology RealInnerProductSpace

lemma exponential_packet_relative_error (s t e v₀ v₁ : ℂ) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1/2) (he : ‖e‖ ≤ η)
    (hv₀ : ‖v₀-1‖ ≤ η) (hv₁ : ‖v₁-1‖ ≤ η) :
    ‖Complex.exp (s+t+e)*v₁-Complex.exp t*Complex.exp s*v₀‖ ≤
      (10*η)*‖Complex.exp t*Complex.exp s*v₀‖ := by
  have h₀ : 1-η ≤ ‖v₀‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) v₀
    rw [norm_one,norm_sub_rev] at hh
    linarith
  have h₁ : ‖v₁‖ ≤ 1+η := by
    have hh := norm_sub_norm_le v₁ (1 : ℂ)
    rw [norm_one] at hh
    linarith
  have he' : ‖Complex.exp e-1‖ ≤ 2*η :=
    (Complex.norm_exp_sub_one_le (he.trans (by linarith))).trans (by linarith)
  have hd : ‖v₁-v₀‖ ≤ 2*η := by
    have hh := norm_add_le (v₁-1) ((1 : ℂ)-v₀)
    rw [sub_add_sub_cancel,norm_sub_rev (1 : ℂ)] at hh
    linarith
  have herr : ‖Complex.exp e*v₁-v₀‖ ≤ 10*η*‖v₀‖ := by
    calc
      _ = ‖(Complex.exp e-1)*v₁+(v₁-v₀)‖ := by congr 1; ring
      _ ≤ ‖Complex.exp e-1‖*‖v₁‖+‖v₁-v₀‖ := by
        simpa only [norm_mul] using norm_add_le ((Complex.exp e-1)*v₁) (v₁-v₀)
      _ ≤ (2*η)*(1+η)+2*η := add_le_add
        (mul_le_mul he' h₁ (norm_nonneg _) (by positivity)) hd
      _ ≤ 10*η*‖v₀‖ := by nlinarith [mul_nonneg hη (show 0 ≤ 1/2-η by linarith)]
  rw [Complex.exp_add,Complex.exp_add]
  have heq : Complex.exp s*Complex.exp t*Complex.exp e*v₁-Complex.exp t*Complex.exp s*v₀ =
      (Complex.exp t*Complex.exp s)*(Complex.exp e*v₁-v₀) := by ring
  rw [heq,norm_mul,norm_mul (Complex.exp t*Complex.exp s) v₀]
  nlinarith [mul_le_mul_of_nonneg_left herr (norm_nonneg (Complex.exp t*Complex.exp s))]

lemma exponential_wave_ratio_bound {E : Type*} (S V : E → ℂ) (n a θ : ℝ) (x y : E)
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/2)
    (hphase : ‖(n : ℂ)*(S y-S x)-((a : ℂ)+(θ : ℂ)*Complex.I)‖ ≤ η)
    (hx : ‖V x-1‖ ≤ η) (hy : ‖V y-1‖ ≤ η) :
    ‖Complex.exp ((n : ℂ)*S y)*V y-
        (Real.exp a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*(Complex.exp ((n : ℂ)*S x)*V x)‖ ≤
      (10*η)*‖(Real.exp a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*
        (Complex.exp ((n : ℂ)*S x)*V x)‖ := by
  have hh := exponential_packet_relative_error ((n : ℂ)*S x) ((a : ℂ)+(θ : ℂ)*Complex.I)
    ((n : ℂ)*(S y-S x)-((a : ℂ)+(θ : ℂ)*Complex.I)) (V x) (V y) hη hηsmall hphase hx hy
  rw [show (n : ℂ)*S x+((a : ℂ)+(θ : ℂ)*Complex.I)+
      ((n : ℂ)*(S y-S x)-((a : ℂ)+(θ : ℂ)*Complex.I)) = (n : ℂ)*S y by ring,
    Complex.exp_add,←Complex.ofReal_exp] at hh
  simpa only [mul_assoc] using hh

variable {I : Type*} [Fintype I]
lemma complexValueVector_relative_error (z w : I → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i, ‖z i-w i‖ ≤ δ*‖z i‖) :
    ‖complexValueVector z-complexValueVector w‖ ≤ δ*‖complexValueVector z‖ := by
  rw [←complexValueVector_sub]
  have hs : ‖complexValueVector (fun i => z i-w i)‖^2 ≤ δ^2*‖complexValueVector z‖^2 := by
    rw [complexValueVector_norm_sq,complexValueVector_norm_sq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mpr (h i)
    simpa only [mul_pow] using hh
  nlinarith [norm_nonneg (complexValueVector (fun i => z i-w i)),
    mul_nonneg hδ (norm_nonneg (complexValueVector z))]
end



section
open Set Filter
open scoped Topology ContDiff
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_wave_endpoint_ratio (S : X → E → ℂ) (V : X → ℕ → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    (hV0 : ∀ p j, V p j 0 = if j = 0 then 1 else 0)
    (hSB : UniformJetBounds S univ (Metric.closedBall 0 1))
    (hVB : ∀ j, UniformJetBounds (fun p => V p j) univ (Metric.closedBall 0 1)) (J : ℕ) :
    ∃ C > 0, ∀ p (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r ≤ 1 → 0 ≤ δ →
      ∀ x y : E, ‖x‖ ≤ r → ‖y‖ ≤ r → n*‖y-x‖ ≤ 1 →
      ∀ L : E →L[ℝ] ℂ, ‖fderiv ℝ (S p) 0-L‖ ≤ δ → C*r+δ ≤ 1/2 →
      ‖smoothFiniteWave (S p) (V p) J n y-
        Complex.exp ((n : ℂ)*L (y-x))*smoothFiniteWave (S p) (V p) J n x‖ ≤
      (10*(C*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*smoothFiniteWave (S p) (V p) J n x‖ := by
  obtain ⟨A,hA,ha⟩ := finite_amplitude_near_center V hV hV0 hVB J
  obtain ⟨B,hB,hb⟩ := hSB 2
  let C := A+B
  have hC : 0 < C := add_pos hA hB
  refine ⟨C,hC,?_⟩
  intro p n r δ hn hr hr1 hδ x y hx hy hsep L hL hsmall
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hx1 : x ∈ Metric.closedBall (0 : E) 1 := by simpa using hx.trans hr1
  have hy1 : y ∈ Metric.closedBall (0 : E) 1 := by simpa using hy.trans hr1
  have hxr : x ∈ Metric.closedBall (0 : E) r := by simpa using hx
  have hyr : y ∈ Metric.closedBall (0 : E) r := by simpa using hy
  have hη : 0 ≤ C*r+δ := add_nonneg (mul_nonneg hC.le hr) hδ
  have ham (t : E) (ht : ‖t‖ ≤ r) (ht1 : t ∈ Metric.closedBall (0 : E) 1) :
      ‖finiteWaveAmplitude (V p) J n t-1‖ ≤ C*r+δ := by
    have hh := (ha p n hn t ht1).1
    have hh' : A*‖t‖ ≤ A*r := mul_le_mul_of_nonneg_left ht hA.le
    have hh'' : A*r ≤ C*r := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hr
    exact hh.trans (hh'.trans (hh''.trans (le_add_of_nonneg_right hδ)))
  have hph : ‖(n : ℂ)*(S p y-S p x)-(n : ℂ)*L (y-x)‖ ≤ C*r+δ := by
    have hh := phase_endpoint_linear_error (S p) (hS p) hr hB.le hn0 hxr hyr
      (fun z hz => hb p (mem_univ _) z (Metric.closedBall_subset_closedBall hr1 hz)) L hL
    have hnsep : n*(B*r+δ)*‖y-x‖ ≤ B*r+δ := by
      calc
        _ = (B*r+δ)*(n*‖y-x‖) := by ring
        _ ≤ (B*r+δ)*1 := mul_le_mul_of_nonneg_left hsep
          (add_nonneg (mul_nonneg hB.le hr) hδ)
        _ = _ := mul_one _
    have hBr : B*r+δ ≤ C*r+δ := by
      have hh : B*r ≤ C*r := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hr
      linarith
    exact hh.trans (hnsep.trans hBr)
  have hh := exponential_packet_relative_error ((n : ℂ)*S p x) ((n : ℂ)*L (y-x))
    ((n : ℂ)*(S p y-S p x)-(n : ℂ)*L (y-x))
    (finiteWaveAmplitude (V p) J n x) (finiteWaveAmplitude (V p) J n y)
    hη hsmall hph (ham x hx hx1) (ham y hy hy1)
  rw [show (n : ℂ)*S p x+(n : ℂ)*L (y-x)+
    ((n : ℂ)*(S p y-S p x)-(n : ℂ)*L (y-x)) = (n : ℂ)*S p y by ring] at hh
  simpa only [smoothFiniteWave,finiteWaveAmplitude,mul_assoc] using hh
end



open Set Filter
open scoped Topology ContDiff

theorem generated_cutoff_wave_endpoint_ratio {X : Type*} [TopologicalSpace X] [CompactSpace X]
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
    let S := fun p => realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1))
    let U := fun p n => canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n
    ∃ r₀ > 0, ∃ C > 0, ∀ p (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
      ∀ x y : Fin 3 → ℝ, ‖x‖ ≤ r → ‖y‖ ≤ r → n*‖y-x‖ ≤ 1 →
      ∀ L : (Fin 3 → ℝ) →L[ℝ] ℂ, ‖fderiv ℝ (S p) 0-L‖ ≤ δ → C*r+δ ≤ 1/2 →
      ‖U p n y-Complex.exp ((n : ℂ)*L (y-x))*U p n x‖ ≤
        (10*(C*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U p n x‖ := by
  dsimp only
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hjet := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz
    (fun p => phase_vector_ne_zero _ (hnull p)) Q hQ hsym hnull hQz K J
    (by dsimp [K]; omega) isCompact_univ (isCompact_closedBall (0 : Fin 3 → ℝ) 1)
  have hspec (p) := smoothPhasePolynomial_spec (g p) (hg p) (hg0 p) (hdg0 p)
    (s p) (z p) (Q p) (phase_vector_ne_zero _ (hnull p)) (hsym p) (hnull p) (hQz p)
    (K+J+1) (by dsimp [K,J]; omega)
  have hv0 (p) (j) : realPolyEval (V p j) 0 = if j = 0 then 1 else 0 := by
    rw [realPolyEval_at_zero]
    exact (uniformSmoothWaveAmplitudes_genuine (g p) (b p) (hg p) (hb p) (hg0 p) (S p)
      (z p) (phase_vector_ne_zero _ (hnull p)) (hspec p).2.1 K J (by dsimp [K]; omega)).1 j
  obtain ⟨C,hC,hbnd⟩ := finite_wave_endpoint_ratio (fun p => realPolyEval (S p))
    (fun p j => realPolyEval (V p j)) (fun p => contDiff_realPolyEval _)
    (fun p j => contDiff_realPolyEval _) hv0 hjet.1 hjet.2.2.2.2 J
  obtain ⟨r₁,hr₁,hcut⟩ := Metric.mem_nhds_iff.mp hζ
  refine ⟨min r₁ 1,lt_min hr₁ zero_lt_one,C,hC,?_⟩
  intro p n r δ hn hr hrr hδ x y hx hy hsep L hL he
  have hr1 : r ≤ 1 := hrr.le.trans (min_le_right r₁ 1)
  have heq (t : Fin 3 → ℝ) (ht : ‖t‖ ≤ r) :
      canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n t =
        smoothFiniteWave (realPolyEval (S p)) (fun j => realPolyEval (V p j)) J n t := by
    have htball : t ∈ Metric.ball (0 : Fin 3 → ℝ) r₁ := by
      simpa only [Metric.mem_ball,dist_zero_right] using ht.trans_lt (hrr.trans_le (min_le_left r₁ 1))
    have hζt : ζ =ᶠ[𝓝 t] fun _ => 1 :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds htball) hcut
    exact (smoothFiniteWave_cutoff_germ_at (realPolyEval (S p))
      (fun j => realPolyEval (V p j)) hζt J n).self_of_nhds
  simpa only [heq x hx,heq y hy] using hbnd p n r δ hn hr hr1 hδ x y hx hy hsep L hL he


end YauCounterexamples
end

end OAI
