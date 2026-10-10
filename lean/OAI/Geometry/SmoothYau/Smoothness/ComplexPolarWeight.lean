import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CanonicalCutoffWave
import OAI.Geometry.SmoothYau.ProductMetric.FourColumnSmallBall
import OAI.Geometry.SmoothYau.Spectrum.FiniteWaveAmplitude

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

lemma smoothFiniteWave_cutoff_germ_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E → ℂ) (V : ℕ → E → ℂ) {ζ : E → ℂ} {x : E}
    (hζ : ζ =ᶠ[𝓝 x] fun _ => 1) (J : ℕ) (n : ℝ) :
    smoothFiniteWave S (fun j x => ζ x*V j x) J n =ᶠ[𝓝 x] smoothFiniteWave S V J n := by
  filter_upwards [hζ] with y hy
  simp only [smoothFiniteWave,hy,one_mul]

theorem generated_cutoff_waves_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
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
    ∃ r > 0, ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : Fin 3 → ℝ,
      ‖x‖ < r → ‖x‖ ≤ 1/n →
      ‖(Complex.exp ((n : ℂ)*S p x))⁻¹*canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n x-1‖ ≤ C/n ∧
      ‖fun i => (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*S p x))⁻¹*
        waveDeriv (Pi.single i 1) (canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n) x-z p i‖ ≤ C/n := by
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
  obtain ⟨C,hC,hbnd⟩ := finite_wave_near_center (fun p => realPolyEval (S p))
    (fun p j => realPolyEval (V p j)) (fun p => contDiff_realPolyEval _)
    (fun p j => contDiff_realPolyEval _) hv0 hjet.1 hjet.2.2.2.2 J
  obtain ⟨r,hr,hbr⟩ := Metric.mem_nhds_iff.mp hζ
  refine ⟨r,hr,C,hC,?_⟩
  intro p n hn x hxr hx
  have hxball : x ∈ Metric.ball (0 : Fin 3 → ℝ) r := by simpa using hxr
  have hζx : ζ =ᶠ[𝓝 x] fun _ => 1 :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxball) hbr
  have hge := smoothFiniteWave_cutoff_germ_at (realPolyEval (S p))
    (fun j => realPolyEval (V p j)) hζx J n
  have heq : canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n =ᶠ[𝓝 x]
      smoothFiniteWave (realPolyEval (S p)) (fun j => realPolyEval (V p j)) J n := hge
  obtain ⟨hval,hder⟩ := hbnd p n hn x hx
  constructor
  · simpa only [heq.self_of_nhds] using hval
  · apply (pi_norm_le_iff_of_nonneg (div_nonneg hC.le (zero_lt_one.trans_le hn).le)).mpr
    intro i
    have hv : ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ ≤ 1 := by rw [Pi.norm_single,norm_one]
    have hh := hder (Pi.single i 1) hv
    change ‖_ * _ * fderiv ℝ _ x (Pi.single i 1)-_‖ ≤ _
    rw [heq.fderiv_eq]
    change ‖_ * _ * waveDeriv (Pi.single i 1) _ x-_‖ ≤ _
    have hzero : waveDeriv (Pi.single i 1) (realPolyEval (S p)) 0 = z p i := by
      rw [waveDeriv_realPolyEval_single,realPolyEval_at_zero,(hspec p).2.1]
    simpa only [hzero] using hh


end

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
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology Matrix Matrix.Norms.Elementwise ENNReal

def phaseFrameMatrix (ν b c : PhaseSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun i j => ![ν i,b i,c i] j)

lemma phaseFrameMatrix_gram (ν b c : PhaseSpace) :
    (phaseFrameMatrix ν b c)ᵀ * phaseFrameMatrix ν b c =
      !![inner ℝ ν ν,inner ℝ ν b,inner ℝ ν c;
         inner ℝ b ν,inner ℝ b b,inner ℝ b c;
         inner ℝ c ν,inner ℝ c b,inner ℝ c c] := by
  simp_rw [PiLp.inner_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseFrameMatrix,Matrix.mul_apply,Fin.sum_univ_succ,mul_comm,pow_two]

lemma phaseFrameMatrix_det_sq (ν b c : PhaseSpace) (hν : ‖ν‖ = 1)
    (hb : inner ℝ ν b = 0) (hc : inner ℝ ν c = 0) :
    (phaseFrameMatrix ν b c).det^2 = ‖b‖^2*‖c‖^2-(inner ℝ b c)^2 := by
  have h := congrArg Matrix.det (phaseFrameMatrix_gram ν b c)
  rw [Matrix.det_mul,Matrix.det_transpose] at h
  conv_rhs at h => rw [Matrix.det_fin_three]
  simpa [real_inner_self_eq_norm_sq,hν,hb,hc,real_inner_comm c b,pow_two] using h

def physicalWaveJetMatrix (a ν b c : PhaseSpace) (δ : ℝ) :
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of (fun _ j => ![1,0,0] j)) (Matrix.of (fun i _ => a i))
    (Matrix.of (fun i j => ![a i+δ*ν i,b i,c i] j))

lemma physicalWaveJetMatrix_det (a ν b c : PhaseSpace) (δ : ℝ) :
    (physicalWaveJetMatrix a ν b c δ).det = δ*(phaseFrameMatrix ν b c).det := by
  rw [physicalWaveJetMatrix,Matrix.det_fromBlocks_one₁₁]
  simp [phaseFrameMatrix,Matrix.det_fin_three,Matrix.sub_apply,Matrix.mul_apply]
  ring

lemma phaseFrameMatrix_det_lower (a ν b c : PhaseSpace) (η : ℝ)
    (hν : ‖ν‖ = 1) (hb : inner ℝ ν b = 0) (hc : inner ℝ ν c = 0)
    (hbn : ‖b‖^2 = 1+‖a‖^2) (hcn : ‖c‖^2 = 1+‖a‖^2)
    (hη : 0 < η) (hangle : η ≤ transverseAngleSq b c) :
    Real.sqrt η ≤ |(phaseFrameMatrix ν b c).det| := by
  have hL : 1 ≤ ‖b‖^2*‖c‖^2 := by rw [hbn,hcn]; nlinarith [sq_nonneg ‖a‖]
  have hh : η*(‖b‖^2*‖c‖^2) ≤ ‖b‖^2*‖c‖^2-(inner ℝ b c)^2 :=
    (le_div_iff₀ (zero_lt_one.trans_le hL)).mp hangle
  have hmul : η ≤ η*(‖b‖^2*‖c‖^2) := by nlinarith
  have hsq : η ≤ (phaseFrameMatrix ν b c).det^2 := by
    rw [phaseFrameMatrix_det_sq ν b c hν hb hc]
    exact hmul.trans hh
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hsq

lemma physicalWaveJetMatrix_det_lower (a ν b c : PhaseSpace) (δ η : ℝ)
    (hν : ‖ν‖ = 1) (hb : inner ℝ ν b = 0) (hc : inner ℝ ν c = 0)
    (hbn : ‖b‖^2 = 1+‖a‖^2) (hcn : ‖c‖^2 = 1+‖a‖^2)
    (hη : 0 < η) (hangle : η ≤ transverseAngleSq b c) (hδ : 0 ≤ δ) :
    Real.sqrt η*δ ≤ |(physicalWaveJetMatrix a ν b c δ).det| := by
  rw [physicalWaveJetMatrix_det,abs_mul,abs_of_nonneg hδ]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (phaseFrameMatrix_det_lower a ν b c η hν hb hc hbn hcn hη hangle) hδ

lemma physicalWaveJetMatrix_bound (a ν b c : PhaseSpace) (δ M : ℝ)
    (hM : 1 ≤ M) (ha : ‖a‖ ≤ M) (hν : ‖ν‖ = 1)
    (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖physicalWaveJetMatrix a ν b c δ‖ ≤ M+1 := by
  apply (Matrix.norm_le_iff (by linarith : 0 ≤ M+1)).mpr
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · fin_cases i; fin_cases j
    norm_num [physicalWaveJetMatrix]
    linarith
  · fin_cases j <;> simp [physicalWaveJetMatrix] <;> linarith
  · simpa [physicalWaveJetMatrix] using (PiLp.norm_apply_le a i).trans (ha.trans (by linarith))
  · fin_cases j
    · change ‖a i+δ*ν i‖ ≤ M+1
      calc
        _ ≤ ‖a i‖+‖δ*ν i‖ := norm_add_le _ _
        _ = ‖a i‖+δ*‖ν i‖ := by rw [norm_mul,Real.norm_of_nonneg hδ]
        _ ≤ M+δ*1 := add_le_add ((PiLp.norm_apply_le a i).trans ha)
          (mul_le_mul_of_nonneg_left (by simpa [hν] using PiLp.norm_apply_le ν i) hδ)
        _ ≤ M+1 := by linarith
    · simpa [physicalWaveJetMatrix] using (PiLp.norm_apply_le b i).trans (hb.trans (by linarith))
    · simpa [physicalWaveJetMatrix] using (PiLp.norm_apply_le c i).trans (hc.trans (by linarith))

theorem physical_wave_smallBall_uniform (M C η : ℝ) (hM : 1 ≤ M)
    (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ a ν b c : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
        inner ℝ ν b = 0 → inner ℝ ν c = 0 →
        ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
        ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
      ∀ R : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ, ‖R‖ ≤ C*δ^2 →
      ∀ q : ℝ, 0 < q → ∀ w : (Fin 1 ⊕ Fin 3) → ℝ, (∀ i, q ≤ w i) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (g : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable g → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 1 ⊕ Fin 3 => gaussianReal 0 1)))
        {v | Matrix.toLin' ((physicalWaveJetMatrix a ν b c δ+R)*Matrix.diagonal w) v.2 + g v.1 ∈
          Metric.closedBall 0 r} ≤
      ENNReal.ofReal (Real.sqrt η/2*δ*q^4)⁻¹*(ENNReal.ofReal (2*r))^4 := by
  have hd : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  obtain ⟨ε,hε,he⟩ := determinant_uniform_error_bound (ι := Fin 1 ⊕ Fin 3) (M+1) C (Real.sqrt η) hC hd
  refine ⟨min ε 1,lt_min hε zero_lt_one,?_⟩
  intro δ hδ hδε a ν b c ha hν hb hc hbn hcn hbM hcM hang R hR q hq w hw Ω _ μ _ g hg r hr
  have hδ1 : δ ≤ 1 := (hδε.trans_le (min_le_right _ _)).le
  have hdet : Real.sqrt η/2*δ ≤ |(physicalWaveJetMatrix a ν b c δ+R).det| :=
    he δ hδ (hδε.trans_le (min_le_left _ _)) _ R
      (physicalWaveJetMatrix_bound a ν b c δ M hM ha hν hbM hcM hδ.le hδ1)
      (physicalWaveJetMatrix_det_lower a ν b c δ η hν hb hc hbn hcn hη hang hδ.le) hR
  have hdets := column_scaled_det_lower (physicalWaveJetMatrix a ν b c δ+R) w
    (Real.sqrt η/2*δ) q hq.le hdet hw
  norm_num only [Fintype.card_sum,Fintype.card_fin] at hdets
  have hdetpos : 0 < |((physicalWaveJetMatrix a ν b c δ+R)*Matrix.diagonal w).det| :=
    lt_of_lt_of_le (by positivity) hdets
  have hne : LinearMap.det (Matrix.toLin' ((physicalWaveJetMatrix a ν b c δ+R)*Matrix.diagonal w)) ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact abs_pos.mp hdetpos
  have hgau := gaussian_independent_smallBall μ g hg (fun _ => 0) 0
    (Matrix.toLin' ((physicalWaveJetMatrix a ν b c δ+R)*Matrix.diagonal w)) hne r hr
  norm_num only [Fintype.card_sum,Fintype.card_fin] at hgau
  apply hgau.trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  rw [LinearMap.det_toLin',abs_inv]
  exact inv_anti₀ (by positivity) hdets


end

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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def complexWaveJet (n : ℝ) (e : ℂ) (u : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) :
    (Fin 1 ⊕ Fin 3) → ℂ :=
  Sum.elim (fun _ => e⁻¹*u x)
    (fun i => (n : ℂ)⁻¹*e⁻¹*waveDeriv (Pi.single i 1) u x)

def leadingComplexJet (z : Fin 3 → ℂ) : (Fin 1 ⊕ Fin 3) → ℂ :=
  Sum.elim (fun _ => 1) z

def selectedComplexJetMatrix (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) :
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  Matrix.of (fun i j => Sum.elim (fun _ => (J 0 i).re)
    (fun k => ![(J 2 i).re,(J 0 i).im,(J 1 i).im] k) j)

lemma selectedComplexJetMatrix_leading (a ν b c d : PhaseSpace) (δ : ℝ) :
    selectedComplexJetMatrix (fun ℓ => leadingComplexJet
      (![complexPhaseVector a b,complexPhaseVector a c,
        complexPhaseVector (a+δ • ν) d] ℓ)) = physicalWaveJetMatrix a ν b c δ := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · fin_cases i; fin_cases j; simp [selectedComplexJetMatrix,leadingComplexJet,physicalWaveJetMatrix]
  · fin_cases j <;> simp [selectedComplexJetMatrix,leadingComplexJet,physicalWaveJetMatrix]
  · simp [selectedComplexJetMatrix,leadingComplexJet,complexPhaseVector,physicalWaveJetMatrix]
  · fin_cases j <;>
      simp [selectedComplexJetMatrix,leadingComplexJet,physicalWaveJetMatrix,complexPhaseVector,
        PiLp.add_apply,PiLp.smul_apply]

lemma selectedComplexJetMatrix_error (J K : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hJ : ∀ ℓ, ‖J ℓ-K ℓ‖ ≤ ε) :
    ‖selectedComplexJetMatrix J-selectedComplexJetMatrix K‖ ≤ ε := by
  apply (Matrix.norm_le_iff hε).mpr
  intro i j
  have hr (ℓ) : |(J ℓ i).re-(K ℓ i).re| ≤ ε := by
    have hh := (Complex.abs_re_le_norm (J ℓ i-K ℓ i)).trans
      ((norm_le_pi_norm (J ℓ-K ℓ) i).trans (hJ ℓ))
    simpa only [Complex.sub_re] using hh
  have hi (ℓ) : |(J ℓ i).im-(K ℓ i).im| ≤ ε := by
    have hh := (Complex.abs_im_le_norm (J ℓ i-K ℓ i)).trans
      ((norm_le_pi_norm (J ℓ-K ℓ) i).trans (hJ ℓ))
    simpa only [Complex.sub_im] using hh
  rcases j with j|j
  · exact hr 0
  · fin_cases j
    · exact hr 2
    · exact hi 0
    · exact hi 1

lemma complexWaveJet_error (n : ℝ) (e : ℂ) (u : (Fin 3 → ℝ) → ℂ)
    (x : Fin 3 → ℝ) (z : Fin 3 → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hv : ‖e⁻¹*u x-1‖ ≤ ε)
    (hd : ‖fun i => (n : ℂ)⁻¹*e⁻¹*waveDeriv (Pi.single i 1) u x-z i‖ ≤ ε) :
    ‖complexWaveJet n e u x-leadingComplexJet z‖ ≤ ε := by
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro i
  rcases i with i|i
  · exact hv
  · exact (norm_le_pi_norm _ i).trans hd

theorem generated_selected_columns_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → Fin 3 → ℂ)
    (hz : ∀ ℓ i, Continuous (fun p => z p ℓ i))
    (Q : X → Fin 3 → ComplexPhaseMatrix) (hQ : ∀ ℓ i j, Continuous (fun p => Q p ℓ i j))
    (hsym : ∀ p ℓ i j, Q p ℓ i j = Q p ℓ j i)
    (hnull : ∀ p ℓ, ∑ i, z p ℓ i*z p ℓ i = -1)
    (hQz : ∀ p ℓ k, ∑ i, z p ℓ i*Q p ℓ k i = 0)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    let S := fun p ℓ => realPolyEval (smoothPhasePolynomial (g p) (s p) (z p ℓ) (Q p ℓ)
      ((2*D+3*m+6)+(D+m+1)+1))
    let U := fun p ℓ n => canonicalCutoffWave (g p) (b p) (s p) (z p ℓ) (Q p ℓ) ζ m D n
    ∃ r > 0, ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : Fin 3 → ℝ,
      ‖x‖ < r → ‖x‖ ≤ 1/n →
      ‖selectedComplexJetMatrix (fun ℓ => complexWaveJet n (Complex.exp ((n : ℂ)*S p ℓ x)) (U p ℓ n) x)-
        selectedComplexJetMatrix (fun ℓ => leadingComplexJet (z p ℓ))‖ ≤ C/n := by
  dsimp only
  have hj (ℓ : Fin 3) := generated_cutoff_waves_near_center g b hg hb hg0 hdg0 hgc hbc s hs
    (fun p => z p ℓ) (hz ℓ) (fun p => Q p ℓ) (hQ ℓ) (fun p => hsym p ℓ)
    (fun p => hnull p ℓ) (fun p => hQz p ℓ) ζ hζ m D
  choose r hr C hC hbound using hj
  let r₀ := min (r 0) (min (r 1) (r 2))
  let C₀ := C 0+C 1+C 2
  have hr₀ : 0 < r₀ := lt_min (hr 0) (lt_min (hr 1) (hr 2))
  have hC₀ : 0 < C₀ := add_pos (add_pos (hC 0) (hC 1)) (hC 2)
  have hrle (ℓ : Fin 3) : r₀ ≤ r ℓ := by
    fin_cases ℓ
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hCle (ℓ : Fin 3) : C ℓ ≤ C₀ := by
    fin_cases ℓ <;> dsimp [C₀] <;> linarith [hC 0,hC 1,hC 2]
  refine ⟨r₀,hr₀,C₀,hC₀,?_⟩
  intro p n hn x hxr hx
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  apply selectedComplexJetMatrix_error _ _ _ (div_nonneg hC₀.le hn0.le)
  intro ℓ
  obtain ⟨hv,hd⟩ := hbound ℓ p n hn x (hxr.trans_le (hrle ℓ)) hx
  exact (complexWaveJet_error _ _ _ _ _ _ (div_nonneg (hC ℓ).le hn0.le) hv hd).trans
    (div_le_div_of_nonneg_right (hCle ℓ) hn0.le)


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
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal Matrix.Norms.Elementwise

lemma complex_polar_weight (e : ℂ) (W : ℝ) :
    (Circle.exp (Complex.arg e) : ℂ)*(‖e‖/W : ℝ) = e/(W : ℂ) := by
  rw [Circle.coe_exp,Complex.ofReal_div]
  calc
    _ = ((‖e‖ : ℂ)*Complex.exp ((Complex.arg e : ℂ)*Complex.I))/(W : ℂ) := by ring
    _ = _ := by rw [Complex.norm_mul_exp_arg_mul_I]

lemma complexWaveJet_factor (n W : ℝ) (e : ℂ) (he : e ≠ 0)
    (u : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) :
    complexWaveJet n (W : ℂ) u x = fun i =>
      (Circle.exp (Complex.arg e) : ℂ)*((‖e‖/W : ℝ) : ℂ)*complexWaveJet n e u x i := by
  ext i
  rw [complex_polar_weight]
  rcases i with i|i
  · change (W : ℂ)⁻¹*u x = (e/(W:ℂ))*(e⁻¹*u x)
    calc
      _ = (e*e⁻¹)*((W : ℂ)⁻¹*u x) := by rw [mul_inv_cancel₀ he,one_mul]
      _ = _ := by ring
  · change (n : ℂ)⁻¹*(W : ℂ)⁻¹*waveDeriv (Pi.single i 1) u x =
      (e/(W:ℂ))*((n : ℂ)⁻¹*e⁻¹*waveDeriv (Pi.single i 1) u x)
    calc
      _ = (e*e⁻¹)*((n : ℂ)⁻¹*(W : ℂ)⁻¹*waveDeriv (Pi.single i 1) u x) := by
        rw [mul_inv_cancel₀ he,one_mul]
      _ = _ := by ring

lemma phase_weight_lower (c n φ R : ℝ) (hc : 0 < c) (hn : 1 ≤ n)
    (hR0 : 0 ≤ R) (hR : R ≤ n^6*Real.exp (n*φ)) (e : ℂ)
    (heB : c*Real.exp (n*φ) ≤ ‖e‖) :
    c/2*(n^6)⁻¹ ≤ ‖e‖/(Real.exp (n*φ)+R) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hn6 : 1 ≤ n^6 := one_le_pow₀ hn
  have hexp : 0 < Real.exp (n*φ) := Real.exp_pos _
  have hW : 0 < Real.exp (n*φ)+R := add_pos_of_pos_of_nonneg hexp hR0
  have hupper : Real.exp (n*φ)+R ≤ 2*n^6*Real.exp (n*φ) := by
    nlinarith [mul_le_mul_of_nonneg_right hn6 hexp.le]
  apply (le_div_iff₀ hW).mpr
  calc
    _ ≤ (c/2*(n^6)⁻¹)*(2*n^6*Real.exp (n*φ)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = c*Real.exp (n*φ) := by field_simp
    _ ≤ ‖e‖ := heB


end YauCounterexamples
end

end OAI
