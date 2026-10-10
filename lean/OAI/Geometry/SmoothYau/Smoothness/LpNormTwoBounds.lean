import Mathlib
import OAI.Geometry.SmoothYau.Estimates.BasisWordEval
import OAI.Geometry.SmoothYau.Estimates.PullbackLintegral
import OAI.Geometry.SmoothYau.Smoothness.ContinuousSobolevFirstDerivative

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma besselPotential_two_eq (f : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 f = f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ f := by
  have h := quadraticMultiplier_eq (F := ℂ) 1 f
  simp only [one_smul] at h
  convert h using 1
  simp only [besselPotential, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]

def schwartzEllipticShift : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  ContinuousLinearMap.id ℂ _ - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • LineDeriv.laplacianCLM ℂ E 𝓢(E, ℂ)

omit [MeasurableSpace E] [BorelSpace E] in
lemma schwartzEllipticShift_apply (f : 𝓢(E, ℂ)) :
    schwartzEllipticShift f = f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ f := by
  simp [schwartzEllipticShift, SchwartzMap.laplacianCLM_eq]

lemma schwartzEllipticShift_distribution (f : 𝓢(E, ℂ)) :
    (schwartzEllipticShift f : 𝓢'(E, ℂ)) = besselPotential E ℂ 2 (f : 𝓢'(E, ℂ)) := by
  rw [schwartzEllipticShift_apply, besselPotential_two_eq]
  simp

lemma schwartzToSobolev_shift (s : ℝ) (f : 𝓢(E, ℂ)) :
    schwartzToSobolev s (schwartzEllipticShift f) = schwartzToSobolev (s + 2) f := by
  apply fourierSobolevDistribution_injective s
  rw [schwartzToSobolev_distribution, schwartzEllipticShift_distribution]
  have h := besselPotential_fourierSobolevDistribution (s + 2) 2 (schwartzToSobolev (s + 2) f)
  rw [show s + 2 - 2 = s by ring] at h
  simpa only [schwartzToSobolev_distribution] using h

lemma schwartzToSobolev_zero (f : 𝓢(E, ℂ)) :
    schwartzToSobolev 0 f = 𝓕 (f.toLp 2 volume) := by
  rw [schwartzToSobolev_apply, SchwartzMap.toLp_fourier_eq]
  congr 1
  ext x
  simp [weightedSchwartz_apply, sobolevWeight]

lemma norm_schwartzToSobolev_zero (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev 0 f‖ = ‖f.toLp 2 volume‖ := by
  rw [schwartzToSobolev_zero, Lp.norm_fourier_eq]

lemma schwartzToSobolev_iterate_shift (k : ℕ) (s : ℝ) (f : 𝓢(E, ℂ)) :
    schwartzToSobolev s ((schwartzEllipticShift (E := E))^[k] f) =
      schwartzToSobolev (s + 2 * (k : ℝ)) f := by
  induction k generalizing s with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact congrArg (β := Lp ℂ 2 (volume : Measure E)) (fun t : ℝ => schwartzToSobolev t f) (by simp)
  | succ k ih =>
    rw [Function.iterate_succ_apply', schwartzToSobolev_shift, ih]
    exact congrArg (β := Lp ℂ 2 (volume : Measure E)) (fun t : ℝ => schwartzToSobolev t f) (by push_cast; ring)

theorem norm_schwartzToSobolev_even (k : ℕ) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev (2 * (k : ℝ)) f‖ =
      ‖(((schwartzEllipticShift (E := E))^[k]) f).toLp 2 volume‖ := by
  have h := schwartzToSobolev_iterate_shift k 0 f
  have he := congrArg (β := Lp ℂ 2 (volume : Measure E)) (fun t : ℝ => schwartzToSobolev t f) (zero_add (2 * (k : ℝ)))
  exact (congrArg norm (h.trans he).symm).trans (norm_schwartzToSobolev_zero _)

lemma sobolevInclusion_schwartz (s t : ℝ) (h : t ≤ s) (f : 𝓢(E, ℂ)) :
    sobolevInclusion s t h (schwartzToSobolev s f) = schwartzToSobolev t f := by
  apply fourierSobolevDistribution_injective t
  rw [sobolevInclusion_distribution, schwartzToSobolev_distribution, schwartzToSobolev_distribution]

lemma norm_schwartzToSobolev_mono (s t : ℝ) (h : t ≤ s) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev t f‖ ≤ ‖schwartzToSobolev s f‖ := by
  rw [← sobolevInclusion_schwartz s t h f]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right
          (norm_sobolevInclusion_le (E := E) (F := ℂ) s t h) (norm_nonneg (schwartzToSobolev s f)))

lemma schwartz_derivative_norm_bound (s : ℝ) (v : E) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev (s - 1) (∂_{v} f)‖ ≤ 2 * Real.pi * ‖v‖ * ‖schwartzToSobolev s f‖ := by
  rw [← sobolevDerivative_schwartz]
  exact sobolevDerivative_bound s v _


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma norm_schwartz_word_bound (k : ℕ) (m : Fin k → E) (s : ℝ) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev s (∂^{m} f)‖ ≤
      (2 * Real.pi) ^ k * (∏ i, ‖m i‖) * ‖schwartzToSobolev (s + (k : ℝ)) f‖ := by
  induction k generalizing s with
  | zero =>
    simp only [LineDeriv.iteratedLineDerivOp_fin_zero, pow_zero, Fin.prod_univ_zero, one_mul]
    have he : s + (0 : ℕ) = s := by simp
    rw [he]
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    have hd := schwartz_derivative_norm_bound (s + 1) (m 0) (∂^{Fin.tail m} f)
    rw [show s + 1 - 1 = s by ring] at hd
    have hi := ih (Fin.tail m) (s + 1)
    refine hd.trans ((mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq ?_)
    rw [Fin.prod_univ_succ, pow_succ, Nat.cast_succ]
    have he : s + 1 + (k : ℝ) = s + ((k : ℝ) + 1) := by ring
    rw [he]
    simp only [Fin.tail_def]
    ring

lemma schwartz_word_L2_bound (k : ℕ) (m : Fin k → E) (s : ℝ) (h : (k : ℝ) ≤ s)
    (f : 𝓢(E, ℂ)) :
    ‖(∂^{m} f).toLp 2 volume‖ ≤
      (2 * Real.pi) ^ k * (∏ i, ‖m i‖) * ‖schwartzToSobolev s f‖ := by
  rw [← norm_schwartzToSobolev_zero]
  have hb := norm_schwartz_word_bound k m 0 f
  have he : (0 : ℝ) + (k : ℝ) = (k : ℝ) := zero_add _
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (norm_schwartzToSobolev_mono s k h f) (by positivity))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma norm_schwartz_shift_le (s : ℝ) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev (s + 2) f‖ ≤ ‖schwartzToSobolev s f‖ +
      ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * ∑ i : Fin (Module.finrank ℝ E),
        ‖schwartzToSobolev s (∂_{stdOrthonormalBasis ℝ E i}
          (∂_{stdOrthonormalBasis ℝ E i} f))‖ := by
  rw [← schwartzToSobolev_shift, schwartzEllipticShift_apply,
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  let L := (schwartzToSobolev (E := E) s).restrictScalars ℝ
  change ‖L (f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • ∑ i : Fin (Module.finrank ℝ E),
    ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E i} f))‖ ≤
    ‖L f‖ + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * ∑ i : Fin (Module.finrank ℝ E),
      ‖L (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E i} f))‖
  rw [map_sub, map_smul, map_sum]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ ((2 * Real.pi) ^ 2 : ℝ)⁻¹)]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg (2 * Real.pi)))
  exact norm_sum_le _ _

def SchwartzWordBound (k : ℕ) (f : 𝓢(E, ℂ)) (B : ℝ) : Prop :=
  ∀ j, j ≤ k → ∀ w : Fin j → Fin (Module.finrank ℝ E),
    ‖(∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f).toLp 2 volume‖ ≤ B

lemma SchwartzWordBound.mono {k l : ℕ} {f : 𝓢(E, ℂ)} {B : ℝ}
    (h : SchwartzWordBound k f B) (hle : l ≤ k) : SchwartzWordBound l f B :=
  fun j hj w => h j (hj.trans hle) w

lemma SchwartzWordBound.second {k : ℕ} {f : 𝓢(E, ℂ)} {B : ℝ}
    (h : SchwartzWordBound (k + 2) f B) (i : Fin (Module.finrank ℝ E)) :
    SchwartzWordBound k (∂_{stdOrthonormalBasis ℝ E i}
      (∂_{stdOrthonormalBasis ℝ E i} f)) B := by
  intro j hj w
  have hh := h (j + 2) (by omega) (Fin.snoc (Fin.snoc w i) i)
  change ‖(∂^{(stdOrthonormalBasis ℝ E) ∘ Fin.snoc (Fin.snoc w i) i} f).toLp 2 volume‖ ≤ B at hh
  simp only [Fin.comp_snoc, LineDeriv.iteratedLineDerivOp_succ_right,
    Fin.init_snoc, Fin.snoc_last] at hh
  exact hh

theorem sobolev_even_le_word_bound (k : ℕ) (f : 𝓢(E, ℂ)) (B : ℝ)
    (h : SchwartzWordBound (2 * k) f B) :
    ‖schwartzToSobolev (2 * (k : ℝ)) f‖ ≤
      (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ k * B := by
  induction k generalizing f with
  | zero =>
    have hh := h 0 (by omega) Fin.elim0
    rw [Nat.cast_zero, mul_zero, pow_zero, one_mul, norm_schwartzToSobolev_zero]
    exact hh
  | succ k ih =>
    have hf := ih f (h.mono (by omega))
    have hD : ∀ i : Fin (Module.finrank ℝ E),
        ‖schwartzToSobolev (2 * (k : ℝ)) (∂_{stdOrthonormalBasis ℝ E i}
          (∂_{stdOrthonormalBasis ℝ E i} f))‖ ≤
        (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ k * B := by
      intro i
      apply ih
      apply SchwartzWordBound.second
      exact h.mono (by omega)
    have hs := norm_schwartz_shift_le (2 * (k : ℝ)) f
    have he : 2 * (k : ℝ) + 2 = 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [he] at hs
    refine hs.trans ((add_le_add hf
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hD i)) (by positivity))).trans_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
    ring


open MeasureTheory

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open scoped LineDeriv NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_word_eLpNorm_bound (j : ℕ) (w : Fin j → Fin (Module.finrank ℝ E))
    (s : ℝ) (hjs : (j : ℝ) ≤ s) (f : 𝓢(E, ℂ)) :
    eLpNorm ((∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f : 𝓢(E, ℂ)) : E → ℂ) 2 volume ≤
      ENNReal.ofReal ((2 * Real.pi) ^ j * ‖schwartzToSobolev s f‖) := by
  rw [← Lp.enorm_toLp ((∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f).memLp 2 volume),
    ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [SchwartzMap.toLp, OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one] using
    schwartz_word_L2_bound j (fun a => stdOrthonormalBasis ℝ E (w a)) s hjs f

theorem iteratedFDeriv_eLpNorm_bound (j : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (s : ℝ), (j : ℝ) ≤ s → ∀ f : 𝓢(E, ℂ),
      eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≤
        ENNReal.ofReal (C * ‖schwartzToSobolev s f‖) := by
  classical
  obtain ⟨C, hC, hbound⟩ := multilinear_norm_le_basis_sum
    (stdOrthonormalBasis ℝ E).toBasis j
  refine ⟨C * (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) + 1) *
    (2 * Real.pi) ^ j, by positivity, fun s hjs f => ?_⟩
  let W (w : Fin j → Fin (Module.finrank ℝ E)) : 𝓢(E, ℂ) :=
    ∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f
  have hp (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ C * ∑ w, ‖W w x‖ := by
    convert hbound (iteratedFDeriv ℝ j f x) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    simp only [W, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl
  have hnorm : eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≤
      ENNReal.ofReal C * ∑ w, eLpNorm (W w) 2 volume := by
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ j f) (volume : Measure E) :=
      ((f.smooth ⊤).continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).aestronglyMeasurable
    calc
      _ ≤ eLpNorm (fun x => C * ∑ w, ‖W w x‖) 2 volume :=
        eLpNorm_mono_real hmeas hp
      _ = ENNReal.ofReal C * eLpNorm (∑ w, fun x => ‖W w x‖) 2 volume := by
        rw [show (fun x => C * ∑ w, ‖W w x‖) = C • (∑ w, fun x => ‖W w x‖) by
          ext x; simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul],
          eLpNorm_const_smul, Real.enorm_eq_ofReal hC.le]
      _ ≤ ENNReal.ofReal C * ∑ w, eLpNorm (W w) 2 volume := by
        apply mul_le_mul' le_rfl
        simpa only [eLpNorm_norm _ (W _).continuous.aestronglyMeasurable] using eLpNorm_sum_le
          (s := Finset.univ) (μ := (volume : Measure E)) (p := 2)
          (f := fun w x => ‖W w x‖) (by norm_num)
  refine hnorm.trans ?_
  have hh := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ :
      Finset (Fin j → Fin (Module.finrank ℝ E)))) =>
    schwartz_word_eLpNorm_bound j w s hjs f)
  refine (mul_le_mul' le_rfl hh).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hC.le]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = C * (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ) *
      (2 * Real.pi) ^ j * ‖schwartzToSobolev s f‖ := by ring
    _ ≤ _ := by
      gcongr
      linarith


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def jetMajorant (N : ℕ) (f : E → ℂ) (x : E) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ j f x‖

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma jetMajorant_nonneg (N : ℕ) (f : E → ℂ) (x : E) : 0 ≤ jetMajorant N f x :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma le_jetMajorant (N : ℕ) (f : E → ℂ) (x : E) (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ jetMajorant N f x :=
by
  unfold jetMajorant
  exact Finset.single_le_sum (f := fun i : ℕ => ‖iteratedFDeriv ℝ i f x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega : j < N + 1))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_jetMajorant (N : ℕ) (f : 𝓢(E, ℂ)) : Continuous (jetMajorant N f) := by
  apply continuous_finsetSum
  intro j _
  exact ((f.smooth ⊤).continuous_iteratedFDeriv
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).norm

theorem jetMajorant_eLpNorm_bound (N : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (s : ℝ), (N : ℝ) ≤ s → ∀ f : 𝓢(E, ℂ),
      eLpNorm (jetMajorant N f) 2 volume ≤
        ENNReal.ofReal (C * ‖schwartzToSobolev s f‖) := by
  classical
  choose C hC hc using (fun j => iteratedFDeriv_eLpNorm_bound (E := E) j)
  have hsumpos : 0 ≤ ∑ j ∈ Finset.range (N + 1), C j :=
    Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨1 + ∑ j ∈ Finset.range (N + 1), C j, by linarith, fun s hs f => ?_⟩
  have hsum : eLpNorm (jetMajorant N f) 2 volume ≤
      ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (C j * ‖schwartzToSobolev s f‖) := by
    have hmeas (j : ℕ) : AEStronglyMeasurable
        (iteratedFDeriv ℝ j f) (volume : Measure E) :=
      (((f.smooth ⊤).continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).aestronglyMeasurable)
    have hh := eLpNorm_sum_le (s := Finset.range (N + 1)) (μ := (volume : Measure E)) (p := 2)
      (f := fun j x => ‖iteratedFDeriv ℝ j f x‖) (by norm_num)
    have heq : (∑ j ∈ Finset.range (N + 1), fun x => ‖iteratedFDeriv ℝ j f x‖) =
        jetMajorant N f := by ext x; simp only [Finset.sum_apply, jetMajorant]
    rw [heq] at hh
    simp only [eLpNorm_norm _ (hmeas _)] at hh
    refine hh.trans (Finset.sum_le_sum ?_)
    intro j hj
    apply hc j s _ f
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    exact (show (j : ℝ) ≤ N by exact_mod_cast hjN).trans hs
  refine hsum.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hC j).le (norm_nonneg _)),
    ← Finset.sum_mul]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith


open Function

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_derivative_bound {K : Set E} (hK : IsCompact K)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  classical
  have h (j : ℕ) := hK.exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).continuousOn)
  choose c hc using h
  refine ⟨1 + ∑ j ∈ Finset.range (N + 1), |c j|,
    le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro j hj x hx
  calc
    _ ≤ c j := hc j x hx
    _ ≤ |c j| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (N + 1), |c j| :=
      Finset.single_le_sum (f := fun i : ℕ => |c i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega : j < N + 1))
    _ ≤ _ := by linarith

lemma cutoff_comp_derivative_bound {K : Set E} (hK : IsCompact K)
    {η : E → ℂ} (hη : ContDiff ℝ ∞ η) {φ : E → E} (hφ : ContDiff ℝ ∞ φ)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (f : E → ℂ), ContDiff ℝ ∞ f →
      ∀ n ≤ N, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (fun y => η y * f (φ y)) x‖ ≤
          C * jetMajorant N f (φ x) := by
  classical
  obtain ⟨B, hB, hb⟩ := compact_derivative_bound hK hη N
  obtain ⟨D, hD, hd⟩ := compact_derivative_bound hK hφ N
  let c (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * B * (n - i).factorial * D ^ (n - i)
  have hc (n : ℕ) : 0 ≤ c n := by unfold c; positivity
  refine ⟨1 + ∑ n ∈ Finset.range (N + 1), c n, by positivity, ?_⟩
  intro f hf n hn x hx
  have H (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j (f ∘ φ) x‖ ≤
      j.factorial * jetMajorant N f (φ x) * D ^ j := by
    apply norm_iteratedFDeriv_comp_le hf hφ
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    · intro i hi
      exact le_jetMajorant N f (φ x) i (hi.trans hj)
    · intro i hi hi'
      exact (hd i (hi'.trans hj) x hx).trans (le_self_pow₀ hD (by omega))
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i η x‖ * ‖iteratedFDeriv ℝ (n - i) (f ∘ φ) x‖ :=
      norm_iteratedFDeriv_mul_le hη (hf.comp hφ) x
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B *
        ((n - i).factorial * jetMajorant N f (φ x) * D ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hb i (by have := Finset.mem_range.mp hi; omega) x hx)
          (Nat.cast_nonneg _)
      · exact H (n - i) ((Nat.sub_le n i).trans hn)
      · exact norm_nonneg _
      · positivity
    _ = c n * jetMajorant N f (φ x) := by
      simp only [c, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (1 + ∑ n ∈ Finset.range (N + 1), c n) * jetMajorant N f (φ x) := by
      apply mul_le_mul_of_nonneg_right _ (jetMajorant_nonneg ..)
      have hh := Finset.single_le_sum (fun j _ => hc j)
        (Finset.mem_range.mpr (by omega : n < N + 1))
      linarith

lemma cutoff_comp_derivative_zero {η : E → ℂ} {φ : E → E} {f : E → ℂ}
    {x : E} (hx : x ∉ tsupport η) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => η y * f (φ y)) x = 0 := by
  apply notMem_support.mp
  intro hx'
  exact hx (tsupport_mul_subset_left (f := η) (g := f ∘ φ)
    (support_iteratedFDeriv_subset n hx'))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cutoffPullback (η : E → ℂ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ ∞ η)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (hηc.mul_right (f' := fun y => f (φ y))).toSchwartzMap (hη.mul ((f.smooth ⊤).comp hφ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma cutoffPullback_apply (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (f : 𝓢(E, ℂ)) (x : E) :
    cutoffPullback η hηc hη φ hφ f x = η x * f (φ x) := rfl

lemma supported_pullback_eLpNorm_le {F : Type*} [NormedAddCommGroup F]
    {S : Set E} (hS : MeasurableSet S) {f : E → F} (hf : Function.support f ⊆ S)
    {φ : E → E} (hφ : ContDiff ℝ ∞ φ) (hinj : Set.InjOn φ S)
    (J : ℝ≥0) (hJ : ∀ x ∈ S, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (g : E → ℝ) (A : ℝ) (hA : 0 ≤ A) (hb : ∀ x ∈ S, ‖f x‖ ≤ A * g (φ x)) :
    eLpNorm' f 2 volume ≤ ENNReal.ofReal A * ((J : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm' g 2 volume) := by
  calc
    _ = eLpNorm' f 2 (volume.restrict S) := by
      simp only [eLpNorm'_eq_lintegral_enorm]
      congr 1
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra hnot
      have hzero : f x = 0 := by
        by_contra hnonzero
        exact hnot (hf hnonzero)
      simp [Function.mem_support, hzero] at hx
    _ ≤ eLpNorm' (fun x => A * g (φ x)) 2 (volume.restrict S) := by
      apply eLpNorm'_mono_ae (by norm_num)
      filter_upwards [ae_restrict_mem hS] with x hx
      exact (hb x hx).trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)
    _ = ENNReal.ofReal A * eLpNorm' (g ∘ φ) 2 (volume.restrict S) := by
      rw [show (fun x => A * g (φ x)) = A • (g ∘ φ) by rfl,
        eLpNorm'_const_smul A (by norm_num), Real.enorm_eq_ofReal hA]
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      have hbound := pullback_lintegral_le volume hS
        (fun x _ => (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        hinj J hJ (fun x => ‖g x‖ₑ ^ (2 : ℝ))
      simpa only [eLpNorm'_eq_lintegral_enorm, Function.comp_apply,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))] using
        ENNReal.rpow_le_rpow hbound (by norm_num : 0 ≤ (1 / 2 : ℝ))

lemma cutoffPullback_derivative_L2 (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ), (N : ℝ) ≤ s → ∀ f : 𝓢(E, ℂ),
      ∀ n ≤ N, eLpNorm (iteratedFDeriv ℝ n (cutoffPullback η hηc hη φ hφ f)) 2 volume ≤
        ENNReal.ofReal (C * ‖schwartzToSobolev s f‖) := by
  obtain ⟨A, hA, ha⟩ := cutoff_comp_derivative_bound hηc hη hφ N
  obtain ⟨B, hB, hb⟩ := jetMajorant_eLpNorm_bound (E := E) N
  let D : ℝ := (J : ℝ) ^ (1 / 2 : ℝ)
  have hD : 0 ≤ D := Real.rpow_nonneg J.coe_nonneg _
  have heD : (J : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal D := by
    dsimp only [D]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_rpow_of_nonneg (p := (1 / 2 : ℝ)) J.coe_nonneg (by norm_num))
  refine ⟨A * (D + 1) * B, by positivity, fun s hs f n hn => ?_⟩
  let g := cutoffPullback η hηc hη φ hφ f
  have hsup : Function.support (iteratedFDeriv ℝ n g) ⊆ tsupport η :=
    (support_iteratedFDeriv_subset n).trans tsupport_mul_subset_left
  have hbound : eLpNorm (iteratedFDeriv ℝ n g) 2 volume ≤
      ENNReal.ofReal A * ((J : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm (jetMajorant N f) 2 volume) := by
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ n g) (volume : Measure E) :=
      ((g.smooth ⊤).continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).aestronglyMeasurable
    rw [eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hmeas,
      eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num)
        (continuous_jetMajorant N f).aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat]
    exact supported_pullback_eLpNorm_le isClosed_closure.measurableSet hsup hφ hinj
      J hJ (jetMajorant N f) A hA.le (ha f (f.smooth ⊤) n hn)
  apply hbound.trans
  calc
    ENNReal.ofReal A * ((J : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm (jetMajorant N f) 2 volume)
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal D *
        ENNReal.ofReal (B * ‖schwartzToSobolev s f‖)) := by
      rw [heD]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hb s hs f))
    _ = ENNReal.ofReal (A * D * B * ‖schwartzToSobolev s f‖) := by
      rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul hA.le]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      linarith


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lp_norm_le_two_bounds {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g h : Lp ℂ 2 μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ a * ‖g x‖ + b * ‖h x‖) :
    ‖f‖ ≤ a * ‖g‖ + b * ‖h‖ := by
  let G : Lp ℝ 2 μ := (Lp.memLp g).norm.toLp (fun x => ‖g x‖)
  let H : Lp ℝ 2 μ := (Lp.memLp h).norm.toLp (fun x => ‖h x‖)
  have hG : ‖G‖ = ‖g‖ := by
    dsimp only [G]
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.memLp g).aestronglyMeasurable, Lp.norm_def]
  have hH : ‖H‖ = ‖h‖ := by
    dsimp only [H]
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.memLp h).aestronglyMeasurable, Lp.norm_def]
  have hh : ‖f‖ ≤ ‖a • G + b • H‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf, (Lp.memLp g).norm.coeFn_toLp, (Lp.memLp h).norm.coeFn_toLp,
      Lp.coeFn_add (a • G) (b • H), Lp.coeFn_smul a G, Lp.coeFn_smul b H] with x hx hg hh hs ha' hb'
    rw [hs]
    simp only [Pi.add_apply]
    rw [ha', hb']
    change ‖f x‖ ≤ ‖a * G x + b * H x‖
    change G x = ‖g x‖ at hg
    change H x = ‖h x‖ at hh
    rw [hg, hh, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hx
  exact hh.trans ((norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, hG, hH]))

lemma power_interpolation {q ε : ℝ} (hq : 1 ≤ q) (hε : 0 < ε) (k : ℕ) :
    q ^ k ≤ ε * q ^ (k + 1) + (ε⁻¹) ^ k := by
  by_cases h : ε⁻¹ ≤ q
  · have he : 1 ≤ ε * q := by
      simpa only [mul_inv_cancel₀ hε.ne.symm] using mul_le_mul_of_nonneg_left h hε.le
    have hmul := mul_le_mul_of_nonneg_right he (pow_nonneg (by linarith : 0 ≤ q) k)
    rw [one_mul] at hmul
    calc
      _ ≤ ε * q ^ (k + 1) := by simpa only [pow_succ] using hmul.trans_eq (by ring)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hp := pow_le_pow_left₀ (by linarith : 0 ≤ q) (le_of_not_ge h) k
    exact hp.trans (le_add_of_nonneg_left (by positivity))

lemma norm_schwartz_interpolation (k : ℕ) {ε : ℝ} (hε : 0 < ε) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev (2 * (k : ℝ)) f‖ ≤
      ε * ‖schwartzToSobolev (2 * ((k + 1 : ℕ) : ℝ)) f‖ +
      (ε⁻¹)^k * ‖schwartzToSobolev 0 f‖ := by
  apply lp_norm_le_two_bounds _ _ _ hε.le (by positivity)
  rw [schwartzToSobolev_apply, schwartzToSobolev_apply, schwartzToSobolev_apply]
  filter_upwards [(weightedSchwartz (2 * (k : ℝ)) (𝓕 f)).coeFn_toLp 2 volume,
    (weightedSchwartz (2 * ((k + 1 : ℕ) : ℝ)) (𝓕 f)).coeFn_toLp 2 volume,
    (weightedSchwartz 0 (𝓕 f)).coeFn_toLp 2 volume] with x hx hy hz
  rw [hx, hy, hz, norm_weightedSchwartz, norm_weightedSchwartz, norm_weightedSchwartz]
  simp only [sobolevWeight, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    zero_div, Real.rpow_zero, one_mul, Real.rpow_natCast]
  have hh := mul_le_mul_of_nonneg_right (power_interpolation (by linarith [sq_nonneg ‖x‖] : 1 ≤ 1 + ‖x‖ ^ 2) hε k)
    (norm_nonneg ((𝓕 f) x))
  convert hh using 1
  first | rfl | ring

lemma sobolev_interpolation (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (u : FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ))) :
    ‖sobolevInclusion _ (2 * (k : ℝ)) (by push_cast; linarith) u‖ ≤
      ε * ‖u‖ + (ε⁻¹)^k * ‖sobolevInclusion _ 0 (by positivity) u‖ := by
  refine (denseRange_schwartzToSobolev _).induction_on u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    simp only [sobolevInclusion_schwartz]
    exact norm_schwartz_interpolation k hε f


end YauCounterexamples
end

end OAI
