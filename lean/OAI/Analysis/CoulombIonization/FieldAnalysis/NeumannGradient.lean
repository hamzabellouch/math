import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannCube
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannSine

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannGradient_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

variable {d : ℕ}

lemma cubeNeumannMode_split (i : Fin (d+1)) (n : Fin (d+1) → ℕ)
    (t : I) (y : Fin d → I) :
    cubeNeumannMode n (i.insertNth t y) =
      neumannMode (n i) t * cubeNeumannMode (n ∘ i.succAbove) y := by
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,i.prod_univ_succAbove,
    Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,Function.comp_def]

lemma cubeSineMode_split (i : Fin (d+1)) (n : {n : Fin (d+1) → ℕ // n i ≠ 0})
    (t : I) (y : Fin d → I) :
    cubeSineMode i n (i.insertNth t y) =
      sineMode (n.1 i-1) t * cubeNeumannMode (n.1 ∘ i.succAbove) y := by
  simp [cubeSineMode,cubeNeumannMode,i.prod_univ_succAbove,Fin.succAbove_ne]

lemma coe_insertNth (i : Fin (d+1)) (t : I) (y : Fin d → I) :
    (fun j => (i.insertNth (α := fun _ => I) t y j : ℝ)) = i.insertNth (α := fun _ => ℝ) (t:ℝ) (fun j => (y j:ℝ)) := by
  ext j
  refine i.succAboveCases ?_ (fun k => ?_) j <;> simp

lemma contDiff_insertNth (i : Fin (d+1)) (y : Fin d → ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => i.insertNth (α := fun _ => ℝ) t y) := by
  rw [contDiff_pi]
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j <;> simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove] <;> fun_prop

lemma hasDerivAt_insertNth (i : Fin (d+1)) (y : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => i.insertNth (α := fun _ => ℝ) t y) (Pi.single i 1) t := by
  rw [hasDerivAt_pi]
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simpa only [Fin.insertNth_apply_same,Pi.single_eq_same] using hasDerivAt_id' t
  · simpa only [Fin.insertNth_apply_succAbove,Pi.single_eq_of_ne (Fin.succAbove_ne i k)] using hasDerivAt_const t (y k)

def cubeFunction {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) : C(Fin (d+1) → I,ℂ) where
  toFun x := f (fun i => (x i:ℝ))
  continuous_toFun := hf.continuous.comp (by fun_prop)

def cubeGradient {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin (d+1)) :
    C(Fin (d+1) → I,ℂ) where
  toFun x := fderiv ℝ f (fun j => (x j:ℝ)) (Pi.single i 1)
  continuous_toFun := ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp (by fun_prop)

lemma deriv_slice {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (i : Fin (d+1)) (y : Fin d → ℝ) (t : ℝ) :
    deriv (fun t => f (i.insertNth t y)) t =
      fderiv ℝ f (i.insertNth t y) (Pi.single i 1) := by
  exact (((hf.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_insertNth i y t)).deriv

lemma cube_derivative_pairing {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (i : Fin (d+1)) (n : {n : Fin (d+1) → ℕ // n i ≠ 0}) :
    (∫ x, conj (cubeSineMode i n x)*cubeGradient hf i x) =
      -(Real.pi*n.1 i:ℝ)*(∫ x, conj (cubeNeumannMode n.1 x)*cubeFunction hf x) := by
  have hs : Integrable (fun x => conj (cubeSineMode i n x)*cubeGradient hf i x) :=
    (by fun_prop : Continuous (fun x => conj (cubeSineMode i n x)*cubeGradient hf i x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun x => conj (cubeNeumannMode n.1 x)*cubeFunction hf x) :=
    (by fun_prop : Continuous (fun x => conj (cubeNeumannMode n.1 x)*cubeFunction hf x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_cube_split i _ hs,integral_cube_split i _ hc,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [cubeSineMode_split,cubeNeumannMode_split,map_mul,cubeGradient,cubeFunction,
    ContinuousMap.coe_mk,coe_insertNth]
  have hp := normalized_sine_derivative_pairing
    (hf.comp (contDiff_insertNth i (fun j => (y j:ℝ)))) n.2
  simp only [Function.comp_def,deriv_slice hf] at hp
  simp only [mul_right_comm _ (conj (cubeNeumannMode (n.1 ∘ i.succAbove) y)),integral_mul_const]
  rw [hp]
  ring

end Work_NeumannGradient_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

lemma continuous_toLp_norm_sq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X,ℂ)) : ‖ContinuousMap.toLp 2 μ ℂ f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),ContinuousMap.inner_toLp]
  simp_rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [integral_complex_ofReal]
  rfl

variable {d : Type*} [Fintype d]

def neumannCoeff (f : C(d → I,ℂ)) (n : d → ℕ) : ℂ :=
  ∫ x, conj (cubeNeumannMode n x)*f x

lemma neumannCoeff_eq_inner (f : C(d → I,ℂ)) (n : d → ℕ) :
    neumannCoeff f n = inner ℂ (neumannLp n) (ContinuousMap.toLp 2 volume ℂ f) := by
  rw [ContinuousMap.inner_toLp]
  simp only [neumannCoeff,mul_comm]

lemma neumann_parseval (f : C(d → I,ℂ)) :
    (∑' n, ‖neumannCoeff f n‖^2) = ∫ x, ‖f x‖^2 := by
  let v := ContinuousMap.toLp 2 volume ℂ f
  have h := lp.norm_rpow_eq_tsum (p := (2:ENNReal)) (by norm_num)
    (neumannBasis.repr v)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,HilbertBasis.repr_apply_apply,
    neumannBasis_apply,LinearIsometryEquiv.norm_map] at h
  simpa only [v,neumannCoeff_eq_inner,continuous_toLp_norm_sq] using h.symm

lemma neumannCoeff_summable (f : C(d → I,ℂ)) :
    Summable (fun n => ‖neumannCoeff f n‖^2) := by
  simp only [neumannCoeff_eq_inner]
  exact orthonormal_neumann.inner_products_summable _

variable {D : ℕ}

lemma neumann_derivative_bessel {f : (Fin (D+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (i : Fin (D+1)) (S : Finset {n : Fin (D+1) → ℕ // n i ≠ 0}) :
    ∑ n ∈ S, (Real.pi*(n.1 i:ℝ))^2*‖neumannCoeff (cubeFunction hf) n.1‖^2 ≤
      ∫ x, ‖cubeGradient hf i x‖^2 := by
  have h := (orthonormal_cubeSine i).sum_inner_products_le
    (s := S) (ContinuousMap.toLp 2 volume ℂ (cubeGradient hf i))
  rw [continuous_toLp_norm_sq] at h
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro n _
  rw [ContinuousMap.inner_toLp]
  have he : (∫ x, cubeGradient hf i x*conj (cubeSineMode i n x)) =
      -(Real.pi*n.1 i:ℝ)*neumannCoeff (cubeFunction hf) n.1 := by
    simpa only [neumannCoeff,mul_comm] using cube_derivative_pairing hf i n
  simp only [he,norm_mul,norm_neg,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem neumann_spectral_lower {f : (Fin (D+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (S : Finset (Fin (D+1) → ℕ)) :
    ∑ n ∈ S, (∑ i, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (cubeFunction hf) n‖^2 ≤
      ∑ i, ∫ x, ‖cubeGradient hf i x‖^2 := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  let S' := S.subtype (fun n => n i ≠ 0)
  have h := neumann_derivative_bessel hf i S'
  refine le_trans (le_of_eq ?_) h
  dsimp only [S']
  rw [Finset.sum_subtype_eq_sum_filter
    (fun n : Fin (D+1) → ℕ => (Real.pi*(n i:ℝ))^2*‖neumannCoeff (cubeFunction hf) n‖^2),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n i = 0 <;> simp [hn]

end CoulombNeumann

end

end OAI
