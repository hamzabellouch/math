import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyPrefix
import OAI.Probability.SKBarriers.Gaussian.MeanStein

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def normalizedDot {N : ℕ} (a b : Fin N → ℝ) : ℝ := (∑ i, a i*b i)/(N : ℝ)

def normalizedSquare {N : ℕ} (a : Fin N → ℝ) : ℝ := (∑ i, (a i)^2)/(N : ℝ)

theorem normalizedSquare_nonneg {N : ℕ} (a : Fin N → ℝ) : 0 ≤ normalizedSquare a := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem normalizedSquare_le_one {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    normalizedSquare a ≤ 1 := by
  by_cases hN : N = 0
  · simp [normalizedSquare,hN]
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  apply (div_le_iff₀ hn).2
  calc
    (∑ i, (a i)^2) ≤ ∑ _ : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [ha i,sq_abs (a i),abs_nonneg (a i)]
    _ = 1*(N : ℝ) := by simp

theorem normalizedDot_self {N : ℕ} (a : Fin N → ℝ) :
    normalizedDot a a = normalizedSquare a := by simp [normalizedDot,normalizedSquare,pow_two]

theorem normalizedDot_sq_le {N : ℕ} (a b : Fin N → ℝ) :
    (normalizedDot a b)^2 ≤ normalizedSquare a*normalizedSquare b := by
  have H := div_le_div_of_nonneg_right
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b) (sq_nonneg (N : ℝ))
  simpa only [normalizedDot,normalizedSquare,div_pow,div_mul_div_comm,← pow_two] using H

theorem abs_normalizedDot_le {N : ℕ} (a b : Fin N → ℝ) :
    |normalizedDot a b| ≤ Real.sqrt (normalizedSquare a)*Real.sqrt (normalizedSquare b) := by
  rw [← Real.sqrt_mul (normalizedSquare_nonneg a)]
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using normalizedDot_sq_le a b

theorem normalizedDot_sub_right {N : ℕ} (a b c : Fin N → ℝ) :
    normalizedDot a (fun i => b i-c i) = normalizedDot a b-normalizedDot a c := by
  simp only [normalizedDot,mul_sub,Finset.sum_sub_distrib,sub_div]

theorem normalizedDot_add_left {N : ℕ} (a b c : Fin N → ℝ) :
    normalizedDot (fun i => a i+b i) c = normalizedDot a c+normalizedDot b c := by
  simp only [normalizedDot,add_mul,Finset.sum_add_distrib,add_div]

theorem normalizedDot_comm {N : ℕ} (a b : Fin N → ℝ) : normalizedDot a b = normalizedDot b a := by
  simp only [normalizedDot,mul_comm]

theorem mean_cross_replacement {N : ℕ} (a b : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |normalizedDot a b-normalizedSquare a| ≤ Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
  rw [← normalizedDot_self,← normalizedDot_sub_right]
  calc
    _ ≤ Real.sqrt (normalizedSquare a)*Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
      abs_normalizedDot_le _ _
    _ ≤ 1*Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one a ha)
    _ = _ := one_mul _

theorem mean_square_replacement {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |normalizedSquare b-normalizedSquare a| ≤ 2*Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
  have he : normalizedSquare b-normalizedSquare a =
      normalizedDot b (fun i => b i-a i)+normalizedDot a (fun i => b i-a i) := by
    rw [normalizedDot_sub_right,normalizedDot_sub_right,normalizedDot_self,normalizedDot_self,
      normalizedDot_comm b a]
    ring
  rw [he]
  have H (c : Fin N → ℝ) (hc : ∀ i, |c i| ≤ 1) :
      |normalizedDot c (fun i => b i-a i)| ≤ Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
    calc
      _ ≤ Real.sqrt (normalizedSquare c)*Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
        abs_normalizedDot_le _ _
      _ ≤ 1*Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
        mul_le_mul_of_nonneg_right (by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one c hc))
          (Real.sqrt_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ |normalizedDot b (fun i => b i-a i)|+|normalizedDot a (fun i => b i-a i)| := abs_add_le _ _
    _ ≤ Real.sqrt (normalizedSquare (fun i => b i-a i))+Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
      add_le_add (H b hb) (H a ha)
    _ = _ := by ring

theorem mean_variance_replacement {N : ℕ} (a b : Fin N → ℝ) (r : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |(normalizedDot a b-r)*normalizedSquare b-
      (normalizedSquare a-r)*normalizedSquare a| ≤
      3*Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
  have hA := normalizedSquare_le_one a ha
  have hA₀ := normalizedSquare_nonneg a
  have hB := normalizedSquare_le_one b hb
  have hB₀ := normalizedSquare_nonneg b
  have hAr : |normalizedSquare a-r| ≤ 1 := abs_le.2 ⟨by linarith [hr.2],by linarith [hr.1]⟩
  have he : (normalizedDot a b-r)*normalizedSquare b-
      (normalizedSquare a-r)*normalizedSquare a =
      (normalizedDot a b-normalizedSquare a)*normalizedSquare b+
      (normalizedSquare a-r)*(normalizedSquare b-normalizedSquare a) := by ring
  rw [he]
  calc
    _ ≤ |(normalizedDot a b-normalizedSquare a)*normalizedSquare b|+
        |(normalizedSquare a-r)*(normalizedSquare b-normalizedSquare a)| := abs_add_le _ _
    _ = |normalizedDot a b-normalizedSquare a| *normalizedSquare b+
        |normalizedSquare a-r| *|normalizedSquare b-normalizedSquare a| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hB₀]
    _ ≤ Real.sqrt (normalizedSquare (fun i => b i-a i))*1+
        1*(2*Real.sqrt (normalizedSquare (fun i => b i-a i))) := by
      exact add_le_add
        (mul_le_mul (mean_cross_replacement a b ha) hB hB₀ (Real.sqrt_nonneg _))
        (mul_le_mul hAr (mean_square_replacement a b ha hb) (abs_nonneg _) (by norm_num))
    _ = _ := by ring
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanSquare
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyMeanSquare {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) : ℝ :=
  normalizedSquare (fun i => hierarchySpinMean n m U (c i) j z)

theorem hierarchyMeanSquare_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMeanSquare n m U c j z ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨normalizedSquare_nonneg _,normalizedSquare_le_one _ ?_⟩
  intro i
  exact (hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) j).2 z

theorem hierarchyMeanSquare_fixed {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
      (hierarchyMeanSquare n m U c j) j = hierarchyMeanSquare n m U c j := by
  exact hierarchyMomentLevel_family n m _ (fun i => affineMoment (fun _ => 0) U (c i))
    (affineLogPartition_boundedDerivs (fun _ => 0) U) normalizedSquare j

theorem hierarchyMeanSquare_eq_gradient {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1))
    (u : Fin N → ParameterSpace n) (hu : ∀ i, TailZero n j (u i)) (hU : ∀ i s, U s (u i) = c i s) :
    hierarchyMeanSquare n m U c j = fun z => (N : ℝ)⁻¹ *
      gradientSquareSum (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u z := by
  funext z
  simp only [hierarchyMeanSquare,normalizedSquare,gradientSquareSum,
    hierarchyLevel_spinMean n m U _ j _ (hu _) (hU _),← pow_two]
  ring

theorem hierarchyMeanSquare_regular {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1))
    (u : Fin N → ParameterSpace n) (hu : ∀ i, TailZero n j (u i)) (hU : ∀ i s, U s (u i) = c i s) :
    ContDiff ℝ 1 (hierarchyMeanSquare n m U c j) ∧
      HasExpGrowth (hierarchyMeanSquare n m U c j) ∧
      HasExpGrowth (fderiv ℝ (hierarchyMeanSquare n m U c j)) := by
  rw [hierarchyMeanSquare_eq_gradient n m U c j u hu hU]
  have H := gradientSquareSum_regular
    (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j)
    (hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j) u
  refine ⟨contDiff_const.mul H.1,(HasExpGrowth.const _).mul H.2.1,?_⟩
  have he : fderiv ℝ (fun z => (N : ℝ)⁻¹ *
      gradientSquareSum (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u z) =
      fun z => (N : ℝ)⁻¹ • fderiv ℝ
        (gradientSquareSum (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u) z := by
    funext z
    exact ((H.1.differentiable (by norm_num) z).hasFDerivAt.const_mul _).fderiv
  rw [he]
  exact (HasExpGrowth.const _).smul H.2.2

theorem hierarchyMeanSquare_invariant {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1))
    (u : Fin N → ParameterSpace n) (hu : ∀ i, TailZero n j (u i)) (hU : ∀ i s, U s (u i) = c i s)
    (v : ParameterSpace n) (hv : TranslationInvariant
      (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) v) :
    TranslationInvariant (hierarchyMeanSquare n m U c j) v := by
  rw [hierarchyMeanSquare_eq_gradient n m U c j u hu hU]
  intro z t
  dsimp only
  rw [(hv.gradientSquareSum u) z t]
end MeanSquare

section MeanSquareStein
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyMeanSquare_stein {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (hc : ∀ i s, ‖c i s‖ ≤ 1)
    (a : Fin N → Fin n → ℝ) (j l : Fin (n+1)) (hjl : j ≤ l)
    (u v : Fin N → ParameterSpace n) (ha : ∀ i, coordinateVector n (a i) = u i+v i)
    (hu : ∀ i, TailZero n j (u i)) (hv : ∀ i, PrefixZero n j (v i))
    (huc : ∀ i s, U s (u i) = c i s) (hU : ∀ i s, U s (coordinateVector n (a i)) = 0)
    (hi : ∀ i k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) (coordinateVector n (a i)))
    (ul : Fin N → ParameterSpace n) (hul : ∀ i, TailZero n l (ul i))
    (hulc : ∀ i s, U s (ul i) = c i s)
    (hil : ∀ i, TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) l)
      (coordinateVector n (a i))) (i : Fin N) :
    (∫ sz, coordinateLinear n (a i) sz.2*(c i sz.1*hierarchyMeanSquare n m U c l sz.2)
      ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 j * ∫ z,
        (hierarchySpinMean n m U (c i) j z*hierarchySpinMean n m U (c i) l z)*
          hierarchyMeanSquare n m U c l z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  have Hr := hierarchyMeanSquare_regular n m U c l ul hul hulc
  have hb (z : ParameterSpace n) : ‖hierarchyMeanSquare n m U c l z‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc l z).1]
    exact (hierarchyMeanSquare_bounds n m U c hc l z).2
  exact hierarchyGaussian_retained_stein n m U (c i) _ (C := 1) (D := 1)
    (by norm_num) (by norm_num) (hc i) hb Hr.1 Hr.2.2 (a i) j l hjl
    (u i) (v i) (ha i) (hu i) (hv i) (huc i) (hU i) (hi i)
    (hierarchyMeanSquare_invariant n m U c l ul hul hulc _ (hil i))
    (hierarchyMeanSquare_fixed n m U c l)
end MeanSquareStein
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanTower
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyMeanOverlap {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1)) : ℝ :=
  ∫ z, hierarchyMeanSquare n m U c j z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0

theorem hierarchyMeanSquare_continuous {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    Continuous (hierarchyMeanSquare n m U c j) := by
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact ((hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) j).1).pow 2

theorem hierarchyMeanSquare_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (x : ℝ) :
    Integrable (hierarchyMeanSquare n m U c j)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) x) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hierarchyMeanSquare_continuous n m U c hc j) (C := 1) _ x
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc j z).1]
  exact (hierarchyMeanSquare_bounds n m U c hc j z).2

theorem hierarchyMeanOverlap_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m U c j ∈ Set.Icc (0 : ℝ) 1 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  refine ⟨integral_nonneg (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (1 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono (hierarchyMeanSquare_integrable n m U c hc j 0) (integrable_const 1)
        (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).2)
    _ = 1 := by simp

theorem hierarchyMean_increment_identity {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j l : Fin (n+1)) (hjl : j ≤ l) :
    (∫ z, normalizedSquare (fun i => hierarchySpinMean n m U (c i) l z-
        hierarchySpinMean n m U (c i) j z)
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) =
      hierarchyMeanOverlap n m U c l-hierarchyMeanOverlap n m U c j := by
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  let μ := hierarchyPathLaw n m f 0
  have hr (i : Fin N) (k : Fin (n+1)) := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) k
  have hI (i : Fin N) (k : Fin (n+1)) : Integrable (fun z => (hierarchySpinMean n m U (c i) k z)^2) μ :=
    hierarchyPathLaw_integrable n m f _ hf ((hr i k).1.pow 2) (C := 1)
      (fun z => by dsimp only [Pi.pow_apply]; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ((hr i k).2 z)) 0
  have hInc (i : Fin N) : Integrable (fun z => (hierarchySpinMean n m U (c i) l z-
      hierarchySpinMean n m U (c i) j z)^2) μ := by
    apply hierarchyPathLaw_integrable n m f _ hf (((hr i l).1.sub (hr i j).1).pow 2) (C := 4) _ 0
    intro z
    have h := (norm_sub_le (hierarchySpinMean n m U (c i) l z) (hierarchySpinMean n m U (c i) j z)).trans
      (add_le_add ((hr i l).2 z) ((hr i j).2 z))
    dsimp only [Pi.pow_apply,Pi.sub_apply]
    rw [norm_pow]
    nlinarith [norm_nonneg (hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z)]
  have horth (i : Fin N) := hierarchyPathLaw_moment_orthogonality n m f (affineMoment (fun _ => 0) U (c i))
    hf (affineMoment_continuous (fun _ => 0) U (c i)) (by norm_num : (0 : ℝ) ≤ 1)
    (affineMoment_norm_le (fun _ => 0) U (c i) (hc i)) j l hjl 0
  change (∫ z, (∑ i, (hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z)^2)/(N : ℝ) ∂μ) =
    (∫ z, (∑ i, (hierarchySpinMean n m U (c i) l z)^2)/(N : ℝ) ∂μ)-
      (∫ z, (∑ i, (hierarchySpinMean n m U (c i) j z)^2)/(N : ℝ) ∂μ)
  rw [integral_div,integral_div,integral_div,
    integral_finsetSum _ (fun i _ => hInc i),
    integral_finsetSum _ (fun i _ => hI i l),integral_finsetSum _ (fun i _ => hI i j)]
  have he : (∑ i, ∫ z, (hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z)^2 ∂μ) =
      ∑ i, ((∫ z, (hierarchySpinMean n m U (c i) l z)^2 ∂μ)-
      (∫ z, (hierarchySpinMean n m U (c i) j z)^2 ∂μ)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact horth i
  rw [he,Finset.sum_sub_distrib,sub_div]

theorem hierarchyMeanOverlap_mono {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) : Monotone (hierarchyMeanOverlap n m U c) := by
  intro j l hjl
  have H := integral_nonneg (μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)
    (f := fun z => normalizedSquare (fun i => hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z))
    (fun z => normalizedSquare_nonneg _)
  rw [hierarchyMean_increment_identity n m U c hc j l hjl] at H
  exact sub_nonneg.mp H
end MeanTower
end SK.Analytic
namespace SK.Analytic

def massFromAtoms (n : ℕ) (w : Fin (n+1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n+1), if j.val ≤ i.val then w j else 0

theorem massFromAtoms_castSucc (n : ℕ) (w : Fin (n+2) → ℝ) (i : Fin n) :
    massFromAtoms (n+1) w i.castSucc = massFromAtoms n (fun j => w j.castSucc) i := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  have h : ¬ n+1 ≤ i.val := by omega
  rw [ite_eq_right h,add_zero]

theorem massFromAtoms_last (n : ℕ) (w : Fin (n+2) → ℝ) :
    massFromAtoms (n+1) w (Fin.last n) = ∑ j : Fin (n+1), w j.castSucc := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,show ¬ n+1 ≤ n by omega,ite_false,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (by omega)]

theorem hierarchyAtom_massFromAtoms (n : ℕ) (w : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    hierarchyAtom n (massFromAtoms n w) (∑ k, w k) j = w j := by
  induction n with
  | zero => simp [hierarchyAtom,Fin.eq_zero j]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyAtom,Fin.lastCases_last,massFromAtoms_last]
      rw [Fin.sum_univ_castSucc]
      ring
    · simp only [hierarchyAtom,Fin.lastCases_castSucc,massFromAtoms_castSucc,massFromAtoms_last]
      exact ih (fun j => w j.castSucc) j

theorem massFromAtoms_nonneg (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) :
    0 ≤ massFromAtoms n w i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hw j
  · exact le_rfl

theorem massFromAtoms_le_sum (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) :
    massFromAtoms n w i ≤ ∑ j, w j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact hw j

theorem massFromAtoms_monotone (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Monotone (massFromAtoms n w) := by
  intro i k hik
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j.val ≤ i.val
  · rw [ite_eq_left hj,ite_eq_left (hj.trans hik)]
  · rw [ite_eq_right hj]
    split_ifs
    · exact hw j
    · exact le_rfl
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

abbrev blockDimension (D N k : ℕ) : ℕ := D+(k+1)*N

def fieldIndex (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) : Fin (blockDimension D N k) :=
  ⟨D+b.val*N+i.val, by
    have hb : (b.val+1)*N ≤ (k+1)*N := Nat.mul_le_mul_right N b.isLt
    dsimp only [blockDimension]
    nlinarith [i.isLt]⟩

def blockLevel (D N k : ℕ) (b : Fin (k+1)) : Fin (blockDimension D N k+1) :=
  ⟨D+(b.val+1)*N, by
    have hb : (b.val+1)*N ≤ (k+1)*N := Nat.mul_le_mul_right N b.isLt
    dsimp only [blockDimension]
    omega⟩

@[simp] theorem fieldIndex_val (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    (fieldIndex D N k b i).val = D+b.val*N+i.val := rfl
@[simp] theorem blockLevel_val (D N k : ℕ) (b : Fin (k+1)) :
    (blockLevel D N k b).val = D+(b.val+1)*N := rfl

theorem fieldIndex_injective (D N k : ℕ) :
    Function.Injective (fun bi : Fin (k+1) × Fin N => fieldIndex D N k bi.1 bi.2) := by
  intro a b hab
  have h : a.1.val*N+a.2.val = b.1.val*N+b.2.val := by
    have h := congrArg Fin.val hab
    simp only [fieldIndex_val] at h
    omega
  have hq : a.1.val = b.1.val := by
    have hN : 0 < N := Nat.zero_lt_of_lt a.2.isLt
    have he := congrArg (fun x => x/N) h
    simpa only [Nat.mul_comm _ N,Nat.mul_add_div hN,
      Nat.div_eq_of_lt a.2.isLt,Nat.div_eq_of_lt b.2.isLt,add_zero] using he
  apply Prod.ext
  · exact Fin.ext hq
  · apply Fin.ext
    rw [hq] at h
    omega

theorem blockLevel_injective (D N k : ℕ) (hN : 0 < N) :
    Function.Injective (blockLevel D N k) := by
  intro a b hab
  apply Fin.ext
  have h := congrArg Fin.val hab
  simp only [blockLevel_val] at h
  exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_right hN (Nat.add_left_cancel h))

theorem fieldIndex_lt_level (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    (fieldIndex D N k b i).val < (blockLevel D N k b).val := by
  simp only [fieldIndex_val,blockLevel_val]
  nlinarith [i.isLt]

theorem fieldIndex_mono_block (D N k : ℕ) (a b : Fin (k+1)) (hab : a ≤ b) (i : Fin N) :
    fieldIndex D N k a i ≤ fieldIndex D N k b i := by
  change D+a.val*N+i.val ≤ D+b.val*N+i.val
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right N hab) D) i.val

theorem blockLevel_mono (D N k : ℕ) : Monotone (blockLevel D N k) := by
  intro a b hab
  change D+(a.val+1)*N ≤ D+(b.val+1)*N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right N (Nat.add_le_add_right hab 1)) D

def blockAtom (D N k : ℕ) (t : Fin (blockDimension D N k+1)) : ℝ :=
  ∑ b : Fin (k+1), if blockLevel D N k b = t then ((k+1 : ℕ) : ℝ)⁻¹ else 0

theorem blockAtom_nonneg (D N k : ℕ) (t : Fin (blockDimension D N k+1)) :
    0 ≤ blockAtom D N k t := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> positivity

theorem blockAtom_sum (D N k : ℕ) : ∑ t, blockAtom D N k t = 1 := by
  unfold blockAtom
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem blockAtom_at (D N k : ℕ) (hN : 0 < N) (b : Fin (k+1)) :
    blockAtom D N k (blockLevel D N k b) = ((k+1 : ℕ) : ℝ)⁻¹ := by
  unfold blockAtom
  have he (a : Fin (k+1)) : blockLevel D N k a = blockLevel D N k b ↔ a=b :=
    (blockLevel_injective D N k hN).eq_iff
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem blockAtom_zero_off (D N k : ℕ) (t : Fin (blockDimension D N k+1))
    (ht : ∀ b, blockLevel D N k b ≠ t) : blockAtom D N k t = 0 := by
  simp only [blockAtom,ht,ite_false,Finset.sum_const_zero]

def blockMass (D N k : ℕ) := massFromAtoms (blockDimension D N k) (blockAtom D N k)

theorem blockMass_valid (D N k : ℕ) :
    (∀ i, 0 ≤ blockMass D N k i) ∧ (∀ i, blockMass D N k i ≤ 1) ∧ Monotone (blockMass D N k) := by
  refine ⟨massFromAtoms_nonneg _ _ (blockAtom_nonneg D N k),?_,
    massFromAtoms_monotone _ _ (blockAtom_nonneg D N k)⟩
  intro i
  exact (massFromAtoms_le_sum _ _ (blockAtom_nonneg D N k) i).trans_eq (blockAtom_sum D N k)

theorem hierarchyAtom_blockMass (D N k : ℕ) (t : Fin (blockDimension D N k+1)) :
    hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 t = blockAtom D N k t := by
  rw [← blockAtom_sum D N k]
  exact hierarchyAtom_massFromAtoms _ _ t

theorem blockLevel_outside_pair (D N k : ℕ) (j : Fin k) (i : Fin N) (b : Fin (k+1))
    (hb : b ≠ j.castSucc) :
    (blockLevel D N k b).val ≤ (fieldIndex D N k j.castSucc i).val ∨
      (fieldIndex D N k j.succ i).val < (blockLevel D N k b).val := by
  have hjb : b.val ≠ j.val := by intro h; apply hb; exact Fin.ext h
  simp only [blockLevel_val,fieldIndex_val,Fin.val_castSucc,Fin.val_succ]
  rcases lt_or_gt_of_ne hjb with h | h
  · left
    have hh : (b.val+1)*N ≤ j.val*N := Nat.mul_le_mul_right N h
    omega
  · right
    have hh : (j.val+1)*N ≤ b.val*N := Nat.mul_le_mul_right N h
    nlinarith [i.isLt]

theorem blockLevel_prefix_second (D N k : ℕ) (j : Fin k) (i : Fin N) :
    (blockLevel D N k j.castSucc).val ≤ (fieldIndex D N k j.succ i).val := by
  simp only [blockLevel_val,fieldIndex_val,Fin.val_castSucc,Fin.val_succ]
  omega
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def pairCoefficients (n : ℕ) (p q : Fin n) (a b : ℝ) : Fin n → ℝ :=
  fun t => (if t=p then a else 0)+(if t=q then b else 0)

theorem coordinateVector_pair (n : ℕ) (p q : Fin n) (a b : ℝ) :
    coordinateVector n (pairCoefficients n p q a b) = a • coordinateAxis n p+b • coordinateAxis n q := by
  simp only [coordinateVector,pairCoefficients,add_smul,Finset.sum_add_distrib,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem coordinateLinear_pair (n : ℕ) (p q : Fin n) (a b : ℝ) (z : ParameterSpace n) :
    coordinateLinear n (pairCoefficients n p q a b) z =
      a*coordinateProjection n p z+b*coordinateProjection n q z := by
  simp only [coordinateLinear_apply,pairCoefficients,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

def sharedFieldCoefficients (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k) (i : Fin N) :=
  pairCoefficients (blockDimension D N k) (fieldIndex D N k j.castSucc i) (fieldIndex D N k j.succ i)
    (Real.sqrt (Δ j.castSucc))⁻¹ (-(Real.sqrt (Δ j.succ))⁻¹)

def retainedFieldDirection (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (b : Fin (k+1)) (i : Fin N) :=
  (Real.sqrt (Δ b))⁻¹ • coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)

section BlockSpin
variable {N D k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem retainedFieldDirection_spin (b : Fin (k+1)) (i : Fin N) (s : Config N) :
    U s (retainedFieldDirection D N k Δ b i) = spin (s i) := by
  simp only [retainedFieldDirection,map_smul,smul_eq_mul,hU]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (hΔ b)),one_mul]

theorem sharedField_termination (j : Fin k) (i : Fin N) (s : Config N) :
    U s (coordinateVector (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i)) = 0 := by
  rw [sharedFieldCoefficients,coordinateVector_pair,map_add]
  rw [neg_smul,map_neg]
  change U s (retainedFieldDirection D N k Δ j.castSucc i) -
    U s (retainedFieldDirection D N k Δ j.succ i) = 0
  rw [retainedFieldDirection_spin U Δ hΔ hU,retainedFieldDirection_spin U Δ hΔ hU,sub_self]

theorem sharedField_level_invariant (j : Fin k) (i : Fin N) (b : Fin (k+1)) (hb : b ≠ j.castSucc) :
    TranslationInvariant (hierarchyLevel (blockDimension D N k) (blockMass D N k)
      (affineLogPartition (fun _ => 0) U) (blockLevel D N k b))
      (coordinateVector (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i)) := by
  have ht := affineLogPartition_translation (fun _ => 0) U _ (sharedField_termination U Δ hΔ hU j i)
  rw [sharedFieldCoefficients,coordinateVector_pair] at ht ⊢
  exact hierarchyLevel_pair_invariance _ _ _ _ _ _ _
    (fieldIndex_mono_block D N k _ _ (by exact Nat.le_succ _) i) ht _
    (blockLevel_outside_pair D N k j i b hb)

theorem sharedField_atom_cancellation (j : Fin k) (i : Fin N)
    (t : Fin (blockDimension D N k+1)) (ht : t ≠ blockLevel D N k j.castSucc) :
    hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 t = 0 ∨
      TranslationInvariant (hierarchyLevel (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) U) t)
        (coordinateVector (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i)) := by
  by_cases hb : ∃ b, blockLevel D N k b = t
  · obtain ⟨b,rfl⟩ := hb
    right
    apply sharedField_level_invariant U Δ hΔ hU j i b
    intro h
    exact ht (congrArg (blockLevel D N k) h)
  · left
    rw [hierarchyAtom_blockMass]
    exact blockAtom_zero_off D N k t (not_exists.mp hb)

theorem blockMeanSquare_stein (j : Fin k) (i : Fin N) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    (∫ sz, coordinateLinear n (sharedFieldCoefficients D N k Δ j i) sz.2*
      (c i sz.1*hierarchyMeanSquare n m U c L sz.2) ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 J * ∫ z,
        (hierarchySpinMean n m U (c i) J z*hierarchySpinMean n m U (c i) L z)*
          hierarchyMeanSquare n m U c L z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let n := blockDimension D N k
  let u := retainedFieldDirection D N k Δ j.castSucc
  let v := fun i => -retainedFieldDirection D N k Δ j.succ i
  have hJL : blockLevel D N k j.castSucc ≤ blockLevel D N k j.succ :=
    blockLevel_mono D N k (show j.castSucc ≤ j.succ from Nat.le_succ _)
  have hu (i : Fin N) : TailZero n (blockLevel D N k j.castSucc) (u i) :=
    (tailZero_coordinateAxis n _ _ (fieldIndex_lt_level D N k j.castSucc i)).smul _
  have hv (i : Fin N) : PrefixZero n (blockLevel D N k j.castSucc) (v i) := by
    simpa only [v,retainedFieldDirection,neg_smul] using
      (prefixZero_coordinateAxis n _ _ (blockLevel_prefix_second D N k j i)).smul (-(Real.sqrt (Δ j.succ))⁻¹)
  have hul (i : Fin N) : TailZero n (blockLevel D N k j.succ) (u i) :=
    (tailZero_coordinateAxis n _ _ ((fieldIndex_lt_level D N k j.castSucc i).trans_le hJL)).smul _
  apply hierarchyMeanSquare_stein n (blockMass D N k) U (fun i s => spin (s i))
    (by intro i s; cases s i <;> norm_num [spin])
    (sharedFieldCoefficients D N k Δ j) _ _ hJL u v
    (by intro i; dsimp only [n]; simp only [sharedFieldCoefficients,coordinateVector_pair,u,v,retainedFieldDirection,neg_smul])
    hu hv (retainedFieldDirection_spin U Δ hΔ hU j.castSucc)
    (sharedField_termination U Δ hΔ hU j)
    (sharedField_atom_cancellation U Δ hΔ hU j)
    u hul (retainedFieldDirection_spin U Δ hΔ hU j.castSucc) _ i
  intro i
  apply sharedField_level_invariant U Δ hΔ hU j i j.succ
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_succ,Fin.val_castSucc] at hh
  omega
end BlockSpin
end SK.Analytic

end
end

end

end OAI
