import OAI.Analysis.Steinitz.Prekopa

namespace OAI

/-! Convexity and norm inequalities for Gaussian kernels. -/

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

lemma le_of_shifted_pow_le_const_mul_pow {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, a^(n+2) ≤ K*b^n) : a ≤ b := by
  by_cases hz : a = 0
  · simpa [hz] using hb
  have hp : 0 < a^2 := sq_pos_of_ne_zero hz
  apply le_of_pow_le_const_mul_pow ha hb (C := K/a^2)
  intro n
  rw [div_mul_eq_mul_div, le_div_iff₀ hp, ← pow_add]
  exact h n

section
variable {X : Type*} [MeasurableSpace X]
variable (k : BoundedKernel X) (hs : ∀ x y, k.value (x,y) = k.value (y,x))
variable (μ ν ω : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ω]

include hs in
lemma kernel_norm_logconcave_of_pathMass {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (h : ∀ n, pathMass (μ := μ) k n^(1-t) * pathMass (μ := ν) k n^t ≤ pathMass (μ := ω) k n) :
    ‖kernelOp (μ := μ) k‖^(1-t) * ‖kernelOp (μ := ν) k‖^t ≤ ‖kernelOp (μ := ω) k‖ := by
  let A := k.bound^2 * ‖(oneLp : Lp ℂ 2 μ)‖^2
  let B := k.bound^2 * ‖(oneLp : Lp ℂ 2 ν)‖^2
  let C := ‖(oneLp : Lp ℂ 2 ω)‖^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply le_of_shifted_pow_le_const_mul_pow (by positivity) (norm_nonneg _)
    (K := A^(1-t)*B^t*C)
  intro n
  rw [mul_pow, Real.rpow_pow_comm (norm_nonneg _), Real.rpow_pow_comm (norm_nonneg _)]
  calc
    _ ≤ (A*pathMass (μ := μ) k n)^(1-t) * (B*pathMass (μ := ν) k n)^t := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity) (kernel_norm_pow_le_pathMass k hs n) (sub_nonneg.mpr ht.2)
      · exact Real.rpow_le_rpow (by positivity) (kernel_norm_pow_le_pathMass k hs n) ht.1
      · exact Real.rpow_nonneg (by positivity) _
      · exact Real.rpow_nonneg (mul_nonneg hA (pathMass_nonneg k n)) _
    _ = (A^(1-t)*B^t) * (pathMass (μ := μ) k n^(1-t)*pathMass (μ := ν) k n^t) := by
      rw [Real.mul_rpow hA (pathMass_nonneg k n), Real.mul_rpow hB (pathMass_nonneg k n)]
      ring
    _ ≤ (A^(1-t)*B^t)*pathMass (μ := ω) k n :=
      mul_le_mul_of_nonneg_left (h n) (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
    _ ≤ (A^(1-t)*B^t)*(C*‖kernelOp (μ := ω) k‖^n) :=
      mul_le_mul_of_nonneg_left (pathMass_le k n) (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
    _ = _ := by ring
end

section Haar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddHaarMeasure]
variable (k : BoundedKernel E) (hk : Continuous k.value) (hp : ∀ z, 0 < k.value z)
variable {A B C : Set E} [IsFiniteMeasure (volume.restrict A)]
  [IsFiniteMeasure (volume.restrict B)] [IsFiniteMeasure (volume.restrict C)]

include hk hp in
lemma pathMass_logconcave_haar
    (ha : Bornology.IsBounded A) (hb : Bornology.IsBounded B) (hc : Bornology.IsBounded C)
    (hca : Convex ℝ A) (hcb : Convex ℝ B) (hcc : Convex ℝ C)
    (hneA : A.Nonempty) (hneB : B.Nonempty) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hl : ∀ x y : E × E, k.value x^(1-t)*k.value y^t ≤ k.value ((1-t)•x+t•y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-t)•a+t•b ∈ C) (n : ℕ) :
    pathMass (μ := volume.restrict A) k n^(1-t) * pathMass (μ := volume.restrict B) k n^t ≤
      pathMass (μ := volume.restrict C) k n := by
  let PA := Set.pi univ (fun _ : Fin (n+1) => A)
  let PB := Set.pi univ (fun _ : Fin (n+1) => B)
  let PC := Set.pi univ (fun _ : Fin (n+1) => C)
  have hnePA : PA.Nonempty := by
    obtain ⟨a,ha'⟩ := hneA
    exact ⟨fun _ => a, fun _ _ => ha'⟩
  have hnePB : PB.Nonempty := by
    obtain ⟨b,hb'⟩ := hneB
    exact ⟨fun _ => b, fun _ _ => hb'⟩
  have hM : 0 < k.bound^n := by
    have : 0 < k.bound := (hp (0,0)).trans_le (k.le_bound _)
    positivity
  have hwpos (p : Fin (n+1) → E) : 0 < chainWeight k n p := tailWeight_pos k hp n _ _
  have hh := Prekopa.bounded_weight_convex_haar (volume : Measure (Fin (n+1) → E))
    (chainWeight_continuous k hk n) hwpos hM (fun p => tailWeight_le k n (p 0) (fun i => p i.succ))
    (Bornology.IsBounded.pi (fun _ => ha)) (Bornology.IsBounded.pi (fun _ => hb))
    (Bornology.IsBounded.pi (fun _ => hc))
    (convex_pi (fun _ _ => hca)) (convex_pi (fun _ _ => hcb)) (convex_pi (fun _ _ => hcc))
    hnePA hnePB ht (chainWeight_logconcave k hl n) (by
      intro a ha' b hb' i hi
      exact hABC (a i) (ha' i hi) (b i) (hb' i hi))
  simpa only [pathMass_pi, volume_pi, Measure.restrict_pi_pi] using hh

end Haar
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma kernel_value_continuous (v : ι → ℝ≥0) : Continuous (kernel v).value := by
  exact (density_continuous v).comp (continuous_snd.sub continuous_fst)

lemma kernel_value_pos (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : 0 < (kernel v).value z :=
  density_pos v hv _

lemma kernel_value_logconcave (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (kernel v).value x^(1-t)*(kernel v).value y^t ≤ (kernel v).value ((1-t)•x+t•y) := by
  change density v (x.2-x.1)^(1-t)*density v (y.2-y.1)^t ≤
    density v (((1-t)•x+t•y).2-((1-t)•x+t•y).1)
  have he : ((1-t)•x+t•y).2-((1-t)•x+t•y).1 =
      (1-t)•(x.2-x.1)+t•(y.2-y.1) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    module
  rw [he]
  exact density_logconcave v hv ht (x.2-x.1) (y.2-y.1)

lemma compressed_norm_logconcave (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {A B C : Set (EuclideanSpace ℝ ι)} (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C)
    (ha : Bornology.IsBounded A) (hb : Bornology.IsBounded B) (hc : Bornology.IsBounded C)
    (hca : Convex ℝ A) (hcb : Convex ℝ B) (hcc : Convex ℝ C)
    (hneA : A.Nonempty) (hneB : B.Nonempty) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-t)•a+t•b ∈ C) :
    ‖HeatL2.compressedHeat A hAo.measurableSet (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖^(1-t) *
    ‖HeatL2.compressedHeat B hBo.measurableSet (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖^t ≤
    ‖HeatL2.compressedHeat C hCo.measurableSet (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖ := by
  classical
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr ha.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  rw [← kernel_norm_eq v hv A hAo.measurableSet, ← kernel_norm_eq v hv B hBo.measurableSet,
    ← kernel_norm_eq v hv C hCo.measurableSet]
  apply HeatL2.kernel_norm_logconcave_of_pathMass (kernel v) (kernel_symmetric v) _ _ _ ht
  intro n
  exact HeatL2.pathMass_logconcave_haar (kernel v) (kernel_value_continuous v) (kernel_value_pos v hv)
    ha hb hc hca hcb hcc hneA hneB ht (kernel_value_logconcave v hv ht) hABC n

end GaussianKernel

end

end OAI
