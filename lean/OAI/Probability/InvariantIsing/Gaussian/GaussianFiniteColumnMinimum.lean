import OAI.Probability.InvariantIsing.Gaussian.BilinearGaussianMinmaxMean
import OAI.Probability.InvariantIsing.Core.UnitInnerMaximum

namespace OAI

/-! Passing the row tests to the full unit sphere in Gordon's matrix comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology
namespace InvariantIsing

lemma continuous_gaussianPattern_apply {N m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => gaussianPatternEuclideanOperator z v) := by
  change Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
    WithLp.toLp 2 (fun i => ∑ j, z (i,j)*v j))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
    (continuous_pi (fun i => by fun_prop))

theorem gaussian_finite_column_minimum {V : Type*} [Fintype V] [Nonempty V]
    {N m : ℕ} (hN : 0 < N) (v : V → EuclideanSpace ℝ (Fin m)) (hv : ∀ b, ‖v b‖ = 1) :
    (∫ z : EuclideanSpace ℝ (Fin N), ‖z‖ ∂stdGaussian _)-Real.sqrt m ≤
    ∫ z : EuclideanSpace ℝ (Fin N × Fin m),
      Finset.univ.inf' Finset.univ_nonempty (fun b => ‖gaussianPatternEuclideanOperator z (v b)‖)
      ∂stdGaussian _ := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : Nonempty (UnitVector (EuclideanSpace ℝ (Fin N))) := unitVector_nonempty _
  let S := UnitVector (EuclideanSpace ℝ (Fin N))
  let s : ℕ → S := TopologicalSpace.denseSeq S
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  let μ := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1)
  let Z (g : (Fin N × Fin m) → ℝ) : EuclideanSpace ℝ (Fin N × Fin m) := WithLp.toLp 2 g
  let W (g : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 g
  let A (n : ℕ) (g : Fin N → ℝ) : ℝ :=
    indexedGaussianMaximum (fun i : Fin (n+1) => fun j => (s i).1 j) g
  let C (n : ℕ) (g : (Fin N × Fin m) → ℝ) : ℝ :=
    finiteMinmax (fun x : Fin (n+1) × V => ∑ ij, ((s x.1).1 ij.1*v x.2 ij.2)*g ij)
  let M (z : EuclideanSpace ℝ (Fin N × Fin m)) :=
    Finset.univ.inf' Finset.univ_nonempty (fun b => ‖gaussianPatternEuclideanOperator z (v b)‖)
  have hAlim (g : Fin N → ℝ) : Tendsto (fun n => A n g) atTop (𝓝 ‖W g‖) := by
    have he (n : ℕ) : A n g = prefixMaximum (fun i => ⟪(s i).1,W g⟫) n := by
      unfold A indexedGaussianMaximum prefixMaximum
      congr 1
      funext i
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,W,
        mul_comm]
    simp_rw [he]
    exact unitInner_prefix_tendsto s hs (W g)
  have hClim (g : (Fin N × Fin m) → ℝ) : Tendsto (fun n => C n g) atTop (𝓝 (M (Z g))) := by
    have he (n : ℕ) : C n g = Finset.univ.inf' Finset.univ_nonempty
        (fun b => prefixMaximum (fun i => ⟪(s i).1,gaussianPatternEuclideanOperator (Z g) (v b)⟫) n) := by
      unfold C finiteMinmax finiteRowMax prefixMaximum
      congr 1
      funext b
      congr 1
      funext i
      exact (gaussianPattern_unitBilinear (Z g) (s i).1 (v b)).symm
    simp_rw [he]
    exact Tendsto.finset_inf'_nhds_apply Finset.univ_nonempty
      (fun b _ => unitInner_prefix_tendsto s hs (gaussianPatternEuclideanOperator (Z g) (v b)))
  have hAbound (n : ℕ) (g : Fin N → ℝ) : |A n g| ≤ ‖W g‖ := by
    obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin (n+1) => ∑ j, (s i).1 j*g j)
    change |Finset.univ.sup' Finset.univ_nonempty _| ≤ _
    rw [he]
    have h := abs_real_inner_le_norm (s i).1 (W g)
    rw [(s i).2,one_mul] at h
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,W,
      PiLp.toLp_apply,mul_comm] using h
  have hCbound (n : ℕ) (g : (Fin N × Fin m) → ℝ) : |C n g| ≤ ‖Z g‖ := by
    apply finiteMinmax_abs_le
    intro x
    rw [← gaussianPattern_unitBilinear (Z g) (s x.1).1 (v x.2)]
    calc
      _ ≤ ‖(s x.1).1‖*‖gaussianPatternEuclideanOperator (Z g) (v x.2)‖ := abs_real_inner_le_norm _ _
      _ = ‖gaussianPatternEuclideanOperator (Z g) (v x.2)‖ := by rw [(s x.1).2,one_mul]
      _ ≤ ‖gaussianPatternEuclideanOperator (Z g)‖*‖v x.2‖ :=
        (gaussianPatternEuclideanOperator (Z g)).le_opNorm _
      _ ≤ ‖Z g‖ := by rw [hv,mul_one]; exact gaussianPatternEuclideanOperator_norm_le _
  have hAint := tendsto_integral_of_dominated_convergence (μ := μ) (fun g => ‖W g‖)
    (fun n => (measurable_indexedGaussianMaximum _).aestronglyMeasurable)
    (((gaussianCoordinateVector_memLp (id : Fin N → Fin N)).integrable (by norm_num)).norm)
    (fun n => ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hAbound n g))
    (ae_of_all _ hAlim)
  have hCint := tendsto_integral_of_dominated_convergence (μ := ν) (fun g => ‖Z g‖)
    (fun n => (indexedGaussianMinmax_integrable _).aestronglyMeasurable)
    (((gaussianCoordinateVector_memLp (id : (Fin N × Fin m) → (Fin N × Fin m))).integrable
      (by norm_num)).norm)
    (fun n => ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hCbound n g))
    (ae_of_all _ hClim)
  have hbound (n : ℕ) : (∫ g, A n g ∂μ)-Real.sqrt m ≤ ∫ g, C n g ∂ν :=
    bilinear_gaussian_minmax_mean (fun i : Fin (n+1) => (s i).1) v (fun i => (s i).2) hv
  have hh := le_of_tendsto_of_tendsto (hAint.sub_const (Real.sqrt m)) hCint
    (Filter.Eventually.of_forall hbound)
  have hW : HasLaw W (stdGaussian _) μ :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have hZ : HasLaw Z (stdGaussian _) ν :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).measurable.aemeasurable,
      map_pi_eq_stdGaussian⟩
  have heW : (∫ g, ‖W g‖ ∂μ) = ∫ z : EuclideanSpace ℝ (Fin N), ‖z‖ ∂stdGaussian _ := by
    simpa only [Function.comp_def] using hW.integral_comp (f := norm) (by fun_prop)
  have heZ : (∫ g, M (Z g) ∂ν) = ∫ z, M z ∂stdGaussian _ := by
    have hM : Continuous M := Continuous.finset_inf'_apply Finset.univ_nonempty
      (fun b _ => (continuous_gaussianPattern_apply (v b)).norm)
    simpa only [Function.comp_def] using hZ.integral_comp hM.aestronglyMeasurable
  rw [heW,heZ] at hh
  exact hh

end InvariantIsing

end

end OAI
