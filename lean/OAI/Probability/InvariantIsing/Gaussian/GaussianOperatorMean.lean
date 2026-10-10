import OAI.Probability.InvariantIsing.Core.UnitBilinearNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Sharp finite-dimensional upper mean bound for a rectangular Gaussian matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology
namespace InvariantIsing

theorem gaussianPatternSingularMax_mean_le_pos {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∫ z, gaussianPatternSingularMax (N := N) (m := m) z ∂stdGaussian _) ≤
      Real.sqrt N + Real.sqrt m := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : Nonempty (UnitVector (EuclideanSpace ℝ (Fin N))) := unitVector_nonempty _
  let : Nonempty (UnitVector (EuclideanSpace ℝ (Fin m))) := unitVector_nonempty _
  let S := UnitVector (EuclideanSpace ℝ (Fin N)) × UnitVector (EuclideanSpace ℝ (Fin m))
  let s : ℕ → S := TopologicalSpace.denseSeq S
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  let A (n : ℕ) (g : (Fin N × Fin m) → ℝ) : ℝ :=
    indexedGaussianMaximum (fun i : Fin (n+1) => fun ij =>
      (s i).1.1 ij.1*(s i).2.1 ij.2) g
  let Z (g : (Fin N × Fin m) → ℝ) : EuclideanSpace ℝ (Fin N × Fin m) := WithLp.toLp 2 g
  let μ := Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1)
  have hZ : HasLaw Z (stdGaussian _) μ :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).measurable.aemeasurable,
      map_pi_eq_stdGaussian⟩
  have hA (n : ℕ) (g : (Fin N × Fin m) → ℝ) :
      A n g = prefixMaximum
        (fun i => ⟪(s i).1.1,gaussianPatternEuclideanOperator (Z g) (s i).2.1⟫) n := by
    unfold A indexedGaussianMaximum prefixMaximum
    congr 1
    funext i
    exact (gaussianPattern_unitBilinear (Z g) (s i).1.1 (s i).2.1).symm
  have hlim (g : (Fin N × Fin m) → ℝ) :
      Tendsto (fun n => A n g) atTop (𝓝 (gaussianPatternSingularMax (Z g))) := by
    simp_rw [hA]
    have hc : Continuous (fun p : S =>
        ⟪p.1.1,gaussianPatternEuclideanOperator (Z g) p.2.1⟫) := by
      dsimp [S]
      fun_prop
    have hb : BddAbove (range (fun p : S =>
        ⟪p.1.1,gaussianPatternEuclideanOperator (Z g) p.2.1⟫)) :=
      ⟨‖gaussianPatternEuclideanOperator (Z g)‖,by
        rintro _ ⟨p,rfl⟩
        exact unitBilinear_le_norm _ p⟩
    have ht := dense_prefixMaximum_tendsto s hs _ hc hb
    have hn := norm_eq_iSup_unitBilinear (gaussianPatternEuclideanOperator (Z g))
    change ‖gaussianPatternEuclideanOperator (Z g)‖ =
      (⨆ p : S, ⟪p.1.1,gaussianPatternEuclideanOperator (Z g) p.2.1⟫) at hn
    rw [← hn] at ht
    exact ht
  have hbound (n : ℕ) (g : (Fin N × Fin m) → ℝ) : |A n g| ≤ ‖Z g‖ := by
    obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin (n+1) => ∑ ij, (s i).1.1 ij.1*(s i).2.1 ij.2*g ij)
    change |Finset.univ.sup' Finset.univ_nonempty _| ≤ _
    rw [he,← gaussianPattern_unitBilinear (Z g) (s i).1.1 (s i).2.1]
    calc
      _ ≤ ‖(s i).1.1‖*‖gaussianPatternEuclideanOperator (Z g) (s i).2.1‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖gaussianPatternEuclideanOperator (Z g) (s i).2.1‖ := by rw [(s i).1.2,one_mul]
      _ ≤ ‖gaussianPatternEuclideanOperator (Z g)‖*‖(s i).2.1‖ :=
        (gaussianPatternEuclideanOperator (Z g)).le_opNorm _
      _ ≤ ‖Z g‖ := by rw [(s i).2.2,mul_one]; exact gaussianPatternEuclideanOperator_norm_le _
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun g => ‖Z g‖)
    (fun n => (measurable_indexedGaussianMaximum _).aestronglyMeasurable)
    (((gaussianCoordinateVector_memLp (id : (Fin N × Fin m) → (Fin N × Fin m))).integrable
      (by norm_num)).norm)
    (fun n => ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hbound n g))
    (ae_of_all _ hlim)
  have hb (n : ℕ) : (∫ g, A n g ∂μ) ≤ Real.sqrt N + Real.sqrt m :=
    bilinear_gaussian_mean_le (fun i : Fin (n+1) => (s i).1.1)
      (fun i : Fin (n+1) => (s i).2.1) (fun i => (s i).1.2) (fun i => (s i).2.2)
  have he : (∫ g, gaussianPatternSingularMax (Z g) ∂μ) =
      ∫ z : EuclideanSpace ℝ (Fin N × Fin m), gaussianPatternSingularMax z ∂stdGaussian _ := by
    simpa only [Function.comp_def] using hZ.integral_comp
      (gaussianPatternSingularMax_lipschitz N m).continuous.aestronglyMeasurable
  rw [← he]
  exact le_of_tendsto ht (Filter.Eventually.of_forall hb)

end InvariantIsing

end

end OAI
