import Mathlib
import OAI.Probability.SKRatio.Matrices.FiniteMax

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian
section ArbitraryCoordinates
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype κ]

def gaussianCoordinates (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance : IsProbabilityMeasure (gaussianCoordinates κ) := by
  unfold gaussianCoordinates
  infer_instance

def gaussianAffine (m : I → ℝ) (a : I → κ → ℝ) (z : κ → ℝ) (i : I) : ℝ :=
  m i + ∑ k, a i k * z k

def gaussianSup (m : I → ℝ) (a : I → κ → ℝ) (z : κ → ℝ) : ℝ :=
  sSup (Set.range (gaussianAffine m a z))

omit [CompactSpace I] [Nonempty I] in
 theorem continuous_gaussianAffine {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) :
    Continuous (gaussianAffine m a z) :=
  hm.add (continuous_finsetSum _ (fun k _ =>
    ((continuous_apply k).comp ha).mul continuous_const))

theorem gaussianSup_attained {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) :
    ∃ i, gaussianSup m a z = gaussianAffine m a z i ∧
      ∀ j, gaussianAffine m a z j ≤ gaussianAffine m a z i := by
  obtain ⟨i, _, he, hi⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    Set.univ_nonempty (continuous_gaussianAffine hm ha z).continuousOn
  exact ⟨i, by simpa [gaussianSup] using he, fun j => hi j (Set.mem_univ _)⟩

theorem gaussianSup_le {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) {c : ℝ}
    (hc : ∀ i, gaussianAffine m a z i ≤ c) : gaussianSup m a z ≤ c := by
  obtain ⟨i, he, _⟩ := gaussianSup_attained hm ha z
  rw [he]
  exact hc i

omit [Nonempty I] in
 theorem continuous_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) : Continuous (gaussianSup m a) := by
  have hc : Continuous (fun p : (κ → ℝ) × I => gaussianAffine m a p.1 p.2) := by
    exact (hm.comp continuous_snd).add (continuous_finsetSum _ (fun k _ =>
      (((continuous_apply k).comp ha).comp continuous_snd).mul
        ((continuous_apply k).comp continuous_fst)))
  change Continuous (fun z => sSup (Set.range (gaussianAffine m a z)))
  simpa only [Set.image_univ] using isCompact_univ.continuous_sSup hc

theorem integrable_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) :
    Integrable (gaussianSup m a) (gaussianCoordinates κ) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hm.continuousOn
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  have hMb : ∀ i, |m i| ≤ M := fun i => by
    simpa only [Real.norm_eq_abs] using hM i (Set.mem_univ _)
  have hAb : ∀ i k, |a i k| ≤ A := by
    intro i k
    have hk : |a i k| ≤ ‖a i‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a i) k
    exact hk.trans (hA i (Set.mem_univ _))
  apply ((integrable_const M).add ((integrable_finsetSum (Finset.univ : Finset κ) (fun k _ =>
    ((integrable_eval (i := k) IsGaussian.integrable_id).norm))).const_mul A)).mono'
    (continuous_gaussianSup hm ha).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨i, he, _⟩ := gaussianSup_attained hm ha z
  rw [he, Real.norm_eq_abs]
  change |gaussianAffine m a z i| ≤ M + A * ∑ k, |z k|
  calc
    _ ≤ |m i| + |∑ k, a i k * z k| := abs_add_le _ _
    _ ≤ M + ∑ k, |a i k * z k| :=
      add_le_add (hMb i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ M + ∑ k, A * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hAb i k) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem gaussianSup_comparison [Nonempty κ] {m : I → ℝ} {a b : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (hb : Continuous b)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, gaussianSup m b z ∂gaussianCoordinates κ) ≤
      ∫ z, gaussianSup m a z ∂gaussianCoordinates κ := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := κ))
  let e : Fin (n + 1) ≃ κ := (finCongr hn.symm).trans (Fintype.equivFin κ).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let a' : I → Fin (n + 1) → ℝ := fun i k => a i (e k)
  let b' : I → Fin (n + 1) → ℝ := fun i k => b i (e k)
  have ha' : Continuous a' := continuous_pi (fun k => (continuous_apply (e k)).comp ha)
  have hb' : Continuous b' := continuous_pi (fun k => (continuous_apply (e k)).comp hb)
  have he (f : κ → ℝ) : ∑ k : Fin (n + 1), f (e k) = ∑ k : κ, f k := e.sum_comp f
  have horth' (i j : I) : ∑ k, (a' i k - a' j k) * (b' i k - b' j k) = 0 := by
    dsimp [a', b']
    rw [he (fun k => (a i k - a j k) * (b i k - b j k))]
    exact horth i j
  have hinc' (i j : I) : (∑ k, (b' i k - b' j k)^2) ≤ ∑ k, (a' i k - a' j k)^2 := by
    dsimp [a', b']
    rw [he (fun k => (b i k - b j k)^2), he (fun k => (a i k - a j k)^2)]
    exact hinc i j
  have hpres : MeasurePreserving E (standardGaussianProduct (n + 1)) (gaussianCoordinates κ) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) e
  have hpoint (c : I → κ → ℝ) (z : Fin (n + 1) → ℝ) :
      gaussianSup m c (E z) = supProcess m (fun i k => c i (e k)) z := by
    unfold gaussianSup supProcess
    congr 1
    congr 1
    funext i
    dsimp [gaussianAffine, affineProcess]
    rw [← he (fun k => c i k * E z k)]
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [← hpres.integral_comp' (gaussianSup m b), ← hpres.integral_comp' (gaussianSup m a)]
  simp_rw [hpoint]
  exact gaussian_supProcess_comparison hm ha' hb' horth' hinc'

end ArbitraryCoordinates
end SKRatioGaussian

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
