import Mathlib
import OAI.Probability.SKGap.Matrix.LogDetConcentration
import OAI.Probability.SKGap.Localization.CubeApprox

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

lemma logdet_mesh_tail {j γ α u : ℝ} (hj : 0 < j) (hγ : 0 < γ) (hu : 0 ≤ u)
    {n : ℕ} (hn : 0 < n) (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Icc (0:ℝ) 1)
    (hmean : ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ 1) →
      (∫ g, LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a (goeMatrix (j/(n:ℝ)) g) 1)
        ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)) ≤ j*(coordAverage a)^2+α) :
    (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ∃ v : Fin n → s, j*(coordAverage (fun i => (v i:ℝ)))^2+α+u <
        LogDet.regularizedLogDet γ (logPath (j*coordAverage (fun i => (v i:ℝ)))
          (fun i => (v i:ℝ)) (goeMatrix (j/(n:ℝ)) g) 1)} ≤
      (s.card:ℝ)^n*(2*Real.exp (-γ*(n:ℝ)^2*u^2/(π^2*j))) := by
  classical
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)
  let F (a : Fin n → ℝ) (g : MatrixCoordinates (Fin n) → ℝ) :=
    LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a (goeMatrix (j/(n:ℝ)) g) 1)
  let T (v : Fin n → s) := {g | u ≤ |F (fun i => (v i:ℝ)) g-∫ x,F (fun i => (v i:ℝ)) x ∂μ|}
  have ht (v : Fin n → s) : μ.real (T v) ≤ 2*Real.exp (-γ*(n:ℝ)^2*u^2/(π^2*j)) := by
    have hh := logPath_regularized_tail hj hγ hu
      (fun i => (hs _ (v i).property).1) (fun i => (hs _ (v i).property).2)
    have he : (j/(n:ℝ))*∑ i,(v i:ℝ)=j*coordAverage (fun i => (v i:ℝ)) := by
      simp only [coordAverage,Fintype.card_fin]; ring
    simpa only [Fintype.card_fin,he] using hh
  apply (measureReal_mono (s₂ := ⋃ v,T v) ?_ (measure_ne_top _ _)).trans
    ((measureReal_iUnion_fintype_le T).trans ?_)
  · rintro g ⟨v,hv⟩
    refine mem_iUnion.mpr ⟨v,?_⟩
    have hm := hmean (fun i => (v i:ℝ)) (fun i => (hs _ (v i).property).1)
      (fun i => (hs _ (v i).property).2)
    change u ≤ |F (fun i => (v i:ℝ)) g-∫ x,F (fun i => (v i:ℝ)) x ∂μ|
    have hab := le_abs_self (F (fun i => (v i:ℝ)) g-∫ x,F (fun i => (v i:ℝ)) x ∂μ)
    change (∫ x,F (fun i => (v i:ℝ)) x ∂μ) ≤ j*(coordAverage (fun i => (v i:ℝ)))^2+α at hm
    change j*(coordAverage (fun i => (v i:ℝ)))^2+α+u < F (fun i => (v i:ℝ)) g at hv
    linarith
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => ht v)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_coe,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow] using hh
end SKGap
end
end

end OAI
