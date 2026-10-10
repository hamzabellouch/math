import Mathlib
import OAI.Probability.LogConcave.JetEstimates.PolyC1

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma PolyC1.of_lipschitz {d : ℕ} {f : Point d → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hL : LipschitzWith K f) : PolyC1 f := by
  refine ⟨hf,growth_of_lipschitz hL,fun v => ⟨(K:ℝ)*‖v‖,by positivity,0,fun x => ?_⟩⟩
  have hn := (fderiv ℝ f x).le_opNorm v
  have hb := norm_fderiv_le_of_lipschitz ℝ hL (x₀:=x)
  change ‖(fderiv ℝ f x) v‖ ≤ _
  simp only [pow_zero]
  exact hn.trans ((mul_le_mul_of_nonneg_right hb (norm_nonneg v)).trans (by nlinarith [mul_nonneg K.coe_nonneg (norm_nonneg v)]))

lemma polyC1_directional_potential {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H)) (v : Point d) :
    PolyC1 (directional v H) := by
  apply PolyC1.of_lipschitz ((directional_smooth hH v).of_le (by simp))
  have he : (fun x => (innerSL ℝ v) (gradient H x))=directional v H := by
    funext x
    rw [innerSL_apply_apply,real_inner_comm,directional_gradient]
  simpa only [Function.comp_def,he] using (innerSL ℝ v).lipschitzWith.comp hL

lemma polyC1_adjointCoordinate {d : ℕ} {H f : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H))
    (hf : PolyC1 f) (v : Point d) (hd : PolyC1 (directional v f)) :
    PolyC1 (adjointCoordinate H v f) :=
  hd.neg.add ((polyC1_directional_potential hH hL v).mul hf)

lemma polyC1_tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H))
    (b : ι → Point d) (hV : ∀i,PolyC1 (V i)) (hD : ∀i,PolyC1 (directional (b i) (V i))) :
    PolyC1 (tensorAdjoint H b V) :=
  PolyC1.sum Finset.univ (fun i _ => polyC1_adjointCoordinate hH hL (hV i) (b i) (hD i))

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
