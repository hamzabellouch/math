import Mathlib
import OAI.Analysis.AffineBernstein.FlatBlockCalculus
import OAI.Analysis.AffineBernstein.NewtonBasis
import OAI.Analysis.AffineBernstein.TubeChartConstruction
import OAI.Analysis.AffineBernstein.TubeWeightAlgebra

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The manuscript's invariant density `μ₀` on base times unit normals. -/
def tubeMeasureDensity (n : ℕ) (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (q : S × E) : ℝ :=
  tubeMeasureCoefficient n (H q) (tubeBaseMatrix H q bS).det (tubeAngularDensity H q bE)

omit [DecidableEq ι] [DecidableEq κ] in
lemma tube_dimension_eq {n : ℕ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : n = Fintype.card ι+Fintype.card κ := by
  obtain ⟨j⟩ := tube_dimension_equiv bS bE L
  simpa only [Fintype.card_fin,Fintype.card_sum] using Fintype.card_congr j

lemma invariantTubeF_unit {n : ℕ} (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hn : n = Fintype.card ι+Fintype.card κ) {q : S × E} (he : ‖q.2‖ = 1) :
    invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) q =
      (Real.log (tubeBaseMatrix H q bS).det-Real.log (tubeAngularDensity H q bE))/((n : ℝ)+2)-
        Real.log (H q) := by
  simp only [invariantTubeF,real_inner_self_eq_norm_sq,he,one_pow,Real.log_one,add_zero,hn,Nat.cast_add]
  ring

lemma tubeMeasureDensity_base {n : ℕ} {H : S × E → ℝ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hn : n = Fintype.card ι+Fintype.card κ) {q : S × E} (he : ‖q.2‖ = 1)
    (hh : 0 < H q) (hB : 0 < (tubeBaseMatrix H q bS).det) (hQ : 0 < tubeAngularDensity H q bE) :
    tubeMeasureDensity n H bS bE q*H q/(tubeBaseMatrix H q bS).det =
      Real.exp (-(n : ℝ)*Real.log (H q)-(((n : ℝ)+2)/2)*
        invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) q) := by
  rw [invariantTubeF_unit H bS bE hn he]
  exact tubeMeasureCoefficient_base hh hB hQ

lemma tubeMeasureDensity_angular {n : ℕ} {H : S × E → ℝ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hn : n = Fintype.card ι+Fintype.card κ) {q : S × E} (he : ‖q.2‖ = 1)
    (hh : 0 < H q) (hB : 0 < (tubeBaseMatrix H q bS).det) (hQ : 0 < tubeAngularDensity H q bE) :
    tubeMeasureDensity n H bS bE q*H q/tubeAngularDensity H q bE =
      Real.exp (2*Real.log (H q)+(((n : ℝ)+2)/2)*
        invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) q) := by
  rw [invariantTubeF_unit H bS bE hn he]
  exact tubeMeasureCoefficient_angular hh hB hQ

omit [Fintype ι] [DecidableEq ι] in
lemma tubeBaseMatrix_eq_slice [CompleteSpace E] {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S) :
    tubeBaseMatrix H q bS = -flatBlockHessian (fun s => H (s,q.2)) bS q.1 := by
  ext i j
  change -fderiv ℝ (fderiv ℝ H) q (bS i,0) (bS j,0) =
    -dirDeriv (bS i) (dirDeriv (bS j) (fun s => H (s,q.2))) q.1
  have hs : ContDiffAt ℝ ∞ (fun s => H (s,q.2)) q.1 := hH.comp q.1 (contDiffAt_id.prodMk contDiffAt_const)
  rw [dirDeriv_eq_second hs]
  exact congrArg Neg.neg (second_fderiv_prod_left (s := q.1) (e := q.2) hH (bS i) (bS j)).symm

end AffineBernstein
end

end OAI
