import OAI.Probability.PosteriorReplicas.Information.FiniteStateDensity
import OAI.Probability.PosteriorReplicas.Information.GenericInformationBound
import OAI.Probability.PosteriorReplicas.Information.StateSide

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma state_gaussian_information_bound {d ℓ k m V W : ℕ} [NeZero W]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k)
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (hq : q.fst = sphereLaw d)
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ]
    (v : Fin V) (hv : q.snd {v} ≠ 0) :
    conditionalInformation (sideLaw ℓ (stateOutputKernel q κ v)) ≤
      ENNReal.ofReal (finiteEntropy (stateOutputKernel q κ v).snd / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)-Real.log (q.snd.real {v}))) := by
  have : NeZero d := ⟨by omega⟩
  have : IsProbabilityMeasure (sphereLaw d) := by
    change IsProbabilityMeasure (BaseLaw.spherical.measure d)
    infer_instance
  obtain ⟨f,hf,hfL,hfp⟩ := finite_state_bounded_density q.snd (initialStateKernel q)
    (sphereLaw d) ((initialStateKernel_marginal q).trans hq) v hv
  have hpos : 0 < q.snd.real {v} := ENNReal.toReal_pos hv (measure_ne_top _ _)
  have hL : 1 ≤ (q.snd.real {v})⁻¹ := (one_le_inv₀ hpos).mpr measureReal_le_one
  have : IsProbabilityMeasure ((sphereLaw d).withDensity f) := hfp.symm ▸ inferInstance
  have hi := gaussian_replica_information hd hk hm hkm hdk hℓk hf hL hfL (stateBlockKernel κ v)
  simp only [hfp,messageEntropy_eq_finiteEntropy,Real.log_inv,← sub_eq_add_neg] at hi
  exact hi

lemma haar_state_information_bound {d ℓ k m V W : ℕ} [NeZero W]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k) (hℓ : ℓ≤d)
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (hq : q.fst = sphereLaw d)
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    cmi (stateHaarSideLaw ℓ (stateMessageLaw q κ)) ≤
      ENNReal.ofReal (terminalConditionalEntropy (stateMessageLaw q κ) / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)+finiteEntropy q.snd)) := by
  let R : Fin V → ℝ := fun v =>
    finiteEntropy (stateOutputKernel q κ v).snd / ((m+1:ℕ):ℝ) +
      (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)-Real.log (q.snd.real {v}))
  have hR (v : Fin V) : 0 ≤ R v := by
    have hE := finiteEntropy_nonneg (stateOutputKernel q κ v).snd
    have hlog : Real.log (q.snd.real {v}) ≤ 0 := Real.log_nonpos measureReal_nonneg measureReal_le_one
    have hl : 0 ≤ Real.log (1+(d:ℝ)-Real.log (q.snd.real {v})) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) d] : 1≤1+(d:ℝ)-Real.log (q.snd.real {v}))
    dsimp [R]
    positivity
  rw [stateHaarInformation_average hℓ q κ]
  calc
    _ ≤ ∑ v, q.snd {v} * ENNReal.ofReal (R v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : q.snd {v} = 0
      · simp [hv]
      · exact mul_le_mul le_rfl (state_gaussian_information_bound hd hk hm hkm hdk hℓk q hq κ v hv) (by positivity) (by positivity)
    _ = ENNReal.ofReal (∑ v, q.snd.real {v} * R v) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun v _ => mul_nonneg measureReal_nonneg (hR v))]
      apply Finset.sum_congr rfl
      intro v _
      rw [ENNReal.ofReal_mul measureReal_nonneg,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have havg := finiteEntropy_log_average q.snd (a := 1+(d:ℝ)) (by positivity)
      have heq : ∑ v, q.snd.real {v} * R v =
          terminalConditionalEntropy (stateMessageLaw q κ) / ((m+1:ℕ):ℝ) +
            (100+Real.pi)*(d:ℝ) +
              ∑ v, q.snd.real {v} * Real.log (1+(d:ℝ)-Real.log (q.snd.real {v})) := by
        simp only [R,mul_add,← mul_div_assoc,Finset.sum_add_distrib,← Finset.sum_div,
          ← Finset.sum_mul,sum_probability_atoms q.snd,one_mul,
          terminalConditionalEntropy_average]
      rw [heq]
      linarith

theorem haarReplicaBlock : HaarReplicaBlock := by
  refine ⟨200+Real.pi,by positivity,?_⟩
  intro d hd V W hV hW q hp hq κ hκ
  have hi := haar_state_information_bound (m := d/16) (ℓ := d/4)
    (by omega : 4*(d/16)+d/16+2≤d) (by omega) (by omega)
    (by omega : d/16+d/16≤d/4) (by omega) (by omega) (by omega) q hq κ
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hE := finiteEntropy_nonneg q.snd
  have hdp : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hl := Real.log_le_log (by positivity : 0<1+(d:ℝ)+finiteEntropy q.snd)
    (show 1+(d:ℝ)+finiteEntropy q.snd ≤ 1+(200+Real.pi)*(d:ℝ)+finiteEntropy q.snd by
      nlinarith [Real.pi_pos])
  have hrem : 0 ≤ (200+Real.pi)*(finiteEntropy q.snd+Real.log (d:ℝ))/(d:ℝ)^2 :=
    div_nonneg (mul_nonneg (by positivity) (add_nonneg hE (Real.log_nonneg hdp))) (sq_nonneg _)
  nlinarith [Real.pi_pos]

end PosteriorReplicas
end

end OAI
