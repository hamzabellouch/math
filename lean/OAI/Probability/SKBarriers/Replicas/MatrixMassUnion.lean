import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixReplicaBridge

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem restrictedPressure_mono {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (β : ℝ)
    {S T : Finset (ReplicaConfig n d)} (hS : S.Nonempty) (hST : S ⊆ T) :
    restrictedPressure β S ≤ restrictedPressure β T := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply integral_mono (restrictedLogPartition_integrable hn hd β hS)
    (restrictedLogPartition_integrable hn hd β (hS.mono hST))
  intro J
  apply Real.log_le_log (restrictedPartition_pos β hS J)
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun s _ _ => (Real.exp_pos _).le)

theorem replicaGibbsMass_integral_code_union {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β : ℝ) {C : Type} [Fintype C] (code : ReplicaConfig n d → C)
    (hcode : ∀ s t,code s=code t → replicaGram s=replicaGram t)
    (S : Finset (ReplicaConfig n d)) (η E : ℝ) (hE : 0 ≤ E)
    (hgap : ∀ s∈S,matrixConstrainedPressure n d β (replicaGram s) ≤ (d:ℝ)*finiteParisiInf β-η)
    (hprob : ∀ T : Finset (ReplicaConfig n d),T.Nonempty →
      restrictedPressure β T ≤ (d:ℝ)*finiteParisiInf β-η →
      (∫ J,replicaGibbsMass β J T ∂disorderLaw n) ≤ E) :
    (∫ J,replicaGibbsMass β J S ∂disorderLaw n) ≤ (Fintype.card C:ℝ)*E := by
  classical
  let T (c : C) := S.filter (fun s => code s=c)
  have he (J : Disorder n) : replicaGibbsMass β J S=∑ c,replicaGibbsMass β J (T c) := by
    exact (Finset.sum_fiberwise S code (fun s => ∏ a,gibbs β J (s a))).symm
  simp_rw [he]
  rw [integral_finsetSum _ (fun c _ => replicaGibbsMass_integrable β (T c))]
  calc
    _ ≤ ∑ _c : C,E := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : (T c).Nonempty
      · obtain ⟨s,hs⟩ := hc
        have hs' := Finset.mem_filter.mp hs
        have hsub : T c ⊆ matrixReplicaSet n d (replicaGram s) := by
          intro t ht
          apply (mem_matrixReplicaSet _ _).mpr
          exact hcode t s ((Finset.mem_filter.mp ht).2.trans hs'.2.symm)
        apply hprob (T c) ⟨s,hs⟩
        exact (restrictedPressure_mono hn hd β ⟨s,hs⟩ hsub).trans
          (by rw [restrictedPressure_matrixReplicaSet]; exact hgap s hs'.1)
      · have ht : T c=∅ := Finset.not_nonempty_iff_eq_empty.mp hc
        simpa only [ht,replicaGibbsMass,Finset.sum_empty,integral_zero] using hE
    _ = _ := by simp

theorem eventual_replicaGibbsMass_code_gap {β : ℝ} (hβ : 0 < β) (d : ℕ) (hd : 0 < d) :
    ∃ K : ℝ,0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ (C : Type) [Fintype C]
      (code : ReplicaConfig n d → C),
      (∀ s t,code s=code t → replicaGram s=replicaGram t) →
      ∀ (S : Finset (ReplicaConfig n d)) (η : ℝ), 0 ≤ η →
      2*(d:ℝ)*K*(n:ℝ)^(-(1:ℝ)/24) ≤ η →
      (∀ s∈S,matrixConstrainedPressure n d β (replicaGram s) ≤ (d:ℝ)*finiteParisiInf β-η) →
      (∫ J,replicaGibbsMass β J S ∂disorderLaw n) ≤ (Fintype.card C:ℝ)*
        (Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2))) := by
  obtain ⟨K,hK,H⟩ := eventual_replicaGibbsMass_pressure_gap hβ d hd
  refine ⟨K,hK,?_⟩
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro C _ code hcode S η hη herr hgap
  exact replicaGibbsMass_integral_code_union hn0 hd β code hcode S η _ (by positivity)
    hgap (fun T hT hP => hn T η hT hη herr hP)

end SK.Analytic

end
end

end OAI
