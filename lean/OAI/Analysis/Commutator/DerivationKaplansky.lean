import Mathlib
import OAI.Analysis.Commutator.CyclicDecomposition
import OAI.Analysis.Commutator.Definitions
import OAI.Analysis.Commutator.DerivationCyclicColumns
import OAI.Analysis.Commutator.KaplanskyFullRange
import OAI.Analysis.Commutator.MatrixTowerGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.DerivationColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

theorem seminorm_bicommutant_le (Y : H →L[ℂ] H) {c : ℝ} (hc : 0≤c)
    (hY : ∀ a : A,‖Y*σ a-σ a*Y‖≤c*‖a‖) :
    commutatorSeminorm (NormalGNS.bicommutant σ.range) Y≤c := by
  classical
  change sSup {r : ℝ | ∃ T : H →L[ℂ] H,T∈NormalGNS.bicommutant σ.range ∧ ‖T‖≤1 ∧ r=‖Y*T-T*Y‖}≤c
  refine csSup_le ⟨0,0,zero_mem _,by simp,by simp⟩ ?_
  rintro r ⟨T,hT,hnT,rfl⟩
  have hTb := (NormalGNS.mem_bicommutant σ.range T).mp hT
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have ht := ((Y.continuous.tendsto (T x)).comp
    (Kaplansky.fullNet_tendsto σ T hTb hnT x)).sub
      (Kaplansky.fullNet_tendsto σ T hTb hnT (Y x))
  change Tendsto (fun j => (Y*σ (Kaplansky.fullNet σ T hTb hnT j)-
    σ (Kaplansky.fullNet σ T hTb hnT j)*Y) x) atTop (𝓝 ((Y*T-T*Y) x)) at ht
  apply le_of_tendsto ht.norm
  apply Filter.Eventually.of_forall
  intro j
  calc
    _≤‖Y*σ (Kaplansky.fullNet σ T hTb hnT j)-σ (Kaplansky.fullNet σ T hTb hnT j)*Y‖*‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _≤(c*‖Kaplansky.fullNet σ T hTb hnT j‖)*‖x‖ :=
      mul_le_mul_of_nonneg_right (hY _) (norm_nonneg x)
    _≤c*‖x‖ := by
      have hn := (Kaplansky.fullNet_spec σ T hTb hnT j).1
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hn hc).trans_eq (mul_one c)) (norm_nonneg x)

variable (D : A →L[ℂ] (H →L[ℂ] H))
  (hD : ∀ a b,D (a*b)=(D a).comp (σ b)+(σ a).comp (D b))
  (Q : CyclicDecomposition.Decomposition σ.range)

lemma finite_seminorm_bound (s : Finset Q.I) :
    commutatorSeminorm (NormalGNS.bicommutant σ.range) (finiteImplementer σ D hD Q s)≤‖D‖ :=
  seminorm_bicommutant_le σ _ (norm_nonneg D) (finite_scalar_bound σ D hD Q s)

end Kadison.DerivationColumns

end

end
end

end OAI
