import Mathlib
import OAI.Analysis.Commutator.CStarContractiveLifts
import OAI.Analysis.Commutator.CommutatorPerturbation
import OAI.Analysis.Commutator.MatrixTowerGNS

namespace OAI

noncomputable section

noncomputable section

open scoped Topology

open Filter ContinuousLinearMap

namespace Kadison

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutator_normClosure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (δ : ℝ)
    (hb : ∀ a∈S,‖Y*a-a*Y‖≤δ*‖a‖) :
    ∀ a∈S.topologicalClosure,‖Y*a-a*Y‖≤δ*‖a‖ := by
  have hc : IsClosed {a : H →L[ℂ] H | ‖Y*a-a*Y‖≤δ*‖a‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact closure_minimal hb hc

lemma commutator_bicommutant_contraction (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed (S : Set (H →L[ℂ] H))) (Y : H →L[ℂ] H) (δ : ℝ) (hδ : 0≤δ)
    (hb : ∀ a∈S,‖Y*a-a*Y‖≤δ*‖a‖)
    (T : H →L[ℂ] H) (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hnT : ‖T‖≤1) : ‖Y*T-T*Y‖≤δ := by
  classical
  let a := Kaplansky.approximationNet S hS T hT hnT
  have ha (j : Finset H × ℕ) := Kaplansky.approximationNet_spec S hS T hT hnT j
  have hlim (x : H) : Tendsto (fun j => a j x) atTop (𝓝 (T x)) :=
    Kaplansky.approximationNet_tendsto S hS T hT hnT x
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro x
  have hcomm : Tendsto (fun j => (Y*a j-a j*Y) x) atTop (𝓝 ((Y*T-T*Y) x)) :=
    (Y.continuous.tendsto _ |>.comp (hlim x)).sub (hlim (Y x))
  apply le_of_tendsto hcomm.norm
  apply Eventually.of_forall
  intro j
  exact ((Y*a j-a j*Y).le_opNorm x).trans (mul_le_mul_of_nonneg_right
    ((hb (a j) (ha j).1).trans ((mul_le_mul_of_nonneg_left (ha j).2.1 hδ).trans_eq (mul_one δ)))
    (norm_nonneg x))

lemma commutatorSeminorm_bicommutant_le (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (δ : ℝ) (hδ : 0≤δ)
    (hb : ∀ a∈S,‖Y*a-a*Y‖≤δ*‖a‖) :
    commutatorSeminorm (NormalGNS.bicommutant S) Y≤δ := by
  apply commutatorSeminorm_le
  intro T hT hnT
  apply commutator_bicommutant_contraction S.topologicalClosure S.isClosed_topologicalClosure
    Y δ hδ (commutator_normClosure S Y δ hb) T _ hnT
  intro R hR
  exact ((NormalGNS.mem_bicommutant S T).mp hT) R (fun a ha => hR a (S.le_topologicalClosure ha))

variable [CStarAlgebra A]

lemma commutatorSeminorm_image_bicommutant_le (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (δ : ℝ) (hδ : 0≤δ)
    (hb : ∀ a,‖Y*φ a-φ a*Y‖≤δ*‖a‖) :
    commutatorSeminorm (NormalGNS.bicommutant φ.range) Y≤δ := by
  apply commutatorSeminorm_bicommutant_le _ _ _ hδ
  intro b hbr
  obtain ⟨a,ha,rfl⟩ := CStarContractiveLifts.norm_lift φ hbr
  exact (hb a).trans (mul_le_mul_of_nonneg_left ha hδ)

end Kadison
end
end

end OAI
