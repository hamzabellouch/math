import OAI.NumberTheory.DirichletL.Reflection.CubeSlotBounds
import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_cube_shifted_tuple_energy (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ κ : Type*} [Fintype σ] [DecidableEq σ]
      (H : Ideal Eis),H≠0 → ∀ (L : σ→Finset (Ideal Eis))
      (_hmax : ∀ i,∀ P∈L i,P.IsMaximal)
      (_hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
      (w : ∀ i,L i→ℂ), (∀ i P,‖w i P‖≤1) → Fintype.card σ≤rmax →
    ∀ (rows : Finset κ) (Ψ : κ→(Eis→*ℂ)) (W : ℝ→ℂ) (X E : ℝ),0≤E →
      (∀ T : Finset σ,
        (∑ k∈rows,‖∑ a : ∀ i : T,cubeAwayList H (L i.val),
          (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
            markedCompletedT (Ψ k) W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)‖^2)≤E) →
      (∑ k∈rows,‖∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (Ψ k) W X
        (fun A => ∏ i,if (p i).val∣H^3*A then (1:ℂ) else 0)‖^2)≤
      C*(Ideal.absNorm H:ℝ)^ε*E := by
  obtain ⟨C,hC,hb⟩ := cubeAbsorbedCoefficient_small_power rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ κ _ _ H hH L hmax hgood w hw hr rows Ψ W X E hE he
  simp_rw [original_cube_shifted_tuple_source H L hmax hgood w]
  apply (weighted_finite_row_energy_uniform Finset.univ rows (cubeAbsorbedCoefficient H L w)
    (fun T k => ∑ a : ∀ i : T,cubeAwayList H (L i.val),
      (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
        markedCompletedT (Ψ k) W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)) E
    (fun T _ => he T)).trans
  exact mul_le_mul_of_nonneg_right (hb H hH L w hw hr) hE
end
end SevenEighths.InverseReflectedPhase

end OAI
