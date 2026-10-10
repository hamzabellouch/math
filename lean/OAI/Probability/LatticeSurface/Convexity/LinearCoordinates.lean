import Mathlib

namespace OAI

open scoped ENNReal NNReal

open MeasureTheory Measure

theorem linear_statistic_coordinates {I : Type*} [Fintype I]
    (l : (I → ℝ) →L[ℝ] ℝ) (hl : l≠0) :
    ∃ n : ℕ,∃ e : (I → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ),∃ c : ℝ≥0,
      0<c ∧ (∀ x,e x 0=l x) ∧ Measure.map e volume=(c:ENNReal) • volume := by
  classical
  obtain ⟨x,hx⟩ : ∃ x,l x≠0 := by
    by_contra hn
    push Not at hn
    exact hl (ContinuousLinearMap.ext hn)
  let v := (l x)⁻¹ • x
  have hv : l v=1 := by simp [v,hx]
  obtain ⟨S,b,i,hbi,hli⟩ := exists_basis_of_pairing_ne_zero (show l.toLinearMap v≠0 by rw [show l.toLinearMap v=l v from rfl,hv];norm_num)
  let := FiniteDimensional.fintypeBasisIndex b
  have hc : 0<Fintype.card S := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  let e₀ : S ≃ Fin (n+1) := (Fintype.equivFin S).trans (finCongr hn)
  let a : S ≃ Fin (n+1) := e₀.trans (Equiv.swap (e₀ i) 0)
  have ha : a i=0 := by simp [a]
  let r : (S → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) := LinearEquiv.piCongrLeft' ℝ (fun _ => ℝ) a
  let e := (b.equivFun.trans r).toContinuousLinearEquiv
  have he (y : I → ℝ) : e y 0=l y := by
    have hai : a.symm 0=i := by rw [← ha,a.symm_apply_apply]
    change b.equivFun y (a.symm 0)=l y
    rw [hai]
    have hl' : l.toLinearMap=b.coord i := by simpa only [show l.toLinearMap v=1 from hv,one_smul] using hli
    rw [show l y=b.coord i y by change l.toLinearMap y=_;rw [hl']]
    rfl
  have : IsAddHaarMeasure (Measure.map e volume) := e.isAddHaarMeasure_map volume
  let c := addHaarScalarFactor (Measure.map e volume) (volume:Measure (Fin (n+1) → ℝ))
  refine ⟨n,e,c,addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,he,?_⟩
  exact isAddLeftInvariant_eq_smul _ _

end OAI
