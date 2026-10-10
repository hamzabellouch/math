import OAI.Analysis.Laughlin.FourBody.RetainedIndex

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev RetainedFourColumns (Q : ℕ) :=
  Σ d : Fin 23, OddPairLabel (d.val+1) × Fin (fourSpinWeight Q (d.val+1)+1)

noncomputable def retainedFourColumnsEquiv (Q : ℕ) (hQ : 25 ≤ Q) :
    RetainedFourColumns Q ≃ {s : FourCoupledIndex Q // fourCoupledDeficit s ≤ 23} := by
  let f : RetainedFourColumns Q → {s : FourCoupledIndex Q // fourCoupledDeficit s ≤ 23} :=
    fun x => ⟨retainedFourIndex Q (x.1.val+1) (by have := x.1.isLt; omega) x.2.1 x.2.2,
      by rw [retainedFourIndex_deficit]; have := x.1.isLt; omega⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨d,x⟩ ⟨e,y⟩ h
    have hv := congrArg (fun s => fourCoupledDeficit s.val) h
    change fourCoupledDeficit (retainedFourIndex Q _ (by omega) x.1 x.2) =
      fourCoupledDeficit (retainedFourIndex Q _ (by omega) y.1 y.2) at hv
    simp only [retainedFourIndex_deficit] at hv
    have hd : d=e := Fin.ext (by omega)
    subst e
    have he : (retainedFourIndexEquiv Q (d.val+1) (by omega)) x =
        (retainedFourIndexEquiv Q (d.val+1) (by omega)) y := by
      apply Subtype.ext
      exact congrArg (fun s => s.val) h
    exact congrArg (Sigma.mk d) ((retainedFourIndexEquiv Q (d.val+1) (by omega)).injective he)
  · intro s
    let d : Fin 23 := ⟨fourCoupledDeficit s.val-1,by
      have := fourCoupledDeficit_pos s.val; have := s.property; omega⟩
    let t : {t : FourCoupledIndex Q // fourCoupledDeficit t=d.val+1} :=
      ⟨s.val,by have := fourCoupledDeficit_pos s.val; dsimp [d]; omega⟩
    refine ⟨⟨d,(retainedFourIndexEquiv Q (d.val+1) (by omega)).symm t⟩,?_⟩
    apply Subtype.ext
    exact congrArg (fun x : {t : FourCoupledIndex Q // fourCoupledDeficit t=d.val+1} => x.val)
      ((retainedFourIndexEquiv Q (d.val+1) (by omega)).apply_symm_apply t)

theorem sum_fourCoupled_retained {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (hQ : 25 ≤ Q) (f : FourCoupledIndex Q → A)
    (hz : ∀ s, 23 < fourCoupledDeficit s → f s=0) :
    (∑ s, f s) = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      ∑ n : Fin (fourSpinWeight Q (d.val+1)+1),
        f (retainedFourIndex Q (d.val+1) (by have := d.isLt; omega) r n) := by
  classical
  rw [Finset.sum_congr_set (s := {s : FourCoupledIndex Q | fourCoupledDeficit s ≤ 23})
    f (fun s => f s.val) (fun _ _ => rfl) (by intro s hs; exact hz s (by simpa using hs))]
  have h := Fintype.sum_equiv (retainedFourColumnsEquiv Q hQ)
    (fun x => f (retainedFourIndex Q (x.1.val+1) (by have := x.1.isLt; omega) x.2.1 x.2.2))
    (fun s => f s.val) (fun _ => rfl)
  convert (by simpa only [Fintype.sum_sigma,Fintype.sum_prod_type] using h.symm) using 1
  apply Fintype.sum_equiv (Equiv.refl _)
  intro s
  rfl

end Laughlin.Spin

end OAI
