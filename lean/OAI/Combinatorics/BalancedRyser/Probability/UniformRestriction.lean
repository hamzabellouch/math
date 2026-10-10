import OAI.Combinatorics.BalancedRyser.Local.TupleAlignment

namespace OAI

namespace Balanced.TupleAlignment

open scoped BigOperators ENNReal

theorem uniform_map_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  classical
  ext a
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype,
    Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp [ENNReal.mul_inv, ENNReal.mul_inv_cancel, Fintype.card_ne_zero, mul_left_comm]

noncomputable def restrictionEquiv {ι D A : Type*} (e : ι ↪ D) :
    (D → A) ≃ (ι → A) × ({d : D // d ∉ Set.range e} → A) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun d => d ∈ Set.range e) (fun _ => A)).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft (fun _ : Set.range e => A)
        (Equiv.ofInjective e e.injective)).symm
      (Equiv.refl _))

@[simp] theorem restrictionEquiv_fst {ι D A : Type*} (e : ι ↪ D)
    (o : D → A) (i : ι) : (restrictionEquiv e o).1 i = o (e i) := rfl

theorem uniform_map_restrict {ι D A : Type*}
    [Fintype ι] [Fintype D] [Fintype A] [DecidableEq ι] [DecidableEq D] [Nonempty A] (e : ι ↪ D) :
    (PMF.uniformOfFintype (D → A)).map (fun o i => o (e i)) =
      PMF.uniformOfFintype (ι → A) := by
  classical
  have h := congrArg (fun p => p.map Prod.fst) (uniform_map_equiv (restrictionEquiv (A:=A) e))
  rw [PMF.map_comp, uniform_map_fst] at h
  exact h

end Balanced.TupleAlignment

end OAI
