import OAI.Geometry.SurfaceImmersion.Primitive.CircularPrefixMetrics

namespace OAI

/-! Ordered prefixes of a finite sequence of primitive cycles. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma finite_cycle_order {m j j' k k' : ℕ} (hj : j < m) (hj' : j' < m) :
    j'+m*k' < j+m*k ↔ k' < k ∨ k' = k ∧ j' < j := by
  by_cases hk : k' < k
  · have hb := Nat.mul_le_mul_left m hk
    simp only [Nat.mul_succ] at hb
    constructor
    · exact fun _ => Or.inl hk
    · intro _
      nlinarith
  by_cases he : k' = k
  · subst k'
    simp only [lt_self_iff_false,false_or,true_and]
    omega
  · have hk' : k < k' := by omega
    have hb := Nat.mul_le_mul_left m hk'
    simp only [Nat.mul_succ] at hb
    constructor
    · intro h
      exfalso
      nlinarith
    · rintro (h | ⟨h,_⟩) <;> contradiction

 theorem finite_cycle_prefix_sum {V : Type*} [AddCommMonoid V] {N m : ℕ}
    (T : Fin N → Fin m → V) (u : V) (hsum : ∀ k, ∑ j, T k j = u)
    (k : Fin N) (j : Fin m) :
    (∑ a ∈ CircularPrimitiveFamily.prefixIndices
        ((finProdFinEquiv (k,j)).castSucc),
      T a.divNat a.modNat) =
      k.val • u + ∑ b ∈ CircularPrimitiveFamily.prefixIndices j.castSucc, T k b := by
  classical
  have horder (k' : Fin N) (j' : Fin m) :
      (finProdFinEquiv (k',j')).val < (finProdFinEquiv (k,j)).val ↔
        k'.val < k.val ∨ k' = k ∧ j'.val < j.val := by
    change j'.val+m*k'.val < j.val+m*k.val ↔ _
    rw [Fin.ext_iff]
    exact finite_cycle_order j.isLt j'.isLt
  have hprefix : (∑ a ∈ CircularPrimitiveFamily.prefixIndices
        ((finProdFinEquiv (k,j)).castSucc), T a.divNat a.modNat) =
      ∑ k' : Fin N, ∑ j' : Fin m,
        if k'.val < k.val ∨ k' = k ∧ j'.val < j.val then T k' j' else 0 := by
    rw [CircularPrimitiveFamily.prefixIndices,Finset.sum_filter]
    rw [← Equiv.sum_comp finProdFinEquiv]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k' _
    apply Finset.sum_congr rfl
    intro j' _
    have hinv : (finProdFinEquiv (k',j')).divNat = k' ∧
        (finProdFinEquiv (k',j')).modNat = j' := by
      exact Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k',j'))
    simp only [Fin.val_castSucc,horder,hinv.1,hinv.2]
  rw [hprefix]
  have hinner (k' : Fin N) :
      (∑ j' : Fin m, if k'.val < k.val ∨ k' = k ∧ j'.val < j.val then T k' j' else 0) =
      (if k'.val < k.val then u else 0) +
        (if k' = k then ∑ b ∈ CircularPrimitiveFamily.prefixIndices j.castSucc, T k b else 0) := by
    by_cases hk : k'.val < k.val
    · have hne : k' ≠ k := by intro h; subst k'; omega
      simp [hk,hne,hsum]
    · by_cases he : k' = k
      · subst k'
        simp [CircularPrimitiveFamily.prefixIndices,Finset.sum_filter]
      · simp [hk,he]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]
  have hcount : (∑ k' : Fin N, if k'.val < k.val then u else 0) = k.val • u := by
    rw [← Finset.sum_filter,Finset.sum_const]
    congr 1
    have hf : Finset.univ.filter (fun k' : Fin N => k'.val < k.val) = Finset.Iio k := by
      ext a
      simp
    rw [hf,Fin.card_Iio]
  rw [hcount]
  simp

theorem finite_cycle_total_sum {V : Type*} [AddCommMonoid V] {N m : ℕ}
    (T : Fin N → Fin m → V) (u : V) (hsum : ∀ k, ∑ j, T k j = u) :
    (∑ a : Fin (N*m), T a.divNat a.modNat) = N • u := by
  rw [← Equiv.sum_comp finProdFinEquiv,Fintype.sum_prod_type]
  have hinv (k : Fin N) (j : Fin m) :
      (finProdFinEquiv (k,j)).divNat = k ∧ (finProdFinEquiv (k,j)).modNat = j :=
    Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,j))
  simp_rw [(hinv _ _).1,(hinv _ _).2,hsum]
  simp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
