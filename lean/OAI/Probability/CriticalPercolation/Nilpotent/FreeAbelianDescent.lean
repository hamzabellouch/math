import Mathlib
import OAI.Probability.CriticalPercolation.Classification.AlgebraicDescent
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteKernelDescent

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

universe uA

private lemma free_abelian_descent_rank (n : ℕ) :
    ∀ (A : Type uA) [AddCommGroup A] [Module.Free ℤ A] [Module.Finite ℤ A],
      Module.finrank ℤ A=n → AlgebraicDescent (Multiplicative A) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ _ hrank
    let b : Module.Basis (Fin n) ℤ A := hrank ▸ Module.finBasis ℤ A
    let e := b.equivFun
    cases n with
    | zero =>
      let _ : Subsingleton A := ⟨fun x y => e.injective (funext fun i => Fin.elim0 i)⟩
      exact AlgebraicDescent.finite _
    | succ n =>
      cases n with
      | zero =>
        let f : A →+ ℤ := {
          toFun := fun x => e x 0
          map_zero' := by simp
          map_add' := by intros; simp }
        have hs : Surjective f := by
          intro z
          exact ⟨e.symm (fun _ => z),by simp [f]⟩
        have hk : (f.toMultiplicative.ker : Set (Multiplicative A))={1} := by
          ext a
          change e a.toAdd 0=0 ↔ a.toAdd=0
          constructor
          · intro ha
            apply e.injective
            funext i
            have hi : i=(0 : Fin 1) := Fin.ext (by omega)
            subst i
            simpa using ha
          · intro ha
            simp [ha]
        apply AlgebraicDescent.cyclic _ f.toMultiplicative (fun z => hs z.toAdd)
        rw [hk]
        exact Set.finite_singleton _
      | succ n =>
        let f : A →+ (ℤ×ℤ) := {
          toFun := fun x => (e x ⟨0,by omega⟩,e x ⟨1,by omega⟩)
          map_zero' := by simp
          map_add' := by intros; simp }
        have hs : Surjective f := by
          intro z
          refine ⟨e.symm (Fin.cons z.1 (Fin.cons z.2 (fun _ => 0))),?_⟩
          simp [f]
        apply AlgebraicDescent.plane _ f.toMultiplicative (fun z => hs z.toAdd)
        intro J hJ
        let K : Submodule ℤ A := {
          carrier := {a | Multiplicative.ofAdd a∈J}
          zero_mem' := J.one_mem
          add_mem' := fun hx hy => J.mul_mem hx hy
          smul_mem' := fun z a ha => by
            change Multiplicative.ofAdd (z • a)∈J
            rw [ofAdd_zsmul]
            exact J.zpow_mem ha z }
        have hzero (a : K) : e a.val ⟨0,by omega⟩=0 :=
          congrArg (fun z : Multiplicative (ℤ×ℤ) => z.toAdd.1) (hJ a.property)
        let d : K →ₗ[ℤ] (Fin (n+1) → ℤ) := {
          toFun := fun a i => e a.val i.succ
          map_add' := by intros; ext i; simp
          map_smul' := by intros; ext i; simp }
        have hd : Injective d := by
          intro a a' haa
          apply Subtype.ext
          apply e.injective
          funext i
          refine Fin.cases ?_ (fun j => congrFun haa j) i
          exact (hzero a).trans (hzero a').symm
        have hr : Module.finrank ℤ K≤n+1 := by
          simpa using d.finrank_le_finrank_of_injective hd
        have hK := ih (Module.finrank ℤ K) (by omega) K rfl
        let equiv : J ≃* Multiplicative K := {
          toFun := fun j => Multiplicative.ofAdd ⟨j.val.toAdd,j.property⟩
          invFun := fun a => ⟨Multiplicative.ofAdd a.toAdd.val,a.toAdd.property⟩
          left_inv := by intro j; rfl
          right_inv := by intro a; rfl
          map_mul' := by intro j k; rfl }
        exact hK.of_equiv equiv

theorem free_abelian_descent (A : Type uA) [AddCommGroup A]
    [Module.Free ℤ A] [Module.Finite ℤ A] : AlgebraicDescent (Multiplicative A) :=
  free_abelian_descent_rank (Module.finrank ℤ A) A rfl

end CriticalPercolation
end
end
end

end OAI
