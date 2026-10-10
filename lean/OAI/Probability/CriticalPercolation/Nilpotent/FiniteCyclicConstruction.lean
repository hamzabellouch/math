import Mathlib

namespace OAI

universe u

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

inductive FiniteCyclicConstruction : (G : Type u) → [Group G] → ℕ → Prop
  | finite (G : Type u) [Group G] [Finite G] : FiniteCyclicConstruction G 0
  | cyclic (G : Type u) [Group G] (e : G ≃* Multiplicative ℤ) :
      FiniteCyclicConstruction G 1
  | extension {G Q : Type u} [Group G] [Group Q] (f : G →* Q)
      (hf : Surjective f) {n m : ℕ}
      (hker : FiniteCyclicConstruction f.ker n)
      (hquot : FiniteCyclicConstruction Q m) : FiniteCyclicConstruction G (n+m)

lemma FiniteCyclicConstruction.of_finite_kernel {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : FiniteCyclicConstruction Q n) (f : G →* Q)
    (hf : Surjective f) [Finite f.ker] : FiniteCyclicConstruction G n := by
  simpa using FiniteCyclicConstruction.extension f hf (.finite f.ker) hQ

lemma FiniteCyclicConstruction.of_equiv {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : FiniteCyclicConstruction Q n) (e : G ≃* Q) :
    FiniteCyclicConstruction G n := by
  have he : e.toMonoidHom.ker=⊥ := e.toMonoidHom.ker_eq_bot e.injective
  let _ : Finite e.toMonoidHom.ker := he.symm ▸ (inferInstance : Finite (⊥ : Subgroup G))
  exact hQ.of_finite_kernel e.toMonoidHom e.surjective

private lemma free_finite_cyclic_construction_rank (n : ℕ) :
    ∀ (A : Type u) [AddCommGroup A] [Module.Free ℤ A] [Module.Finite ℤ A],
      Module.finrank ℤ A=n → ∃ k≤n, FiniteCyclicConstruction (Multiplicative A) k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ _ hrank
    let b : Module.Basis (Fin n) ℤ A := hrank ▸ Module.finBasis ℤ A
    let e := b.equivFun
    cases n with
    | zero =>
      let _ : Subsingleton A := ⟨fun x y => e.injective (funext fun i => Fin.elim0 i)⟩
      exact ⟨0,le_rfl,.finite _⟩
    | succ n =>
      let f : A →+ ULift.{u} ℤ := {
        toFun := fun a => ⟨e a 0⟩
        map_zero' := by apply ULift.ext; simp
        map_add' := by intros; apply ULift.ext; simp }
      have hf : Surjective f := by
        intro z
        exact ⟨e.symm (fun _ => z.down),by apply ULift.ext; simp [f]⟩
      let K := f.ker.toIntSubmodule
      have hzero (a : K) : e a.val 0=0 := congrArg ULift.down a.property
      let d : K →ₗ[ℤ] (Fin n → ℤ) := {
        toFun := fun a i => e a.val i.succ
        map_add' := by intros; ext i; simp
        map_smul' := by intros; ext i; simp }
      have hd : Injective d := by
        intro a a' haa
        apply Subtype.ext
        apply e.injective
        funext i
        exact Fin.cases ((hzero a).trans (hzero a').symm) (fun j => congrFun haa j) i
      have hr : Module.finrank ℤ K≤n := by
        simpa using d.finrank_le_finrank_of_injective hd
      obtain ⟨k,hk,hC⟩ := ih (Module.finrank ℤ K) (by omega) K rfl
      let ek : f.toMultiplicative.ker ≃* Multiplicative K := {
        toFun := fun a => Multiplicative.ofAdd ⟨a.val.toAdd,a.property⟩
        invFun := fun a => ⟨Multiplicative.ofAdd a.toAdd.val,a.toAdd.property⟩
        left_inv := by intro a; rfl
        right_inv := by intro a; rfl
        map_mul' := by intros; rfl }
      refine ⟨k+1,by omega,?_⟩
      exact FiniteCyclicConstruction.extension f.toMultiplicative (fun z => hf z.toAdd)
        (hC.of_equiv ek) (.cyclic _ AddEquiv.ulift.toMultiplicative)

theorem free_finite_cyclic_construction (A : Type u) [AddCommGroup A]
    [Module.Free ℤ A] [Module.Finite ℤ A] :
    ∃ n, FiniteCyclicConstruction (Multiplicative A) n := by
  obtain ⟨n,_,hn⟩ := free_finite_cyclic_construction_rank (Module.finrank ℤ A) A rfl
  exact ⟨n,hn⟩

theorem abelian_finite_cyclic_construction (A : Type u) [CommGroup A] [Group.FG A] :
    ∃ n, FiniteCyclicConstruction A n := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive A)
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let φ₀ := (AddMonoidHom.fst (Fin n →₀ ℤ) T).comp f.toAddMonoidHom
  let φ : Additive A →+ ULift.{u} (Fin n →₀ ℤ) := AddEquiv.ulift.symm.toAddMonoidHom.comp φ₀
  have hs : Surjective φ := by
    intro z
    refine ⟨f.symm (z.down,0),?_⟩
    change ULift.up (φ₀ (f.symm (z.down,0)))=z
    apply ULift.ext
    change φ₀ (f.symm (z.down,0))=z.down
    simp [φ₀]
  have hk : (φ.toMultiplicativeRight.ker : Set A).Finite := by
    apply ((Set.finite_singleton (0 : Fin n →₀ ℤ)).prod
      (Set.toFinite (Set.univ : Set T))).preimage f.injective.injOn |>.subset
    intro x hx
    exact ⟨congrArg (fun z : Multiplicative (ULift (Fin n →₀ ℤ)) => z.toAdd.down) hx,
      Set.mem_univ _⟩
  let _ := hk.to_subtype
  obtain ⟨k,hk⟩ := free_finite_cyclic_construction (ULift.{u} (Fin n →₀ ℤ))
  exact ⟨k,hk.of_finite_kernel φ.toMultiplicativeRight (fun z => hs z.toAdd)⟩

end CriticalPercolation
end
end
end

end OAI
