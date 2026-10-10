import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.FiniteLaw

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic.FiniteLaw
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def iid (P : FiniteLaw X) (I : Type*) [Fintype I] [DecidableEq I] : FiniteLaw (I → X) :=
  pi (fun _ : I => X) (fun _ => P)

theorem iid_expect_equiv (P : FiniteLaw X) (e : I ≃ J) (f : (J → X) → ℝ) :
    (P.iid I).expect (fun z => f (z ∘ e.symm))=(P.iid J).expect f := by
  classical
  unfold expect iid pi
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl X))
  intro z
  dsimp only [Equiv.arrowCongr_apply,Equiv.coe_refl,Function.comp_def]
  congr 1
  exact (e.symm.prod_comp (fun i => P.weight (z i))).symm

theorem iid_expect_restrict (P : FiniteLaw X) (s : I → Prop)
    (f : ({i // s i} → X) → ℝ) :
    (P.iid I).expect (fun z => f (fun i => z i))=(P.iid {i // s i}).expect f := by
  classical
  let Q := P.iid {i // ¬s i}
  calc
    _ = ((P.iid {i // s i}).prod Q).expect (fun z => f z.1) := by
      unfold expect iid pi prod
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd s (fun _ => X))
      intro z
      change (∏ i, P.weight (z i))*f (fun i => z i) =
        ((∏ i : {i // s i}, P.weight (z i))*(∏ i : {i // ¬s i}, P.weight (z i)))*f (fun i => z i)
      congr 1
      exact (Fintype.prod_subtype_mul_prod_subtype s (fun i => P.weight (z i))).symm
    _ = _ := prod_expect_fst _ _ f

theorem iid_expect_injective (P : FiniteLaw X) (e : J → I) (he : Function.Injective e)
    (f : (J → X) → ℝ) :
    (P.iid I).expect (fun z => f (z ∘ e))=(P.iid J).expect f := by
  classical
  let : Fintype {i // i∈Set.range e} := Subtype.fintype _
  let k := Equiv.ofInjective e he
  have H := P.iid_expect_restrict (fun i => i∈Set.range e) (fun z => f (z ∘ k))
  have H' := P.iid_expect_equiv k.symm f
  apply H.trans
  unfold expect iid pi at H' ⊢
  simp only [Equiv.symm_symm] at H'
  refine Eq.trans ?_ H'
  apply Finset.sum_congr
  · ext z; simp
  · intro z _
    congr 1
    apply Finset.prod_congr
    · ext i; simp
    · intros; rfl

theorem iid_expect_single (P : FiniteLaw X) (i : I) (f : X → ℝ) :
    (P.iid I).expect (fun z => f (z i))=P.expect f := by
  classical
  have H := P.iid_expect_injective (fun _ : Unit => i)
    (fun _ _ _ => Subsingleton.elim _ _) (fun z => f (z ()))
  change (P.iid I).expect (fun z => f ((z ∘ (fun _ : Unit => i)) ())) = _
  rw [H]
  unfold expect iid pi
  simp only [Fintype.prod_unique]
  apply Fintype.sum_equiv (Equiv.funUnique Unit X)
  intro z
  rfl

theorem iid_expect_fin_succ (P : FiniteLaw X) (p : ℕ) (f : (Fin (p+1) → X) → ℝ) :
    (P.iid (Fin (p+1))).expect f=
      (P.iid (Fin p)).expect (fun z => P.expect (fun a => f (Fin.snoc z a))) := by
  classical
  unfold expect iid pi
  calc
    _ = ∑ z : (Fin p → X) × X, (∏ i, P.weight (z.1 i))*P.weight z.2*f (Fin.snoc z.1 z.2) := by
      apply Fintype.sum_equiv ((Fin.snocEquiv (fun _ : Fin (p+1) => X)).symm.trans (Equiv.prodComm _ _))
      intro z
      simp only [Equiv.trans_apply,Equiv.prodComm_apply,Fin.snocEquiv_symm_apply,Prod.swap,Fin.prod_univ_castSucc]
      simp only [Fin.snoc_init_self,Fin.init]
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem iid_expect_zero (P : FiniteLaw X) (f : (Fin 0 → X) → ℝ) :
    (P.iid (Fin 0)).expect f=f Fin.elim0 := by
  classical
  unfold expect iid pi
  rw [Fintype.sum_unique]
  simp only [Fin.prod_univ_zero,one_mul]
  congr 1

theorem iid_predictable_bound (P : FiniteLaw X) (E : (j : ℕ) → (Fin j → X) → X → Prop)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hE : ∀ j z, P.prob (E j z) ≤ a j) (p : ℕ) :
    (P.iid (Fin p)).prob (fun z => ∀ i : Fin p,
      E i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) (z i)) ≤ ∏ i : Fin p, a i := by
  classical
  induction p with
  | zero => simp [prob]
  | succ p ih =>
    simp only [prob] at ih ⊢
    rw [iid_expect_fin_succ]
    have H : (P.iid (Fin p)).expect (fun z => P.expect (fun b =>
        if ∀ i : Fin (p+1), E i.val (fun j => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.isLt⟩) (Fin.snoc (α := fun _ : Fin (p+1) => X) z b i)
        then 1 else 0)) ≤
        (P.iid (Fin p)).expect (fun z => (if ∀ i : Fin p,
          E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i) then 1 else 0)*a p) := by
      apply expect_mono
      intro z
      have hpref (b : X) (i : Fin p) :
          (fun j : Fin i.val => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.castSucc.isLt⟩) =
          (fun j : Fin i.val => z ⟨j.val,j.isLt.trans i.isLt⟩) := by
        funext j
        exact Fin.snoc_castSucc (α := fun _ : Fin (p+1) => X) b z ⟨j.val,j.isLt.trans i.isLt⟩
      have hlast (b : X) : (fun j : Fin p => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans (Nat.lt_succ_self p)⟩)=z := by
        funext j
        exact Fin.snoc_castSucc (α := fun _ : Fin (p+1) => X) b z j
      have heq (b : X) : (∀ i : Fin (p+1),
          E i.val (fun j => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.isLt⟩) (Fin.snoc (α := fun _ : Fin (p+1) => X) z b i)) ↔
          (∀ i : Fin p, E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i)) ∧ E p z b := by
        rw [Fin.forall_iff_castSucc, and_comm]
        constructor
        · intro h
          constructor
          · intro i
            simpa only [Fin.val_castSucc,Fin.snoc_castSucc,hpref] using h.1 i
          · simpa only [Fin.val_last,Fin.snoc_last,hlast] using h.2
        · rintro ⟨h,hp⟩
          constructor
          · intro i
            simpa only [Fin.val_castSucc,Fin.snoc_castSucc,hpref] using h i
          · simpa only [Fin.val_last,Fin.snoc_last,hlast] using hp
      simp_rw [heq]
      by_cases hz : ∀ i : Fin p, E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i)
      · simpa [hz,prob] using hE p z
      · simp only [hz,false_and,ite_false,zero_mul,expect_zero,le_refl]
    convert H.trans (show (P.iid (Fin p)).expect (fun z => (if ∀ i : Fin p,
          E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i) then 1 else 0)*a p) ≤ ∏ i : Fin (p+1), a i from by
      rw [expect_mul_const,Fin.prod_univ_castSucc]
      apply mul_le_mul_of_nonneg_right _ (ha p)
      convert ih using 1 <;> first | rfl | (congr 1; funext z; split_ifs <;> rfl)) using 1
    all_goals first | rfl | (congr 1; funext z; congr 1; funext b; split_ifs <;> rfl)

end SK.Analytic.FiniteLaw

end
end

end OAI
