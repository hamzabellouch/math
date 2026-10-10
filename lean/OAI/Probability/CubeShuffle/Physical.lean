import OAI.Probability.CubeShuffle.Generation
import OAI.RepresentationTheory.FiniteUnitary.Sampling

namespace OAI

namespace CubeShuffle
open scoped BigOperators Classical

lemma insertNth_castSucc_snoc {α : Type*} {d : ℕ} (i : Fin (d+1)) (b a : α) (y : Fin d → α) :
    Fin.insertNth i.castSucc b (Fin.snoc (α := fun _ => α) y a)=Fin.snoc (α := fun _ => α) (Fin.insertNth i b y) a := by
  apply Fin.lastCases ?_ (fun j => ?_) |> fun h => funext h
  · rw [←show i.castSucc.succAbove (Fin.last d)=Fin.last (d+1) from
        Fin.succAbove_castSucc_of_le i (Fin.last d) (Fin.le_last i),Fin.insertNth_apply_succAbove]
    simp
  · cases j using Fin.succAboveCases i with
    | x => simp
    | p j =>
      have he : i.castSucc.succAbove j.castSucc=(i.succAbove j).castSucc := by
        simp only [Fin.succAbove,Fin.castSucc_lt_castSucc_iff]
        split_ifs <;> rfl
      rw [←he,Fin.insertNth_apply_succAbove]
      simp

lemma rotate_cons (d : ℕ) (b : Bool) (y : Card d) :
    rotate (d+1) (Fin.cons b y)=Fin.snoc y b := (Fin.snoc_eq_cons_rotate y b).symm

lemma rotate_insert (d : ℕ) (i : Fin (d+1)) (b : Bool) (y : Card (d+1)) :
    rotate (d+2) (Fin.insertNth i.succ b y)=Fin.insertNth i.castSucc b (rotate (d+1) y) := by
  rw [←Fin.cons_self_tail y,Fin.insertNth_succ_cons,rotate_cons,rotate_cons,insertNth_castSucc_snoc]

/-- Move the first coordinate to a specified slot, without changing the order of the others. -/
def insertionPerm (d : ℕ) (i : Fin (d+1)) : Equiv.Perm (Card (d+1)) :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm.trans
    (Fin.insertNthEquiv (fun _ : Fin (d+1) => Bool) i)

lemma insertionPerm_apply (d : ℕ) (i : Fin (d+1)) (x : Card (d+1)) :
    insertionPerm d i x=Fin.insertNth i (x 0) (Fin.tail x) := rfl

lemma insertionPerm_zero (d : ℕ) : insertionPerm d 0=1 := by
  ext x j
  simp [insertionPerm_apply]

lemma insertionPerm_last (d : ℕ) : insertionPerm d (Fin.last d)=rotate (d+1) := by
  apply Equiv.ext
  intro x
  rw [insertionPerm_apply,Fin.insertNth_last',←rotate_cons,Fin.cons_self_tail]

lemma physical_carry_step (d : ℕ) (i : Fin (d+1)) (ξ : Bool → Coins (d+1)) :
    step (d+2) (fun y => ξ (y i) (Fin.removeNth i y))*insertionPerm (d+1) i.succ=
      insertionPerm (d+1) i.castSucc*childLift (fun b => step (d+1) (ξ b)) := by
  apply Equiv.ext
  intro x
  have he : Fin.cons (Bool.xor ((Fin.tail x) 0) (ξ (x 0) (Fin.tail (Fin.tail x))))
      (Fin.insertNth i (x 0) (Fin.tail (Fin.tail x))) =
      (Fin.insertNth i.succ (x 0) (switchFun (ξ (x 0)) (Fin.tail x)) : Card (d+2)) := by
    simp only [switchFun,Fin.insertNth_succ_cons]
  have hs : switchFun (fun y => ξ (y i) (Fin.removeNth i y))
      (Fin.insertNth i.succ (x 0) (Fin.tail x)) =
      (Fin.insertNth i.succ (x 0) (switchFun (ξ (x 0)) (Fin.tail x)) : Card (d+2)) := by
    conv_lhs => rw [←Fin.cons_self_tail (Fin.tail x),Fin.insertNth_succ_cons]
    simp only [switchFun,Fin.cons_zero,Fin.tail_cons,Fin.insertNth_apply_same,Fin.removeNth_insertNth]
    exact he
  change rotate (d+2) (switchFun (fun y => ξ (y i) (Fin.removeNth i y))
      (Fin.insertNth i.succ (x 0) (Fin.tail x))) = _
  rw [hs,rotate_insert]
  rfl

end CubeShuffle
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω : Type*} [Fintype Ω]

lemma sampleOperator_mul_const (ρ : Representation ℂ G V) (P : Ω → G) (g : G) :
    sampleOperator ρ (fun ω => P ω*g)=sampleOperator ρ P*continuousRepresentation ρ g := by
  simp only [sampleOperator,map_mul,Finset.sum_mul,smul_mul_assoc]

lemma sampleOperator_const_mul (ρ : Representation ℂ G V) (P : Ω → G) (g : G) :
    sampleOperator ρ (fun ω => g*P ω)=continuousRepresentation ρ g*sampleOperator ρ P := by
  simp only [sampleOperator,map_mul,Finset.mul_sum,mul_smul_comm]

lemma sampleOperator_run (d t : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    sampleOperator ρ (run d t)=(sampleOperator ρ (step d))^t := by
  induction t with
  | zero => exact sampleOperator_one ρ
  | succ t ih =>
    let e : Coins d × (Fin t → Coins d) ≃ (Fin (t+1) → Coins d) :=
      Fin.snocEquiv (fun _ => Coins d)
    have he : run d (t+1) ∘ e=fun w => step d w.1*run d t w.2 := by
      funext w
      simp only [Function.comp_apply,e,Fin.snocEquiv_apply,
        run,Fin.snoc_last,Fin.snoc_castSucc]
    rw [←sampleOperator_equiv ρ (run d (t+1)) e,he,sampleOperator_prod,ih,pow_succ']

end CubeShuffle.UnitaryFinite

namespace CubeShuffle
open scoped BigOperators Classical
open UnitaryFinite

/-- Splitting a fair coin layer according to an inserted carried bit is a bijection. -/
def carryCoins (d : ℕ) (i : Fin (d+1)) : (Bool → Coins (d+1)) ≃ Coins (d+2) where
  toFun ξ y := ξ (y i) (Fin.removeNth i y)
  invFun ξ b y := ξ (Fin.insertNth i b y)
  left_inv ξ := by funext b y; simp
  right_inv ξ := by funext y; simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma physical_carry_average (d : ℕ) (i : Fin d)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    sampleOperator ρ (step (d+1))*continuousRepresentation ρ (insertionPerm d i.succ)=
      continuousRepresentation ρ (insertionPerm d i.castSucc)*
        sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b))) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    have he : (fun ξ : Bool → Coins (d+1) =>
        step (d+2) (carryCoins d i ξ)*insertionPerm (d+1) i.succ)=
      (fun ξ => insertionPerm (d+1) i.castSucc*childLift (fun b => step (d+1) (ξ b))) := by
      funext ξ
      exact physical_carry_step d i ξ
    have h := congrArg (sampleOperator ρ) he
    rw [sampleOperator_mul_const,sampleOperator_const_mul] at h
    change sampleOperator ρ (step (d+2) ∘ carryCoins d i)*_=_ at h
    rw [sampleOperator_equiv] at h
    exact h

/-- Exact physical sweep recursion, with rotations telescoped rather than
replacing physical time by an independent network time parameter. -/
theorem physical_sweep_recursion (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    (sampleOperator ρ (step (d+1)))^(d+1)=
      (sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b))))^d*
        sampleOperator ρ (pairSwitch (d := d)) := by
  let A := sampleOperator ρ (step (d+1))
  let K := sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b)))
  have h (t : ℕ) (ht : t≤d) : A^t*continuousRepresentation ρ (insertionPerm d ⟨t,by omega⟩)=K^t := by
    induction t with
    | zero =>
      change 1*continuousRepresentation ρ (insertionPerm d 0)=1
      rw [insertionPerm_zero,map_one,one_mul]
    | succ t ih =>
      have hc := physical_carry_average d (⟨t,by omega⟩ : Fin d) ρ
      change A*continuousRepresentation ρ (insertionPerm d ⟨t+1,by omega⟩)=
        continuousRepresentation ρ (insertionPerm d ⟨t,by omega⟩)*K at hc
      rw [pow_succ,mul_assoc,hc,←mul_assoc,ih (by omega),←pow_succ]
  have he : sampleOperator ρ (step (d+1))=
      continuousRepresentation ρ (rotate (d+1))*sampleOperator ρ (pairSwitch (d := d)) :=
    sampleOperator_const_mul ρ (pairSwitch (d := d)) (rotate (d+1))
  calc
    _ = A^d*A := pow_succ A d
    _ = A^d*(continuousRepresentation ρ (insertionPerm d (Fin.last d))*
        sampleOperator ρ (pairSwitch (d := d))) := by rw [insertionPerm_last]; rw [←he]
    _ = _ := by
      rw [←mul_assoc]
      exact congrArg (fun z => z*sampleOperator ρ (pairSwitch (d := d))) (h d le_rfl)

end CubeShuffle
namespace CubeShuffle
open scoped BigOperators Classical
open UnitaryFinite

lemma childInjection_product (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    childInjection d false (p false)*childInjection d true (p true)=childLift p := by
  change childLift _*childLift _=_
  rw [childLift_mul]
  congr 1
  funext b
  cases b <;> simp

lemma childInjection_commute (d : ℕ) (p q : Equiv.Perm (Card d)) :
    Commute (childInjection d false p) (childInjection d true q) := by
  change childLift _*childLift _=childLift _*childLift _
  rw [childLift_mul,childLift_mul]
  congr 1
  funext b
  cases b <;> simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω : Type*} [Fintype Ω]

lemma sampleOperator_child (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V)
    (P : Ω → Equiv.Perm (Card d)) :
    sampleOperator ρ (fun ω : Bool → Ω => childLift (fun b => P (ω b)))=
      sampleOperator (ρ.comp (childInjection d false)) P*
        sampleOperator (ρ.comp (childInjection d true)) P := by
  let e := (Equiv.boolArrowEquivProd Ω).symm
  have he : (fun ω : Bool → Ω => childLift (fun b => P (ω b))) ∘ e=
      fun w : Ω × Ω => childInjection d false (P w.1)*childInjection d true (P w.2) := by
    funext w
    change childLift (fun b => P (e w b))=_
    rw [←childInjection_product]
    rfl
  rw [←sampleOperator_equiv ρ _ e,he]
  exact sampleOperator_prod ρ (fun w => childInjection d false (P w))
    (fun w => childInjection d true (P w))

lemma sampleOperator_child_commute (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V)
    (P : Ω → Equiv.Perm (Card d)) :
    Commute (sampleOperator (ρ.comp (childInjection d false)) P)
      (sampleOperator (ρ.comp (childInjection d true)) P) := by
  rw [sampleOperator_comp,sampleOperator_comp]
  exact sampleOperator_commute ρ _ _ (fun _ _ => childInjection_commute d _ _)

lemma inverse_butterfly_average_step (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    sampleOperator ρ (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹)=
      sampleOperator ρ (fun ω : Bool → (SwitchIndex d → Bool) =>
        childLift (fun b => (butterflyPerm d (decodeButterfly d (ω b)))⁻¹))*
      sampleOperator ρ (pairSwitch (d := d)) := by
  let e := ((Equiv.prodCongr (Equiv.boolArrowEquivProd (SwitchIndex d → Bool)) (Equiv.refl (Card d → Bool))).trans
    (coinStepEquiv d).symm)
  have he : (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹) ∘ e=
      fun w : (Bool → (SwitchIndex d → Bool)) × (Card d → Bool) =>
        childLift (fun b => (butterflyPerm d (decodeButterfly d (w.1 b)))⁻¹)*pairSwitch w.2 := by
    funext w
    change (butterflyPerm (d+1) (decodeButterfly (d+1)
      ((coinStepEquiv d).symm ((w.1 false,w.1 true),w.2))))⁻¹=_
    rw [butterflyPerm_step,mul_inv_rev,childLift_inv,pairSwitch_inv]
    congr 2
    funext b
    cases b <;> rfl
  rw [←sampleOperator_equiv ρ _ e,he]
  exact sampleOperator_prod ρ
    (fun ω : Bool → (SwitchIndex d → Bool) => childLift (fun b => (butterflyPerm d (decodeButterfly d (ω b)))⁻¹))
    (pairSwitch (d := d))

/-- A physical sweep of exactly d shuffles is the adjoint-oriented fair
butterfly, on every representation and every labeled card. -/
theorem physical_sweep_inverse_butterfly (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    (sampleOperator ρ (step d))^d=
      sampleOperator ρ (fun ω => (butterflyPerm d (decodeButterfly d ω))⁻¹) := by
  induction d with
  | zero =>
    symm
    exact sampleOperator_one ρ
  | succ d ih =>
    rw [physical_sweep_recursion,sampleOperator_child,
      (sampleOperator_child_commute d ρ (step d)).mul_pow,ih,ih,
      inverse_butterfly_average_step]
    rw [sampleOperator_child d ρ (fun ω => (butterflyPerm d (decodeButterfly d ω))⁻¹)]

lemma physical_sweep_adjoint (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) (hρ : IsUnitary ρ) :
    sampleOperator ρ (run d d)=
      (sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint := by
  rw [sampleOperator_run,physical_sweep_inverse_butterfly,sampleOperator_inv ρ hρ]

end CubeShuffle

end OAI
