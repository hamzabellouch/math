import OAI.GroupTheory.Kervaire.Suppression

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev Fiber (r : Setoid D) (c : Quotient r) := {d : D // Quotient.mk r d = c}

def fiberPerm (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r) (c : Quotient r) :
    Equiv.Perm (Fiber r c) :=
  σ.subtypePerm (fun d ↦ by
    have he : Quotient.mk r (σ d) = Quotient.mk r d := Quotient.sound (h SameCycle.rfl.apply_left)
    exact he ▸ Iff.rfl)

omit [Fintype D] [DecidableEq D] in
lemma fiberPerm_apply (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r)
    (c : Quotient r) (d : Fiber r c) : (fiberPerm σ r h c d).val = σ d := rfl

omit [DecidableEq D] in
lemma numCycles_fiber_sum (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r) :
    (∑ c : Quotient r, numCycles (fiberPerm σ r h c)) = numCycles σ := by
  have he (c : Quotient r) : SameCycle.setoid (fiberPerm σ r h c) =
      (SameCycle.setoid σ).comap (Subtype.val : Fiber r c → D) := by
    ext x y
    exact sameCycle_subtypePerm
  have hc := Fintype.card_congr (Setoid.sigmaQuotientEquivOfLe h)
  rw [Fintype.card_sigma] at hc
  unfold numCycles
  convert hc using 1
  apply Finset.sum_congr rfl
  intro c _
  exact Fintype.card_congr (Quotient.congrRight (Setoid.ext_iff.mp (he c)))

omit [DecidableEq D] in
lemma card_fiber_sum (r : Setoid D) :
    (∑ c : Quotient r, Fintype.card (Fiber r c)) = Fintype.card D := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk r))

lemma fiberPerm_mul (σ θ : Equiv.Perm D) (r : Setoid D)
    (hs : SameCycle.setoid σ ≤ r) (ht : SameCycle.setoid θ ≤ r) (c : Quotient r) :
    fiberPerm (σ*θ) r (cycles_mul_le σ θ r hs ht) c = fiberPerm σ r hs c * fiberPerm θ r ht c := by
  ext d
  rfl

lemma fiber_connected (σ θ : Equiv.Perm D) (c : Quotient (components σ θ)) :
    components (fiberPerm σ (components σ θ) le_sup_left c)
      (fiberPerm θ (components σ θ) le_sup_right c) = ⊤ := by
  let r := components σ θ
  let σ' := fiberPerm σ r le_sup_left c
  let θ' := fiberPerm θ r le_sup_right c
  let r' := components σ' θ'
  let f : D → Option (Quotient r') := fun d ↦ if h : Quotient.mk r d = c then some (Quotient.mk r' ⟨d,h⟩) else none
  have step (τ : Equiv.Perm D) (ht : SameCycle.setoid τ ≤ r)
      (ht' : SameCycle.setoid (fiberPerm τ r ht c) ≤ r') (d : D) : f (τ d) = f d := by
    have he : Quotient.mk r (τ d) = Quotient.mk r d := Quotient.sound (ht SameCycle.rfl.apply_left)
    by_cases hd : Quotient.mk r d = c
    · have htd : Quotient.mk r (τ d) = c := he.trans hd
      simp only [f,dite_eq_left htd,dite_eq_left hd]
      apply congrArg some
      apply Quotient.sound
      exact ht' (SameCycle.rfl.apply_left (x := (⟨d,hd⟩ : Fiber r c)))
    · have htd : Quotient.mk r (τ d) ≠ c := fun h ↦ hd (he.symm.trans h)
      simp only [f,dite_eq_right htd,dite_eq_right hd]
  have hrker : r ≤ Setoid.ker f := sup_le
    (cycle_le_of_step σ _ (step σ le_sup_left le_sup_left))
    (cycle_le_of_step θ _ (step θ le_sup_right le_sup_right))
  apply top_unique
  intro d e _
  have hde : r d.val e.val := Quotient.exact (d.property.trans e.property.symm)
  have hh := hrker hde
  have hd : f d.val = some (Quotient.mk r' d) := by
    dsimp [f]
    split
    · rfl
    · exact False.elim (‹¬ _› d.property)
  have he : f e.val = some (Quotient.mk r' e) := by
    dsimp [f]
    split
    · rfl
    · exact False.elim (‹¬ _› e.property)
  change f d.val = f e.val at hh
  rw [hd,he] at hh
  exact Quotient.exact (Option.some.inj hh)

lemma classes_top {B : Type*} [Fintype B] [Nonempty B] : classes (⊤ : Setoid B) = 1 := by
  let _ : Subsingleton (Quotient (⊤ : Setoid B)) := Quotient.subsingleton_iff.mpr rfl
  exact Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ (Classical.arbitrary B),fun _ ↦ Subsingleton.elim _ _⟩

lemma planar_fiber (σ θ : Equiv.Perm D) (hp : planar σ θ) (c : Quotient (components σ θ)) :
    planar (fiberPerm σ (components σ θ) le_sup_left c)
      (fiberPerm θ (components σ θ) le_sup_right c) := by
  let r := components σ θ
  let σ' := fun c : Quotient r ↦ fiberPerm σ r le_sup_left c
  let θ' := fun c : Quotient r ↦ fiberPerm θ r le_sup_right c
  have hnon (c : Quotient r) : Nonempty (Fiber r c) := ⟨⟨c.out,c.out_eq⟩⟩
  have hcl (c : Quotient r) : classes (components (σ' c) (θ' c)) = 1 := by
    let _ := hnon c
    rw [fiber_connected,classes_top]
  let f : Quotient r → ℕ := fun c ↦ numCycles (σ' c) + numCycles (θ' c) + numCycles ((σ' c)*(θ' c))
  let g : Quotient r → ℕ := fun c ↦ Fintype.card (Fiber r c) + 2
  have hle (c : Quotient r) : f c ≤ g c := by
    have hh := euler_inequality (σ' c) (θ' c)
    change _ ≤ _ + 2*classes (components (σ' c) (θ' c)) at hh
    simpa only [hcl c,mul_one] using hh
  have hsum : ∑ c, f c = ∑ c, g c := by
    simp only [f,g,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_fiber_sum]
    rw [numCycles_fiber_sum σ r le_sup_left,numCycles_fiber_sum θ r le_sup_right]
    have hh := numCycles_fiber_sum (σ*θ) r (cycles_mul_le σ θ r le_sup_left le_sup_right)
    have hh' : (∑ z, numCycles ((σ' z)*(θ' z))) = numCycles (σ*θ) := by
      calc
        _ = ∑ z, numCycles (fiberPerm (σ*θ) r (cycles_mul_le σ θ r le_sup_left le_sup_right) z) := by
          apply Finset.sum_congr rfl
          intro z _
          exact congrArg numCycles (fiberPerm_mul σ θ r le_sup_left le_sup_right z).symm
        _ = _ := hh
    rw [hh']
    change _ = _ + Fintype.card (Quotient r)*2
    rw [Nat.mul_comm]
    exact hp
  have hc := (Finset.sum_eq_sum_iff_of_le (fun z (_ : z ∈ Finset.univ) ↦ hle z)).mp hsum c (Finset.mem_univ c)
  change f c = _ + 2*classes (components (σ' c) (θ' c))
  rw [hcl,mul_one]
  exact hc
end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma sameCycle_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (x y : D) :
    θ.SameCycle x y ↔ y = x ∨ y = θ x := by
  constructor
  · intro h
    obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ',mul_apply]
      rcases ih SameCycle.rfl.pow_right with h | h
      · exact Or.inr (congrArg θ h)
      · exact Or.inl ((congrArg θ h).trans (hθ x))
  · rintro (rfl|rfl)
    · exact SameCycle.rfl
    · exact SameCycle.rfl.apply_right

omit [DecidableEq D] in
lemma card_fiber_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hne : ∀ d, θ d ≠ d) (c : Cycles θ) : Fintype.card (Fiber (SameCycle.setoid θ) c) = 2 := by
  let d := c.out
  have hd : Quotient.mk (SameCycle.setoid θ) d = c := c.out_eq
  have ht : Quotient.mk (SameCycle.setoid θ) (θ d) = c :=
    (Quotient.sound SameCycle.rfl.apply_left).trans hd
  let f : Bool → Fiber (SameCycle.setoid θ) c := fun b ↦ if b then ⟨θ d,ht⟩ else ⟨d,hd⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      cases a <;> cases b <;> simp only [f,Bool.false_eq_true,ite_false,ite_true] at hab' ⊢
      · exact (hne d hab'.symm).elim
      · exact (hne d hab').elim
    · intro x
      have hx : θ.SameCycle d x.val := Quotient.exact (hd.trans x.property.symm)
      rcases (sameCycle_involution θ hθ _ _).mp hx with he | he
      · exact ⟨false,Subtype.ext he.symm⟩
      · exact ⟨true,Subtype.ext he.symm⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans Fintype.card_bool

omit [DecidableEq D] in
lemma numCycles_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hne : ∀ d, θ d ≠ d) : 2 * numCycles θ = Fintype.card D := by
  have hh := card_fiber_sum (SameCycle.setoid θ)
  simp only [card_fiber_involution θ hθ hne,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  change 2 * Fintype.card (Cycles θ) = _
  simpa only [Cycles,Nat.mul_comm,Nat.cast_id] using hh

omit [Fintype D] [DecidableEq D] in
lemma numCycles_eq_card_of_projection {V : Type*} [Fintype D] [Fintype V]
    (σ : Perm D) (f : D → V) (hf : Function.Surjective f)
    (hs : ∀ x y, σ.SameCycle x y ↔ f x = f y) : numCycles σ = Fintype.card V := by
  have he : SameCycle.setoid σ = Setoid.ker f := Setoid.ext hs
  unfold numCycles Cycles
  exact (Fintype.card_congr (Quotient.congrRight (Setoid.ext_iff.mp he))).trans
    (Fintype.card_congr (Setoid.quotientKerEquivOfSurjective f hf))

omit [DecidableEq D] in
lemma numCycles_equiv {B : Type*} [Fintype B] (e : D ≃ B) (σ : Perm D) :
    numCycles (e.symm.trans (σ.trans e)) = numCycles σ := by
  symm
  apply Fintype.card_congr
  exact Quotient.congr e (fun x y ↦ by
    change (∃ n : ℤ, (σ^n) x = y) ↔ ∃ n : ℤ, ((e.permCongrHom σ)^n) (e x) = e y
    apply exists_congr
    intro n
    rw [← map_zpow]
    change (σ^n) x = y ↔ e ((σ^n) (e.symm (e x))) = e y
    rw [e.symm_apply_apply,e.injective.eq_iff])
end

open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma reachable_of_cycle {r : D → D → Prop} (σ : Perm D)
    (hs : ∀ d, r d (σ d)) {x y : D} (hxy : σ.SameCycle x y) : Relation.ReflTransGen r x y := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [pow_succ',mul_apply]
    exact ih.tail (hs _)

omit [DecidableEq D] in
lemma reachable_of_component (σ θ : Perm D) {x y : D} (h : components σ θ x y) :
    Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) x y := by
  change (SameCycle.setoid σ ⊔ SameCycle.setoid θ) x y at h
  rw [Setoid.sup_eq_eqvGen] at h
  have hh : Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) x y ∧
      Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) y x := by
    induction h with
    | rel x y h =>
      rcases h with h | h
      · exact ⟨reachable_of_cycle σ (fun _ ↦ Or.inl rfl) h,
          reachable_of_cycle σ (fun _ ↦ Or.inl rfl) h.symm⟩
      · exact ⟨reachable_of_cycle θ (fun _ ↦ Or.inr rfl) h,
          reachable_of_cycle θ (fun _ ↦ Or.inr rfl) h.symm⟩
    | refl x => exact ⟨.refl,.refl⟩
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,ih₂.2.trans ih₁.2⟩
  exact hh.1
end KervaireRibbon

end

end OAI
