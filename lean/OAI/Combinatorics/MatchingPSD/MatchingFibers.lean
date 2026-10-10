import OAI.Combinatorics.MatchingPSD.SimultaneousSmoothing

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
namespace Pairing
variable {A : Type u_1} {B : Type u_2} {C : Type u_3}

def transport (e : A ≃ B) (M : Pairing A) : Pairing B :=
  ⟨e.symm.trans (M.1.trans e), by
    constructor
    · intro b
      simp
    · intro b hb
      apply M.partner_ne (e.symm b)
      simpa using congrArg e.symm hb⟩

@[simp] lemma transport_apply (e : A ≃ B) (M : Pairing A) (b : B) :
    (transport e M).1 b = e (M.1 (e.symm b)) := rfl

@[simp] lemma transport_refl (M : Pairing A) : transport (Equiv.refl A) M = M := by
  ext a
  rfl

@[simp] lemma transport_trans (e : A ≃ B) (f : B ≃ C) (M : Pairing A) :
    transport (e.trans f) M = transport f (transport e M) := by
  ext c
  rfl

@[simp] lemma transport_symm (e : A ≃ B) (M : Pairing A) :
    transport e.symm (transport e M) = M := by
  ext a
  simp

def transportEquiv (e : A ≃ B) : Pairing A ≃ Pairing B where
  toFun := transport e
  invFun := transport e.symm
  left_inv := transport_symm e
  right_inv := transport_symm e.symm

lemma transport_perm (p : Equiv.Perm A) (M : Pairing A) : transport p M = relabel p M := rfl

def sum (M : Pairing A) (N : Pairing B) : Pairing (A ⊕ B) :=
  ⟨Equiv.sumCongr M.1 N.1, by
    constructor
    · intro v
      cases v <;> simp
    · intro v hv
      cases v with
      | inl a => exact M.partner_ne a (Sum.inl.inj hv)
      | inr b => exact N.partner_ne b (Sum.inr.inj hv)⟩

@[simp] lemma sum_inl (M : Pairing A) (N : Pairing B) (a : A) :
    (sum M N).1 (.inl a) = .inl (M.1 a) := rfl
@[simp] lemma sum_inr (M : Pairing A) (N : Pairing B) (b : B) :
    (sum M N).1 (.inr b) = .inr (N.1 b) := rfl

lemma sum_relabel_left (p : Equiv.Perm A) (M : Pairing A) (N : Pairing B) :
    sum (relabel p M) N = relabel (Equiv.sumCongr p (Equiv.refl B)) (sum M N) := by
  ext v
  cases v <;> rfl

lemma transport_relabel (e : A ≃ B) (p : Equiv.Perm A) (M : Pairing A) :
    transport e (relabel p M) = relabel (e.symm.trans (p.trans e)) (transport e M) := by
  ext b
  simp only [transport_apply, relabel_apply, Equiv.Perm.inv_def,
    Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]

def cellwise {I : Type u_4} (M : I → Pairing A) : Pairing (I × A) :=
  ⟨{ toFun := fun v => (v.1,(M v.1).1 v.2)
     invFun := fun v => (v.1,(M v.1).1 v.2)
     left_inv := by intro v; simp
     right_inv := by intro v; simp }, by
    constructor
    · intro v; simp
    · intro v hv
      exact (M v.1).partner_ne v.2 (congrArg Prod.snd hv)⟩

@[simp] lemma cellwise_apply {I : Type u_5} (M : I → Pairing A) (i : I) (a : A) :
    (cellwise M).1 (i,a) = (i,(M i).1 a) := rfl

end Pairing

section Coordinates
variable {A : Type u_6} {B : Type u_7} {C : Type u_8} [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable

lemma tableCoordinate_transport (e : A ≃ B) (z : B → C) (c : C × C) (M : Pairing A) :
    tableCoordinate z c (Pairing.transport e M) = tableCoordinate (z ∘ e) c M := by
  unfold tableCoordinate
  rw [← e.sum_comp (fun b => if z b = c.1 ∧ z ((Pairing.transport e M).1 b) = c.2 then (1:ℝ) else 0)]
  simp only [Pairing.transport_apply, Equiv.symm_apply_apply, Function.comp_apply]

lemma tableCoordinate_sum (z : A → C) (w : B → C) (c : C × C)
    (M : Pairing A) (N : Pairing B) :
    tableCoordinate (Sum.elim z w) c (Pairing.sum M N) =
      tableCoordinate z c M + tableCoordinate w c N := by
  simp only [tableCoordinate, Fintype.sum_sum_type, Pairing.sum_inl, Pairing.sum_inr,
    Sum.elim_inl, Sum.elim_inr]
  rfl

lemma tableCoordinate_nonneg (z : A → C) (c : C × C) (M : Pairing A) :
    0 ≤ tableCoordinate z c M := by
  unfold tableCoordinate
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma tableCoordinate_eq_zero_iff (z : A → C) (c : C × C) (M : Pairing A) :
    tableCoordinate z c M = 0 ↔ ∀ a, ¬ (z a = c.1 ∧ z (M.1 a) = c.2) := by
  unfold tableCoordinate
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by split_ifs <;> norm_num)]
  simp

lemma tableCoordinate_constant (z : C) (c : C × C) (M : Pairing A) :
    tableCoordinate (fun _ : A => z) c M =
      if z=c.1 ∧ z=c.2 then (Fintype.card A : ℝ) else 0 := by
  simp only [tableCoordinate]
  split_ifs <;> simp_all

end Coordinates
end MatchingSmoothing

namespace MatchingSmoothing.Pairing
variable {A : Type u_9} {B : Type u_10}

lemma sum_injective : Function.Injective (fun p : Pairing A × Pairing B => sum p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · ext a
    exact Sum.inl.inj (congrArg (fun M : Pairing (A ⊕ B) => M.1 (.inl a)) hpq)
  · ext b
    exact Sum.inr.inj (congrArg (fun M : Pairing (A ⊕ B) => M.1 (.inr b)) hpq)

lemma exists_sum (M : Pairing (A ⊕ B))
    (hl : ∀ a : A, ∃ a' : A, M.1 (.inl a) = .inl a') :
    ∃ L : Pairing A, ∃ R : Pairing B, M = sum L R := by
  classical
  have hr (b : B) : ∃ b' : B, M.1 (.inr b) = .inr b' := by
    cases he : M.1 (.inr b) with
    | inl a =>
      obtain ⟨a',ha⟩ := hl a
      have hh := M.partner_partner (.inr b)
      rw [he, ha] at hh
      cases hh
    | inr b' => exact ⟨b',rfl⟩
  choose f hf using hl
  choose g hg using hr
  have hff : Function.Involutive f := by
    intro a
    apply Sum.inl_injective (β := B)
    rw [← hf, ← hf, M.partner_partner]
  have hgg : Function.Involutive g := by
    intro b
    apply Sum.inr_injective (α := A)
    rw [← hg, ← hg, M.partner_partner]
  let L : Pairing A := ⟨⟨f,f,hff,hff⟩,hff,fun a ha =>
    M.partner_ne (.inl a) ((hf a).trans (congrArg Sum.inl ha))⟩
  let R : Pairing B := ⟨⟨g,g,hgg,hgg⟩,hgg,fun b hb =>
    M.partner_ne (.inr b) ((hg b).trans (congrArg Sum.inr hb))⟩
  refine ⟨L,R,?_⟩
  ext v
  cases v with
  | inl a => exact hf a
  | inr b => exact hg b

noncomputable def sumFiberEquiv (P : Pairing (A ⊕ B) → Prop) (Q : Pairing A → Prop)
    (hs : ∀ L R, P (sum L R) ↔ Q L)
    (hc : ∀ M, P M → ∀ a : A, ∃ a' : A, M.1 (.inl a) = .inl a') :
    {L : Pairing A // Q L} × Pairing B ≃ {M : Pairing (A ⊕ B) // P M} :=
  Equiv.ofBijective (fun p => ⟨sum p.1.1 p.2, (hs _ _).mpr p.1.2⟩) (by
    constructor
    · intro p q he
      have hh : (p.1.1,p.2) = (q.1.1,q.2) :=
        sum_injective (congrArg Subtype.val he)
      apply Prod.ext
      · exact Subtype.ext (congrArg (fun x : Pairing A × Pairing B => x.1) hh)
      · exact congrArg (fun x : Pairing A × Pairing B => x.2) hh
    · intro M
      obtain ⟨L,R,hM⟩ := exists_sum M.1 (hc M.1 M.2)
      refine ⟨(⟨L,(hs L R).mp (hM ▸ M.2)⟩,R),?_⟩
      exact Subtype.ext hM.symm)

end MatchingSmoothing.Pairing

end OAI
