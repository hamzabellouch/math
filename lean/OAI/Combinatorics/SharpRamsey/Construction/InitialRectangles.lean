import Mathlib
import OAI.Combinatorics.SharpRamsey.Construction.FlagConstruction

namespace OAI

section
namespace SharpLogRamsey.InitialRectangles
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedInitialRectangles_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedInitialRectangles_2 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective Projectivization.rep (fun a b h => by
    rw [←a.mk_rep,←b.mk_rep]; congr 1)
local instance flat_JoinedInitialRectangles_3 : Finite (Projectivization K (Module.Dual K V)) :=
  Finite.of_injective Projectivization.rep (fun a b h => by
    rw [←a.mk_rep,←b.mk_rep]; congr 1)
local instance flat_JoinedInitialRectangles_4 : Finite (Flag K V) :=
  Finite.of_injective (fun f : Flag K V => (f.point,f.dualPoint)) (by
    intro a b h
    cases a; cases b
    cases h
    rfl)
local instance flat_JoinedInitialRectangles_5 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective

def IsRectangle (W : Submodule K V) (f : Flag K V) : Prop :=
  f.point.submodule≤W ∧ f.dualPoint.submodule≤W.dualAnnihilator

omit [FiniteDimensional K V] in
lemma card_points (W : Submodule K V) :
    Nat.card {a : Projectivization K V // a.submodule≤W} =
      ∑ i∈range (Module.finrank K W),(Nat.card K)^i := by
  rw [←Nat.card_congr (projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

lemma card_rectangle_le (W : Submodule K V) :
    Nat.card {f : Flag K V // IsRectangle W f} ≤
      (∑ i∈range (Module.finrank K W),(Nat.card K)^i)*
      (∑ i∈range (Module.finrank K W.dualAnnihilator),(Nat.card K)^i) := by
  let f : {f : Flag K V // IsRectangle W f} →
      {a : Projectivization K V // a.submodule≤W} ×
      {b : Projectivization K (Module.Dual K V) // b.submodule≤W.dualAnnihilator} :=
    fun z => (⟨z.1.point,z.2.1⟩,⟨z.1.dualPoint,z.2.2⟩)
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have hp := congrArg (fun z => z.1.val) h
    have hd := congrArg (fun z => z.2.val) h
    cases a with | mk a ha =>
      cases b with | mk b hb =>
        cases a; cases b
        simp only [f] at hp hd
        cases hp; cases hd; rfl
  exact (Nat.card_le_card_of_injective f hi).trans_eq (by
    rw [Nat.card_prod,card_points,card_points])

lemma card_subspaces_le :
    Nat.card (Submodule K V)≤(Nat.card K)^(Module.finrank K V)^2 := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (V→ₗ[K]V) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hs : Function.Surjective (LinearMap.range : (V→ₗ[K]V)→Submodule K V) := by
    intro W
    obtain ⟨Q,hQ⟩ := W.exists_isCompl
    exact ⟨W.projection Q hQ,W.range_projection hQ⟩
  apply (Nat.card_le_card_of_surjective _ hs).trans_eq
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (V→ₗ[K]V) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card,Module.finrank_linearMap,pow_two] using
    (Module.card_eq_pow_finrank (K:=K) (V:=V→ₗ[K]V))

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma sum_powers_le_two {q n : ℕ} (hq : 2≤q) (hn : 0<n) :
    ∑ i∈range n,q^i≤2*q^(n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel] at *
    have hm : 2*q^m≤q^(m+1) := by
      rw [pow_succ]
      simpa only [mul_comm] using Nat.mul_le_mul_left (q^m) hq
    omega

lemma card_rectangle_bound {d : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1) (W : Submodule K V) :
    Nat.card {f : Flag K V // IsRectangle W f} ≤ 4*(Nat.card K)^(d-1) := by
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hs := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [hdim] at hs
  let r := Module.finrank K W
  let s := Module.finrank K W.dualAnnihilator
  by_cases hr : r=0
  · apply (card_rectangle_le W).trans
    change (∑ i∈range r,(Nat.card K)^i)*_≤_
    simp [hr]
  by_cases ht : s=0
  · apply (card_rectangle_le W).trans
    change _*(∑ i∈range s,(Nat.card K)^i)≤_
    simp [ht]
  have he : (r-1)+(s-1)=d-1 := by dsimp [r,s] at *; omega
  calc
    _ ≤ (∑ i∈range r,(Nat.card K)^i)*(∑ i∈range s,(Nat.card K)^i) := card_rectangle_le W
    _ ≤ (2*(Nat.card K)^(r-1))*(2*(Nat.card K)^(s-1)) :=
      Nat.mul_le_mul (sum_powers_le_two hq (Nat.pos_of_ne_zero hr))
        (sum_powers_le_two hq (Nat.pos_of_ne_zero ht))
    _ = _ := by rw [show (2*(Nat.card K)^(r-1))*(2*(Nat.card K)^(s-1))=
        4*((Nat.card K)^(r-1)*(Nat.card K)^(s-1)) by ring,←pow_add,he]

lemma card_flags_lower {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1) :
    (Nat.card K)^(2*d-1)≤Nat.card (Flag K V) := by
  rw [card_flags hdim]
  have h1 : (Nat.card K)^d≤∑ i∈range (d+1),(Nat.card K)^i :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  have h2 : (Nat.card K)^(d-1)≤∑ i∈range d,(Nat.card K)^i :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  have he : 2*d-1=d+(d-1) := by omega
  rw [he,pow_add]
  exact Nat.mul_le_mul h1 h2

lemma finite_flags : Finite (Flag K V) := inferInstance

lemma finite_subspaces : Finite (Submodule K V) := inferInstance

end
end SharpLogRamsey.InitialRectangles

end

end OAI
