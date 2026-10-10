/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

noncomputable section
namespace Pureness.OrderedSemigroup
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]
open Algebra

omit [PartialOrder S] [IsOrderedAddMonoid S] in
theorem grothendieck_eq_iff [PartialOrder S] [IsOrderedAddMonoid S] (a b : S) :
    GrothendieckAddGroup.of a = GrothendieckAddGroup.of b ↔ ∃ c : S, a+c=b+c := by
  change AddLocalization.mk a 0 = AddLocalization.mk b 0 ↔ _
  simp only [AddLocalization.mk_eq_mk_iff, AddLocalization.r_iff_exists,
    AddSubmonoid.coe_zero, zero_add, Subtype.exists, AddSubmonoid.mem_top]
  simp [add_comm]

theorem grothendieck_difference_eq_iff (a b c d : S) :
    GrothendieckAddGroup.of b - GrothendieckAddGroup.of a =
      GrothendieckAddGroup.of d - GrothendieckAddGroup.of c ↔
        ∃ e : S, b+c+e=d+a+e := by
  rw [sub_eq_sub_iff_add_eq_add, ← map_add, ← map_add, grothendieck_eq_iff]

omit [PartialOrder S] [IsOrderedAddMonoid S] in
theorem grothendieck_exists_difference [PartialOrder S] [IsOrderedAddMonoid S]
    (g : GrothendieckAddGroup S) :
    ∃ a b : S, g = GrothendieckAddGroup.of b - GrothendieckAddGroup.of a := by
  induction g using AddLocalization.ind with
  | H p =>
    refine ⟨p.2,p.1,?_⟩
    change AddLocalization.mk p.1 p.2 = (AddLocalization.mk p.1 0 : GrothendieckAddGroup S) - (AddLocalization.mk p.2 0 : GrothendieckAddGroup S)
    rw [GrothendieckAddGroup.mk_sub_mk]
    simp

def grothendieckCone : AddSubmonoid (GrothendieckAddGroup S) where
  carrier := {g | ∃ a b : S, a ≤ b ∧ g = GrothendieckAddGroup.of b - GrothendieckAddGroup.of a}
  zero_mem' := ⟨0,0,le_rfl,by simp⟩
  add_mem' := by
    rintro g h ⟨a,b,hab,rfl⟩ ⟨c,d,hcd,rfl⟩
    exact ⟨a+c,b+d,add_le_add hab hcd,by simp only [map_add]; abel⟩

theorem grothendieck_mem_cone_iff (a b : S) :
    GrothendieckAddGroup.of b - GrothendieckAddGroup.of a ∈ grothendieckCone ↔
      ∃ c : S, a+c ≤ b+c := by
  constructor
  · rintro ⟨c,d,hcd,heq⟩
    obtain ⟨e,he⟩ := (grothendieck_difference_eq_iff a b c d).mp heq
    refine ⟨c+e,?_⟩
    calc
      a+(c+e) ≤ a+(d+e) := add_le_add le_rfl (add_le_add hcd le_rfl)
      _ = b+(c+e) := by rw [← add_assoc, add_comm a d, ← he, add_assoc]
  · rintro ⟨c,hc⟩
    refine ⟨a+c,b+c,hc,?_⟩
    simp only [map_add]
    abel

lemma grothendieck_of_nonneg (hzero : ∀ a : S, 0 ≤ a) (a : S) :
    GrothendieckAddGroup.of a ∈ grothendieckCone :=
  ⟨0,a,hzero a,by simp⟩

theorem grothendieck_orderUnit (hzero : ∀ a : S, 0 ≤ a)
    (u : S) (hunit : ∀ a : S, ∃ n : ℕ, a ≤ n • u)
    (g : GrothendieckAddGroup S) :
    ∃ n : ℕ, n • GrothendieckAddGroup.of u + g ∈ grothendieckCone := by
  obtain ⟨a,b,rfl⟩ := grothendieck_exists_difference g
  obtain ⟨n,hn⟩ := hunit a
  refine ⟨n,a,n • u+b,hn.trans (le_add_of_nonneg_right (hzero b)),?_⟩
  simp only [map_add,map_nsmul]
  abel

end Pureness.OrderedSemigroup

namespace Pureness.OrderedSemigroup
variable (G : Type*) [AddCommGroup G]

abbrev RationalGroup := LocalizedModule (nonZeroDivisors ℤ) G
instance rationalGroupModule : Module ℚ (RationalGroup G) :=
  LocalizedModule.moduleOfIsLocalization (S := nonZeroDivisors ℤ) (M := G) (T := ℚ)

abbrev toRationalGroup : G →ₗ[ℤ] RationalGroup G :=
  LocalizedModule.mkLinearMap (nonZeroDivisors ℤ) G

theorem rationalGroup_eq_iff (g h : G) :
    toRationalGroup G g = toRationalGroup G h ↔
      ∃ n : ℕ, 0 < n ∧ n • g = n • h := by
  change LocalizedModule.mk g 1 = LocalizedModule.mk h 1 ↔ _
  rw [LocalizedModule.mk_eq]
  simp only [one_smul]
  constructor
  · rintro ⟨⟨k,hk⟩,he⟩
    have hk0 := nonZeroDivisors.ne_zero hk
    change k • g = k • h at he
    cases k with
    | ofNat n =>
      exact ⟨n, by
        apply Nat.pos_of_ne_zero
        intro hn
        apply hk0
        simp [hn], by simpa using he⟩
    | negSucc n =>
      refine ⟨n+1, Nat.succ_pos n, ?_⟩
      change (-((n+1 : ℕ) : ℤ)) • g = (-((n+1 : ℕ) : ℤ)) • h at he
      simpa only [neg_smul, neg_inj, natCast_zsmul] using he
  · rintro ⟨n,hn,he⟩
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    simpa using he

theorem rationalGroup_denominator (z : RationalGroup G) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : G, (n : ℚ) • z = toRationalGroup G g := by
  induction z using LocalizedModule.induction_on with
  | h g s =>
   obtain ⟨k,hk⟩ := s
   have he : (k : ℚ) • (LocalizedModule.mk g ⟨k,hk⟩ : RationalGroup G) = toRationalGroup G g := by
     have heq : (k : ℚ) = IsLocalization.mk' ℚ k (1 : nonZeroDivisors ℤ) := by simp
     rw [heq, LocalizedModule.mk'_smul_mk, one_mul]
     exact LocalizedModule.mk_cancel ⟨k,hk⟩ g
   have hk0 := nonZeroDivisors.ne_zero hk
   cases k with
   | ofNat n =>
    refine ⟨n, ?_, g, ?_⟩
    · apply Nat.pos_of_ne_zero
      intro hn
      apply hk0
      simp [hn]
    · exact he
   | negSucc n =>
    refine ⟨n+1, Nat.succ_pos n, -g, ?_⟩
    change (-((n+1 : ℕ) : ℚ)) • _ = _ at he
    rw [neg_smul] at he
    have h := congrArg Neg.neg he
    simpa only [neg_neg, map_neg] using h

end Pureness.OrderedSemigroup

open Set LinearMap

namespace Pureness
namespace RationalRiesz
variable {E : Type*}

variable [AddCommGroup E] [Module ℚ E]

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis

The Riesz extension declarations below are adapted from Mathlib.Analysis.Convex.Cone.Extension.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Convex/Cone/Extension.lean

This code has been modified.
-/

namespace RieszExtension

open Submodule

variable (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)

theorem step (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x := by
  obtain ⟨y, -, hy⟩ : ∃ y ∈ ⊤, y ∉ f.domain := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hdom)
  obtain ⟨c, le_c, c_le⟩ :
      ∃ c, (∀ x : f.domain, -(x : E) - y ∈ s → f x ≤ c) ∧
        ∀ x : f.domain, (x : E) + y ∈ s → c ≤ f x := by
    set Sp := f '' { x : f.domain | (x : E) + y ∈ s }
    set Sn := f '' { x : f.domain | -(x : E) - y ∈ s }
    suffices (upperBounds Sn ∩ lowerBounds Sp).Nonempty by
      simpa only [Sp, Sn, Set.Nonempty, upperBounds, lowerBounds, forall_mem_image] using! this
    refine exists_between_of_forall_le (Nonempty.image f ?_) (Nonempty.image f (dense y)) ?_
    · rcases dense (-y) with ⟨x, hx⟩
      rw [← neg_neg x, NegMemClass.coe_neg, ← sub_eq_add_neg] at hx
      exact ⟨_, hx⟩
    rintro a ⟨xn, hxn, rfl⟩ b ⟨xp, hxp, rfl⟩
    have := s.add_mem hxp hxn
    rw [add_assoc, add_sub_cancel, ← sub_eq_add_neg, ← AddSubgroupClass.coe_sub] at this
    replace := nonneg _ this
    rwa [f.map_sub, sub_nonneg] at this
  refine ⟨f.supSpanSingleton y (-c) hy, ?_, ?_⟩
  · refine lt_iff_le_not_ge.2 ⟨f.left_le_sup _ _, fun H => ?_⟩
    replace H := LinearPMap.domain_mono.monotone H
    rw [LinearPMap.domain_supSpanSingleton, sup_le_iff, span_le, singleton_subset_iff] at H
    exact hy H.2
  · rintro ⟨z, hz⟩ hzs
    rcases mem_sup.1 hz with ⟨x, hx, y', hy', rfl⟩
    rcases mem_span_singleton.1 hy' with ⟨r, rfl⟩
    simp only at hzs
    rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ hx, smul_neg, ← sub_eq_add_neg, sub_nonneg]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · have : -(r⁻¹ • x) - y ∈ s := by
        rwa [← s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul, neg_neg, smul_smul,
          mul_inv_cancel₀ hr.ne, one_smul, sub_eq_add_neg, neg_smul, neg_neg]
      replace := le_c (r⁻¹ • ⟨x, hx⟩) this
      have hrR : (r : ℝ) < 0 := by exact_mod_cast hr
      simp only [f.map_smul, Rat.smul_def, Rat.cast_inv] at this
      simp only [RingHom.id_apply, Rat.smul_def]
      have h := mul_le_mul_of_nonpos_left this hrR.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hrR.ne, one_mul] using h
    · subst r
      simp only [zero_smul, add_zero] at hzs ⊢
      rw [RingHom.id_apply, zero_smul]
      apply nonneg
      exact hzs
    · have : r⁻¹ • x + y ∈ s := by
        rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      replace := c_le (r⁻¹ • ⟨x, hx⟩) this
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      simp only [f.map_smul, Rat.smul_def, Rat.cast_inv] at this
      simp only [RingHom.id_apply, Rat.smul_def]
      have h := mul_le_mul_of_nonneg_left this hrR.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hrR.ne', one_mul] using h

theorem exists_top (p : E →ₗ.[ℚ] ℝ) (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
    (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
    ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x := by
  set S := { p : E →ₗ.[ℚ] ℝ | ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x }
  have hSc : ∀ c, c ⊆ S → IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcs c_chain y hy
    clear hp_nonneg hp_dense p
    have cne : c.Nonempty := ⟨y, hy⟩
    have hcd : DirectedOn (· ≤ ·) c := c_chain.directedOn
    refine ⟨LinearPMap.sSup c hcd, ?_, fun _ ↦ LinearPMap.le_sSup hcd⟩
    rintro ⟨x, hx⟩ hxs
    have hdir : DirectedOn (· ≤ ·) (LinearPMap.domain '' c) :=
      directedOn_image.2 (hcd.mono LinearPMap.domain_mono.monotone)
    rcases (mem_sSup_of_directed (cne.image _) hdir).1 hx with ⟨_, ⟨f, hfc, rfl⟩, hfx⟩
    have : f ≤ LinearPMap.sSup c hcd := LinearPMap.le_sSup _ hfc
    convert! ← hcs hfc ⟨x, hfx⟩ hxs using 1
    exact this.2 rfl
  obtain ⟨q, hpq, hqs, hq⟩ := zorn_le_nonempty₀ S hSc p hp_nonneg
  refine ⟨q, hpq, ?_, hqs⟩
  contrapose! hq
  have hqd : ∀ y, ∃ x : q.domain, (x : E) + y ∈ s := fun y ↦
    let ⟨x, hx⟩ := hp_dense y
    ⟨Submodule.inclusion hpq.left x, hx⟩
  rcases step s q hqs hqd hq with ⟨r, hqr, hr⟩
  exact ⟨r, hr, hqr.le, fun hrq ↦ hqr.ne' <| hrq.antisymm hqr.le⟩

end RieszExtension

theorem riesz_extension (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℚ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x := by
  rcases RieszExtension.exists_top s f nonneg dense
    with ⟨⟨g_dom, g⟩, ⟨-, hfg⟩, rfl : g_dom = ⊤, hgs⟩
  refine ⟨g.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial), ?_, ?_⟩
  · exact fun x => (hfg rfl).symm
  · exact fun x hx => hgs ⟨x, _⟩ hx

end RationalRiesz
end Pureness
end

end OAI
