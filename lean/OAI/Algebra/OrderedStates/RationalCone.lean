/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Rat
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.DivisibleHull

namespace OAI

noncomputable section

/-! Rational cones and extension of positive states on ordered groups. -/

namespace Kaplansky

section
variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Positive fractions in the rational hull. A positive numerator may be
chosen after multiplying numerator and denominator; no unperforation of G
is assumed. -/
def orderedGroupRationalCone : PointedCone ℚ (DivisibleHull G) where
  carrier := {x | ∃ g : G, ∃ d : ℕ+, 0 ≤ g ∧ DivisibleHull.mk g d = x}
  zero_mem' := ⟨0,1,le_rfl,by simp⟩
  add_mem' := by
    rintro _ _ ⟨g,d,hg,rfl⟩ ⟨h,e,hh,rfl⟩
    exact ⟨e.val • g+d.val • h,d*e,
      add_nonneg (nsmul_nonneg hg _) (nsmul_nonneg hh _),DivisibleHull.mk_add_mk.symm⟩
  smul_mem' := by
    rintro ⟨q,hq⟩ _ ⟨g,d,hg,rfl⟩
    refine ⟨q.num • g,⟨q.den,q.den_pos⟩*d,?_,?_⟩
    · exact zsmul_nonneg hg (Rat.num_nonneg.mpr hq)
    · exact (DivisibleHull.qsmul_mk q g d).symm

theorem orderedGroupRationalCone_coe {g : G} (hg : 0 ≤ g) :
    (g : DivisibleHull G) ∈ orderedGroupRationalCone := ⟨g,1,hg,rfl⟩

/-- A unit with no nonpositive positive multiple stays outside the
negative of the rational cone, even if the group has torsion elsewhere. -/
theorem orderedGroupRationalCone_neg_unit (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) :
    -(u : DivisibleHull G) ∉ orderedGroupRationalCone := by
  rintro ⟨g,d,hg,he⟩
  change DivisibleHull.mk g d = -DivisibleHull.mk u 1 at he
  rw [DivisibleHull.neg_mk] at he
  obtain ⟨k,hk⟩ := DivisibleHull.mk_eq_mk.mp he
  simp only [PNat.val_ofNat, one_nsmul, smul_neg, smul_smul] at hk
  have hp : 0 ≤ -((k.val*d.val) • u) := by
    rw [← hk]
    exact nsmul_nonneg hg _
  exact hu (k.val*d.val) (Nat.mul_pos k.pos d.pos) (neg_nonneg.mp hp)

theorem orderedGroupRationalCone_unit_ne_zero (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) : (u : DivisibleHull G) ≠ 0 := by
  intro h
  apply orderedGroupRationalCone_neg_unit u hu
  rw [h, neg_zero]
  exact (orderedGroupRationalCone (G := G)).zero_mem

/-- Nonnegativity along the rational unit ray is reflected in its scalar. -/
theorem orderedGroupRationalCone_unit_scalar (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) {q : ℚ}
    (hq : q • (u : DivisibleHull G) ∈ orderedGroupRationalCone) : 0 ≤ q := by
  by_contra h
  have hn : q < 0 := lt_of_not_ge h
  have hp : 0 < -q⁻¹ := neg_pos.mpr (inv_neg''.mpr hn)
  have hc := (orderedGroupRationalCone (G := G)).smul_mem hp.le hq
  rw [smul_smul, neg_mul, inv_mul_cancel₀ hn.ne, neg_one_smul] at hc
  exact orderedGroupRationalCone_neg_unit u hu hc

/-- An order unit in G dominates every rational fraction after passage
to the cone. The dominating vector is an integer multiple of the unit. -/
theorem orderedGroupRationalCone_cofinal (u : G) (hu : 0 ≤ u)
    (hb : ∀ g : G, ∃ N : ℕ, -(N • u) ≤ g) (x : DivisibleHull G) :
    ∃ N : ℕ, (N : ℚ) • (u : DivisibleHull G) + x ∈ orderedGroupRationalCone := by
  induction x using DivisibleHull.ind with | mk g d =>
  obtain ⟨N,hN⟩ := hb g
  refine ⟨N, ?_⟩
  have hunit : N • u ≤ d.val • (N • u) := by
    simpa only [one_nsmul] using
      nsmul_le_nsmul_left (nsmul_nonneg hu N) (Nat.one_le_iff_ne_zero.mpr d.ne_zero)
  have hnon : 0 ≤ d.val • (N • u)+g := by
    have h := (neg_le_neg hunit).trans hN
    simpa only [add_comm] using neg_le_iff_add_nonneg.mp h
  refine ⟨d.val • (N • u)+g,d,hnon,?_⟩
  rw [Nat.cast_smul_eq_nsmul ℚ N, DivisibleHull.coe, DivisibleHull.nsmul_mk,
    DivisibleHull.mk_add_mk]
  simp

end

section
open Set LinearMap
variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis

The Riesz extension declarations below are adapted from Mathlib.Analysis.Convex.Cone.Extension.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Convex/Cone/Extension.lean

This code has been modified.
-/

namespace RationalRieszExtension

open Submodule

variable (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)

/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain → ℝ`, assume that `f` is nonnegative on `f.domain ∩ p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
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
      have hm := smul_le_smul_of_nonpos_left this hr.le
      simpa only [f.map_smul, RingHom.id_apply, smul_smul, mul_inv_cancel₀ hr.ne, one_smul] using hm
    · subst r
      simp only [zero_smul, add_zero] at hzs ⊢
      rw [RingHom.id_apply, zero_smul]
      apply nonneg
      exact hzs
    · have : r⁻¹ • x + y ∈ s := by
        rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      replace := c_le (r⁻¹ • ⟨x, hx⟩) this
      have hm := smul_le_smul_of_nonneg_left this hr.le
      simpa only [f.map_smul, RingHom.id_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hm

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

end RationalRieszExtension

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p → ℝ`, assume that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then
there exists a globally defined linear function `g : E → ℝ` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem rational_riesz_extension (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℚ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x := by
  rcases RationalRieszExtension.exists_top s f nonneg dense
    with ⟨⟨g_dom, g⟩, ⟨-, hfg⟩, rfl : g_dom = ⊤, hgs⟩
  refine ⟨g.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial), ?_, ?_⟩
  · exact fun x => (hfg rfl).symm
  · exact fun x hx => hgs ⟨x, _⟩ hx

end

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- A normalized monotone real-valued additive state on an ordered group
with an order unit. Positive unit multiples must not be nonpositive.
Neither linear order nor unperforation of the group is assumed. -/
theorem orderedGroup_normalized_state (u : G) (hu : 0 ≤ u)
    (hn : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0)
    (hb : ∀ g : G, ∃ N : ℕ, -(N • u) ≤ g) :
    ∃ f : G →+ ℝ, Monotone f ∧ f u = 1 := by
  let v : DivisibleHull G := u
  have hv : v ≠ 0 := orderedGroupRationalCone_unit_ne_zero u hn
  let p : DivisibleHull G →ₗ.[ℚ] ℝ := LinearPMap.mkSpanSingleton v 1 hv
  have hp : ∀ x : p.domain, (x : DivisibleHull G) ∈ orderedGroupRationalCone → 0 ≤ p x := by
    rintro ⟨x,hx⟩ hxc
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hq : 0 ≤ q := orderedGroupRationalCone_unit_scalar u hn hxc
    change 0 ≤ LinearPMap.mkSpanSingleton' v (1 : ℝ) _ ⟨q • v, _⟩
    rw [LinearPMap.mkSpanSingleton'_apply]
    simpa using (smul_nonneg hq (zero_le_one : (0 : ℝ) ≤ 1))
  have hd : ∀ y : DivisibleHull G, ∃ x : p.domain, (x : DivisibleHull G)+y ∈ orderedGroupRationalCone := by
    intro y
    obtain ⟨N,hN⟩ := orderedGroupRationalCone_cofinal u hu hb y
    exact ⟨⟨(N : ℚ) • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩,hN⟩
  obtain ⟨g,hg,hpos⟩ := rational_riesz_extension orderedGroupRationalCone p hp hd
  let f : G →+ ℝ := g.toAddMonoidHom.comp (DivisibleHull.coeAddMonoidHom G)
  have hfpos : ∀ x : G, 0 ≤ x → 0 ≤ f x := by
    intro x hx
    exact hpos _ (orderedGroupRationalCone_coe hx)
  refine ⟨f,?_,?_⟩
  · intro a b hab
    have h := hfpos (b-a) (sub_nonneg.mpr hab)
    rwa [map_sub,sub_nonneg] at h
  · have he := hg ⟨v,Submodule.mem_span_singleton_self v⟩
    change g v = 1
    rw [he]
    exact LinearPMap.mkSpanSingleton_apply ℚ ℚ hv (1 : ℝ)

end Kaplansky

end

end OAI
