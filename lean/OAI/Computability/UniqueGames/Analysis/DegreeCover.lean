import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic.Abel

namespace OAI

section

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/
namespace UniqueGamesTheorem.Appendix.DegreeCover

abbrev F2 := ZMod 2
variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

@[simp] theorem binary_add_self (v : V) : v + v = 0 := by
  have h : (1 + 1 : F2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : F2 => c • v) h

@[simp] theorem binary_neg (v : V) : -v = v := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact binary_add_self v

/-- Glue a linear map on P to zero on Q when the restrictions agree. -/
theorem exists_glue_zero (P Q : Submodule F2 W) (f : W →ₗ[F2] V)
    (cover : P ⊔ Q = ⊤) (compatible : ∀ w ∈ P, w ∈ Q → f w = 0) :
    ∃ g : W →ₗ[F2] V,
      (∀ w ∈ P, g w = f w) ∧ (∀ w ∈ Q, g w = 0) := by
  let p : W →ₗ.[F2] V := ⟨P, f.comp P.subtype⟩
  let q : W →ₗ.[F2] V := ⟨Q, 0⟩
  have hc : ∀ (x : p.domain) (y : q.domain), (x : W) = y → p x = q y := by
    intro x y hxy
    exact compatible x x.property (hxy ▸ y.property)
  let t := p.sup q hc
  have ht : ∀ w : W, w ∈ t.domain := by
    intro w
    change w ∈ P ⊔ Q
    rw [cover]
    exact Submodule.mem_top
  let inc : W →ₗ[F2] t.domain := (LinearMap.id : W →ₗ[F2] W).codRestrict t.domain ht
  refine ⟨t.toFun.comp inc, ?_, ?_⟩
  · intro w hw
    exact ((p.left_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm
  · intro w hw
    exact ((p.right_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm

private theorem binary_cross {a b c d : V} (h : a + b = c + d) : c + a = d + b := by
  calc
    c + a = (c + a) + (b + b) := by simp
    _ = c + (a + b) + b := by abel
    _ = c + (c + d) + b := by rw [h]
    _ = (c + c) + (d + b) := by abel
    _ = d + b := by simp

theorem exists_cover_component (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R : W →ₗ[F2] V,
      (∀ w ∈ LinearMap.ker Z, R w = Y w) ∧
      (∀ w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z), R w = 0) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y := by
  have cov : LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) = ⊤ := by
    simpa only [sup_assoc, sup_comm, sup_left_comm] using cover
  have compatible : ∀ w ∈ LinearMap.ker Z,
      w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z) → Y w = 0 := by
    intro w hw hz
    change Z w = 0 at hw
    rcases Submodule.mem_sup.mp hz with ⟨a, ha, b, hb, hab⟩
    change Y a = 0 at ha
    change (Y + Z) b = 0 at hb
    have hYb : Y b = Z b := by
      have h := congrArg (fun v : V => v + Z b) hb
      simpa only [LinearMap.add_apply, add_assoc, binary_add_self, add_zero, zero_add] using h
    have hYw : Y w = Z b := by rw [← hab, map_add, ha, zero_add, hYb]
    have hmem : Y w ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z :=
      ⟨⟨⟨w, by simp only [LinearMap.add_apply, hw, add_zero]⟩, ⟨w, rfl⟩⟩,
        ⟨b, hYw.symm⟩⟩
    rw [triple] at hmem
    exact hmem
  obtain ⟨R, hRZ, hRYX⟩ := exists_glue_zero (LinearMap.ker Z)
    (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) Y cov compatible
  refine ⟨R, hRZ, hRYX, ?_⟩
  rintro v ⟨w, rfl⟩
  have hw : w ∈ LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) := by
    rw [cov]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, b, hb, hab⟩
  have heq : R w = Y a := by rw [← hab, map_add, hRZ a ha, hRYX b hb, add_zero]
  refine ⟨⟨a, ?_⟩, ⟨a, heq.symm⟩⟩
  change Z a = 0 at ha
  rw [LinearMap.add_apply, ha, add_zero, heq]

/-- A general, dimension-free decomposition with pairwise disjoint images.
These are exactly the linear-algebra data used to establish the cover in A.1. -/
theorem exists_disjoint_decomposition (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Disjoint (LinearMap.range R) (LinearMap.range S) ∧
      Disjoint (LinearMap.range R) (LinearMap.range C) ∧
      Disjoint (LinearMap.range S) (LinearMap.range C) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y ∧
      LinearMap.range S ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Z ∧
      LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
  obtain ⟨R, hRZ, hRYX, rangeR⟩ := exists_cover_component Y Z triple cover
  obtain ⟨S, hSY, hSZX, rangeS⟩ := exists_cover_component Z Y
    (by simpa only [add_comm Z Y, inf_assoc, inf_comm, inf_left_comm] using triple)
    (by simpa only [add_comm Z Y, sup_assoc, sup_comm, sup_left_comm] using cover)
  rw [add_comm Z Y] at hSZX rangeS
  have eqX : Set.EqOn (R + S) (Y + Z) (LinearMap.ker (Y + Z)) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    rw [LinearMap.add_apply, hRYX w (Submodule.mem_sup_right hw), hSZX w (Submodule.mem_sup_right hw)]
    simpa only [zero_add] using hw.symm
  have eqY : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Y) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Y w = 0 at hw
    simp only [LinearMap.add_apply, hRYX w (Submodule.mem_sup_left hw), hSY w hw, hw, zero_add]
  have eqZ : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Z) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Z w = 0 at hw
    simp only [LinearMap.add_apply, hRZ w hw, hSZX w (Submodule.mem_sup_left hw), hw, add_zero]
  have hRS : R + S = Y + Z := by
    ext w
    exact LinearMap.eqOn_sup (LinearMap.eqOn_sup eqX eqY) eqZ (cover ▸ Submodule.mem_top)
  let C := Y + R
  have hC : C = Z + S := by
    ext w
    exact binary_cross (congrArg (fun f : W →ₗ[F2] V => f w) hRS)
  have hY : Y = R + C := by
    ext w
    change Y w = R w + (Y w + R w)
    rw [add_left_comm, binary_add_self, add_zero]
  have hZ : Z = S + C := by
    rw [hC]
    ext w
    change Z w = S w + (Z w + S w)
    rw [add_left_comm, binary_add_self, add_zero]
  have rangeC : LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
    apply le_inf
    · exact (LinearMap.range_add_le Y R).trans (sup_le le_rfl (rangeR.trans inf_le_right))
    · rw [hC]
      exact (LinearMap.range_add_le Z S).trans (sup_le le_rfl (rangeS.trans inf_le_right))
  have kill : ∀ v, v ∈ LinearMap.range (Y + Z) → v ∈ LinearMap.range Y →
      v ∈ LinearMap.range Z → v = 0 := by
    intro v hx hy hz
    have h : v ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z := ⟨⟨hx, hy⟩, hz⟩
    rwa [triple] at h
  refine ⟨R, S, C, hRS.symm, hY, hZ, ?_, ?_, ?_, rangeR, rangeS, rangeC⟩
  · exact Submodule.disjoint_def.mpr (fun v hr hs => kill v (rangeR hr).1 (rangeR hr).2 (rangeS hs).2)
  · exact Submodule.disjoint_def.mpr (fun v hr hc => kill v (rangeR hr).1 (rangeR hr).2 (rangeC hc).2)
  · exact Submodule.disjoint_def.mpr (fun v hs hc => kill v (rangeS hs).1 (rangeC hc).1 (rangeS hs).2)

/-- Rank additivity needs image containment as well as disjointness. -/
theorem rank_add_of_disjoint [FiniteDimensional F2 V] (R S : W →ₗ[F2] V)
    (hd : Disjoint (LinearMap.range R) (LinearMap.range S))
    (hR : LinearMap.range R ≤ LinearMap.range (R + S))
    (hS : LinearMap.range S ≤ LinearMap.range (R + S)) :
    Module.finrank F2 (LinearMap.range (R + S)) =
      Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) := by
  have heq := le_antisymm (LinearMap.range_add_le R S) (sup_le hR hS)
  rw [heq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range R) (LinearMap.range S)
  have hb : LinearMap.range R ⊓ LinearMap.range S = ⊥ := hd.eq_bot
  rw [hb, finrank_bot, add_zero] at h
  exact h

/-- The cover F(X) \ F₂(X) ⊆ F₁(X), with all three rank-additive decompositions.
There is no bound on dimension, and both bad-event exclusions are discharged. -/
theorem outside_bad_rank_cover [FiniteDimensional F2 V] (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Module.finrank F2 (LinearMap.range (Y + Z)) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) ∧
      Module.finrank F2 (LinearMap.range Y) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range C) ∧
      Module.finrank F2 (LinearMap.range Z) =
        Module.finrank F2 (LinearMap.range S) + Module.finrank F2 (LinearMap.range C) := by
  obtain ⟨R, S, C, hX, hY, hZ, dRS, dRC, dSC, rR, rS, rC⟩ :=
    exists_disjoint_decomposition Y Z triple cover
  refine ⟨R, S, C, hX, hY, hZ, ?_, ?_, ?_⟩
  · rw [hX]
    exact rank_add_of_disjoint R S dRS
      (hX ▸ rR.trans inf_le_left) (hX ▸ rS.trans inf_le_left)
  · rw [hY]
    exact rank_add_of_disjoint R C dRC
      (hY ▸ rR.trans inf_le_right) (hY ▸ rC.trans inf_le_left)
  · rw [hZ]
    exact rank_add_of_disjoint S C dSC
      (hZ ▸ rS.trans inf_le_right) (hZ ▸ rC.trans inf_le_right)

end UniqueGamesTheorem.Appendix.DegreeCover

end

end OAI
