import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SimpleIncomingElement
import OAI.Combinatorics.Chromatic.Walls.CompletedPureComparison
import OAI.Combinatorics.Chromatic.Walls.CompletedBiUnit

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
lemma laurent_shiftedElementary_zero : shiftedElementary LaurentRay.vUnit 0=
    elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ)) := by
  rw [shiftedElementary_zero,←zpow_neg_one, LaurentRay.vUnit_zpow,LaurentRay.vUnit_zpow]
  rfl
omit [Fintype I] in
include hcoord in
lemma pureDegree_simple_self : pureDegree coord pc (simpleRoot C pc)=1 := by
  change coord (simpleRoot C pc) pc=1
  rw [simpleRoot_coordinates C coord hcoord,Pi.single_eq_same]

lemma completedBiUnit_pure (h : M →+ ℝ)
    (hg : ∀N,RayGeneric C N (simpleRoot C pc) h) :
    completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
      (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C))=
    oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) := by
  apply Units.ext
  apply Subtype.ext
  change (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val=
    raySeries LaurentRay.vUnit Ω (simpleRoot C pc) (shiftedElementary LaurentRay.vUnit 0)
  rw [laurent_shiftedElementary_zero]
  apply PowerSeries.ext
  intro n
  exact pure_simple_wall Ω C coord hcoord pc hΩ n h (hg n) n le_rfl
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.BiTruncation
open PowerSeries
variable {R : Type*} [Semiring R]
def Through (N : ℕ) (f g : PowerSeries (PowerSeries R)) : Prop :=
  ∀d e,d+e≤N → coeff e (coeff d f)=coeff e (coeff d g)
lemma Through.refl (N : ℕ) (f : PowerSeries (PowerSeries R)) : Through N f f := by
  intro d e h; rfl
lemma Through.symm {N : ℕ} {f g : PowerSeries (PowerSeries R)} (h : Through N f g) :
    Through N g f := by intro d e he; exact (h d e he).symm
lemma Through.trans {N : ℕ} {f g h : PowerSeries (PowerSeries R)}
    (hfg : Through N f g) (hgh : Through N g h) : Through N f h := by
  intro d e he; exact (hfg d e he).trans (hgh d e he)
lemma Through.mul {N : ℕ} {f f' g g' : PowerSeries (PowerSeries R)}
    (hf : Through N f f') (hg : Through N g g') : Through N (f*g) (f'*g') := by
  intro d e hde
  simp only [coeff_mul,map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro kl hkl
  have H1:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have H2:=Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rw [hf ij.1 kl.1 (by omega),hg ij.2 kl.2 (by omega)]
lemma Through.conjugate {N : ℕ} {u w : PowerSeries (PowerSeries R)}
    (hu : Through N u 1) (hw : Through N w 1) (f : PowerSeries (PowerSeries R)) :
    Through N (u*f*w) f := by
  simpa only [one_mul,mul_one] using (hu.mul (Through.refl N f)).mul hw
lemma ext {f g : PowerSeries (PowerSeries R)} (h : ∀N,Through N f g) : f=g := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  exact h (d+e) d e le_rfl
end ElementaryPositivity.BiTruncation

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries BiTruncation
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance biThroughRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance biThroughAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance biThroughAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance biThroughNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance biThroughNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma biRegrade_through {f g : PowerSeries (Torus v Ω)} (N : ℕ)
    (h : ∀n≤N,coeff n f=coeff n g) :
    Through N (biRegrade v Ω δ κ f) (biRegrade v Ω δ κ g) := by
  intro d e he
  rw [biRegrade_coeff,biRegrade_coeff,h (d+e) he]
lemma oldLaurent_through {f g : PowerSeries (Torus v Ω)} (N : ℕ)
    (h : ∀n≤N,coeff n f=coeff n g) (d e : ℕ) (he : d+e≤N) :
    (coeff d (oldLaurent v Ω δ κ f)).coeff (e:ℤ)=
      (coeff d (oldLaurent v Ω δ κ g)).coeff (e:ℤ) := by
  simp only [oldLaurent,coeff_map,HahnSeries.ofPowerSeries_apply_coeff]
  exact biRegrade_through v Ω δ κ N h d e he
lemma oldLaurent_inner_through (u : (biSupportedSubring v Ω δ κ)ˣ) (N : ℕ)
    (hv : ∀n≤N,coeff n u.val.val=coeff n 1)
    (hi : ∀n≤N,coeff n u.inv.val=coeff n 1)
    (f : PowerSeries (PowerSeries (Torus v Ω))) (d e : ℕ) (he : d+e≤N) :
    (coeff d (oldLaurent v Ω δ κ u.val.val*
      PowerSeries.map (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) f*
      oldLaurent v Ω δ κ u.inv.val)).coeff (e:ℤ)=coeff e (coeff d f) := by
  have H:=Through.conjugate
    (show Through N (biRegrade v Ω δ κ u.val.val) 1 by
      simpa only [biRegrade_one] using biRegrade_through v Ω δ κ N hv)
    (show Through N (biRegrade v Ω δ κ u.inv.val) 1 by
      simpa only [biRegrade_one] using biRegrade_through v Ω δ κ N hi) f d e he
  unfold oldLaurent
  rw [←map_mul,←map_mul,coeff_map,HahnSeries.ofPowerSeries_apply_coeff]
  exact H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
local instance rationalThroughRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalThroughAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rationalThroughAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance rationalThroughNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalThroughNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma regrade_congr_through (D : ℕ) {f g : PowerSeries (Torus v Ω)}
    (he : ∀n≤B*D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (regrade v Ω δ B f)=coeff d (regrade v Ω δ B g) := by
  intro d hd
  rw [regrade_coeff,regrade_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [he n (by have H:=Finset.mem_range.mp hn; have HH:=Nat.mul_le_mul_left B hd; omega)]
lemma rationalRegrade_congr_through (D : ℕ) {f g : PowerSeries (Torus v Ω)}
    (he : ∀n≤B*D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (rationalRegrade v Ω hΩ k p hp δ B f)=
      coeff d (rationalRegrade v Ω hΩ k p hp δ B g) := by
  intro d hd
  simp only [rationalRegrade,coeff_map]
  rw [regrade_congr_through v Ω δ B D he d hd]
lemma oldUnit_inverse_congr (u w : (biSupportedSubring v Ω δ k)ˣ) (N : ℕ)
    (h : ∀n≤N,coeff n u.val.val=coeff n w.val.val) :
    ∀n≤N,coeff n u.inv.val=coeff n w.inv.val := by
  intro n hn
  have HE:=FormalLog.mul_coeff_congr u.inv.val (u.val.val*w.inv.val)
    u.inv.val (w.val.val*w.inv.val) n (fun _ _=>rfl) (by
      intro j hj
      exact FormalLog.mul_coeff_congr _ _ _ _ j (fun t ht=>h t (ht.trans (hj.trans hn))) (fun _ _=>rfl))
  have hu : u.inv.val*u.val.val=1:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) u.inv_val
  have hw : w.val.val*w.inv.val=1:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) w.val_inv
  rw [←mul_assoc,hu,one_mul,hw,mul_one] at HE
  exact HE.symm
lemma innerHom_coeff_congr {A : Type*} [Ring A] (u w : (PowerSeries A)ˣ)
    (f g : PowerSeries A) (N : ℕ)
    (hv : ∀n≤N,coeff n u.val=coeff n w.val)
    (hi : ∀n≤N,coeff n u.inv=coeff n w.inv)
    (hf : ∀n≤N,coeff n f=coeff n g) :
    coeff N (innerHom u f)=coeff N (innerHom w g) := by
  change coeff N (u.val*f*u.inv)=coeff N (w.val*g*w.inv)
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact FormalLog.mul_coeff_congr _ _ _ _ j (fun t ht=>hv t (ht.trans hj))
      (fun t ht=>hf t (ht.trans hj))
  · exact hi
lemma comparisonAction_input_congr (c : ComparisonCrossing v Ω δ k B)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (N : ℕ) (hg : ∀n≤N,coeff n f=coeff n g) :
    coeff N (comparisonAction v Ω hΩ δ k p hp B c f)=
      coeff N (comparisonAction v Ω hΩ δ k p hp B c g) := by
  cases c with
  | bounded u hf hi=>exact innerHom_coeff_congr _ _ _ _ N (fun _ _=>rfl) (fun _ _=>rfl) hg
  | pure b=>
    cases b
    · change coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).symm.toRingHom f)=
        coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).symm.toRingHom g)
      rw [coeff_map,coeff_map,hg N le_rfl]
    · change coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom f)=
        coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom g)
      rw [coeff_map,coeff_map,hg N le_rfl]
lemma bounded_action_congr (D : ℕ) (u w : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (hf' : RegradeBound v Ω δ B w.val.val) (hi' : RegradeBound v Ω δ B w.inv.val)
    (he : ∀n≤B*D,coeff n u.val.val=coeff n w.val.val)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (hg : ∀n≤D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded u hf hi) f)=
      coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded w hf' hi') g) := by
  intro d hd
  apply innerHom_coeff_congr
  · intro n hn
    exact rationalRegrade_congr_through v Ω hΩ δ k p hp B D he n (hn.trans hd)
  · intro n hn
    exact rationalRegrade_congr_through v Ω hΩ δ k p hp B D
      (oldUnit_inverse_congr v Ω δ k u w (B*D) he) n (hn.trans hd)
  · exact fun n hn=>hg n (hn.trans hd)
end
end ElementaryPositivity.RationalFiber

end

end OAI
