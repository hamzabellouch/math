import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance mutationSimpleIncomingRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationSimpleIncomingAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance mutationSimpleIncomingAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma regrade_homogeneous_identity (δ : M →+ ℤ) (B : ℕ) (f : PowerSeries (Torus v Ω))
    (hf : FullHomogeneous v Ω δ f) : regrade v Ω δ (B+1) f=f := by
  classical
  apply PowerSeries.ext
  intro d
  ext m
  rw [regrade_coeff_eval]
  by_cases hd : d=(δ m).toNat
  · rw [ite_eq_left hd]
    apply Finset.sum_eq_single d
    · intro n hn hnd
      by_contra hnz
      have H:=hf n m hnz
      rw [H,Int.toNat_natCast] at hd
      exact hnd hd.symm
    · intro hn
      have hb : d<(B+1)*d+1:=by nlinarith
      exact (hn (Finset.mem_range.mpr hb)).elim
  · rw [ite_eq_right hd]
    by_contra HH
    have H:=hf d m (Ne.symm HH)
    rw [H,Int.toNat_natCast] at hd
    exact hd rfl

lemma normalizedSimple_homogeneous (δ : M →+ ℤ) (r : M) (hr : δ r=1) :
    FullHomogeneous LaurentRay.vUnit Ω δ (normalizedSimple Ω r) := by
  intro n m hm
  have he : m=n • r:=by
    by_contra hh
    apply hm
    rw [normalizedSimple,coeff_raySeries]
    exact Finsupp.single_eq_of_ne hh
  subst m
  rw [map_nsmul,hr,nsmul_eq_mul,mul_one]

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (hΩ : ∀m,Ω m m=0) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
lemma mutation_incoming_simple_image (i : I) (hi : i≠pc) :
    mutationLinearPiece Ω C pc (decide (0≤ mutationPairing Ω C pc i)) (simpleRoot C i)=
      simpleRoot (mutatedRoots Ω C pc) i := by
  rw [mutatedRoot_off Ω C pc i hi]
  by_cases ha : 0≤ mutationPairing Ω C pc i
  · simp only [ha,decide_true,mutationLinearPiece,ite_true,max_eq_left (by omega : -mutationPairing Ω C pc i≤0),zero_zsmul,add_zero,AddMonoidHom.id_apply]
  · have ha' : 0≤ -mutationPairing Ω C pc i:=by omega
    simp only [ha,decide_false,mutationLinearPiece,Bool.false_eq_true,ite_false,max_eq_right ha']
    change simpleRoot C i-Ω (simpleRoot C pc) (simpleRoot C i) • simpleRoot C pc=
      simpleRoot C i+(-Ω (simpleRoot C pc) (simpleRoot C i)) • simpleRoot C pc
    rw [neg_zsmul,sub_eq_add_neg]

include hcoord in
lemma mutation_incoming_simple_order (i : I) (hi : i≠pc) :
    mutationNewOrder Ω C coord pc (decide (0≤ mutationPairing Ω C pc i)) (simpleRoot C i)=1 := by
  apply mutationNewOrder_of_root Ω C coord hcoord
  rw [mutation_incoming_simple_image Ω C pc i hi]
  exact simpleRoot_degree (mutatedRoots Ω C pc) i

omit [Fintype I] in
lemma mutation_push_normalizedSimple (pos : Bool) (r : M) :
    PowerSeries.map (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit) (normalizedSimple Ω r)=
      normalizedSimple Ω (mutationLinearPiece Ω C pc pos r) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_map,normalizedSimple,coeff_raySeries,normalizedSimple,coeff_raySeries]
  change Torus.push LaurentRay.vUnit Ω Ω (mutationLinearPiece Ω C pc pos) _ (Torus.monomial _ _ _ _)=_
  rw [Torus.push_monomial,map_nsmul]

include hcoord in
theorem mutation_normalized_incoming_simple (i : I) (hi : i≠pc) :
    mutationCompletion Ω hΩ C coord pc (decide (0≤ mutationPairing Ω C pc i)) LaurentRay.vUnit
      (normalizedSimple Ω (simpleRoot C i))=
    normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) i) := by
  rw [mutationCompletion,regrade_homogeneous_identity]
  · rw [mutation_push_normalizedSimple,mutation_incoming_simple_image Ω C pc i hi]
  · exact normalizedSimple_homogeneous Ω _ _ (mutation_incoming_simple_order Ω C coord hcoord pc i hi)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)
lemma mutation_side_simple_image (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0) :
    mutationLinearPiece Ω C pc pos (simpleRoot C i)=simpleRoot (mutatedRoots Ω C pc) i := by
  rw [mutatedRoot_off Ω C pc i hi]
  cases pos
  · change mutationPairing Ω C pc i≤0 at hside
    rw [max_eq_right (by omega : 0≤ -mutationPairing Ω C pc i)]
    change simpleRoot C i-Ω (simpleRoot C pc) (simpleRoot C i) • simpleRoot C pc=
      simpleRoot C i+(-Ω (simpleRoot C pc) (simpleRoot C i)) • simpleRoot C pc
    rw [neg_zsmul,sub_eq_add_neg]
  · change 0≤ mutationPairing Ω C pc i at hside
    rw [max_eq_left (by omega : -mutationPairing Ω C pc i≤0),zero_zsmul,add_zero]
    rfl

include hcoord in
lemma mutation_side_simple_order (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0) :
    mutationNewOrder Ω C coord pc pos (simpleRoot C i)=1 := by
  apply mutationNewOrder_of_root Ω C coord hcoord
  rw [mutation_side_simple_image Ω C pc pos i hi hside]
  exact simpleRoot_degree (mutatedRoots Ω C pc) i

include hcoord in
lemma mutation_normalized_simple_side (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (normalizedSimple Ω (simpleRoot C i))=
      normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) i) := by
  rw [mutationCompletion,regrade_homogeneous_identity]
  · rw [mutation_push_normalizedSimple,mutation_side_simple_image Ω C pc pos i hi hside]
  · exact normalizedSimple_homogeneous Ω _ _ (mutation_side_simple_order Ω C coord hcoord pc pos i hi hside)

variable {R : Type*} [CommRing R] (v : Rˣ)
local instance mutationSimpleSideRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationSimpleSideAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance mutationSimpleSideAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma mutationCompletion_congr_through (f g : PowerSeries (Torus v Ω)) (d N : ℕ)
    (hd : (mutationSize Ω C pc+1)*d≤N) (hfg : ∀n≤N,coeff n f=coeff n g) :
    coeff d (mutationCompletion Ω hΩ C coord pc pos v f)=
      coeff d (mutationCompletion Ω hΩ C coord pc pos v g) := by
  rw [mutationCompletion,mutationCompletion,coeff_map,coeff_map,regrade_coeff,regrade_coeff]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [hfg n (by have HH:=Finset.mem_range.mp hn; omega)]

include hcoord in
lemma actual_simple_wall_mutation_through (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0)
    (h : M →+ ℝ) (d : ℕ)
    (hg : RayGeneric C ((mutationSize Ω C pc+1)*d) (simpleRoot C i) h) :
    coeff d (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
      (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val)=
    coeff d (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) i)) := by
  rw [←mutation_normalized_simple_side Ω hΩ C coord hcoord pc pos i hi hside]
  exact mutationCompletion_congr_through Ω hΩ C coord pc pos LaurentRay.vUnit _ _ d _ le_rfl
    (pure_simple_wall Ω C coord hcoord i hΩ _ h hg)

include hcoord in
lemma actual_simple_wall_mutation (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0)
    (h : M →+ ℝ) (hg : ∀N,RayGeneric C N (simpleRoot C i) h) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
      (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val=
    normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) i) := by
  apply PowerSeries.ext
  intro d
  exact actual_simple_wall_mutation_through Ω hΩ C coord hcoord pc pos i hi hside h d (hg _)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
