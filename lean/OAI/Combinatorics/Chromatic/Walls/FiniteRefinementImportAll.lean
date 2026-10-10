import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationSimpleIncoming
import OAI.Combinatorics.Chromatic.Walls.ComparisonLine
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentBiTruncation

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma finite_refinement_import
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (D : ℕ) (l : List (ComparisonCrossing v Ω δ k B))
    (href : ∀N,∃l',WordRefines v Ω δ k B D l l' ∧ ∀n≤N,
      coeff n (comparisonWordOld v Ω hΩ δ k p hp hδ B l').val.val=coeff n 1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    coeff D (comparisonWordAction v Ω hΩ δ k p hp B l f)=coeff D f := by
  apply expandFiber_injective v Ω hΩ k p hp
  apply HahnSeries.ext
  funext z
  obtain ⟨N,hN⟩:=BiTruncation.inner_eventually
    (PowerSeries.map (expandFiber v Ω hΩ k p) f) D z
  obtain ⟨l',hR,hloop⟩:=href N
  rw [hR.action v Ω hΩ δ k p hp B f f (fun _ _=>rfl) D le_rfl]
  have HW:=congrArg (fun a : PowerSeries (HahnSeries ℤ (Torus v Ω))=>(coeff D a).coeff z)
    (comparisonWord_expansion v Ω hΩ δ k p hp hδ B hq l' f)
  simp only [coeff_map] at HW
  rw [HW]
  let u:=comparisonWordOld v Ω hΩ δ k p hp hδ B l'
  have HU : BiTruncation.Through N (biRegrade v Ω δ k u.val.val) 1 := by
    simpa only [biRegrade_one] using biRegrade_through v Ω δ k N hloop
  have HI : BiTruncation.Through N (biRegrade v Ω δ k u.inv.val) 1 := by
    simpa [biRegrade_one] using biRegrade_through v Ω δ k N
      (oldUnit_inverse_congr v Ω δ k u 1 N hloop)
  have HE:=hN _ _ HU HI
  change (coeff D (oldLaurent v Ω δ k u.val.val*
    PowerSeries.map (expandFiber v Ω hΩ k p) f*oldLaurent v Ω δ k u.inv.val)).coeff z=_
  simpa only [oldLaurent,coeff_map] using HE

lemma all_finite_refinements_import
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (l : List (ComparisonCrossing v Ω δ k B))
    (href : ∀D N,∃l',WordRefines v Ω δ k B D l l' ∧ ∀n≤N,
      coeff n (comparisonWordOld v Ω hΩ δ k p hp hδ B l').val.val=coeff n 1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    comparisonWordAction v Ω hΩ δ k p hp B l f=f := by
  apply PowerSeries.ext
  intro D
  exact finite_refinement_import v Ω hΩ δ k p hp hδ B hq D l (href D) f
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def actualLineWord (lo hi : ℝ) (N : ℕ) :
    List (ComparisonCrossing LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1)) :=
  (intervalEventList C e v k lo hi N).map
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H)

lemma actualLineWord_refines (lo hi : ℝ) (D A N : ℕ)
    (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) (hAN : A≤N) :
    WordRefines LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) D
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi A)
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N) := by
  classical
  unfold actualLineWord
  rw [←intervalEventList_filter C e v k lo hi hAN]
  apply filter_word_refines
  intro a ha hn
  have hnot : a∉intervalLineEvents C e v k lo hi A:=of_decide_eq_false hn
  exact (actualLineLetter_high Ω C coord hcoord pc e he S hS hcomp L hdeg v k H
    a A hA (event_not_retained C e v k lo hi a ha hnot)).mono _ _ _ _ _ hDA

lemma actualLineWord_refinements (lo hi : ℝ) (D : ℕ) :
    ∀N,WordRefines LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) D
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi
        (max 1 ((mutationSize Ω C pc+1)*D)))
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi
        (max N (max 1 ((mutationSize Ω C pc+1)*D)))) := by
  intro N
  exact actualLineWord_refines Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi
    D _ _ (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {A : Type*} [Ring A]
def orientPowerSeries (forward : Bool) (f : PowerSeries A) : PowerSeries A :=
  if forward then f else PowerSeries.invOfUnit f 1
lemma orientPowerSeries_trivial (forward : Bool) (f : PowerSeries A) (N : ℕ)
    (hf : ∀n≤N,coeff n f=coeff n 1) :
    ∀n≤N,coeff n (orientPowerSeries forward f)=coeff n 1 := by
  cases forward
  · have hi : PowerSeries.invOfUnit (1 : PowerSeries A) 1=1 := by
      simpa only [mul_one] using (PowerSeries.invOfUnit_mul (1 : PowerSeries A) 1 (by simp))
    simpa only [orientPowerSeries,Bool.false_eq_true,ite_false,hi] using
      PowerSeriesAdjoint.inverse_coeff_congr f 1 N hf
  · exact hf

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def mutatedLineFactor (a : ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) := by
  classical
  exact if ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k then
    if (k+a • v) (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
    else
      let data:=lineRayData C e he L hdeg v k H a ha
      let pos:=decide (0<(k+a • v) (e (simpleRoot C pc)))
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (orientPowerSeries (decide (v (e data.root)<0))
          (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e)
            (simpleTotalTransport Ω C)).val)
  else 1

lemma mutatedLineFactor_high (D N : ℕ) (hN : 1≤N)
    (hDN : (mutationSize Ω C pc+1)*D≤N) (a : ℝ)
    (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    ∀n≤D,coeff n (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)=coeff n 1 := by
  classical
  unfold mutatedLineFactor
  split
  · next hevent=>
    split
    · next hp=>
      exact False.elim (ha (lineEvents_mono (realRootsThrough_mono C e hN) v k
        (RationalFiber.line_cut_event C pc e L hdeg v k H a hp)))
    · have hf:=line_chart_trivial C e L hdeg LaurentRay.vUnit Ω (simpleTotalTransport Ω C) N v k (H N) a ha
      intro n hn
      rw [←mutationCompletion_one Ω hΩ C coord pc _ LaurentRay.vUnit]
      exact mutationCompletion_congr_through Ω hΩ C coord pc _ LaurentRay.vUnit _ _ n N
        ((Nat.mul_le_mul_left _ hn).trans hDN) (orientPowerSeries_trivial _ _ N hf)
  · exact fun _ _=>rfl

def mutatedLineProduct (lo hi : ℝ) (N : ℕ) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  ((intervalEventList C e v k lo hi N).map (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)).prod
end
end ElementaryPositivity.QuantumTorus

end

end OAI
