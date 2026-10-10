import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationCoordinates
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalRegrade
import OAI.Combinatorics.Chromatic.GradedAlgebra.BiRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance laurentCompletionRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentCompletionAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentCompletionNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma BiSupported.neg {f : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f) :
    BiSupported v Ω δ κ (-f) := by
  intro n m hm
  apply hf n m
  intro hzero
  apply hm
  change -(coeff n f m)=0
  rw [hzero,neg_zero]
def biSupportedSubring : Subring (PowerSeries (Torus v Ω)) where
  carrier:=BiSupported v Ω δ κ
  zero_mem':=BiSupported.zero v Ω δ κ
  one_mem':=BiSupported.one v Ω δ κ
  add_mem':=BiSupported.add v Ω δ κ
  mul_mem':=BiSupported.mul v Ω δ κ
  neg_mem':=BiSupported.neg v Ω δ κ
lemma biRegrade_zero : biRegrade v Ω δ κ 0=0 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  simp only [biRegrade_coeff, _root_.map_zero]
def biRegradeHom : biSupportedSubring v Ω δ κ →+* PowerSeries (PowerSeries (Torus v Ω)) where
  toFun f:=biRegrade v Ω δ κ f.val
  map_zero':=biRegrade_zero v Ω δ κ
  map_one':=biRegrade_one v Ω δ κ
  map_add' f g:=biRegrade_add v Ω δ κ f.val g.val
  map_mul' f g:=biRegrade_mul v Ω δ κ f.property g.property

def oldLaurent (f : PowerSeries (Torus v Ω)) : PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  PowerSeries.map (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) (biRegrade v Ω δ κ f)
def oldLaurentHom : biSupportedSubring v Ω δ κ →+* PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  (PowerSeries.map (HahnSeries.ofPowerSeries ℤ (Torus v Ω))).comp (biRegradeHom v Ω δ κ)
lemma oldLaurent_mul {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g) :
    oldLaurent v Ω δ κ (f*g)=oldLaurent v Ω δ κ f*oldLaurent v Ω δ κ g := by
  unfold oldLaurent
  rw [biRegrade_mul v Ω δ κ hf hg,map_mul]
lemma oldLaurent_injective {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g)
    (he : oldLaurent v Ω δ κ f=oldLaurent v Ω δ κ g) : f=g := by
  apply biRegrade_injective v Ω δ κ hf hg
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ofPowerSeries_injective (Γ:=ℤ)
  have H:=congrArg (PowerSeries.coeff d) he
  simpa only [oldLaurent,PowerSeries.coeff_map] using H
lemma oldLaurent_read (f : PowerSeries (Torus v Ω)) (d e : ℕ) (m : M)
    (hd : δ m=(d:ℤ)) (he : κ m=(e:ℤ)) :
    (PowerSeries.coeff d (oldLaurent v Ω δ κ f)).coeff (e:ℤ) m=PowerSeries.coeff (d+e) f m := by
  rw [oldLaurent,PowerSeries.coeff_map,HahnSeries.ofPowerSeries_apply_coeff]
  exact biRegrade_read v Ω δ κ f d e m hd he

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
def pureDegree : M →+ ℤ where
  toFun m:=coord m pc
  map_zero':=by simp
  map_add' a b:=by simp
include hcoord in
lemma completed_biSupported (f : CompletedPositive v Ω C) :
    BiSupported v Ω (nonpDegree coord pc) (pureDegree coord pc) f.val := by
  intro n m hm
  have hr : HasRootDegree C n m:=by
    by_contra hh
    exact hm (f.property.2 n m hh)
  have hn:=nonpDegree_root_nonneg C coord hcoord pc hr
  have he:=nonpDegree_root_eq C coord hcoord pc hr
  obtain ⟨d,hd,hc,hC⟩:=root_coordinates C coord hcoord hr
  exact ⟨hn,by change 0≤coord m pc; rw [hc]; positivity,he.symm⟩
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance laurentExpansionRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentExpansionAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentExpansionAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentExpansionNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentExpansionNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma expand_embed_coeff (f : Torus v Ω) (n : ℤ) (m : M) :
    ((expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp f)).coeff n) m=
      if n=k m then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>
    simp only [map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single l a=>
    change ((expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp (Torus.monomial v Ω l a))).coeff n) m=_
    rw [expansion_embed_monomial,HahnSeries.coeff_single]
    by_cases hl : l=m
    · subst l; split_ifs <;> rfl
    · by_cases hn : n=k l
      · rw [ite_eq_left hn]
        simp [Torus.monomial,Finsupp.single_eq_of_ne (Ne.symm hl)]
      · rw [ite_eq_right hn]
        simp [Finsupp.single_eq_of_ne (Ne.symm hl)]
lemma hahn_power_negative (f : PowerSeries (Torus v Ω)) (n : ℤ) (hn : n<0) :
    (HahnSeries.ofPowerSeries ℤ (Torus v Ω) f).coeff n=0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨a,ha⟩
  change (a:ℤ)=n at ha
  omega
variable (δ : M →+ ℤ) (B : ℕ)
lemma regrade_eval_vanish (f : PowerSeries (Torus v Ω)) (d : ℕ) (m : M)
    (hz : ∀n,PowerSeries.coeff n f m=0) : PowerSeries.coeff d (regrade v Ω δ B f) m=0 := by
  rw [regrade_coeff_eval]
  simp [hz]
lemma regrade_expand_nat {f : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ k f) (hb : RegradeBound v Ω δ B f) (d e : ℕ) (m : M) :
    ((expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp (PowerSeries.coeff d (regrade v Ω δ B f)))).coeff (e:ℤ)) m=
      PowerSeries.coeff e (PowerSeries.coeff d (biRegrade v Ω δ k f)) m := by
  rw [expand_embed_coeff,biRegrade_coeff,biHomogenize_coeff]
  by_cases hδ : 0≤δ m
  · by_cases hk : 0≤k m
    · have hd : ((δ m).toNat:ℤ)=δ m:=Int.toNat_of_nonneg hδ
      have he : ((k m).toNat:ℤ)=k m:=Int.toNat_of_nonneg hk
      by_cases hD : d=(δ m).toNat
      · by_cases hE : e=(k m).toNat
        · have Hk : (e:ℤ)=k m:=by omega
          rw [ite_eq_left Hk,ite_eq_left ⟨hD,hE⟩]
          have Hτ : FullHomogeneous v Ω (δ+k) f:=by
            intro n m hm
            exact (hf n m hm).2.2.symm
          simpa only [hD] using (regrade_read v Ω δ B (δ+k) hb Hτ (d+e) m (by
            change δ m+k m=((d+e:ℕ):ℤ)
            rw [Nat.cast_add]
            omega))
        · have Hk : (e:ℤ)≠k m:=by omega
          rw [ite_eq_right Hk,ite_eq_right (by tauto)]
      · rw [ite_eq_right (by tauto : ¬(d=(δ m).toNat ∧ e=(k m).toNat))]
        rw [regrade_coeff_eval,ite_eq_right hD]
        split_ifs <;> rfl
    · have hz : ∀j,PowerSeries.coeff j f m=0:=by
        intro j; by_contra H; exact hk (hf j m H).2.1
      rw [regrade_eval_vanish v Ω δ B f d m hz,hz]
      split_ifs <;> rfl
  · have hz : ∀j,PowerSeries.coeff j f m=0:=by
      intro j; by_contra H; exact hδ (hf j m H).1
    rw [regrade_eval_vanish v Ω δ B f d m hz,hz]
    split_ifs <;> rfl
lemma rational_old_square {f : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ k f) (hb : RegradeBound v Ω δ B f) :
    PowerSeries.map (expandFiber v Ω hΩ k p)
      (rationalRegrade v Ω hΩ k p hp δ B f)=oldLaurent v Ω δ k f := by
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext n
  apply Finsupp.ext
  intro m
  simp only [rationalRegrade,oldLaurent,PowerSeries.coeff_map]
  rcases le_or_gt 0 n with hn|hn
  · lift n to ℕ using hn with e he
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact regrade_expand_nat v Ω hΩ k p hp δ B hf hb d e m
  · rw [hahn_power_negative v Ω _ n hn,expand_embed_coeff]
    by_cases he : n=k m
    · rw [ite_eq_left he]
      apply regrade_eval_vanish
      intro j
      by_contra H
      have HH:=(hf j m H).2.1
      omega
    · rw [ite_eq_right he]
      rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
