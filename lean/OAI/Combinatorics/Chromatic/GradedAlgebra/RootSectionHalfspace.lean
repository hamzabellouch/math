import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HalfspacePolynomialCoefficients

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
local instance rootSectionHalfspaceRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance rootSectionHalfspaceAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance rootSectionHalfspaceAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma rootSectionChart_outer (h:M →+ ℝ) :
    (rootSectionChart Ω C h).val=invOfUnit
      ((chartPositive LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val*
       (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val) 1 := by
  unfold rootSectionChart
  dsimp only
  conv_lhs => arg 2; arg 1; rw [←chart_three_factorization LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)]
  rw [inverse_mul _ _ (by simp only [map_mul,
    (chartPositive LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,
    (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,mul_one])
    (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,
    ←mul_assoc,mul_invOfUnit _ 1 (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,one_mul]

omit [DecidableEq I] in
lemma chartPositive_nonnegative [DecidableEq I] (h:M →+ ℝ) (F:CompletedPositive LaurentRay.vUnit Ω C)
    (k:ℕ) (m:M) (hm:coeff k (chartPositive LaurentRay.vUnit Ω C h F).val m≠0) : 0 ≤ h m := by
  cases k with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(chartPositive LaurentRay.vUnit Ω C h F).property.1] at hm
    have he:m=0:=by
      by_contra hn
      exact hm (Finsupp.single_eq_of_ne hn)
    rw [he,map_zero]
  | succ k=> exact (chart_three_support LaurentRay.vUnit Ω C h F).1 k m hm |>.le

omit [DecidableEq I] in
lemma chartZero_nonnegative [DecidableEq I] (h:M →+ ℝ) (F:CompletedPositive LaurentRay.vUnit Ω C)
    (k:ℕ) (m:M) (hm:coeff k (chartZero LaurentRay.vUnit Ω C h F).val m≠0) : 0 ≤ h m := by
  cases k with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(chartZero LaurentRay.vUnit Ω C h F).property.1] at hm
    have he:m=0:=by
      by_contra hn
      exact hm (Finsupp.single_eq_of_ne hn)
    rw [he,map_zero]
  | succ k=> rw [(chart_three_support LaurentRay.vUnit Ω C h F).2.1 k m hm]

lemma rootSectionChart_nonnegative (h:M →+ ℝ) (k:ℕ) (m:M)
    (hm:coeff k (rootSectionChart Ω C h).val m≠0) : 0 ≤ h m := by
  rw [rootSectionChart_outer] at hm
  let P:=nonpositiveCone (-h)
  have hs:∀d x,coeff d
      ((chartPositive LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val*
       (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val) x≠0 → x∈P:=by
    intro d x hx
    obtain ⟨i,j,a,b,hij,ha,hb,he⟩:=series_product_nonzero LaurentRay.vUnit Ω _ _ d x hx
    change (-h) x ≤ 0
    rw [←he,map_add,AddMonoidHom.neg_apply,AddMonoidHom.neg_apply]
    linarith [chartPositive_nonnegative Ω C h (simpleTotalTransport Ω C) i a ha,
      chartZero_nonnegative Ω C h (simpleTotalTransport Ω C) j b hb]
  have H:=inverse_support_addSubmonoid LaurentRay.vUnit Ω P _ hs k m hm
  change -h m ≤ 0 at H
  linarith
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
local instance targetCyclicRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance targetCyclicAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance targetCyclicAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma torus_eval_finset_sum {J:Type*} (s:Finset J) (f:J → Torus v Ω) (m:M) :
    (∑j∈s,f j) m=∑j∈s,f j m := by
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert j s hj ih=>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    change f j m+(∑j∈s,f j) m=_
    rw [ih]
include hΩ

lemma torus_target_cyclic (F G:Torus v Ω) (m:M)
    (h:∀r∈F.support,∀s∈G.support,r+s=m → Ω r m=0) : (F*G) m=(G*F) m := by
  change (Torus.multiply v Ω F G) m=(Torus.multiply v Ω G F) m
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases he:r+s=m
  · have hrs:Ω r s=0 := by
      have H:=h r hr s hs he
      rw [←he,map_add,hΩ r,zero_add] at H
      exact H
    have hsr:Ω s r=0 := by rw [alternating_skew Ω hΩ,hrs,neg_zero]
    simp only [←he,Finsupp.single_eq_same,add_comm s r,hrs,hsr,zpow_zero,
      Units.val_one,mul_comm]
  · have he':s+r≠m:=by simpa only [add_comm s r] using he
    rw [Finsupp.single_eq_of_ne (Ne.symm he),Finsupp.single_eq_of_ne (Ne.symm he')]

lemma series_target_cyclic (F G:PowerSeries (Torus v Ω)) (N:ℕ) (m:M)
    (h:∀i j,i+j=N → ∀r∈(coeff i F).support,∀s∈(coeff j G).support,r+s=m → Ω r m=0) :
    coeff N (F*G) m=coeff N (G*F) m := by
  simp only [coeff_mul,torus_eval_finset_sum]
  rw [←Finset.Nat.sum_antidiagonal_swap (f:=fun p:ℕ×ℕ=>(coeff p.1 G*coeff p.2 F) m)]
  apply Finset.sum_congr rfl
  intro p hp
  exact torus_target_cyclic v Ω hΩ _ _ m (h p.1 p.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hp))

lemma adjoint_target_cyclic (F:PowerSeries (Torus v Ω)) (b m:M) (N:ℕ)
    (hF:constantCoeff F=1)
    (h:∀i j,i+j=N → ∀r∈(coeff i F).support,
       ∀s∈(coeff j (invOfUnit F 1)).support,r+(s+b)=m → Ω r m=0) :
    coeff N (adjoint F (PowerSeries.C (Torus.X v Ω b))) m=
      coeff N (PowerSeries.C (Torus.X v Ω b)) m := by
  rw [adjoint,mul_assoc]
  rw [series_target_cyclic v Ω hΩ F (PowerSeries.C (Torus.X v Ω b)*invOfUnit F 1) N m]
  · rw [mul_assoc,invOfUnit_mul F 1 hF,mul_one]
  · intro i j hij r hr s hs he
    have hs':coeff j (invOfUnit F 1) (s-b)≠0 := by
      have H:=Finsupp.mem_support_iff.mp hs
      rw [coeff_C_mul] at H
      have Hread:=X_mul_coeff v Ω (coeff j (invOfUnit F 1)) (s-b) b
      rw [sub_add_cancel] at Hread
      rw [Hread] at H
      exact (mul_ne_zero_iff.mp H).1
    exact h i j hij r hr (s-b) (Finsupp.mem_support_iff.mpr hs') (by simpa only [sub_add_cancel] using he)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
