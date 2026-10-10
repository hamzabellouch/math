import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R]
noncomputable def geometric (c : R) : PowerSeries R := PowerSeries.mk fun n=>c^n
lemma one_sub_mul_geometric (c : R) :
    (1-PowerSeries.C c*PowerSeries.X)*geometric c=1 := by
  ext n
  cases n with
  | zero => simp [geometric]
  | succ n =>
    rw [sub_mul,one_mul,mul_assoc]
    simp only [map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul,
      geometric,PowerSeries.coeff_mk,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false]
    ring
lemma oneSubUnit_inv (c : R) : (↑(oneSubUnit c)⁻¹ : PowerSeries R)=geometric c := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [oneSubUnit_val,one_sub_mul_geometric]
lemma affineUnit_inv_val (c : R) :
    (↑(affineUnit c)⁻¹ : LaurentSeries R)=
      -(single 1 1 * (ofPowerSeries ℤ R) (geometric c)) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [affineUnit,Units.val_mul,Units.val_neg,Units.coe_map,zUnit_val,oneSubUnit_val]
  change -(single (-1:ℤ) (1:R)) * (ofPowerSeries ℤ R) (1-PowerSeries.C c*PowerSeries.X) *
    -(single 1 1 * (ofPowerSeries ℤ R) (geometric c))=1
  calc
    _ = (single (-1 : ℤ) (1:R)*single 1 1) *
      ((ofPowerSeries ℤ R) (1-PowerSeries.C c*PowerSeries.X) *
        (ofPowerSeries ℤ R) (geometric c)) := by ring
    _ = 1 := by rw [← (ofPowerSeries ℤ R).map_mul,one_sub_mul_geometric,(ofPowerSeries ℤ R).map_one,single_mul_single]; simp
end ElementaryPositivity.LaurentAtInfinity

end
section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries MvPolynomial
variable {σ : Type*}

def IsHomogeneous (f : LaurentSeries (MvPolynomial σ ℚ)) (d : ℤ) : Prop :=
  ∀ k,(f.coeff k).IsWeightedHomogeneous (fun _=>(1:ℤ)) (d+k)

lemma IsHomogeneous.zero (d : ℤ) : IsHomogeneous (0 : LaurentSeries (MvPolynomial σ ℚ)) d := by
  intro k
  exact isWeightedHomogeneous_zero _ _ _

lemma IsHomogeneous.add {f g : LaurentSeries (MvPolynomial σ ℚ)} {d : ℤ}
    (hf : IsHomogeneous f d) (hg : IsHomogeneous g d) : IsHomogeneous (f+g) d := by
  intro k
  exact (hf k).add (hg k)

lemma IsHomogeneous.neg {f : LaurentSeries (MvPolynomial σ ℚ)} {d : ℤ}
    (hf : IsHomogeneous f d) : IsHomogeneous (-f) d := by
  intro k
  exact (hf k).neg

lemma IsHomogeneous.sub {f g : LaurentSeries (MvPolynomial σ ℚ)} {d : ℤ}
    (hf : IsHomogeneous f d) (hg : IsHomogeneous g d) : IsHomogeneous (f-g) d := by
  intro k
  exact (hf k).sub (hg k)

lemma homogeneous_single (k h : ℤ) (p : MvPolynomial σ ℚ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) h) : IsHomogeneous (single k p) (h-k) := by
  intro j
  rw [coeff_single]
  split_ifs with hj
  · subst j
    simpa only [sub_add_cancel] using hp
  · exact isWeightedHomogeneous_zero _ _ _

lemma homogeneous_one : IsHomogeneous (1 : LaurentSeries (MvPolynomial σ ℚ)) 0 := by
  have h:=homogeneous_single 0 0 (1 : MvPolynomial σ ℚ) (isWeightedHomogeneous_one _ _)
  simpa only [sub_zero,HahnSeries.single_zero_one] using h

lemma IsHomogeneous.mul {f g : LaurentSeries (MvPolynomial σ ℚ)} {d e : ℤ}
    (hf : IsHomogeneous f d) (hg : IsHomogeneous g e) : IsHomogeneous (f*g) (d+e) := by
  intro k
  rw [HahnSeries.coeff_mul]
  apply (weightedHomogeneousSubmodule ℚ (fun _ : σ=>(1:ℤ)) (d+e+k)).sum_mem
  intro ij hij
  have heq : ij.1+ij.2=k := (Finset.mem_antidiagonal.mp hij).2.2
  change (f.coeff ij.1*g.coeff ij.2).IsWeightedHomogeneous _ _
  have h:=(hf ij.1).mul (hg ij.2)
  simpa only [show d+ij.1+(e+ij.2)=d+e+k by omega] using h

lemma IsHomogeneous.pow {f : LaurentSeries (MvPolynomial σ ℚ)} {d : ℤ}
    (hf : IsHomogeneous f d) (n : ℕ) : IsHomogeneous (f^n) ((n:ℤ)*d) := by
  induction n with
  | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul] using (homogeneous_one (σ:=σ))
  | succ n ih =>
    rw [pow_succ]
    have h:=ih.mul hf
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

lemma homogeneous_affine (p : MvPolynomial σ ℚ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) 1) : IsHomogeneous (affineUnit p).val 1 := by
  rw [affineUnit_val,zUnit_val]
  have h0 : IsHomogeneous (single 0 p) 1 := by
    simpa only [sub_zero] using homogeneous_single 0 1 p hp
  have h1 : IsHomogeneous (single (-1) (1 : MvPolynomial σ ℚ)) 1 := by
    simpa using homogeneous_single (-1) 0 (1 : MvPolynomial σ ℚ) (isWeightedHomogeneous_one _ _)
  exact h0.sub h1

lemma homogeneous_affine_inv (p : MvPolynomial σ ℚ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) 1) : IsHomogeneous ((affineUnit p)⁻¹).val (-1) := by
  rw [affineUnit_inv_val]
  apply IsHomogeneous.neg
  intro k
  rw [coeff_single_mul,one_mul]
  change (((geometric p : PowerSeries (MvPolynomial σ ℚ)) : LaurentSeries (MvPolynomial σ ℚ)).coeff (k-1)).IsWeightedHomogeneous _ _
  rw [PowerSeries.coeff_coe]
  split_ifs with hk
  · exact isWeightedHomogeneous_zero _ _ _
  · rw [geometric,PowerSeries.coeff_mk]
    have h:=hp.pow (k-1).natAbs
    have hn : ((k-1).natAbs : ℤ)=k-1 := by
      rw [Int.natCast_natAbs,abs_of_nonneg (by omega : 0≤k-1)]
    rw [nsmul_eq_mul,mul_one,hn] at h
    convert h using 1
    omega

lemma homogeneous_affine_zpow (p : MvPolynomial σ ℚ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) 1) (e : ℤ) :
    IsHomogeneous ((affineUnit p)^e).val e := by
  cases e with
  | ofNat n =>
    change IsHomogeneous ((affineUnit p)^(n:ℤ)).val (n:ℤ)
    rw [zpow_natCast,Units.val_pow_eq_pow_val]
    simpa only [mul_one] using (homogeneous_affine p hp).pow n
  | negSucc n =>
    have he : Int.negSucc n=-((n+1:ℕ):ℤ) := by omega
    rw [he,zpow_neg, zpow_natCast,← inv_pow,Units.val_pow_eq_pow_val]
    simpa only [mul_neg_one] using (homogeneous_affine_inv p hp).pow (n+1)

end ElementaryPositivity.LaurentAtInfinity

end
section
namespace ElementaryPositivity.LaurentAtInfinity
open MvPolynomial HahnSeries
variable {σ τ α : Type*}
lemma homogeneous_sum (s : Finset α) (f : α → LaurentSeries (MvPolynomial σ ℚ))
    (d : ℤ) (h : ∀ i∈s,IsHomogeneous (f i) d) : IsHomogeneous (∑ i∈s,f i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsHomogeneous.zero (σ:=σ) d
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
lemma homogeneous_prod (s : Finset α) (f : α → LaurentSeries (MvPolynomial σ ℚ))
    (d : α → ℤ) (h : ∀ i∈s,IsHomogeneous (f i) (d i)) :
    IsHomogeneous (∏ i∈s,f i) (∑ i∈s,d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (homogeneous_one (σ:=σ))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).mul (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
lemma homogeneous_ringHom (h : MvPolynomial σ ℚ →+* LaurentSeries (MvPolynomial τ ℚ))
    (hc : ∀ q,IsHomogeneous (h (MvPolynomial.C q)) 0)
    (hx : ∀ i,IsHomogeneous (h (X i)) 1)
    (f : MvPolynomial σ ℚ) (d : ℤ) (hf : f.IsWeightedHomogeneous (fun _=>(1:ℤ)) d) :
    IsHomogeneous (h f) d := by
  classical
  rw [← f.support_sum_monomial_coeff,map_sum]
  apply homogeneous_sum
  intro m hm
  rw [MvPolynomial.monomial_eq,map_mul,Finsupp.prod,map_prod]
  have hp : IsHomogeneous (∏ i∈m.support,h (X i^(m i))) (∑ i∈m.support,(m i:ℤ)) := by
    apply homogeneous_prod
    intro i hi
    rw [map_pow]
    simpa only [mul_one] using (hx i).pow (m i)
  have hh := (hc (f.coeff m)).mul hp
  have hd : (∑ i∈m.support,(m i:ℤ))=d := by
    simpa only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,mul_one] using hf (mem_support_iff.mp hm)
  simpa only [zero_add,hd] using hh
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
