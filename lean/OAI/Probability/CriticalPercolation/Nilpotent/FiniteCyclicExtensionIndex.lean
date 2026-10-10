import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.CharacteristicNilpotentCore

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A]

lemma finiteIndex_of_finite_kernel_int (f : A →* Multiplicative ℤ)
    [Finite f.ker] (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (H : Subgroup A) (m : ℕ) (hm : 0 < m) (haH : a^m ∈ H) : H.FiniteIndex := by
  let F : f.ker × Fin m → A ⧸ H := fun p => QuotientGroup.mk (p.1.val*a^p.2.val)
  have hF : Surjective F := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
    let n : ℤ := (f x).toAdd
    let k : A := x*a^(-n)
    have hk : k∈f.ker := by
      change f k=1
      apply Multiplicative.toAdd.injective
      simp [k,map_zpow,ha,n]
    let r : Fin m := ⟨(n % (m:ℤ)).toNat,by
      have hr0 := Int.emod_nonneg n (by omega : (m:ℤ)≠0)
      have hr := Int.emod_lt_of_pos n (by omega : 0<(m:ℤ))
      omega⟩
    refine ⟨(⟨k,hk⟩,r),?_⟩
    apply QuotientGroup.eq.mpr
    change (k*a^r.val)⁻¹*x∈H
    have hr : (r.val:ℤ)=n%(m:ℤ) := Int.toNat_of_nonneg
      (Int.emod_nonneg n (by omega : (m:ℤ)≠0))
    have he : (k*a^r.val)⁻¹*x=(a^m)^(n/(m:ℤ)) := by
      calc
        (k*a^r.val)⁻¹*x = a^(-(r.val:ℤ))*a^n := by simp only [k,mul_inv_rev,zpow_neg,←zpow_natCast]; group
        _ = a^((m:ℤ)*(n/(m:ℤ))) := by
          rw [←zpow_add,hr]
          congr 1
          have hh := Int.emod_add_mul_ediv n (m:ℤ)
          omega
        _ = (a^m)^(n/(m:ℤ)) := by rw [zpow_mul,zpow_natCast]
    rw [he]
    exact H.zpow_mem haH _
  let _ : Finite (A ⧸ H) := Finite.of_surjective F hF
  exact Subgroup.finiteIndex_of_finite_quotient

lemma finite_lift_kernel (f : A →* Multiplicative ℤ) (L : Subgroup A) [L.Normal]
    (hL : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex] :
    Finite (QuotientGroup.lift L f hL).ker := by
  let q := QuotientGroup.mk' L
  let p := q.comp f.ker.subtype
  have hpker : p.ker=L.subgroupOf f.ker := by
    ext x
    exact QuotientGroup.eq_one_iff (N := L) x.val
  let _ : p.ker.FiniteIndex := hpker.symm ▸ (inferInstance : (L.subgroupOf f.ker).FiniteIndex)
  let _ : Finite p.range := Finite.of_equiv (f.ker ⧸ p.ker)
    (QuotientGroup.quotientKerEquivRange p).toEquiv
  have he : p.range=(QuotientGroup.lift L f hL).ker := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective L x
      exact ⟨⟨y,hx⟩,rfl⟩
  exact he ▸ (inferInstance : Finite p.range)

lemma finiteIndex_of_normal_kernel_subgroup (f : A →* Multiplicative ℤ)
    (L : Subgroup A) [L.Normal] (hL : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex]
    (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (H : Subgroup A) (hLH : L ≤ H) (m : ℕ) (hm : 0 < m) (haH : a^m ∈ H) :
    H.FiniteIndex := by
  let q := QuotientGroup.mk' L
  let g := QuotientGroup.lift L f hL
  let _ : Finite g.ker := finite_lift_kernel f L hL
  have hi : (H.map q).FiniteIndex := finiteIndex_of_finite_kernel_int g (q a) ha
    (H.map q) m hm (by rw [←map_pow]; exact ⟨a^m,haH,rfl⟩)
  constructor
  rw [←Subgroup.index_map_eq H (QuotientGroup.mk'_surjective L)
    (by simpa only [QuotientGroup.ker_mk'] using hLH)]
  exact hi.index_ne_zero

end CriticalPercolation.SparseGrowth
end
end

end OAI
