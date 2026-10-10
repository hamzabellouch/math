import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicFiniteIndex
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolycyclicDualityComparison

namespace OAI

/-! # Virtual torsion freeness across a cyclic extension

The finite-index subgroup of the kernel is first made characteristic. For an
infinite cyclic quotient, lift its generator and take the subgroup generated
by that lift and the characteristic subgroup. Its torsion lies in the kernel,
where torsion freeness is already known.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise

variable {G : Type} [Group G]

theorem HasNoNontrivialTorsion.of_injective {J : Type} [Group J]
    (h : HasNoNontrivialTorsion G) (f : J →* G) (hf : Function.Injective f) :
    HasNoNontrivialTorsion J := by
  intro g n hn hg
  apply hf
  rw [map_one]
  exact h (f g) n hn (by rw [← map_pow, hg, map_one])

/-- A finite-index subgroup of the kernel gives finitely many cosets whenever
the chosen subgroup surjects onto the quotient. No normality of `H` is needed. -/
theorem finiteIndex_of_kernel_cover (N : Subgroup G) [N.Normal]
    (K : Subgroup N) [K.FiniteIndex] (H : Subgroup G)
    (hKH : K.map N.subtype ≤ H)
    (hcover : ∀ g : G, ∃ h ∈ H, (QuotientGroup.mk' N) h = (QuotientGroup.mk' N) g) :
    H.FiniteIndex := by
  let f : N ⧸ K → G ⧸ H := Quotient.map' (fun n : N => (n : G)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hKH (Subgroup.mem_map.mpr ⟨a⁻¹ * b, hab, rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := Quotient.mk''_surjective x
    obtain ⟨h, hh, he⟩ := hcover g
    have hn : g * h⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' N) (g * h⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    refine ⟨QuotientGroup.mk (⟨g * h⁻¹, hn⟩ : N), ?_⟩
    change QuotientGroup.mk (g * h⁻¹) = QuotientGroup.mk g
    apply QuotientGroup.eq.mpr
    simpa [mul_assoc] using hh
  let : Finite (G ⧸ H) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem torsionFree_finiteIndex_of_cyclic_extension
    (N : Subgroup G) [N.Normal] [Group.FG N] [IsCyclic (G ⧸ N)]
    (hN : ∃ L : Subgroup N, L.FiniteIndex ∧ HasNoNontrivialTorsion L) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ HasNoNontrivialTorsion H := by
  obtain ⟨L, hLi, hLt⟩ := hN
  let := hLi
  obtain ⟨K, hKL, hKc, hKi⟩ := exists_characteristic_finiteIndex_le L
  let := hKc
  let := hKi
  have hKt : HasNoNontrivialTorsion K := hLt.of_injective (Subgroup.inclusion hKL)
    (Subgroup.inclusion_injective hKL)
  let A : Subgroup G := K.map N.subtype
  have hAt : HasNoNontrivialTorsion A := by
    let e := K.equivMapOfInjective N.subtype N.subtype_injective
    exact hKt.of_injective e.symm.toMonoidHom e.symm.injective
  let q := QuotientGroup.mk' N
  have hAq : A ≤ q.ker := by
    rintro a ⟨k, hk, rfl⟩
    change q k = 1
    exact (QuotientGroup.eq_one_iff (k : G)).mpr k.property
  cases finite_or_infinite (G ⧸ N) with
  | inl hfin =>
    let := hfin
    let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hAi : A.FiniteIndex := ⟨by
      change (K.map N.subtype).index ≠ 0
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero hKi.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))⟩
    exact ⟨A, hAi, hAt⟩
  | inr hinf =>
    let := hinf
    obtain ⟨z, hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic (G ⧸ N))
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N z
    have hz0 : orderOf z = 0 := orderOf_eq_card_of_zpowers_eq_top hz
      |>.trans (Nat.card_eq_zero_of_infinite)
    have hzinj : Function.Injective (fun k : ℤ => z ^ k) :=
      injective_zpow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp hz0)
    let H : Subgroup G := A ⊔ Subgroup.zpowers g
    have hHi : H.FiniteIndex := finiteIndex_of_kernel_cover N K H le_sup_left (by
      intro x
      have hx : q x ∈ Subgroup.zpowers z := hz.ge (Subgroup.mem_top _)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨g ^ k, (show Subgroup.zpowers g ≤ H from le_sup_right)
        (Subgroup.zpow_mem_zpowers g k), ?_⟩
      change q (g ^ k) = q x
      rw [map_zpow, hg, hk])
    refine ⟨H, hHi, ?_⟩
    intro x n hn hxn
    have hxf : (x : G) ^ n = 1 := congrArg Subtype.val hxn
    have hx : (x : G) ∈ (A : Set G) * (Subgroup.zpowers g : Set G) := by
      rw [← Subgroup.normal_mul]
      exact x.property
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have haq : q a = 1 := hAq ha
    have hxq : q (x : G) = z ^ k := by
      rw [← hab, map_mul, haq, one_mul, map_zpow, hg]
    have hkn : k * (n : ℤ) = 0 := by
      apply hzinj
      change z ^ (k * (n : ℤ)) = z ^ (0 : ℤ)
      rw [zpow_zero, zpow_mul, zpow_natCast, ← hxq, ← map_pow, hxf, map_one]
    have hk : k = 0 := (mul_eq_zero.mp hkn).resolve_right (by exact_mod_cast hn)
    have hxa : (x : G) ∈ A := by
      have he : (x : G) = a := by simpa [hk] using hab.symm
      rwa [he]
    apply Subtype.ext
    exact congrArg (fun t : A => (t : G)) (hAt ⟨x, hxa⟩ n hn (Subtype.ext hxf))

end PolycyclicRecognition

end

end OAI
