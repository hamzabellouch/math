import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalSpanDenominators

namespace OAI

/-! # Finite generation up to roots in a finite-rank abelian group -/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct
variable {A : Type} [CommGroup A]

theorem rationalAbelianMap_span :
    Submodule.span ℚ (Set.range (rationalAbelianMap (A := A))) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using TensorProduct.inductionOn with
  | tmul r a =>
    have ha := Submodule.subset_span (R := ℚ)
      (Set.mem_range_self (f := rationalAbelianMap (A := A)) a)
    have hr := (Submodule.span ℚ (Set.range (rationalAbelianMap (A := A)))).smul_mem r ha
    change r • (1 ⊗ₜ[ℤ] a) ∈ Submodule.span ℚ (Set.range (rationalAbelianMap (A := A))) at hr
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hr
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem exists_finite_rationalAbelian_spanning_set
    (hA : HasNoNontrivialTorsion A) [Module.Finite ℚ (RationalAbelianSpace A)] :
    ∃ S : Set (Additive A), S.Finite ∧
      Submodule.span ℚ (rationalAbelianMap '' S) = ⊤ := by
  let f := rationalAbelianMap (A := A)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℚ) (M := RationalAbelianSpace A)
  have hTspan : (T : Set (RationalAbelianSpace A)) ⊆ Submodule.span ℚ (Set.range f) := by
    rw [rationalAbelianMap_span]
    exact fun _ _ => trivial
  obtain ⟨U, hU, hTU⟩ := Submodule.subset_span_finite_of_subset_span hTspan
  let S := f ⁻¹' (U : Set (RationalAbelianSpace A))
  have hS : S.Finite := U.finite_toSet.preimage (rationalAbelianMap_injective hA).injOn
  have himage : f '' S = (U : Set (RationalAbelianSpace A)) := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hv
      obtain ⟨a, rfl⟩ := hU hv
      exact ⟨a, hv, rfl⟩
  refine ⟨S, hS, ?_⟩
  rw [himage]
  apply top_unique
  rw [← hT]
  exact Submodule.span_le.mpr hTU

theorem abelian_exists_fg_subgroup_containing_powers
    (hA : HasNoNontrivialTorsion A) [Module.Finite ℚ (RationalAbelianSpace A)] :
    ∃ H : Subgroup A, H.FG ∧ ∀ a : A, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H := by
  obtain ⟨S, hS, hspan⟩ := exists_finite_rationalAbelian_spanning_set hA
  let H : Subgroup A :=
    { carrier := fun a => Additive.ofMul a ∈ Submodule.span ℤ S
      one_mem' := by
        change (0 : Additive A) ∈ Submodule.span ℤ S
        exact Submodule.zero_mem _
      mul_mem' := by
        intro a b ha hb
        change Additive.ofMul a + Additive.ofMul b ∈ Submodule.span ℤ S
        exact Submodule.add_mem _ ha hb
      inv_mem' := by
        intro a ha
        change -Additive.ofMul a ∈ Submodule.span ℤ S
        exact Submodule.neg_mem _ ha }
  have hH : H = Subgroup.closure (Additive.toMul '' S) := by
    apply Subgroup.toAddSubgroup.injective
    change (Submodule.span ℤ S).toAddSubgroup = _
    rw [Submodule.span_int_eq_addSubgroupClosure, Subgroup.toAddSubgroup_closure]
    congr 1
    ext a
    simp
  refine ⟨H, ?_, ?_⟩
  · rw [hH]
    exact (Subgroup.fg_iff _).mpr ⟨_, rfl, hS.image Additive.toMul⟩
  · intro a
    have ha : rationalAbelianMap (Additive.ofMul a) ∈
        Submodule.span ℚ (rationalAbelianMap '' S) := by rw [hspan]; trivial
    obtain ⟨n, hn, hna⟩ := exists_nsmul_mem_integral_span ha
    have hpre : n • Additive.ofMul a ∈ Submodule.span ℤ S := by
      rw [← map_nsmul, ← Submodule.map_span] at hna
      obtain ⟨b, hb, he⟩ := hna
      have he' := rationalAbelianMap_injective hA he
      exact he' ▸ hb
    refine ⟨n, hn, ?_⟩
    change Additive.ofMul (a ^ n) ∈ Submodule.span ℤ S
    simpa only [ofMul_pow] using hpre

end PolycyclicRecognition

end

end OAI
