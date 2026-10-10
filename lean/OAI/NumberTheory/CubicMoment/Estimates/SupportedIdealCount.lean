import OAI.NumberTheory.CubicMoment.Estimates.SmallPrimeParts

namespace OAI

/-! A Rankin bound for ideals supported on a varying small modulus. The
finite Euler product is controlled by an arbitrarily small modulus power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentNorm_prod_of_support_subset (ν : EisensteinIdealExponent)
    (S : Finset EisensteinIdealPrime) (hS : ν.support ⊆ S) :
    idealExponentNorm ν = ∏ p ∈ S, (normNat (idealPrimeRepresentative p):ℝ)^ν p := by
  rw [idealExponentNorm_eq_prod]
  apply Finset.prod_subset hS
  intro p hp hpn
  rw [Finsupp.notMem_support_iff.mp hpn,pow_zero]

lemma supported_norm_rpow (ν : EisensteinIdealExponent)
    (S : Finset EisensteinIdealPrime) (hS : ν.support ⊆ S) (ε : ℝ) :
    idealExponentNorm ν^(-ε) =
      ∏ p : S, ((normNat (idealPrimeRepresentative p):ℝ)^(-ε))^(ν p) := by
  rw [idealExponentNorm_prod_of_support_subset ν S hS,
    ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity),
    ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  ring

lemma finite_geometric_code_sum {α β : Type*} [Fintype α] [Fintype β]
    (M : ℕ) (f : α → β → Fin M) (hf : Function.Injective f)
    (w : β → ℝ) (hw : ∀ p, 0 ≤ w p ∧ w p < 1) :
    (∑ a : α, ∏ p : β, w p^(f a p).val) ≤ ∏ p : β, (1-w p)⁻¹ := by
  classical
  calc
    _ ≤ ∑ g : β → Fin M, ∏ p : β, w p^(g p).val := by
      apply Finset.sum_le_sum_of_injOn f (fun _ _ _ _ h => hf h)
        (Finset.subset_univ _)
      · intro a ha
        exact le_rfl
      · intro g hg hgn
        exact Finset.prod_nonneg (fun p _ => pow_nonneg (hw p).1 _)
    _ = ∏ p : β, ∑ n : Fin M, w p^n.val := (Fintype.prod_sum (fun (p : β) (n : Fin M) => w p^n.val)).symm
    _ ≤ ∏ p : β, (1-w p)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact Finset.sum_nonneg (fun n _ => pow_nonneg (hw p).1 _)
      · intro p hp
        rw [Fin.sum_univ_eq_sum_range]
        exact sum_le_hasSum (Finset.range M) (fun n _ => pow_nonneg (hw p).1 n)
          (hasSum_geometric_of_lt_one (hw p).1 (hw p).2)

lemma ideal_supported_rankin_sum {ε J : ℝ} (hε : 0 < ε)
    (S : Finset EisensteinIdealPrime) (T : Finset EisensteinIdealExponent)
    (hT : ∀ ν ∈ T, ν.support ⊆ S ∧ idealExponentNorm ν ≤ J) :
    (∑ ν ∈ T, idealExponentNorm ν^(-ε)) ≤
      ∏ p ∈ S, (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹ := by
  let M := Nat.log 2 ⌊J⌋₊+1
  let f : T → (S → Fin M) := fun ν p =>
    ⟨ν.val p, Nat.lt_succ_of_le (idealExponent_exponent_bound (hT ν ν.property).2 p)⟩
  have hf : Function.Injective f := by
    intro ν κ he
    apply Subtype.ext
    apply Finsupp.ext
    intro p
    by_cases hp : p ∈ S
    · exact congrArg Fin.val (congrFun he ⟨p,hp⟩)
    · rw [Finsupp.notMem_support_iff.mp (fun h => hp ((hT ν ν.property).1 h)),
        Finsupp.notMem_support_iff.mp (fun h => hp ((hT κ κ.property).1 h))]
  let w : S → ℝ := fun p => (normNat (idealPrimeRepresentative p):ℝ)^(-ε)
  have hw (p : S) : 0 ≤ w p ∧ w p < 1 := by
    have hp : (1:ℝ) < normNat (idealPrimeRepresentative p) := by
      have := idealPrimeRepresentative_normNat_ge_two p
      exact_mod_cast (by omega : 1 < normNat (idealPrimeRepresentative p))
    exact ⟨Real.rpow_nonneg (by positivity) _,Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hε)⟩
  have hnorm (ν : T) : idealExponentNorm ν^(-ε) = ∏ p : S, w p^(f ν p).val :=
    supported_norm_rpow ν S (hT ν ν.property).1 ε
  calc
    _ = ∑ ν : T, ∏ p : S, w p^(f ν p).val := by
      rw [← Finset.sum_coe_sort T]
      exact Finset.sum_congr rfl (fun ν _ => hnorm ν)
    _ ≤ ∏ p : S, (1-w p)⁻¹ := finite_geometric_code_sum M f hf w hw
    _ = _ := Finset.prod_coe_sort S
      (fun p => (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹)

end CubicFirstMoment

end

end OAI
