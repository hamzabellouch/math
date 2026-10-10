import OAI.Probability.SignedSweeps.IndependentNetworks

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def supportedSubgroup {n : ℕ} (S : Finset (Fin n)) : Subgroup (SymmetricGroup n) where
  carrier := {g | ∀ x, x ∉ S → g x = x}
  one_mem' := by intro x hx; rfl
  mul_mem' := by
    intro g h hg hh x hx
    change g (h x) = x
    rw [hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    exact g.injective (by simpa using (hg x hx).symm)

lemma swap_mem_supportedSubgroup {n : ℕ} (S : Finset (Fin n))
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) : Equiv.swap a b ∈ supportedSubgroup S := by
  classical
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb))

lemma Partition.colOf_lt_firstRow {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.colOf x < lam.1.rowLen 0 := by
  have h := (lam.tableau.symm x).property
  have hle := lam.1.rowLen_anti 0 (lam.rowOf x) (Nat.zero_le _)
  exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp h) hle

lemma large_set_column_pair {n : ℕ} (lam : Partition n) (S : Finset (Fin n))
    (hS : lam.1.rowLen 0 < S.card) (g : SymmetricGroup n) :
    ∃ a b : Fin n, a ≠ b ∧ lam.colOf a = lam.colOf b ∧ g a ∈ S ∧ g b ∈ S := by
  classical
  let f : S → Fin (lam.1.rowLen 0) := fun x =>
    ⟨lam.colOf (g⁻¹ x.1), lam.colOf_lt_firstRow _⟩
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hS)
  refine ⟨g⁻¹ x.1, g⁻¹ y.1, ?_, congrArg Fin.val hf, ?_, ?_⟩
  · intro h
    exact hxy (Subtype.ext (g.symm.injective h))
  · simp
  · simp

lemma supportedAverage_annihilates_generator {n : ℕ} (lam : Partition n)
    (S : Finset (Fin n)) (hS : lam.1.rowLen 0 < S.card) (g : SymmetricGroup n) :
    groupAverage ((regularRepresentation n).comp (supportedSubgroup S).subtype)
      (regularRepresentation n g (polytabloid lam)) = 0 := by
  classical
  obtain ⟨a, b, hab, hc, haS, hbS⟩ := large_set_column_pair lam S hS g
  apply groupAverage_anti_fixed _ ⟨Equiv.swap (g a) (g b),
    swap_mem_supportedSubgroup S haS hbS⟩
  change regularRepresentation _ (Equiv.swap (g a) (g b))
    (regularRepresentation _ g (polytabloid lam)) = _
  rw [← Module.End.mul_apply, ← map_mul, Equiv.swap_mul_eq_mul_swap]
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  rw [map_mul, Module.End.mul_apply]
  have ha := polytabloid_column_action lam ⟨Equiv.swap a b, swap_mem_fiberSubgroup _ hc⟩
  have hs : complexSign _ (Equiv.swap a b) = -1 := by
    simp [complexSign, Equiv.Perm.sign_swap hab]
  rw [ha, hs, neg_one_smul, map_neg]

lemma supportedAverage_eq_zero {n : ℕ} (lam : Partition n) (S : Finset (Fin n))
    (hS : lam.1.rowLen 0 < S.card) :
    groupAverage ((spechtRepresentation lam).comp (supportedSubgroup S).subtype) = 0 := by
  classical
  let A := groupAverage ((regularRepresentation n).comp (supportedSubgroup S).subtype)
  have ha : (spechtSubrepresentation lam).toSubmodule ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact supportedAverage_annihilates_generator lam S hS g
  ext x
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  have hx := ha x.property
  rw [LinearMap.zero_apply, map_zero]
  change A (spechtInclusion lam x) = 0 at hx
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have he (g : supportedSubgroup S) : spechtInclusion lam (spechtRepresentation lam g.1 x) =
      regularRepresentation _ g.1 (spechtInclusion lam x) := rfl
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, he]
  simpa only [A, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    MonoidHom.comp_apply, Subgroup.subtype_apply] using hx

lemma specht_supported_invariant_eq_zero {n : ℕ} (lam : Partition n)
    (S : Finset (Fin n)) (hS : lam.1.rowLen 0 < S.card) (x : Specht lam)
    (hx : ∀ g : supportedSubgroup S, spechtRepresentation lam g.1 x = x) : x = 0 := by
  have h := groupAverage_fixed
    ((spechtRepresentation lam).comp (supportedSubgroup S).subtype) x hx
  rw [supportedAverage_eq_zero lam S hS, LinearMap.zero_apply] at h
  exact h.symm

lemma specht_right_supported_sum_eq_zero {n : ℕ} (lam : Partition n)
    (S : Finset (Fin n)) (hS : lam.1.rowLen 0 < S.card) (x : Specht lam)
    (g : SymmetricGroup n) :
    ∑ h : supportedSubgroup S, spechtInclusion lam x (g * h.1) = 0 := by
  classical
  have hz := congrArg (fun A : Specht lam →ₗ[ℂ] Specht lam =>
      spechtInclusion lam (A (spechtRepresentation lam g⁻¹ x)) 1)
    (supportedAverage_eq_zero lam S hS)
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    LinearMap.zero_apply, map_zero, PiLp.zero_apply] at hz
  have he (h : supportedSubgroup S) : spechtInclusion lam
      (((spechtRepresentation lam).comp (supportedSubgroup S).subtype) h
        (spechtRepresentation lam g⁻¹ x)) 1 =
        spechtInclusion lam x (g * h.1⁻¹) := by
    change spechtInclusion lam x ((g⁻¹)⁻¹ * (h.1⁻¹ * 1)) = _
    simp
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, he, smul_eq_mul] at hz
  have hu : (Fintype.card (supportedSubgroup S) : ℂ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have hh := (mul_eq_zero.mp hz).resolve_left hu
  rwa [Fintype.sum_equiv (Equiv.inv (supportedSubgroup S))
    (fun h => spechtInclusion lam x (g * h.1⁻¹))
    (fun h => spechtInclusion lam x (g * h.1)) (fun _ => rfl)] at hh

end SignedSweeps
end

end OAI
