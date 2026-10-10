import OAI.Probability.SignedSweeps.BudgetBounds

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma polytabloid_right_row {n : ℕ} (lam : Partition n)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (g * a.1) = polytabloid lam g := by
  classical
  simp only [polytabloid, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_congr rfl
  intro c _
  symm
  apply Fintype.sum_equiv (Equiv.mulRight a)
  intro b
  have h : (g * a.1 = c.1 * (b * a).1) ↔ g = c.1 * b.1 := by
    simp only [Subgroup.coe_mul, ← mul_assoc, mul_left_inj]
  simp only [Equiv.coe_mulRight, PiLp.single_apply, h]

lemma specht_right_row {n : ℕ} (lam : Partition n) (x : Specht lam)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    (spechtInclusion lam x) (g * a.1) = (spechtInclusion lam x) g := by
  have haux : ∀ y ∈ (spechtSubrepresentation lam).toSubmodule,
      y (g * a.1) = y g := by
    intro y hy
    change y ∈ Submodule.span ℂ _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      simp only [regularRepresentation_apply, ← mul_assoc]
      exact polytabloid_right_row lam a _
    | zero => rfl
    | add y z _ _ hy hz => simpa only [PiLp.add_apply] using congrArg₂ (· + ·) hy hz
    | smul c y _ hy => simpa only [PiLp.smul_apply] using congrArg (c • ·) hy
  exact haux _ x.property

def OffFirstRow {n : ℕ} (lam : Partition n) := {x : Fin n // lam.rowOf x ≠ 0}

instance offFirstRowFintype {n : ℕ} (lam : Partition n) : Fintype (OffFirstRow lam) := by
  classical
  unfold OffFirstRow
  infer_instance

lemma card_offFirstRow {n : ℕ} (lam : Partition n) :
    Fintype.card (OffFirstRow lam) = n - lam.1.rowLen 0 := by
  classical
  let e : {x : Fin n // lam.rowOf x = 0} ≃ Fin (lam.1.rowLen 0) := {
    toFun := fun x => ⟨lam.colOf x.1, by
      have h := (lam.tableau.symm x.1).property
      have hr := x.property
      change ((lam.tableau.symm x.1).1.1) = 0 at hr
      rw [← Prod.mk.eta (p := (lam.tableau.symm x.1).1), hr] at h
      exact YoungDiagram.mem_iff_lt_rowLen.mp h⟩
    invFun := fun j => ⟨lam.tableau ⟨(0, j.1), YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩,
      by simp [Partition.rowOf]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply lam.tableau.symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext x.property.symm rfl
    right_inv := by
      intro j
      apply Fin.ext
      simp [Partition.colOf] }
  have he : Fintype.card {x : Fin n // lam.rowOf x = 0} = lam.1.rowLen 0 := by
    simpa using Fintype.card_congr e
  have hs := Fintype.card_subtype_compl (fun x : Fin n => lam.rowOf x = 0)
  simpa only [OffFirstRow, Fintype.card_fin, he] using hs

lemma restrict_offFirstRow_eq {n : ℕ} (lam : Partition n)
    (g h : SymmetricGroup n) (he : ∀ x : OffFirstRow lam, g x.1 = h x.1) :
    g⁻¹ * h ∈ rowSubgroup lam := by
  have hf : ∀ x, lam.rowOf x ≠ 0 → (g⁻¹ * h) x = x := by
    intro x hx
    change g⁻¹ (h x) = x
    rw [← he ⟨x, hx⟩]; simp
  intro x
  by_cases hx : lam.rowOf x = 0
  · by_contra hn
    have hy : lam.rowOf ((g⁻¹ * h) x) ≠ 0 := by simpa only [hx] using hn
    have ht := hf ((g⁻¹ * h) x) hy
    have heq := (g⁻¹ * h).injective ht
    exact hy ((congrArg lam.rowOf heq).trans hx)
  · rw [hf x hx]

lemma spechtDimension_le_pow_level {n : ℕ} (lam : Partition n) :
    spechtDimension lam ≤ n ^ (n - lam.1.rowLen 0) := by
  classical
  let restrict := fun g : SymmetricGroup n => fun x : OffFirstRow lam => g x.1
  let repr := fun f : OffFirstRow lam → Fin n =>
    if h : ∃ g, restrict g = f then Classical.choose h else 1
  have hrepr (g : SymmetricGroup n) : restrict (repr (restrict g)) = restrict g := by
    dsimp only [repr]
    rw [dite_eq_left (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)]
    exact Classical.choose_spec (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)
  let ev : Specht lam →ₗ[ℂ] ((OffFirstRow lam → Fin n) → ℂ) := {
    toFun := fun x f => (spechtInclusion lam x) (repr f)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hev : Function.Injective ev := by
    intro x y hxy
    apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
    apply PiLp.ext
    intro g
    have hx : (spechtInclusion lam x) g = (spechtInclusion lam x) (repr (restrict g)) := by
      let a : rowSubgroup lam := ⟨(repr (restrict g))⁻¹ * g,
        restrict_offFirstRow_eq lam _ _ (fun c => congrFun (hrepr g) c)⟩
      simpa [a] using specht_right_row lam x a (repr (restrict g))
    have hy : (spechtInclusion lam y) g = (spechtInclusion lam y) (repr (restrict g)) := by
      let a : rowSubgroup lam := ⟨(repr (restrict g))⁻¹ * g,
        restrict_offFirstRow_eq lam _ _ (fun c => congrFun (hrepr g) c)⟩
      simpa [a] using specht_right_row lam y a (repr (restrict g))
    rw [hx, hy]
    exact congrFun hxy (restrict g)
  change finrank ℂ (Specht lam) ≤ _
  have h := LinearMap.finrank_le_finrank_of_injective hev
  simpa [Module.finrank_pi, Fintype.card_fun, card_offFirstRow] using h

end SignedSweeps
end

end OAI
