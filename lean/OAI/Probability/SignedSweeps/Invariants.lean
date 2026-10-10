import OAI.Probability.SignedSweeps.SwitchGeneration

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def complexSign (n : ℕ) : SymmetricGroup n →* ℂ where
  toFun g := (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ)
  map_one' := by simp
  map_mul' g h := by simp

lemma colSubgroup_has_odd {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0) :
    ∃ g : colSubgroup lam, complexSign n g.1 = -1 := by
  classical
  have h0 : (0, 0) ∈ lam.1.cells := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have h1 : (1, 0) ∈ lam.1.cells := YoungDiagram.mem_iff_lt_colLen.mpr hl
  let a := lam.tableau ⟨(0, 0), h0⟩
  let b := lam.tableau ⟨(1, 0), h1⟩
  have hab : a ≠ b := by
    intro he
    have he' := lam.tableau.injective he
    have hc := congrArg (fun c : {c // c ∈ lam.1.cells} => c.1.1) he'
    norm_num at hc
  have hm : Equiv.swap a b ∈ colSubgroup lam := by
    apply swap_mem_fiberSubgroup
    simp [Partition.colOf, a, b]
  refine ⟨⟨Equiv.swap a b, hm⟩, ?_⟩
  simp [complexSign, Equiv.Perm.sign_swap hab]

lemma colSubgroup_sum_sign_eq_zero {n : ℕ} (lam : Partition n)
    (hl : 1 < lam.1.colLen 0) : ∑ g : colSubgroup lam, complexSign n g.1 = 0 := by
  classical
  obtain ⟨g, hg⟩ := colSubgroup_has_odd lam hl
  have hh := Fintype.sum_equiv (Equiv.mulLeft g)
    (fun h => complexSign n (g * h).1) (fun h => complexSign n h.1) (fun _ => rfl)
  simp only [Subgroup.coe_mul, map_mul, hg, ← Finset.mul_sum] at hh
  have htwo : (2 : ℂ) * (∑ h : colSubgroup lam, complexSign n h.1) = 0 := by
    linear_combination -hh
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

def regularSum (n : ℕ) : RegularSpace n →ₗ[ℂ] ℂ where
  toFun f := ∑ g, f g
  map_add' f h := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

lemma regularSum_single {n : ℕ} (g : SymmetricGroup n) (z : ℂ) :
    regularSum n (EuclideanSpace.single g z) = z := by
  classical
  simp [regularSum, PiLp.single_apply]

lemma regularSum_invariant {n : ℕ} (g : SymmetricGroup n) (f : RegularSpace n) :
    regularSum n (regularRepresentation n g f) = regularSum n f := by
  classical
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun _ => rfl)

lemma polytabloid_sum_eq_zero {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0) :
    regularSum n (polytabloid lam) = 0 := by
  classical
  have he : regularSum n (polytabloid lam) =
      ∑ c : colSubgroup lam, (Fintype.card (rowSubgroup lam) : ℂ) * complexSign n c.1 := by
    simp [polytabloid, regularSum_single, complexSign]
  rw [he, ← Finset.mul_sum, colSubgroup_sum_sign_eq_zero lam hl, mul_zero]

def spechtInclusion {n : ℕ} (lam : Partition n) : Specht lam →ₗ[ℂ] RegularSpace n :=
  (spechtSubrepresentation lam).toSubmodule.subtype

lemma spechtSum_eq_zero {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0)
    (x : Specht lam) : regularSum n (spechtInclusion lam x) = 0 := by
  have hle : (spechtSubrepresentation lam).toSubmodule ≤ (regularSum n).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change regularSum n (regularRepresentation n g (polytabloid lam)) = 0
    rw [regularSum_invariant, polytabloid_sum_eq_zero lam hl]
  exact hle x.property

lemma specht_invariant_eq_zero {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0)
    (x : Specht lam) (hx : ∀ g, spechtRepresentation lam g x = x) : x = 0 := by
  classical
  let f : RegularSpace n := spechtInclusion lam x
  have hfixed (g : SymmetricGroup n) : regularRepresentation n g f = f := by
    exact congrArg (spechtInclusion lam) (hx g)
  have hc (g : SymmetricGroup n) : f g = f 1 := by
    have h := congrArg (fun y : RegularSpace n => y 1) (hfixed g⁻¹)
    simpa using h
  have hs := spechtSum_eq_zero lam hl x
  change ∑ g, f g = 0 at hs
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hn : (Fintype.card (SymmetricGroup n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hf : f 1 = 0 := (mul_eq_zero.mp hs).resolve_left hn
  have hinj : Function.Injective (spechtInclusion lam) := Subtype.val_injective
  apply hinj
  rw [map_zero]
  change f = 0
  ext g
  exact (hc g).trans hf

end SignedSweeps
end

end OAI
