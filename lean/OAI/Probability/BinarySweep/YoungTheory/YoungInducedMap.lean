import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.EvenPostselection
import OAI.Probability.BinarySweep.YoungTheory.YoungSpecht

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

def tabloidVector (ρ : Representation ℂ (G μ) V) (v : V) (t : Tabloid μ) : V :=
  ρ ((tabloidOfPerm_surjective μ t).choose) v

lemma tabloidVector_eq (ρ : Representation ℂ (G μ) V) (v : V)
    (hv : ∀ r : rowStabilizer μ, ρ r.val v = v) (g : G μ) :
    tabloidVector μ ρ v (tabloidOfPerm μ g) = ρ g v := by
  let h := (tabloidOfPerm_surjective μ (tabloidOfPerm μ g)).choose
  have hh : tabloidOfPerm μ h = tabloidOfPerm μ g :=
    (tabloidOfPerm_surjective μ (tabloidOfPerm μ g)).choose_spec
  have hr : g⁻¹ * h ∈ rowStabilizer μ := (tabloidOfPerm_eq_iff μ _ _).mp hh.symm
  have he := hv ⟨g⁻¹*h,hr⟩
  have he' := congrArg (ρ g) he
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he'
  exact he'

lemma tabloidVector_smul (ρ : Representation ℂ (G μ) V) (v : V)
    (hv : ∀ r : rowStabilizer μ, ρ r.val v = v) (g : G μ) (t : Tabloid μ) :
    tabloidVector μ ρ v (g • t) = ρ g (tabloidVector μ ρ v t) := by
  obtain ⟨h,rfl⟩ := tabloidOfPerm_surjective μ t
  rw [smul_tabloidOfPerm, tabloidVector_eq μ ρ v hv, tabloidVector_eq μ ρ v hv,
    map_mul, Module.End.mul_apply]

def fromTabloid (ρ : Representation ℂ (G μ) V) (v : V) : (Tabloid μ → ℂ) →ₗ[ℂ] V where
  toFun w := ∑ t, w t • tabloidVector μ ρ v t
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]

lemma fromTabloid_basis (ρ : Representation ℂ (G μ) V) (v : V) (t : Tabloid μ) :
    fromTabloid μ ρ v (tabloidBasis μ t) = tabloidVector μ ρ v t := by
  simp [fromTabloid, tabloidBasis, Pi.single_apply]

lemma fromTabloid_intertwines (ρ : Representation ℂ (G μ) V) (v : V)
    (hv : ∀ r : rowStabilizer μ, ρ r.val v = v) (g : G μ) (w : Tabloid μ → ℂ) :
    fromTabloid μ ρ v (tabloidRepresentation μ g w) = ρ g (fromTabloid μ ρ v w) := by
  conv_lhs => rw [← sum_tabloidBasis μ w]
  rw [map_sum, map_sum]
  conv_rhs => rw [← sum_tabloidBasis μ w]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [map_smul, rep_basis, fromTabloid_basis, tabloidVector_smul μ ρ v hv]

lemma spechtPoly_column (c : C μ) :
    spechtRep μ c.val (spechtPoly μ) = signC μ c.val • spechtPoly μ := by
  apply spechtInclude_injective μ
  simp only [spechtInclude_rep, spechtInclude_poly, map_smul]
  have he : tabloidRepresentation μ c.val (polytabloid μ) =
      signC μ c.val • polytabloid μ := by
    unfold polytabloid
    rw [columnAnti_apply, map_sum]
    have hh := Equiv.sum_comp (Equiv.mulLeft c)
      (fun d : C μ => signC μ c.val • (signC μ d.val •
        tabloidRepresentation μ d.val (tabloidBasis μ (tabloidOfPerm μ 1))))
    rw [Finset.smul_sum, ← hh]
    apply Finset.sum_congr rfl
    intro d hd
    change tabloidRepresentation μ c.val
      (signC μ d.val • tabloidRepresentation μ d.val (tabloidBasis μ (tabloidOfPerm μ 1))) =
      signC μ c.val • (signC μ (c*d).val •
        tabloidRepresentation μ (c*d).val (tabloidBasis μ (tabloidOfPerm μ 1)))
    simp only [map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
    rw [show signC μ c.val * (signC μ c.val * signC μ d.val) = signC μ d.val from by
      rw [← mul_assoc, signC_sq, one_mul]]
  exact he

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm

namespace BinaryCoordinateSweeps.Signed
variable {n : ℕ}

lemma mask_ofSubtype (β : Fin n → Bool) (b : Bool)
    (f : Equiv.Perm {i // β i = b}) : β ∘ (Equiv.Perm.ofSubtype f).symm = β := by
  funext i
  change β ((Equiv.Perm.ofSubtype f⁻¹) i) = β i
  by_cases h : β i = b
  · rw [Equiv.Perm.ofSubtype_apply_of_mem f⁻¹ h]
    exact (f⁻¹ ⟨i,h⟩).property.trans h.symm
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem f⁻¹ h]

lemma koszulSign_ofSubtype (β : Fin n → Bool) (b : Bool)
    (f : Equiv.Perm {i // β i = b}) :
    koszulSign β (Equiv.Perm.ofSubtype f) = if b = true then Equiv.Perm.sign f else 1 := by
  induction f using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f a c hac ih =>
    rw [map_mul, koszulSign_mul, mask_ofSubtype, ofSubtype_swap_eq,
      koszulSign_swap _ _ _ (fun h => hac (Subtype.ext h)) (a.property.trans c.property.symm),
      a.property, ih, map_mul, Equiv.Perm.sign_swap hac]
    split_ifs <;> simp

lemma mask_of_fixed_complement (β : Fin n → Bool) (b : Bool) (g : Equiv.Perm (Fin n))
    (hg : ∀ i, β i ≠ b → g i = i) : ∀ i, β (g i) = b ↔ β i = b := by
  intro i
  constructor
  · intro h
    by_contra hi
    rw [hg i hi] at h
    exact hi h
  · intro h
    by_contra hi
    have he := hg (g i) hi
    have eq := g.injective he
    rw [eq] at hi
    exact hi h

lemma mask_fixed_complement (β : Fin n → Bool) (b : Bool) (g : Equiv.Perm (Fin n))
    (hg : ∀ i, β i ≠ b → g i = i) : β ∘ g.symm = β := by
  let f : Equiv.Perm {i // β i = b} :=
    g.subtypePerm (mask_of_fixed_complement β b g hg)
  have he : Equiv.Perm.ofSubtype f = g := by
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro i hi
    by_contra h
    exact hi (hg i h)
  simpa only [he] using mask_ofSubtype β b f

lemma koszulSign_of_fixed_complement (β : Fin n → Bool) (b : Bool)
    (g : Equiv.Perm (Fin n)) (hg : ∀ i, β i ≠ b → g i = i) :
    koszulSign β g = if b = true then Equiv.Perm.sign g else 1 := by
  let f : Equiv.Perm {i // β i = b} :=
    g.subtypePerm (mask_of_fixed_complement β b g hg)
  have he : Equiv.Perm.ofSubtype f = g := by
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro i hi
    by_contra h
    exact hi (hg i h)
  have hs := koszulSign_ofSubtype β b f
  rw [← Equiv.Perm.sign_ofSubtype f, he] at hs
  exact hs

end BinaryCoordinateSweeps.Signed

end

end OAI
