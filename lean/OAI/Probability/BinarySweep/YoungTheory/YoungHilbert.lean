import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungSpecht
import OAI.Probability.BinarySweep.Representations.UnitaryTransport

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

variable (μ : YoungDiagram)

def spechtHilbertInclude : SpechtSpace μ →ₗ[ℂ] EuclideanSpace ℂ (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm.toLinearMap.comp (spechtInclude μ)

lemma spechtHilbertInclude_injective : Function.Injective (spechtHilbertInclude μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm.injective.comp (spechtInclude_injective μ)

abbrev SpechtHilbert := (spechtHilbertInclude μ).range

def spechtHilbertEquiv : SpechtSpace μ ≃ₗ[ℂ] SpechtHilbert μ :=
  LinearEquiv.ofInjective (spechtHilbertInclude μ) (spechtHilbertInclude_injective μ)

def hilbertSpecht : Representation ℂ (G μ) (SpechtHilbert μ) :=
  letI : AddCommGroup (SpechtSpace μ) := Module.addCommMonoidToAddCommGroup ℂ
  Irrep.conjugateRep (spechtRep μ) (spechtHilbertEquiv μ)

instance : (hilbertSpecht μ).IsIrreducible :=
  letI : AddCommGroup (SpechtSpace μ) := Module.addCommMonoidToAddCommGroup ℂ
  Irrep.irreducible_equiv _ _ (Irrep.conjugateEquiv _ _)

lemma spechtHilbertEquiv_coeff (v : SpechtSpace μ) (t : Tabloid μ) :
    (spechtHilbertEquiv μ v).val t = spechtInclude μ v t := rfl

lemma hilbertSpecht_coeff (g : G μ) (v : SpechtHilbert μ) (t : Tabloid μ) :
    (hilbertSpecht μ g v).val t = v.val (g⁻¹ • t) := by
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm
      (spechtHilbertEquiv μ w)))).val t = _
  rw [LinearEquiv.symm_apply_apply,spechtHilbertEquiv_coeff,spechtInclude_rep]
  rfl

instance hilbertNormed : NormedAddCommGroup (SpechtHilbert μ) :=
  Submodule.normedAddCommGroup _
instance hilbertInner : InnerProductSpace ℂ (SpechtHilbert μ) :=
  Submodule.innerProductSpace _

lemma hilbertSpecht_inner (g : G μ) (v w : SpechtHilbert μ) :
    inner ℂ (hilbertSpecht μ g v) (hilbertSpecht μ g w) = inner ℂ v w := by
  change inner ℂ (hilbertSpecht μ g v).val (hilbertSpecht μ g w).val = inner ℂ v.val w.val
  simp only [PiLp.inner_apply,RCLike.inner_apply,hilbertSpecht_coeff]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun t => w.val t * star (v.val t))

lemma hilbertSpecht_unitary (g : G μ) (v : SpechtHilbert μ) :
    ‖hilbertSpecht μ g v‖ = ‖v‖ :=
  ((hilbertSpecht μ g).isometryOfInner (hilbertSpecht_inner μ g)).norm_map v

lemma hilbertSpecht_finrank : Module.finrank ℂ (SpechtHilbert μ) = Module.finrank ℂ (SpechtSpace μ) :=
  (spechtHilbertEquiv μ).finrank_eq.symm

end BinaryCoordinateSweeps.Young

end

section

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed
variable {n : ℕ}

def koszulSign (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) : ℤˣ :=
  ∏ x ∈ finPairsLT n, if β x.1 = true ∧ β x.2 = true then
    (if g x.1 ≤ g x.2 then -1 else 1) else 1

@[simp] lemma koszulSign_one (β : Fin n → Bool) : koszulSign β 1 = 1 := by
  apply Finset.prod_eq_one
  intro x hx
  simp only [one_apply]
  rw [ite_eq_right (mem_finPairsLT.mp hx).not_ge]
  simp

lemma koszulSign_inv (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    koszulSign (β ∘ g.symm) g⁻¹ = koszulSign β g := by
  unfold koszulSign
  apply prod_nbij (signBijAux g⁻¹) signBijAux_mem signBijAux_injOn signBijAux_surj
  rintro ⟨a,b⟩ hab
  have hab' : b < a := mem_finPairsLT.mp hab
  by_cases h : g.symm b < g.symm a
  · simp [signBijAux, h, hab'.not_ge]
  · simp [signBijAux, h, hab'.le, and_comm, le_of_not_gt h]

lemma koszulSign_mul (β : Fin n → Bool) (f g : Equiv.Perm (Fin n)) :
    koszulSign β (f*g) = koszulSign (β ∘ g.symm) f * koszulSign β g := by
  rw [← koszulSign_inv β g]
  unfold koszulSign
  rw [← Finset.prod_mul_distrib]
  apply prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj
  rintro ⟨a,b⟩ hab
  dsimp only [signBijAux]
  rw [mem_finPairsLT] at hab
  by_cases hg : g b < g a
  · simp [hg, mul_apply, hab.not_ge]
  obtain hf | hf := (f.injective.ne (g.injective.ne hab.ne)).lt_or_gt <;>
    simp_all [mul_apply, le_of_lt, not_le_of_gt, not_lt_of_ge, and_comm]

lemma koszulSign_sq (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    koszulSign β g * koszulSign β g = 1 := by
  exact Int.units_mul_self _

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed
variable {n : ℕ}

lemma adjacent_swap_inversion (a b i j : Fin n) (hab : a.val + 1 = b.val) (hij : j < i) :
    Equiv.swap a b i ≤ Equiv.swap a b j ↔ i = b ∧ j = a := by
  have hn : a ≠ b := by intro h; subst b; omega
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all only [Fin.le_def, Fin.lt_def, Fin.ext_iff, and_true, and_false, iff_true, iff_false] <;> omega

lemma koszulSign_swap_adjacent (β : Fin n → Bool) (a b : Fin n) (hab : a.val+1=b.val) :
    koszulSign β (Equiv.swap a b) = if β a = true ∧ β b = true then -1 else 1 := by
  unfold koszulSign
  rw [Finset.prod_eq_single (⟨b,a⟩ : Σ _ : Fin n, Fin n)]
  · simp only [swap_apply_right, swap_apply_left]
    rw [ite_eq_left (show a ≤ b by omega)]
    simp only [and_comm]
  · rintro ⟨i,j⟩ hij hne
    have hi : ¬ Equiv.swap a b i ≤ Equiv.swap a b j := by
      rw [adjacent_swap_inversion a b i j hab (mem_finPairsLT.mp hij)]
      rintro ⟨rfl,rfl⟩; exact hne rfl
    simp [hi]
  · intro h
    exact False.elim (h (mem_finPairsLT.mpr (show a < b by omega)))

lemma mask_swap (β : Fin n → Bool) (a b : Fin n) (h : β a = β b) :
    β ∘ Equiv.swap a b = β := by
  funext i
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

lemma koszulSign_conjugate (β : Fin n → Bool) (g f : Equiv.Perm (Fin n))
    (hf : β ∘ f.symm = β) :
    koszulSign (β ∘ g.symm) (g*f*g⁻¹) = koszulSign β f := by
  have hc : (g*f*g⁻¹)*g = g*f := by group
  have h := congrArg (koszulSign β) hc
  rw [koszulSign_mul β (g*f*g⁻¹) g, koszulSign_mul β g f, hf] at h
  have he : koszulSign β g * koszulSign β f = koszulSign β f * koszulSign β g := mul_comm _ _
  rw [he] at h
  exact mul_right_cancel h

lemma exists_perm_pair (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm (Fin n), g a = c ∧ g b = d := by
  let h := Equiv.swap a c
  have hh : h b ≠ c := by
    intro hbc
    have ha : h a = c := by simp [h]
    exact hab (h.injective (ha.trans hbc.symm))
  refine ⟨Equiv.swap (h b) d * h, ?_, ?_⟩
  · change Equiv.swap (h b) d (h a) = c
    rw [show h a = c by simp [h]]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hh) hcd
  · simp

lemma koszulSign_swap (β : Fin n → Bool) (a b : Fin n) (hab : a ≠ b)
    (hβ : β a = β b) :
    koszulSign β (Equiv.swap a b) = if β a = true then -1 else 1 := by
  have hn : 2 ≤ n := by
    by_contra h
    have ha := a.isLt
    have hb := b.isLt
    apply hab
    apply Fin.ext
    omega
  let c : Fin n := ⟨0, by omega⟩
  let d : Fin n := ⟨1, by omega⟩
  have hcd : c ≠ d := by intro hh; have := congrArg Fin.val hh; dsimp [c,d] at this; omega
  obtain ⟨g,hga,hgb⟩ := exists_perm_pair a b c d hab hcd
  have hc := koszulSign_conjugate β g (Equiv.swap a b) (by simpa using mask_swap β a b hβ)
  have hconj : g * Equiv.swap a b * g⁻¹ = Equiv.swap c d := by
    have ht := Equiv.symm_trans_swap_trans a b g
    change g * Equiv.swap a b * g⁻¹ = Equiv.swap (g a) (g b) at ht
    simpa only [hga,hgb] using ht
  rw [hconj, koszulSign_swap_adjacent _ c d (by rfl)] at hc
  have hgca : g.symm c = a := by rw [← hga]; simp
  have hgdb : g.symm d = b := by rw [← hgb]; simp
  simpa only [Function.comp_apply, hgca, hgdb, ← hβ, and_self] using hc.symm

end BinaryCoordinateSweeps.Signed

end

end OAI
