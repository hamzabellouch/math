import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungInducedMap

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Equiv Equiv.Perm

namespace BinaryCoordinateSweeps.Young

def InHook (μ : YoungDiagram) (p : ℕ) : Prop :=
  ∀ x : Cell μ, row x < p ∨ col x < p

variable {μ : YoungDiagram} {p : ℕ}

def hookLabel (h : InHook μ p) (x : Cell μ) : Bool × Fin p :=
  if hr : row x < p then (false, ⟨row x,hr⟩)
  else (true, ⟨col x,(h x).resolve_left hr⟩)

lemma hookLabel_top (h : InHook μ p) (x : Cell μ) :
    (hookLabel h x).1 = false ↔ row x < p := by
  unfold hookLabel
  split_ifs <;> simp_all

lemma hookLabel_bottom (h : InHook μ p) (x : Cell μ) :
    (hookLabel h x).1 = true ↔ ¬row x < p := by
  unfold hookLabel
  split_ifs <;> simp_all

lemma hookLabel_eq_top (h : InHook μ p) (x y : Cell μ)
    (hx : row x < p) (he : hookLabel h y = hookLabel h x) : row y = row x := by
  have hy : row y < p := (hookLabel_top h y).mp
    ((congrArg Prod.fst he).trans ((hookLabel_top h x).mpr hx))
  have hh := congrArg (fun z : Bool × Fin p => z.2.val) he
  simpa only [hookLabel, dite_eq_left hx, dite_eq_left hy] using hh

lemma hookLabel_eq_bottom (h : InHook μ p) (x y : Cell μ)
    (hx : ¬row x < p) (he : hookLabel h y = hookLabel h x) : col y = col x := by
  have hy : ¬row y < p := (hookLabel_bottom h y).mp
    ((congrArg Prod.fst he).trans ((hookLabel_bottom h x).mpr hx))
  have hh := congrArg (fun z : Bool × Fin p => z.2.val) he
  simpa only [hookLabel, dite_eq_right hx, dite_eq_right hy] using hh

lemma hook_return_column_fixes (h : InHook μ p) (c : C μ) (r : rowStabilizer μ)
    (hr : ∀ x, hookLabel h ((c.val*r.val) x) = hookLabel h x)
    (x : Cell μ) (hx : row x < p) : c.val x = x := by
  have hrinv : row (r.val⁻¹ x) = row x := (r⁻¹).property x
  have hz : row (r.val⁻¹ x) < p := by rwa [hrinv]
  have hh := hr (r.val⁻¹ x)
  simp only [mul_apply, show r.val (r.val⁻¹ x) = x from r.val.apply_symm_apply x] at hh
  apply Subtype.ext
  apply Prod.ext
  · exact (hookLabel_eq_top h _ _ hz hh).trans ((r⁻¹).property x)
  · exact c.property x

lemma hook_return_row_fixes (h : InHook μ p) (c : C μ) (r : rowStabilizer μ)
    (hr : ∀ x, hookLabel h ((c.val*r.val) x) = hookLabel h x)
    (x : Cell μ) (hx : ¬row x < p) : r.val x = x := by
  apply Subtype.ext
  apply Prod.ext
  · exact r.property x
  · have hh := hookLabel_eq_bottom h x ((c.val*r.val) x) hx (hr x)
    change col (c.val (r.val x)) = col x at hh
    rw [c.property] at hh
    exact hh

variable {n : ℕ}
def hookWord (h : InHook μ p) (e : Cell μ ≃ Fin n) : Fin n → Bool × Fin p :=
  hookLabel h ∘ e.symm

lemma hookWord_comp_eq (h : InHook μ p) (e : Cell μ ≃ Fin n) (g : G μ) :
    hookWord h e ∘ e.permCongr g = hookWord h e ↔
      ∀ x, hookLabel h (g x) = hookLabel h x := by
  constructor
  · intro hh x
    have he := congrFun hh (e x)
    simpa only [hookWord, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply] using he
  · intro hh
    funext i
    simpa only [hookWord, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hh (e.symm i)

lemma hook_return_sign (h : InHook μ p) (e : Cell μ ≃ Fin n)
    (c : C μ) (r : rowStabilizer μ)
    (hr : hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e) :
    Signed.signC (Prod.fst ∘ hookWord h e) (e.permCongr (c.val*r.val))⁻¹ = signC μ c.val := by
  let β := Prod.fst ∘ hookWord h e
  have hh := (hookWord_comp_eq h e _).mp hr
  have hc : ∀ i, β i ≠ true → e.permCongr c.val i = i := by
    intro i hi
    have hx : row (e.symm i) < p := by
      apply (hookLabel_top h _).mp
      exact Bool.eq_false_of_not_eq_true hi
    have hf := hook_return_column_fixes h c r hh (e.symm i) hx
    simp only [Equiv.permCongr_apply, hf, Equiv.apply_symm_apply]
  have hrf : ∀ i, β i ≠ false → e.permCongr r.val i = i := by
    intro i hi
    have hx : ¬row (e.symm i) < p := by
      intro hx
      exact hi ((hookLabel_top h _).mpr hx)
    have hf := hook_return_row_fixes h c r hh (e.symm i) hx
    simp only [Equiv.permCongr_apply, hf, Equiv.apply_symm_apply]
  have hcm := Signed.mask_fixed_complement β true (e.permCongr c.val) hc
  have hrm := Signed.mask_fixed_complement β false (e.permCongr r.val) hrf
  have hcs := Signed.koszulSign_of_fixed_complement β true (e.permCongr c.val) hc
  have hrs := Signed.koszulSign_of_fixed_complement β false (e.permCongr r.val) hrf
  simp only [ite_true, Bool.false_eq_true, ite_false] at hcs hrs
  have hs : Signed.koszulSign β (e.permCongr (c.val*r.val)) = Equiv.Perm.sign c.val := by
    rw [Equiv.permCongr_mul, Signed.koszulSign_mul, hrm, hcs, hrs, mul_one,
      Equiv.Perm.sign_permCongr]
  have hm : β ∘ (e.permCongr (c.val*r.val)).symm = β := by
    change Prod.fst ∘ hookWord h e ∘ (e.permCongr (c.val*r.val)).symm = β
    have hi := congrArg (fun w => w ∘ (e.permCongr (c.val*r.val)).symm) hr
    have hi' : hookWord h e = hookWord h e ∘ (e.permCongr (c.val*r.val)).symm := by
      simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hi
    exact congrArg (fun w => Prod.fst ∘ w) hi'.symm
  have hinv := Signed.koszulSign_inv β (e.permCongr (c.val*r.val))
  rw [hm,hs] at hinv
  change ((Signed.koszulSign β _ : ℤ) : ℂ) = _
  rw [hinv]
  rfl

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Representation

namespace BinaryCoordinateSweeps.Young
variable {μ : YoungDiagram} {p n : ℕ}

instance rowStabilizer_fintype (μ : YoungDiagram) : Fintype (rowStabilizer μ) := Fintype.ofFinite _

def hookRep (e : Cell μ ≃ Fin n) (p : ℕ) :
    Representation ℂ (G μ) ((Fin n → Bool × Fin p) → ℂ) :=
  (Signed.tensorRep Prod.fst n).comp e.permCongrHom.toMonoidHom

def hookRowVector (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    (Fin n → Bool × Fin p) → ℂ :=
  ∑ r : rowStabilizer μ, hookRep e p r.val (Pi.single (hookWord h e) 1)

lemma hookRowVector_fixed (h : InHook μ p) (e : Cell μ ≃ Fin n) (r : rowStabilizer μ) :
    hookRep e p r.val (hookRowVector h e) = hookRowVector h e := by
  rw [hookRowVector,map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft r) (fun t : rowStabilizer μ =>
    hookRep e p t.val (Pi.single (hookWord h e) 1))

def hookMap (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    IntertwiningMap (spechtRep μ) (hookRep e p) where
  toLinearMap := (fromTabloid μ (hookRep e p) (hookRowVector h e)).comp (spechtInclude μ)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, spechtInclude_rep]
    exact fromTabloid_intertwines μ _ _ (hookRowVector_fixed h e) g (spechtInclude μ v)

lemma hookMap_poly (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    hookMap h e (spechtPoly μ) =
      ∑ c : C μ, ∑ r : rowStabilizer μ,
        signC μ c.val • hookRep e p (c.val*r.val) (Pi.single (hookWord h e) 1) := by
  change fromTabloid μ (hookRep e p) (hookRowVector h e)
    (spechtInclude μ (spechtPoly μ)) = _
  rw [spechtInclude_poly, polytabloid, columnAnti_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smul, fromTabloid_intertwines μ _ _ (hookRowVector_fixed h e),
    fromTabloid_basis, tabloidVector_eq μ _ _ (hookRowVector_fixed h e), map_one,
    Module.End.one_apply, hookRowVector, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_mul, Module.End.mul_apply]

lemma hook_term_coefficient (h : InHook μ p) (e : Cell μ ≃ Fin n)
    (c : C μ) (r : rowStabilizer μ) :
    (signC μ c.val • hookRep e p (c.val*r.val) (Pi.single (hookWord h e) 1)) (hookWord h e) =
      if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then (1 : ℂ) else 0 := by
  change signC μ c.val * (Signed.signC (Prod.fst ∘ hookWord h e)
    (e.permCongr (c.val*r.val))⁻¹ *
      (Pi.single (hookWord h e) (1 : ℂ) : (Fin n → Bool × Fin p) → ℂ)
        (hookWord h e ∘ e.permCongr (c.val*r.val))) = _
  by_cases hh : hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e
  · rw [ite_eq_left hh, hook_return_sign h e c r hh, hh, Pi.single_eq_same, mul_one, signC_sq]
  · rw [ite_eq_right hh, Pi.single_eq_of_ne hh, mul_zero, mul_zero]

lemma hookMap_poly_coefficient (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    hookMap h e (spechtPoly μ) (hookWord h e) =
      ∑ c : C μ, ∑ r : rowStabilizer μ,
        if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then (1 : ℂ) else 0 := by
  rw [hookMap_poly]
  simp only [Finset.sum_apply, hook_term_coefficient]

lemma hookMap_nonzero (h : InHook μ p) (e : Cell μ ≃ Fin n) : hookMap h e ≠ 0 := by
  intro hz
  have he := hookMap_poly_coefficient h e
  rw [hz] at he
  change (0 : ℂ) = _ at he
  have hre := congrArg Complex.re he
  simp only [Complex.zero_re, Complex.re_sum, apply_ite,
    Complex.one_re, Complex.zero_re] at hre
  have hs (c : C μ) (r : rowStabilizer μ) :
      (0 : ℝ) ≤ if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then 1 else 0 := by
    split_ifs <;> norm_num
  have hid : (1 : ℝ) ≤ ∑ r : rowStabilizer μ,
      if hookWord h e ∘ e.permCongr ((1 : C μ).val*r.val) = hookWord h e then 1 else 0 := by
    have hi := Finset.single_le_sum (s := Finset.univ) (f := fun r : rowStabilizer μ =>
      if hookWord h e ∘ e.permCongr ((1 : C μ).val*r.val) = hookWord h e then (1 : ℝ) else 0)
      (fun r _ => hs 1 r) (Finset.mem_univ (1 : rowStabilizer μ))
    have he1 : e.permCongr (1 : G μ) = (1 : Equiv.Perm (Fin n)) := by
      apply Equiv.ext
      intro i
      exact e.apply_symm_apply i
    simpa only [Subgroup.coe_one, one_mul, he1, Equiv.Perm.coe_one, Function.comp_id,
      ite_true] using hi
  have hle := Finset.single_le_sum (s := Finset.univ) (f := fun c : C μ =>
      ∑ r : rowStabilizer μ,
        if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then (1 : ℝ) else 0)
    (fun c _ => Finset.sum_nonneg (fun r _ => hs c r)) (Finset.mem_univ (1 : C μ))
  linarith

theorem hookMap_injective (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    Function.Injective (hookMap h e) :=
  (Representation.IsIrreducible.injective_or_eq_zero (k := ℂ) (G := G μ)
    (V := SpechtSpace μ) (W := (Fin n → Bool × Fin p) → ℂ) (hookMap h e)).resolve_right
      (hookMap_nonzero h e)

end BinaryCoordinateSweeps.Young

end

end OAI
