import Mathlib
import OAI.Computability.VertexCover.Analysis.ThresholdListEnergy

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                               

namespace VertexCover.Restriction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure EnergyForm (E : Type*) [AddCommGroup E] [Module ℝ E] where
  form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ
  symm : ∀ x y, form x y = form y x
  nonneg : ∀ x, 0 ≤ form x x

namespace EnergyForm
variable (B : EnergyForm E)

def energy (x : E) : ℝ := B.form x x

@[simp] theorem energy_zero : B.energy 0 = 0 := by simp [energy]
theorem energy_nonneg (x : E) : 0 ≤ B.energy x := B.nonneg x

theorem energy_add (x y : E) :
    B.energy (x + y) = B.energy x + B.energy y + 2 * B.form x y := by
  simp only [energy, map_add, LinearMap.add_apply]
  rw [B.symm y x]
  ring

theorem energy_sub (x y : E) :
    B.energy (x - y) = B.energy x + B.energy y - 2 * B.form x y := by
  simp only [energy, map_sub, LinearMap.sub_apply]
  rw [B.symm y x]
  ring

structure Projection where
  toLinearMap : E →ₗ[ℝ] E
  idem : ∀ x, toLinearMap (toLinearMap x) = toLinearMap x
  selfAdjoint : ∀ x y, B.form (toLinearMap x) y = B.form x (toLinearMap y)

namespace Projection
variable {B : EnergyForm E}
instance : CoeFun (B.Projection) (fun _ => E → E) := ⟨fun P => P.toLinearMap⟩

@[simp] theorem apply_idem (P : B.Projection) (x : E) : P (P x) = P x := P.idem x
@[simp] theorem map_zero (P : B.Projection) : P 0 = 0 := P.toLinearMap.map_zero
@[simp] theorem map_add (P : B.Projection) (x y : E) : P (x + y) = P x + P y :=
  P.toLinearMap.map_add x y
@[simp] theorem map_sub (P : B.Projection) (x y : E) : P (x - y) = P x - P y :=
  P.toLinearMap.map_sub x y
@[simp] theorem map_smul (P : B.Projection) (a : ℝ) (x : E) : P (a • x) = a • P x :=
  P.toLinearMap.map_smul a x

@[ext] theorem ext {P Q : B.Projection} (h : ∀ x, P x = Q x) : P = Q := by
  cases P with
  | mk p hp hs =>
    cases Q with
    | mk q hq ht =>
      have : p = q := LinearMap.ext h
      subst q
      rfl

def ident : B.Projection where
  toLinearMap := LinearMap.id
  idem _ := rfl
  selfAdjoint _ _ := rfl

@[simp] theorem ident_apply (x : E) : (ident : B.Projection) x = x := rfl

def zero : B.Projection where
  toLinearMap := 0
  idem _ := rfl
  selfAdjoint x y := by simp

@[simp] theorem zero_apply (x : E) : (zero : B.Projection) x = 0 := rfl

def residual (P : B.Projection) : B.Projection where
  toLinearMap := LinearMap.id - P.toLinearMap
  idem x := by simp
  selfAdjoint x y := by
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, _root_.map_sub] using
      congrArg (fun value => B.form x y - value) (P.selfAdjoint x y)

@[simp] theorem residual_apply (P : B.Projection) (x : E) : P.residual x = x - P x := rfl
@[simp] theorem residual_residual (P : B.Projection) : P.residual.residual = P := by
  ext x
  simp

theorem inner_image (P : B.Projection) (x : E) : B.form x (P x) = B.energy (P x) := by
  simpa only [P.apply_idem, energy] using (P.selfAdjoint x (P x)).symm

theorem pythagoras (P : B.Projection) (x : E) :
    B.energy x = B.energy (P x) + B.energy (P.residual x) := by
  rw [residual_apply, B.energy_sub, P.inner_image]
  ring

theorem energy_le (P : B.Projection) (x : E) : B.energy (P x) ≤ B.energy x := by
  have h := P.pythagoras x
  have := B.energy_nonneg (P.residual x)
  linarith

def comp (P Q : B.Projection) (h : ∀ x, P (Q x) = Q (P x)) : B.Projection where
  toLinearMap := P.toLinearMap.comp Q.toLinearMap
  idem x := by
    change P (Q (P (Q x))) = P (Q x)
    rw [← h, P.apply_idem, Q.apply_idem]
  selfAdjoint x y := by
    change B.form (P (Q x)) y = B.form x (P (Q y))
    rw [P.selfAdjoint, Q.selfAdjoint, h]

@[simp] theorem comp_apply (P Q : B.Projection) (h) (x : E) : P.comp Q h x = P (Q x) := rfl

theorem residual_commute (P Q : B.Projection) (h : ∀ x, P (Q x) = Q (P x)) (x : E) :
    P.residual (Q x) = Q (P.residual x) := by
  simp [h]

theorem comp_loss_le (P Q : B.Projection) (h : ∀ x, P (Q x) = Q (P x)) (x : E) :
    B.energy ((P.comp Q h).residual x) ≤
      B.energy (P.residual x) + B.energy (Q.residual x) := by
  have h₁ := P.pythagoras (Q x)
  have h₂ := Q.pythagoras x
  have h₃ := (P.comp Q h).pythagoras x
  have h₄ := Q.energy_le (P.residual x)
  rw [← P.residual_commute Q h] at h₄
  simp only [comp_apply] at h₃
  linarith

theorem residual_le_of_nested (P Q : B.Projection) (h : ∀ x, P (Q x) = Q x) (x : E) :
    B.energy (P.residual x) ≤ B.energy (Q.residual x) := by
  have horth : B.form (P.residual x) (P x - Q x) = 0 := by
    rw [residual_apply]
    simp only [_root_.map_sub, LinearMap.sub_apply]
    rw [P.selfAdjoint x (P x), P.apply_idem, P.selfAdjoint x (Q x), h]
    ring
  have he := B.energy_add (P.residual x) (P x - Q x)
  have hs : P.residual x + (P x - Q x) = Q.residual x := by simp
  rw [hs, horth, mul_zero, add_zero] at he
  have := B.energy_nonneg (P x - Q x)
  linarith

def productMap {ι : Type*} (P : ι → B.Projection) : List ι → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | i :: is => (P i).toLinearMap.comp (productMap P is)

@[simp] theorem productMap_nil {ι : Type*} (P : ι → B.Projection) (x : E) :
    productMap P [] x = x := rfl
@[simp] theorem productMap_cons {ι : Type*} (P : ι → B.Projection)
    (i : ι) (is : List ι) (x : E) :
    productMap P (i :: is) x = P i (productMap P is x) := rfl

@[simp] theorem productMap_append {ι : Type*} (P : ι → B.Projection)
    (is js : List ι) (x : E) :
    productMap P (is ++ js) x = productMap P is (productMap P js x) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, productMap_cons, ih]

theorem productMap_commute {ι : Type*} (P : ι → B.Projection)
    (Q : B.Projection) (h : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (is : List ι) (x : E) :
    productMap P is (Q x) = Q (productMap P is x) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [productMap_cons, ih, h]

theorem productMap_fixed_of_mem {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (is : List ι) (j : ι) (hj : j ∈ is) (x : E) :
    P j (productMap P is x) = productMap P is x := by
  induction is with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with rfl | ht
    · simp only [productMap_cons, apply_idem]
    · simp only [productMap_cons, h j i, ih ht]

def product {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (is : List ι) : B.Projection where
  toLinearMap := productMap P is
  idem x := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [productMap_cons]
      rw [productMap_commute P (P i) (fun j => h j i), (P i).apply_idem, ih]
  selfAdjoint x y := by
    induction is generalizing x y with
    | nil => rfl
    | cons i is ih =>
      simp only [productMap_cons]
      rw [(P i).selfAdjoint, ih,
        productMap_commute P (P i) (fun j => h j i)]

@[simp] theorem product_apply {ι : Type*} (P : ι → B.Projection) (h) (is : List ι)
    (x : E) : product P h is x = productMap P is x := rfl

theorem product_loss_le {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (is : List ι) (x : E) :
    B.energy ((product P h is).residual x) ≤
      (is.map (fun i => B.energy ((P i).residual x))).sum := by
  induction is with
  | nil => simp [residual_apply]
  | cons i is ih =>
    have hc : ∀ x, P i (product P h is x) = product P h is (P i x) :=
      fun x => (productMap_commute P (P i) (fun j => h j i) is x).symm
    have he : product P h (i :: is) = (P i).comp (product P h is) hc := by
      ext x
      rfl
    rw [he, List.map_cons, List.sum_cons]
    exact ((P i).comp_loss_le (product P h is) hc x).trans (add_le_add le_rfl ih)

def difference (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (i : ℕ) : B.Projection :=
  (P i).residual.comp (product P h (List.range i)) (fun x => by
    simp only [residual_apply, product_apply, _root_.map_sub]
    rw [productMap_commute P (P i) (fun k => h k i)])

@[simp] theorem difference_apply (P : ℕ → B.Projection) (h) (i : ℕ) (x : E) :
    difference P h i x = productMap P (List.range i) x -
      P i (productMap P (List.range i) x) := rfl

theorem difference_energy_sum (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, B.energy (difference P h i x)) +
      B.energy (productMap P (List.range n) x) = B.energy x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, productMap_append]
    simp only [productMap_cons, productMap_nil]
    rw [productMap_commute P (P n) (fun k => h k n)]
    have he := (P n).pythagoras (productMap P (List.range n) x)
    simp only [residual_apply] at he
    rw [difference_apply]
    linarith

theorem difference_energy_sum_le (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, B.energy (difference P h i x)) ≤ B.energy x := by
  have := difference_energy_sum P h n x
  have := B.energy_nonneg (productMap P (List.range n) x)
  linarith

theorem difference_commute (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (i : ℕ) (x : E) : difference P h i (Q x) = Q (difference P h i x) := by
  simp only [difference_apply, productMap_commute P Q hq, map_sub, hq]

theorem difference_residual_budget (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, B.energy (Q.residual (difference P h i x))) ≤
      B.energy (Q.residual x) := by
  have hr : ∀ i, ∀ x, P i (Q.residual x) = Q.residual (P i x) := by
    intro i x
    simp [hq]
  simpa only [← difference_commute P h Q.residual hr] using
    difference_energy_sum_le P h n (Q.residual x)

theorem difference_retained_le (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (i : ℕ) (x : E) : B.energy (Q (difference P h i x)) ≤ B.energy (Q x) := by
  rw [← difference_commute P h Q hq]
  exact (difference P h i).energy_le (Q x)

theorem productMap_map {ι κ : Type*} (P : κ → B.Projection) (g : ι → κ)
    (is : List ι) (x : E) :
    productMap P (is.map g) x = productMap (fun i => P (g i)) is x := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons, productMap_cons, ih]

def natExtension {d : ℕ} (P : Fin d → B.Projection) (i : ℕ) : B.Projection :=
  if h : i < d then P ⟨i,h⟩ else ident

@[simp] theorem natExtension_fin {d : ℕ} (P : Fin d → B.Projection) (i : Fin d) :
    natExtension P i.val = P i := dite_eq_left i.isLt

theorem natExtension_commute {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) :
    ∀ i j, ∀ x, natExtension P i (natExtension P j x) =
      natExtension P j (natExtension P i x) := by
  intro i j x
  unfold natExtension
  split_ifs <;> simp only [ident_apply, h]

theorem natExtension_commute_of {d : ℕ} (P : Fin d → B.Projection) (Q : B.Projection)
    (h : ∀ i, ∀ x, P i (Q x) = Q (P i x)) (i : ℕ) (x : E) :
    natExtension P i (Q x) = Q (natExtension P i x) := by
  unfold natExtension
  split_ifs <;> simp only [ident_apply, h]

theorem productMap_range_natExtension {d : ℕ} (P : Fin d → B.Projection) (x : E) :
    productMap (natExtension P) (List.range d) x = productMap P (List.finRange d) x := by
  have he : (List.finRange d).map Fin.val = List.range d := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [← he, productMap_map]
  simp only [natExtension_fin]

def finDifference {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (i : Fin d) : B.Projection :=
  difference (natExtension P) (natExtension_commute P h) i.val

theorem finDifference_energy_sum {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (x : E) :
    (∑ i : Fin d, B.energy (finDifference P h i x)) +
      B.energy (productMap P (List.finRange d) x) = B.energy x := by
  have he := difference_energy_sum (natExtension P) (natExtension_commute P h) d x
  rw [← Fin.sum_univ_eq_sum_range, productMap_range_natExtension] at he
  exact he

theorem finDifference_residual_budget {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x)) (x : E) :
    (∑ i : Fin d, B.energy (Q.residual (finDifference P h i x))) ≤
      B.energy (Q.residual x) := by
  have he := difference_residual_budget (natExtension P) (natExtension_commute P h)
    Q (natExtension_commute_of P Q hq) d x
  rw [← Fin.sum_univ_eq_sum_range] at he
  exact he

theorem finDifference_retained_le {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x)) (i : Fin d) (x : E) :
    B.energy (Q (finDifference P h i x)) ≤ B.energy (Q x) :=
  difference_retained_le (natExtension P) (natExtension_commute P h)
    Q (natExtension_commute_of P Q hq) i.val x

theorem finDifference_centered {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (i : Fin d) (x : E) :
    (P i).residual (finDifference P h i x) = finDifference P h i x := by
  simp only [finDifference, difference_apply, natExtension_fin, residual_apply,
    map_sub, apply_idem, sub_self, sub_zero]

theorem finDifference_commute {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x)) (i : Fin d) (x : E) :
    finDifference P h i (Q x) = Q (finDifference P h i x) :=
  difference_commute (natExtension P) (natExtension_commute P h)
    Q (natExtension_commute_of P Q hq) i.val x

theorem product_loss_finset {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (s : Finset ι) (x : E) :
    B.energy ((product P h s.toList).residual x) ≤ ∑ i ∈ s, B.energy ((P i).residual x) := by
  classical
  have he := product_loss_le P h s.toList x
  rw [← List.sum_toFinset _ s.nodup_toList] at he
  simpa using he

end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
