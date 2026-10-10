import OAI.NumberTheory.TwoPoint.Walks.ClosedWordPadding
import OAI.NumberTheory.TwoPoint.Bounds.CatalogVertexIndicator

namespace OAI

/-! A closed nonempty word counts a binary vertex mask once per departure, despite the two edge endpoints. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma closed_binary_mask_product {m : ℕ} (hm : 0 < m)
    (site : Fin (m + 1) → ℤ) (hclosed : site (Fin.last m) = site 0)
    (mask : ℤ → ℝ) (hmask : ∀ z, mask z = 0 ∨ mask z = 1) :
    (∏ i : Fin m, mask (site i.castSucc) * mask (site i.succ)) =
      ∏ i : Fin m, mask (site i.castSucc) := by
  by_cases hz : ∃ i : Fin m, mask (site i.castSucc) = 0
  · obtain ⟨i, hi⟩ := hz
    rw [prod_mul_distrib, prod_eq_zero (mem_univ i) hi, zero_mul]
  · have hd (i : Fin m) : mask (site i.castSucc) = 1 :=
      (hmask _).resolve_left (fun hi => hz ⟨i, hi⟩)
    have ha (i : Fin m) : mask (site i.succ) = 1 := by
      by_cases hi : i.val + 1 < m
      · have he : i.succ = (⟨i.val + 1, hi⟩ : Fin m).castSucc := Fin.ext rfl
        rw [he, hd]
      · have he : i.succ = Fin.last m := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        have he0 : (⟨0, hm⟩ : Fin m).castSucc = (0 : Fin (m + 1)) := Fin.ext rfl
        rw [he, hclosed, ← he0, hd]
    simp only [hd, ha, mul_one, prod_const_one]

theorem closed_masked_scalar_word {m : ℕ} (hm : 0 < m)
    (h : ℕ) (step : Fin m → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0)
    (weight : SignedStep → ℤ → ℝ) (mask : ℤ → ℝ)
    (hmask : ∀ z, mask z = 0 ∨ mask z = 1) :
    scalarWalkProduct h (fun t z => mask z * weight t z * mask (z + t.displacement h))
      n (List.ofFn step) =
      scalarWalkProduct h weight n (List.ofFn step) *
        scalarWalkProduct h (fun _ z => mask z) n (List.ofFn step) := by
  let site (i : Fin (m + 1)) := n + wordDisplacement h ((List.ofFn step).take i.val)
  have hsite : site (Fin.last m) = site 0 := by
    have ht : (List.ofFn step).take m = List.ofFn step :=
      List.take_of_length_le (by simp)
    simp only [site, Fin.val_last, ht, hclosed, add_zero, Fin.val_zero,
      List.take_zero, wordDisplacement_nil]
  have hs (i : Fin m) : site i.castSucc + (step i).displacement h = site i.succ := by
    have ht : wordStepDisplacement h (List.ofFn step) i.val = (step i).displacement h := by
      simp only [wordStepDisplacement, List.getElem?_ofFn, i.isLt, dite_true, Fin.eta,
        Option.map_some, Option.getD_some]
    simp only [site, Fin.val_castSucc, Fin.val_succ, wordDisplacement_take_succ, ht, add_assoc]
  simp only [scalarWalkProduct_ofFn]
  change (∏ i : Fin m, mask (site i.castSucc) * weight (step i) (site i.castSucc) *
      mask (site i.castSucc + (step i).displacement h)) =
    (∏ i : Fin m, weight (step i) (site i.castSucc)) * ∏ i : Fin m, mask (site i.castSucc)
  calc
    _ = (∏ i : Fin m, weight (step i) (site i.castSucc)) *
        ∏ i : Fin m, mask (site i.castSucc) * mask (site i.succ) := by
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      rw [hs]
      ring
    _ = _ := by rw [closed_binary_mask_product hm site hsite mask hmask]

end TwoPointCorrelations

end OAI
