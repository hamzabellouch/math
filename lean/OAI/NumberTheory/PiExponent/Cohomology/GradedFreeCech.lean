import OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech
import OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree

namespace OAI

namespace PiExponent.GradedFreeCech
noncomputable section
open PiExponent.GradedCech PiExponent.GradedLocalizationFree
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R B : Type*} [DecidableEq J] [CommRing R] [Fintype B]
  (w : B → ℤ)

def coordinateIntersection (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d →+
    (∀ b, IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s (d - w b)) where
  toFun z b := coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem s) d z b
  map_zero' := by funext b; exact congrFun (map_zero _) b
  map_add' z z' := by funext b; exact congrFun (map_add _ _ _) b

@[simp] theorem coordinateIntersection_apply (s : Finset J) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d) (b : B) :
    coordinateIntersection w s d z b =
      coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem s) d z b := rfl

def coordinateCochain (d : ℤ) (q : ℕ) :
    Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d q →+
    (∀ b, Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b) q) where
  toFun c b t := coordinateIntersection w (tupleSet t) d (c t) b
  map_zero' := by funext b t; exact congrFun (map_zero _) b
  map_add' c e := by funext b t; exact congrFun (map_add _ _ _) b

theorem coordinateCochain_injective (d : ℤ) (q : ℕ) :
    Function.Injective (coordinateCochain (J := J) (R := R) w d q) := by
  intro c e h
  funext t
  apply coordinatePieces_injective (grading (J := J) (R := R)) w (product (tupleSet t)) _ (product_mem _) d
  funext b
  exact congrFun (congrFun h b) t

theorem coordinateCochain_surjective (d : ℤ) (q : ℕ) :
    Function.Surjective (coordinateCochain (J := J) (R := R) w d q) := by
  intro c
  have ht (t : Fin (q + 1) → J) := coordinatePieces_surjective (grading (J := J) (R := R)) w
    (product (R := R) (tupleSet t)) _ (product_mem _) d (fun b => c b t)
  choose e he using ht
  refine ⟨e, ?_⟩
  funext b t
  exact congrFun (he t) b

theorem coordinate_restriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d) (b : B) :
    coordinatePieces (grading (J := J) (R := R)) w (product t) _ (product_mem _) d
      (setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem hst d z) b =
      setRestriction (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst (d - w b)
        (coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem _) d z b) := by
  apply Subtype.ext
  change localizedMap (product t) (LinearMap.proj b)
      (restriction (product s) (product t)
        (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) z.val) =
    restriction (product s) (product t)
      (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) (localizedMap (product s) (LinearMap.proj b) z.val)
  exact DFunLike.congr_fun (restriction_localizedMap (product s) (product t)
    (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) (LinearMap.proj b)) z.val

theorem coordinateCochain_differential (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d q) (b : B) :
    coordinateCochain w d (q + 1)
        (differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem d c) b =
      differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b)
        (coordinateCochain w d q c b) := by
  funext t
  change (coordinateIntersection w (tupleSet t) d
    (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove)))) b = _
  rw [map_sum]
  simp only [Finset.sum_apply, differential]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  change (-1 : ℤ) ^ k.val • coordinateIntersection w (tupleSet t) d
      (setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))) b = _
  apply congrArg (fun z => (-1 : ℤ) ^ k.val • z)
  exact coordinate_restriction w (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove)) b

variable [Fintype J]

theorem free_cech_exact (d : ℤ) (hd : ∀ b, 0 ≤ d - w b) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d (q + 1))
    (hc : differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d c = 0) :
    ∃ a : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem d a = c := by
  have hclosed (b : B) : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b)
      (coordinateCochain w d (q + 1) c b) = 0 := by
    rw [← coordinateCochain_differential, hc, map_zero]
    rfl
  have hpr (b : B) := GradedPolynomialCech.nonnegative_polynomial_cech_exact
    (d - w b) (hd b) q (coordinateCochain w d (q + 1) c b) (hclosed b)
  choose p hp using hpr
  obtain ⟨a, ha⟩ := coordinateCochain_surjective (J := J) (R := R) w d q p
  refine ⟨a, ?_⟩
  apply coordinateCochain_injective w d (q + 1)
  funext b
  rw [coordinateCochain_differential, ha, hp]

theorem eventually_free_cech_exact :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ,
      ∀ c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        (MvPolynomial.X : J → MvPolynomial J R) variable_mem n (q + 1),
        differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem n c = 0 →
        ∃ a : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem n q,
          differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem n a = c := by
  refine ⟨∑ b, (w b).toNat, ?_⟩
  intro n hn q c hc
  apply free_cech_exact w n ?_ q c hc
  intro b
  have hb : (w b).toNat ≤ ∑ b, (w b).toNat :=
    Finset.single_le_sum (fun b _ => Nat.zero_le ((w b).toNat)) (Finset.mem_univ b)
  have hb' : ((w b).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hb.trans hn
  omega

omit [Fintype J] in
theorem coordinateCochain_augmentation (d : ℤ)
    (m : ShiftedFreeGrading.piece (grading (J := J) (R := R)) w d) (b : B) :
    coordinateCochain w d 0
      (augmentation (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem d m) b =
    augmentation (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem (d - w b) ⟨m.val b, m.property b⟩ := by
  funext t
  apply Subtype.ext
  change coordinateMap (product (tupleSet t)) (fraction (product (tupleSet t)) m.val 0) b =
    fraction (product (tupleSet t)) (m.val b) 0
  exact coordinateMap_fraction _ m.val 0 b

theorem free_augmentation_recovery (d : ℤ) (hd : ∀ b, 0 ≤ d - w b)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d 0)
    (hc : differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d c = 0) :
    ∃ m : ShiftedFreeGrading.piece (grading (J := J) (R := R)) w d,
      augmentation (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem d m = c := by
  have hclosed (b : B) : differential (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem (d - w b) (coordinateCochain w d 0 c b) = 0 := by
    rw [← coordinateCochain_differential, hc, map_zero]
    rfl
  have hrec (b : B) := GradedPolynomialCech.nonnegative_polynomial_augmentation_recovery
    (d - w b) (hd b) (coordinateCochain w d 0 c b) (hclosed b)
  choose m hm using hrec
  refine ⟨⟨fun b => (m b).val, fun b => (m b).property⟩, ?_⟩
  apply coordinateCochain_injective w d 0
  funext b
  rw [coordinateCochain_augmentation]
  exact hm b

end
end PiExponent.GradedFreeCech

end OAI
