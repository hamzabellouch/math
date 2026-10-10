import OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent

namespace OAI

namespace PiExponent.GradedPolynomialCech
noncomputable section
open scoped BigOperators
open PiExponent.GradedLocalizationExact PiExponent.GradedCech PiExponent.GradedPolynomialLaurent PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

def intersectionToPiece (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d →+ Piece (R := R) s d where
  toFun z := ⟨z.val, z.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def intersectionToLaurent (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d →+ Laurent J R d :=
  (pieceToLaurent s d).comp (intersectionToPiece s d)

@[simp] theorem intersectionToLaurent_apply (s : Finset J) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d) :
    intersectionToLaurent s d z = pieceToLaurent s d z := rfl

def cochainToLaurent (d : ℤ) (q : ℕ) :
    Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q →+
      ProjectiveMonomialCechHigher.Cochain J (Laurent J R d) q where
  toFun c t := intersectionToLaurent (tupleSet t) d (c t)
  map_zero' := by funext t; exact map_zero _
  map_add' c b := by funext t; exact map_add _ _ _

@[simp] theorem cochainToLaurent_apply (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q)
    (t : Fin (q + 1) → J) :
    cochainToLaurent d q c t = pieceToLaurent (tupleSet t) d (c t) := rfl

theorem cochainToLaurent_injective (d : ℤ) (q : ℕ) :
    Function.Injective (cochainToLaurent (J := J) (R := R) d q) := by
  intro c b h
  funext t
  exact pieceToLaurent_injective (tupleSet t) d (congrFun h t)

theorem cochainToLaurent_regular (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q) :
    ProjectiveMonomialCechHigher.Regular (cochainToLaurent d q c) := by
  intro t a ha j hj
  have h := pieceToLaurent_regular (tupleSet t) d (c t) a ha j hj
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  exact ⟨k, hk⟩

theorem cochainToLaurent_surjective_regular (d : ℤ) (q : ℕ)
    (c : ProjectiveMonomialCechHigher.Cochain J (Laurent J R d) q)
    (hc : ProjectiveMonomialCechHigher.Regular c) :
    ∃ b, cochainToLaurent d q b = c := by
  have ht (t : Fin (q + 1) → J) : ∃ b : Piece (R := R) (tupleSet t) d,
      pieceToLaurent (tupleSet t) d b = c t := by
    apply pieceToLaurent_surjective_regular
    intro a ha j hj
    obtain ⟨k, hk⟩ := hc t a ha j hj
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  choose b hb using ht
  exact ⟨b, funext hb⟩

theorem cochainToLaurent_differential (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q) :
    cochainToLaurent d (q + 1) (differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c) =
      ProjectiveMonomialCechHigher.differential (cochainToLaurent d q c) := by
  funext t
  change intersectionToLaurent (tupleSet t) d
      (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        setRestriction (grading (J := J) (R := R)) (grading (J := J) (R := R))
          MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  apply congrArg (fun z : Laurent J R d => (-1 : ℤ) ^ k.val • z)
  exact pieceToLaurent_restriction (R := R) (tupleSet_comp_subset t k.succAbove) d
    ⟨(c (t ∘ k.succAbove)).val, (c (t ∘ k.succAbove)).property⟩

theorem nonnegative_polynomial_cech_exact (d : ℤ) (hd : 0 ≤ d) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d (q + 1))
    (hc : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c = 0) :
    ∃ b : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d b = c := by
  have hclosed : ProjectiveMonomialCechHigher.differential (cochainToLaurent d (q + 1) c) = 0 := by
    rw [← cochainToLaurent_differential, hc, map_zero]
  obtain ⟨b, hb, hdb⟩ := ProjectiveMonomialCechHigher.nonnegative_twist_cech_exact_all_positive
    hd (cochainToLaurent d (q + 1) c) (cochainToLaurent_regular d (q + 1) c) hclosed
  obtain ⟨a, ha⟩ := cochainToLaurent_surjective_regular d q b hb
  refine ⟨a, ?_⟩
  apply cochainToLaurent_injective d (q + 1)
  rw [cochainToLaurent_differential, ha, hdb]

theorem nonnegative_polynomial_augmentation_recovery (d : ℤ) (hd : 0 ≤ d)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) (MvPolynomial.X : J → MvPolynomial J R)
      variable_mem d 0)
    (hc : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c = 0) :
    ∃ m : (grading (J := J) (R := R)) d,
      augmentation (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d m = c := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h =>
      refine ⟨0, ?_⟩
      funext t
      exact isEmptyElim (t 0)
  | inr h =>
      have hclosed : ProjectiveMonomialCechHigher.differential (cochainToLaurent d 0 c) = 0 := by
        rw [← cochainToLaurent_differential, hc, map_zero]
      have hreg (j : J) : RegularOn {j} (cochainToLaurent d 0 c (fun _ => j)) := by
        simpa only [Set.range_const] using cochainToLaurent_regular d 0 c (fun _ => j)
      obtain ⟨p, hpreg, hp⟩ := GradedSerre.compatible_vertices_are_polynomial hd
        (fun j => cochainToLaurent d 0 c (fun _ => j)) hreg
        (GradedH0.zeroth_cocycle_vertices_eq _ hclosed)
      obtain ⟨z, hzL⟩ := pieceToLaurent_surjective_regular (R := R) ∅ d p (by simpa using hpreg)
      obtain ⟨n, m, hm, hz⟩ := z.property
      have hm' : m ∈ (grading (J := J) (R := R)) d := by simpa using hm
      refine ⟨⟨m, hm'⟩, ?_⟩
      funext t
      apply pieceToLaurent_injective (tupleSet t) d
      have ht : t = fun _ => t 0 := by
        funext i
        exact congrArg t (show i = 0 by omega)
      calc
        _ = pieceToLaurent ∅ d z := by
          ext a
          change (moduleToGroupAlgebra (tupleSet t) (fraction (product (tupleSet t)) m 0)).coeff a.val =
            (moduleToGroupAlgebra ∅ z.val).coeff a.val
          rw [hz]
          simp only [moduleToGroupAlgebra_fraction_coefficient, zero_smul,
            productExponent, Finset.sum_empty, smul_zero, add_zero]
        _ = p := hzL
        _ = pieceToLaurent (tupleSet t) d (c t) := by
          change p = cochainToLaurent d 0 c t
          rw [ht, hp]

end
end PiExponent.GradedPolynomialCech

end OAI
