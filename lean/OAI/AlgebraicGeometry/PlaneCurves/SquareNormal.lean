import OAI.AlgebraicGeometry.PlaneCurves.LineConfigurations
import OAI.AlgebraicGeometry.PlaneCurves.LineRestriction

namespace OAI

/-!
# Normal evaluation and obstructions for square line arrangements
-/

section

/-! Choosing displacement outside the actual ambient homogeneous evaluation image. -/
noncomputable section
namespace Nagata.Workers.W24

/-- At any k² chosen coordinate representatives, degree-k plane forms have an
evaluation image of dimension strictly below k² for k≥4. -/
theorem exists_displacement_outside_homogeneousEvaluation {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : 4 ≤ k) (hcard : Fintype.card ι = k * k)
    (a : ι → Fin 3 → ℂ) :
    ∃ c : ι → ℂ, c ∉ (homogeneousEvaluation k a).range := by
  apply exists_vector_outside_range
  change Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ k) <
    Module.finrank ℂ (ι → ℂ)
  rw [Nagata.W02.finrank_homogeneousSubmodule,
    Module.finrank_fintype_fun_eq_card, hcard]
  exact ambientDegreeK_dimension_lt k hk

/-- The precise ordered grid of k marks on each of k lines. -/
theorem exists_grid_displacement (k : ℕ) (hk : 4 ≤ k)
    (a : Fin k × Fin k → Fin 3 → ℂ) :
    ∃ c : Fin k × Fin k → ℂ, c ∉ (homogeneousEvaluation k a).range := by
  apply exists_displacement_outside_homogeneousEvaluation k hk
  simp

end Nagata.Workers.W24

end
end

section

noncomputable section
namespace Nagata.Workers.W24
open Polynomial
open Nagata.W04.ReducibleSquare Nagata.W18

/-- Local surface orders at arbitrary normal displacements force the highest
coefficient to vanish on every component when its index is below m. -/
theorem normal_top_coefficients_zero {K : Type*} [Field K] [CharZero K]
    (k m J : ℕ) (hk : 3 ≤ k) (hJm : J < m)
    (H : ℕ → Polynomial (Polynomial K))
    (cFirst : ℕ → K) (cTail : ℕ → ℕ → K)
    (hdegree : ∀ i < k, (H i).natDegree ≤ J)
    (hbase : ∀ i < k, ((H i).coeff J).natDegree ≤ k * (m - J))
    (hfirst : ∀ i < k, H i ∈
      (nestedPointIdeal (-((firstMark k i : ℕ) : K)) (cFirst i)) ^ m)
    (htail : ∀ i < k, ∀ s < k - 1, H i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : K)) (cTail i s)) ^ m)
    (hglue : ∀ i < k, ∀ j < k,
      ((H i).coeff J).eval ((i + j : ℕ) : K) =
      ((H j).coeff J).eval ((i + j : ℕ) : K)) :
    ∀ i < k, (H i).coeff J = 0 := by
  apply line_family_zero_of_marked_factors k (m - J) hk (by omega)
    (fun i => (H i).coeff J) hbase
  · intro i hi
    simpa only [map_neg, sub_neg_eq_add] using
      top_coefficient_base_divisibility (H i) (-((firstMark k i : ℕ) : K))
        (cFirst i) m J (hdegree i hi) (hfirst i hi)
  · intro i hi s hs
    simpa only [map_neg, sub_neg_eq_add] using
      top_coefficient_base_divisibility (H i) (-((s + 2 : ℕ) : K))
        (cTail i s) m J (hdegree i hi) (htail i hi s hs)
  · exact hglue

/-- A nonzero highest component, together with the degree-weight bound, forces
the last possible index and the square equality d=k*m. -/
theorem normal_top_index_eq_and_degree_eq {K : Type*} [Field K] [CharZero K]
    (k d m J : ℕ) (hk : 3 ≤ k) (hd : d ≤ k * m) (hweight : k * J ≤ d)
    (H : ℕ → Polynomial (Polynomial K))
    (cFirst : ℕ → K) (cTail : ℕ → ℕ → K)
    (hdegree : ∀ i < k, (H i).natDegree ≤ J)
    (hbase : ∀ i < k, ((H i).coeff J).natDegree ≤ d - k * J)
    (hfirst : ∀ i < k, H i ∈
      (nestedPointIdeal (-((firstMark k i : ℕ) : K)) (cFirst i)) ^ m)
    (htail : ∀ i < k, ∀ s < k - 1, H i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : K)) (cTail i s)) ^ m)
    (hglue : ∀ i < k, ∀ j < k,
      ((H i).coeff J).eval ((i + j : ℕ) : K) =
      ((H j).coeff J).eval ((i + j : ℕ) : K))
    (hne : ∃ i < k, (H i).coeff J ≠ 0) : J = m ∧ d = k * m := by
  have hle : J ≤ m := leadingIndex_le_m k d m J (by omega) hweight hd
  have hnot : ¬ J < m := by
    intro hlt
    have hz := normal_top_coefficients_zero k m J hk hlt H cFirst cTail hdegree
      (fun i hi => (hbase i hi).trans (by
        simpa only [Nat.mul_sub_left_distrib] using Nat.sub_le_sub_right hd (k * J)))
      hfirst htail hglue
    obtain ⟨i, hi, hni⟩ := hne
    exact hni (hz i hi)
  have heq : J = m := by omega
  exact ⟨heq, Nat.le_antisymm hd (by simpa only [heq] using hweight)⟩

end Nagata.Workers.W24

end
end

section

/-! Equality-case obstruction from actual local normal polynomials. -/
namespace Nagata.Workers.W24
open Polynomial Nagata.W18

/-- A constant nonzero highest coefficient turns the local order equations into
an impossible evaluation vector when the displacement is outside the image. -/
theorem normal_evaluation_contradiction {K V ι : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V]
    (E : V →ₗ[K] (ι → K)) (c : ι → K) (hc : c ∉ E.range)
    (m : ℕ) (hm : 0 < m) (a : K) (ha : a ≠ 0)
    (H : ι → Polynomial (Polynomial K)) (base : ι → K)
    (hdegree : ∀ i, (H i).natDegree ≤ m)
    (horder : ∀ i, H i ∈ (nestedPointIdeal (base i) (c i)) ^ m)
    (htop : ∀ i, ((H i).coeff m).eval (base i) = a)
    (s : V) (hprevious : ∀ i, E s i = ((H i).coeff (m - 1)).eval (base i)) :
    False := by
  apply evaluation_coefficient_contradiction E c hc (-(m : K) * a)
    (mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) ha) s
  funext i
  change E s i = (-(m : K) * a) * c i
  rw [hprevious i]
  have h := surface_order_penultimate_coefficient (H i) (base i) (c i) m hm
    (hdegree i) (horder i) (by rw [htop i]; exact ha)
  simpa only [htop i] using h

end Nagata.Workers.W24

end

section

/-! Actual homogeneous-plane lifts in the lower-index square argument. -/
noncomputable section
namespace Nagata.Workers.W24
open Polynomial Nagata.W18
open Nagata.W04.ReducibleSquare

/-- The literal normal polynomial restricted coefficientwise to component i. -/
def planeNormalOnLine (F : Polynomial (MvPolynomial (Fin 3) ℂ)) (i : ℕ) :
    Polynomial (Polynomial ℂ) := F.map (Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ))

@[simp] theorem planeNormalOnLine_coeff (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (i j : ℕ) : (planeNormalOnLine F i).coeff j =
      Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ) (F.coeff j) :=
  Polynomial.coeff_map _ _

theorem lineRestriction_union_zero (k : ℕ) (i : Fin k) :
    Nagata.W04.ReducibleSquare.lineRestriction (i.val : ℂ) (homogeneousLineUnion ℂ k) = 0 := by
  apply (affine_lineRestriction_eq_zero_iff _ i.val k (homogeneousLineUnion_homogeneous k)).mpr
  exact (homogeneousUnion_dvd_iff_restrictions_zero k _).mp dvd_rfl i

/-- A nonzero quotient normal polynomial with actual homogeneous plane lifts
and local marked orders has last index m and exact equality degree k*m. -/
theorem plane_normal_top_index_eq_and_degree_eq
    (k d m : ℕ) (hk : 3 ≤ k) (hd : d ≤ k * m)
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d - k * j))
    (hweight : ∀ j, F.coeff j ≠ 0 → k * j ≤ d)
    (hne : normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0)
    (cFirst : ℕ → ℂ) (cTail : ℕ → ℕ → ℂ)
    (hfirst : ∀ i < k, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((firstMark k i : ℕ) : ℂ)) (cFirst i)) ^ m)
    (htail : ∀ i < k, ∀ s < k - 1, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : ℂ)) (cTail i s)) ^ m) :
    (normalResiduePolynomial (homogeneousLineUnion ℂ k) F).natDegree = m ∧ d = k * m := by
  let J := (normalResiduePolynomial (homogeneousLineUnion ℂ k) F).natDegree
  have hnot : ¬ homogeneousLineUnion ℂ k ∣ F.coeff J :=
    top_normalResidue_coefficient_not_dvd _ _ hne
  have hcoeff : F.coeff J ≠ 0 := by
    intro hz
    exact hnot (hz ▸ dvd_zero _)
  apply normal_top_index_eq_and_degree_eq k d m J hk hd (hweight J hcoeff)
    (planeNormalOnLine F) cFirst cTail
  · intro i hi
    exact restriction_natDegree_le_normalResidue_degree _ F _
      (lineRestriction_union_zero k ⟨i, hi⟩)
  · intro i hi
    rw [planeNormalOnLine_coeff]
    exact Nagata.W02.lineRestriction_natDegree_le (i : ℂ) (F.coeff J) (d - k * J) (hhom J)
  · exact hfirst
  · exact htail
  · intro i hi j hj
    simp only [planeNormalOnLine_coeff]
    simpa only [Nat.cast_add] using lineRestriction_node_gluing (F.coeff J) (i : ℂ) (j : ℂ)
  · obtain ⟨i, hi⟩ := exists_nonzero_affine_lineRestriction k (d - k * J)
      (F.coeff J) (hhom J) hnot
    exact ⟨i.val, i.isLt, by simpa only [planeNormalOnLine_coeff] using hi⟩

end Nagata.Workers.W24

end
end

section

/-! Equality exclusion using actual degree-zero and degree-k homogeneous lifts. -/
noncomputable section
namespace Nagata.Workers.W24
open Polynomial Nagata.W18

/-- Literal normalized homogeneous coordinates on a selected line. -/
def componentCoordinates (i : ℕ) (a : ℂ) : Fin 3 → ℂ :=
  ![a, (i : ℂ) ^ 2 - (i : ℂ) * a, 1]

/-- The square equality case is impossible for an outside-image displacement.
The central object is an actual polynomial with homogeneous plane coefficients;
only its local normal-point orders are an input from specialization. -/
theorem plane_normal_equality_contradiction {ι : Type*}
    (k m : ℕ) (hm : 0 < m)
    (component : ι → Fin k) (base c : ι → ℂ)
    (hc : c ∉ (homogeneousEvaluation k
      (fun i => componentCoordinates (component i).val (base i))).range)
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (k * m - k * j))
    (hne : normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0)
    (hindex : (normalResiduePolynomial (homogeneousLineUnion ℂ k) F).natDegree = m)
    (horder : ∀ i, planeNormalOnLine F (component i).val ∈
      (nestedPointIdeal (base i) (c i)) ^ m) : False := by
  have hnot : ¬ homogeneousLineUnion ℂ k ∣ F.coeff m := by
    simpa only [hindex] using top_normalResidue_coefficient_not_dvd _ _ hne
  have hcoeff : F.coeff m ≠ 0 := by
    intro hz
    exact hnot (hz ▸ dvd_zero _)
  let T : PlaneForms 0 := ⟨F.coeff m, by
    change (F.coeff m).IsHomogeneous 0
    simpa only [Nat.sub_self] using hhom m⟩
  let a := (F.coeff m).coeff 0
  have hconstant : F.coeff m = MvPolynomial.C a := degreeZeroForm_eq_constant T
  have ha : a ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hconstant, hz, MvPolynomial.C_0])
  let s : PlaneForms k := ⟨F.coeff (m - 1), by
    change (F.coeff (m - 1)).IsHomogeneous k
    simpa only [penultimate_exponent k m hm] using hhom (m - 1)⟩
  refine normal_evaluation_contradiction
    (homogeneousEvaluation k (fun i => componentCoordinates (component i).val (base i)))
    c hc m hm a ha (fun i => planeNormalOnLine F (component i).val) base
    ?_ horder ?_ s ?_
  · intro i
    have h := restriction_natDegree_le_normalResidue_degree (homogeneousLineUnion ℂ k)
      F (Nagata.W04.ReducibleSquare.lineRestriction ((component i).val : ℂ))
      (lineRestriction_union_zero k (component i))
    simpa only [planeNormalOnLine, hindex] using h
  · intro i
    rw [planeNormalOnLine_coeff, hconstant]
    simp [Nagata.W04.ReducibleSquare.lineRestriction]
  · intro i
    rw [homogeneousEvaluation_apply, planeNormalOnLine_coeff,
      Nagata.W04.ReducibleSquare.lineRestriction_eval]
    rfl

end Nagata.Workers.W24

end
end

section

/-! Algebraic square obstruction on the k-line marked arrangement. -/
noncomputable section
namespace Nagata.Workers.W24
open Polynomial Nagata.W18
open Nagata.W06.LineArrangement

def squareMarkedBase (k : ℕ) (p : Fin k × Fin k) : ℂ :=
  -(markedCoordinate k p.1.val p.2 : ℂ)

def squareMarkedCoordinates (k : ℕ) (p : Fin k × Fin k) : Fin 3 → ℂ :=
  componentCoordinates p.1.val (squareMarkedBase k p)

/-- The base points are exactly the actual marked affine configuration. -/
theorem squareMarkedCoordinates_eq (k : ℕ) (p : Fin k × Fin k) :
    squareMarkedCoordinates k p =
      ![(markedPoint ℂ k p.1 p.2).1, (markedPoint ℂ k p.1 p.2).2, 1] := rfl

/-- All source-constructed homogeneous lifts are excluded by a single
outside-image displacement. The local multiplicity condition is an actual
ideal-power condition on literal coefficientwise line restrictions. -/
theorem square_normal_obstruction (k d m : ℕ) (hk : 4 ≤ k) (hm : 0 < m)
    (hd : d ≤ k * m) (c : Fin k × Fin k → ℂ)
    (hc : c ∉ (homogeneousEvaluation k (squareMarkedCoordinates k)).range)
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d - k * j))
    (hweight : ∀ j, F.coeff j ≠ 0 → k * j ≤ d)
    (hne : normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0)
    (horder : ∀ p : Fin k × Fin k, planeNormalOnLine F p.1.val ∈
      (nestedPointIdeal (squareMarkedBase k p) (c p)) ^ m) : False := by
  have hkpos : 0 < k := by omega
  let cFirst : ℕ → ℂ := fun i => if hi : i < k then c (⟨i, hi⟩, ⟨0, hkpos⟩) else 0
  let cTail : ℕ → ℕ → ℂ := fun i s =>
    if hi : i < k then if hs : s + 1 < k then c (⟨i, hi⟩, ⟨s + 1, hs⟩) else 0 else 0
  have hfirst : ∀ i < k, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((Nagata.W04.ReducibleSquare.firstMark k i : ℕ) : ℂ))
        (cFirst i)) ^ m := by
    intro i hi
    simpa only [squareMarkedBase, markedCoordinate_zero, cFirst, dite_eq_left hi] using
      horder (⟨i, hi⟩, ⟨0, hkpos⟩)
  have htail : ∀ i < k, ∀ s < k - 1, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : ℂ)) (cTail i s)) ^ m := by
    intro i hi s hs
    have hs' : s + 1 < k := by omega
    simpa only [squareMarkedBase, markedCoordinate_of_ne_zero k i ⟨s + 1, hs'⟩
      (by change s + 1 ≠ 0; omega), cTail, dite_eq_left hi, dite_eq_left hs', Nat.add_assoc] using
      horder (⟨i, hi⟩, ⟨s + 1, hs'⟩)
  obtain ⟨hindex, hdm⟩ := plane_normal_top_index_eq_and_degree_eq k d m (by omega)
    hd F hhom hweight hne cFirst cTail hfirst htail
  apply plane_normal_equality_contradiction k m hm Prod.fst (squareMarkedBase k) c hc
    F (by simpa only [hdm] using hhom) hne hindex horder

/-- One displacement excludes all degrees and positive multiplicities in the
square slope range at once, for genuine normal polynomials with plane lifts. -/
theorem exists_square_normal_obstruction (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : Fin k × Fin k → ℂ, ∀ d m : ℕ, 0 < m → d ≤ k * m →
      ∀ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ j, (F.coeff j).IsHomogeneous (d - k * j)) →
      (∀ j, F.coeff j ≠ 0 → k * j ≤ d) →
      normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0 →
      ¬ (∀ p : Fin k × Fin k, planeNormalOnLine F p.1.val ∈
        (nestedPointIdeal (squareMarkedBase k p) (c p)) ^ m) := by
  obtain ⟨c, hc⟩ := exists_grid_displacement k hk (squareMarkedCoordinates k)
  exact ⟨c, fun d m hm hd F hhom hweight hne horder =>
    square_normal_obstruction k d m hk hm hd c hc F hhom hweight hne horder⟩

end Nagata.Workers.W24

end
end

end OAI
