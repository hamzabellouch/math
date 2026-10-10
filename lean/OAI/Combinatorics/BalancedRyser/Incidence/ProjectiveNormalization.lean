import OAI.Combinatorics.BalancedRyser.Incidence.ProjectiveModel

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ProjectiveNormalization

open scoped BigOperators

variable {F : Type*} [Field F]

abbrev V (F : Type*) := Fin 3 → F

structure Collineation (F : Type*) [Field F] where
  point : ProjectivePoint F ≃ ProjectivePoint F
  line : ProjectiveLine F ≃ ProjectiveLine F
  incident : ∀ P l, ProjectiveIncident (point P) (line l) ↔ ProjectiveIncident P l

noncomputable def pointEquiv (e : V F ≃ₗ[F] V F) :
    ProjectivePoint F ≃ ProjectivePoint F where
  toFun P := normalizeProjective (e (homogeneousPoint P))
  invFun P := normalizeProjective (e.symm (homogeneousPoint P))
  left_inv P := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneous_normalize
      (e (homogeneousPoint P)) (e.map_ne_zero_iff.mpr (homogeneousPoint_ne_zero P))
    have he : a • e.symm (homogeneousPoint (normalizeProjective (e (homogeneousPoint P)))) =
        homogeneousPoint P := by
      simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm hs
    dsimp only
    rw [← normalizeProjective_smul a ha, he, normalize_homogeneousPoint]
  right_inv P := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneous_normalize
      (e.symm (homogeneousPoint P)) (e.symm.map_ne_zero_iff.mpr (homogeneousPoint_ne_zero P))
    have he : a • e (homogeneousPoint (normalizeProjective (e.symm (homogeneousPoint P)))) =
        homogeneousPoint P := by
      simpa only [map_smul, e.apply_symm_apply] using congrArg e hs
    dsimp only
    rw [← normalizeProjective_smul a ha, he, normalize_homogeneousPoint]

noncomputable def normalizeLine (v : V F) : ProjectiveLine F := by
  classical
  exact if v 1 ≠ 0 then some (some (-v 0 / v 1), -v 2 / v 1)
    else if v 0 ≠ 0 then some (none, -v 2 / v 0) else none

@[simp] theorem normalize_homogeneousLine (l : ProjectiveLine F) :
    normalizeLine (homogeneousLine l) = l := by
  cases l with
  | none => simp [normalizeLine, homogeneousLine]
  | some l =>
    rcases l with ⟨d,b⟩
    cases d <;> simp [normalizeLine, homogeneousLine]

theorem normalizeLine_smul (a : F) (ha : a ≠ 0) (v : V F) :
    normalizeLine (a • v) = normalizeLine v := by
  classical
  simp [normalizeLine, Pi.smul_apply, smul_eq_mul, ha, neg_div,
    mul_div_mul_left]

theorem exists_smul_homogeneousLine (v : V F) (hv : v ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a • homogeneousLine (normalizeLine v) = v := by
  classical
  by_cases h1 : v 1 ≠ 0
  · refine ⟨v 1, h1, ?_⟩
    ext i
    fin_cases i <;> simp [normalizeLine, h1, homogeneousLine, Pi.smul_apply,
      smul_eq_mul, mul_div_cancel₀]
  · have hz1 : v 1 = 0 := not_not.mp h1
    by_cases h0 : v 0 ≠ 0
    · refine ⟨v 0, h0, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeLine, hz1, h0, homogeneousLine,
        Pi.smul_apply, smul_eq_mul, mul_div_cancel₀]
    · have hz0 : v 0 = 0 := not_not.mp h0
      have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        ext i
        fin_cases i <;> simp_all
      refine ⟨v 2, h2, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeLine, hz1, hz0, homogeneousLine,
        Pi.smul_apply, smul_eq_mul]

noncomputable def lineEquiv (e : V F ≃ₗ[F] V F) :
    ProjectiveLine F ≃ ProjectiveLine F where
  toFun l := normalizeLine (e (homogeneousLine l))
  invFun l := normalizeLine (e.symm (homogeneousLine l))
  left_inv l := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneousLine
      (e (homogeneousLine l)) (e.map_ne_zero_iff.mpr (homogeneousLine_ne_zero l))
    have he : a • e.symm (homogeneousLine (normalizeLine (e (homogeneousLine l)))) =
        homogeneousLine l := by
      simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm hs
    dsimp only
    rw [← normalizeLine_smul a ha, he, normalize_homogeneousLine]
  right_inv l := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneousLine
      (e.symm (homogeneousLine l)) (e.symm.map_ne_zero_iff.mpr (homogeneousLine_ne_zero l))
    have he : a • e (homogeneousLine (normalizeLine (e.symm (homogeneousLine l)))) =
        homogeneousLine l := by
      simpa only [map_smul, e.apply_symm_apply] using congrArg e hs
    dsimp only
    rw [← normalizeLine_smul a ha, he, normalize_homogeneousLine]

noncomputable def ofLinear (e f : V F ≃ₗ[F] V F)
    (hpair : ∀ v w, (∑ i, f w i * e v i) = ∑ i, w i * v i) : Collineation F where
  point := pointEquiv e
  line := lineEquiv f
  incident P l := by
    rw [projective_incident_iff_homogeneous, projective_incident_iff_homogeneous]
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneous_normalize
      (e (homogeneousPoint P)) (e.map_ne_zero_iff.mpr (homogeneousPoint_ne_zero P))
    obtain ⟨b, hb, ht⟩ := exists_smul_homogeneousLine
      (f (homogeneousLine l)) (f.map_ne_zero_iff.mpr (homogeneousLine_ne_zero l))
    have hp := hpair (homogeneousPoint P) (homogeneousLine l)
    rw [← hs, ← ht] at hp
    have hp' : (b * a) *
        (∑ i, homogeneousLine (lineEquiv f l) i * homogeneousPoint (pointEquiv e P) i) =
        ∑ i, homogeneousLine l i * homogeneousPoint P i := by
      rw [Finset.mul_sum]
      convert hp using 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.smul_apply, smul_eq_mul, pointEquiv, lineEquiv, Equiv.coe_fn_mk]
      ring
    rw [← hp', mul_eq_zero]
    simp [ha, hb]

namespace Collineation

noncomputable def refl : Collineation F where
  point := Equiv.refl _
  line := Equiv.refl _
  incident _ _ := Iff.rfl

noncomputable def trans (a b : Collineation F) : Collineation F where
  point := a.point.trans b.point
  line := a.line.trans b.line
  incident P l := (b.incident (a.point P) (a.line l)).trans (a.incident P l)

noncomputable def symm (a : Collineation F) : Collineation F where
  point := a.point.symm
  line := a.line.symm
  incident P l := by simpa using (a.incident (a.point.symm P) (a.line.symm l)).symm

end Collineation

def coordAdd (i j : Fin 3) (hij : i ≠ j) (c : F) : V F ≃ₗ[F] V F where
  toFun v k := v k + if k = i then c * v j else 0
  invFun v k := v k - if k = i then c * v j else 0
  map_add' v w := by
    ext k
    by_cases hk : k = i
    · simp [hk]
      ring
    · simp [hk]
  map_smul' a v := by
    ext k
    by_cases hk : k = i
    · simp [hk, smul_eq_mul]
      ring
    · simp [hk]
  left_inv v := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hij.symm]
    · simp [hk]
  right_inv v := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hij.symm]
    · simp [hk]

noncomputable def addCoordinate (i j : Fin 3) (hij : i ≠ j) (c : F) : Collineation F :=
  ofLinear (coordAdd i j hij c) (coordAdd j i hij.symm (-c)) (by
    intro v w
    fin_cases i <;> fin_cases j <;> (try exact (hij rfl).elim) <;>
      simp [coordAdd, Fin.sum_univ_three] <;> ring)

def coordPerm (e : Equiv.Perm (Fin 3)) : V F ≃ₗ[F] V F where
  toFun v i := v (e i)
  invFun v i := v (e.symm i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp

private theorem coordPerm_apply (permutation : Equiv.Perm (Fin 3)) (vector : V F) :
    coordPerm permutation vector = fun index => vector (permutation index) := rfl

noncomputable def permuteCoordinates (e : Equiv.Perm (Fin 3)) : Collineation F :=
  ofLinear (coordPerm e) (coordPerm e) (by
    intro v w
    exact Equiv.sum_comp e (fun i => w i * v i))

noncomputable def pointToInfinity (P : ProjectivePoint F) : Collineation F :=
  match P with
  | Sum.inl p =>
      ((addCoordinate 0 2 (by decide) (-p.1)).trans
        (addCoordinate 1 2 (by decide) (-p.2))).trans
        (permuteCoordinates (Equiv.swap 1 2))
  | Sum.inr none => Collineation.refl
  | Sum.inr (some m) =>
      (addCoordinate 1 0 (by decide) (-m)).trans
        (permuteCoordinates (Equiv.swap 0 1))

theorem pointToInfinity_apply (P : ProjectivePoint F) :
    (pointToInfinity P).point P = Sum.inr none := by
  cases P with
  | inl p =>
    rcases p with ⟨x,y⟩
    simp [pointToInfinity, Collineation.trans, addCoordinate, permuteCoordinates,
      ofLinear, pointEquiv, coordAdd, coordPerm_apply, homogeneousPoint,
      normalizeProjective, Equiv.swap_apply_def]
  | inr d =>
    cases d <;> simp [pointToInfinity, Collineation.refl, Collineation.trans,
      addCoordinate, permuteCoordinates, ofLinear, pointEquiv, coordAdd,
      coordPerm_apply, homogeneousPoint, normalizeProjective, Equiv.swap_apply_def]

noncomputable def verticalToInfinity (b : F) : Collineation F :=
  (addCoordinate 0 2 (by decide) (-b)).trans
    (permuteCoordinates (Equiv.swap 0 2))

theorem verticalToInfinity_point (b : F) :
    (verticalToInfinity b).point (Sum.inr none) = Sum.inr none := by
  simp [verticalToInfinity, Collineation.trans, addCoordinate, permuteCoordinates,
    ofLinear, pointEquiv, coordAdd, coordPerm_apply, homogeneousPoint,
    normalizeProjective, Equiv.swap_apply_def]

theorem verticalToInfinity_line (b : F) :
    (verticalToInfinity b).line (some (none, b)) = none := by
  simp [verticalToInfinity, Collineation.trans, addCoordinate, permuteCoordinates,
    ofLinear, lineEquiv, coordAdd, coordPerm_apply, homogeneousLine,
    normalizeLine, Equiv.swap_apply_def]

theorem exists_flag_normalization (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : ProjectiveIncident P l) :
    ∃ e : Collineation F, e.point P = Sum.inr none ∧ e.line l = none := by
  let a := pointToInfinity P
  have hp : a.point P = Sum.inr none := pointToInfinity_apply P
  have hi : ProjectiveIncident (Sum.inr none) (a.line l) := by
    rw [← hp]
    exact (a.incident P l).mpr h
  cases hl : a.line l with
  | none => exact ⟨a, hp, hl⟩
  | some L =>
    rcases L with ⟨d,b⟩
    have hd : d = none := by
      simpa only [hl, ProjectiveIncident, ThroughProjective] using hi
    subst d
    refine ⟨a.trans (verticalToInfinity b), ?_, ?_⟩
    · change (verticalToInfinity b).point (a.point P) = _
      rw [hp, verticalToInfinity_point]
    · change (verticalToInfinity b).line (a.line l) = _
      rw [hl, verticalToInfinity_line]

section FiniteSets

variable [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem card_image (e : Collineation F) (B : Finset (ProjectivePoint F)) :
    (B.image e.point).card = B.card :=
  Finset.card_image_of_injective B e.point.injective

omit [Fintype F] in
theorem image_filter_incident (e : Collineation F) (B : Finset (ProjectivePoint F))
    (l : ProjectiveLine F) :
    (B.image e.point).filter (fun Q => ProjectiveIncident Q (e.line l)) =
      (B.filter (fun P => ProjectiveIncident P l)).image e.point := by
  rw [Finset.filter_image]
  congr 1
  ext P
  simp [e.incident]

omit [Fintype F] in
theorem card_filter_incident (e : Collineation F) (B : Finset (ProjectivePoint F))
    (l : ProjectiveLine F) :
    ((B.image e.point).filter (fun Q => ProjectiveIncident Q (e.line l))).card =
      (B.filter (fun P => ProjectiveIncident P l)).card := by
  rw [image_filter_incident, card_image]

theorem card_skew_image (e : Collineation F) (B : Finset (ProjectivePoint F)) :
    (skewProjective (B.image e.point)).card = (skewProjective B).card := by
  symm
  apply Finset.card_equiv e.line
  intro l
  simp only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.forall_mem_image, e.incident]

theorem card_tangents_image (e : Collineation F) (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) :
    (Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident (e.point P) l ∧
        ((B.image e.point).filter (fun Q => ProjectiveIncident Q l)).card = 1)).card =
    (Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident P l ∧ (B.filter (fun Q => ProjectiveIncident Q l)).card = 1)).card := by
  symm
  apply Finset.card_equiv e.line
  intro l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    e.incident, card_filter_incident]

theorem exists_tangent_normalization (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : B.filter (fun Q => ProjectiveIncident Q l) = {P}) :
    ∃ e : Collineation F,
      e.point P = Sum.inr none ∧ e.line l = none ∧
      (B.image e.point).filter (fun Q => ProjectiveIncident Q none) = {Sum.inr none} ∧
      (B.image e.point).card = B.card ∧
      (skewProjective (B.image e.point)).card = (skewProjective B).card := by
  have hi : ProjectiveIncident P l := by
    have hm : P ∈ B.filter (fun Q => ProjectiveIncident Q l) := by rw [h]; simp
    exact (Finset.mem_filter.mp hm).2
  obtain ⟨e, hp, hl⟩ := exists_flag_normalization P l hi
  refine ⟨e, hp, hl, ?_, card_image e B, card_skew_image e B⟩
  rw [← hl, image_filter_incident, h, Finset.image_singleton, hp]

omit [Fintype F] in
theorem eq_affinePart_disjSum (B : Finset (ProjectivePoint F))
    (h : B.filter (fun Q => ProjectiveIncident Q none) = {Sum.inr none}) :
    B = B.toLeft.disjSum {none} := by
  have hr : B.toRight = {none} := by
    ext d
    have hd := Finset.ext_iff.mp h (Sum.inr d)
    simp only [Finset.mem_filter] at hd
    simpa only [Finset.mem_toRight, ProjectiveIncident,
      and_true, Finset.mem_singleton, Sum.inr.injEq] using hd
  rw [← hr, Finset.toLeft_disjSum_toRight]

omit [Fintype F] in
theorem card_affinePart_add_one (B : Finset (ProjectivePoint F))
    (h : B.filter (fun Q => ProjectiveIncident Q none) = {Sum.inr none}) :
    B.toLeft.card + 1 = B.card := by
  conv_rhs => rw [eq_affinePart_disjSum B h]
  simp

theorem card_skew_codes (U : Finset (Point F)) :
    (Finset.univ.filter (fun z : Fin 2 → F =>
      ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card =
    (skewProjective (U.disjSum {none})).card := by
  apply Finset.card_bij (fun z _ => some (some (z 1), z 0))
  · intro z hz
    simp only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [ProjectiveIncident, ThroughProjective] using hz
  · intro z hz w hw he
    have he' : z 1 = w 1 ∧ z 0 = w 0 := by simpa using he
    ext i
    fin_cases i <;> simp_all
  · intro l hl
    simp only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    cases l with
    | none => simp [ProjectiveIncident] at hl
    | some l =>
      rcases l with ⟨d,b⟩
      cases d with
      | none => simp [ProjectiveIncident, ThroughProjective] at hl
      | some m =>
        refine ⟨![b,m], ?_, by simp⟩
        simpa [ProjectiveIncident, ThroughProjective] using hl

theorem exists_normalized_affine_set (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : B.filter (fun Q => ProjectiveIncident Q l) = {P}) :
    ∃ (e : Collineation F) (U : Finset (Point F)),
      e.point P = Sum.inr none ∧ e.line l = none ∧
      B.image e.point = U.disjSum {none} ∧
      U.card + 1 = B.card ∧
      (Finset.univ.filter (fun z : Fin 2 → F =>
        ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card = (skewProjective B).card := by
  obtain ⟨e, hp, hl, hi, hc, hs⟩ := exists_tangent_normalization B P l h
  refine ⟨e, (B.image e.point).toLeft, hp, hl,
    eq_affinePart_disjSum _ hi, ?_, ?_⟩
  · rw [card_affinePart_add_one _ hi, hc]
  · rw [card_skew_codes, ← eq_affinePart_disjSum _ hi, hs]

omit [Fintype F] in
theorem card_normalized_vertical_section (U : Finset (Point F)) (c : F) :
    ((U.disjSum {none}).filter (fun P => ProjectiveIncident P (some (none,c)))).card =
      (U.filter (fun p => p.1 = c)).card + 1 := by
  have h : (U.disjSum {none}).filter (fun P => ProjectiveIncident P (some (none,c))) =
      (U.filter (fun p => p.1 = c)).disjSum {none} := by
    ext P
    simp only [Finset.mem_filter]
    cases P <;> simp [ProjectiveIncident, ThroughProjective, OnLine, lineEval, eq_comm]
  rw [h, Finset.card_disjSum]
  simp

omit [Fintype F] in
theorem card_normalized_infinity_section (U : Finset (Point F)) :
    ((U.disjSum {none}).filter (fun P => ProjectiveIncident P none)).card = 1 := by
  have h : (U.disjSum {none}).filter (fun P => ProjectiveIncident P none) =
      {Sum.inr (none : Direction F)} := by
    ext P
    simp only [Finset.mem_filter]
    cases P <;> simp [ProjectiveIncident]
  rw [h, Finset.card_singleton]

theorem card_normalized_tangents (U : Finset (Point F)) :
    (Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident (Sum.inr none) l ∧
        ((U.disjSum {none}).filter (fun P => ProjectiveIncident P l)).card = 1)).card =
      (Finset.univ.filter (fun c : F => ∀ p ∈ U, p.1 ≠ c)).card + 1 := by
  have h : Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident (Sum.inr none) l ∧
        ((U.disjSum {none}).filter (fun P => ProjectiveIncident P l)).card = 1) =
      insert none ((Finset.univ.filter (fun c : F => ∀ p ∈ U, p.1 ≠ c)).image
        (fun c => some (none,c))) := by
    ext l
    cases l with
    | none =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [card_normalized_infinity_section]
      simp [ProjectiveIncident]
    | some l =>
      rcases l with ⟨d,c⟩
      cases d with
      | none =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [card_normalized_vertical_section]
        simp [ProjectiveIncident, ThroughProjective,
          Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      | some m =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp [ProjectiveIncident, ThroughProjective]
  rw [h, Finset.card_insert_of_notMem (by simp)]
  rw [Finset.card_image_of_injective _ (by
    intro c d hcd
    simpa using hcd)]

theorem exists_normalized_affine_set_with_tangents (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : B.filter (fun Q => ProjectiveIncident Q l) = {P}) :
    ∃ (e : Collineation F) (U : Finset (Point F)),
      e.point P = Sum.inr none ∧ e.line l = none ∧
      B.image e.point = U.disjSum {none} ∧ U.card + 1 = B.card ∧
      (Finset.univ.filter (fun z : Fin 2 → F =>
        ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card = (skewProjective B).card ∧
      (Finset.univ.filter (fun L : ProjectiveLine F =>
        ProjectiveIncident P L ∧ (B.filter (fun Q => ProjectiveIncident Q L)).card = 1)).card =
        (Finset.univ.filter (fun c : F => ∀ p ∈ U, p.1 ≠ c)).card + 1 := by
  obtain ⟨e, U, hp, hl, hU, hc, hs⟩ := exists_normalized_affine_set B P l h
  refine ⟨e, U, hp, hl, hU, hc, hs, ?_⟩
  rw [← card_tangents_image e B P, hp, hU, card_normalized_tangents]

end FiniteSets

end ProjectiveNormalization
end Balanced

end OAI
