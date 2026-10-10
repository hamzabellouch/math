import OAI.Analysis.KadisonKastler.PointedPowerCyclicity

namespace OAI

/-! # Independent-site vacuum moments in the countable product

The vacuum rank-one projection at one site commutes with all other
sites. Its corner is the local vector state, giving product moments.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

private def pointedLocalVacuumProjection : PointedLocalHilbert →L[ℂ] PointedLocalHilbert :=
  InnerProductSpace.rankOne ℂ pointedLocalVacuum pointedLocalVacuum

private theorem pointedLocalVacuumProjection_apply :
    pointedLocalVacuumProjection pointedLocalVacuum = pointedLocalVacuum := by
  simp [pointedLocalVacuumProjection, pointedLocalVacuum]

private theorem pointedLocalVacuumProjection_star :
    star pointedLocalVacuumProjection = pointedLocalVacuumProjection := by
  simp only [pointedLocalVacuumProjection, ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne]

private theorem pointedLocalVacuumProjection_corner
    (A : PointedLocalHilbert →L[ℂ] PointedLocalHilbert) :
    pointedLocalVacuumProjection * A * pointedLocalVacuumProjection =
      (inner ℂ pointedLocalVacuum (A pointedLocalVacuum)) • pointedLocalVacuumProjection := by
  ext x
  simp [pointedLocalVacuumProjection, mul_apply_eq_comp, map_smul,
    smul_smul, mul_comm]

private theorem pointedPowerVacuumProjection_fixes (i : ℕ) :
    pointedPowerOperator i pointedLocalVacuumProjection pointedPowerVacuum =
      pointedPowerVacuum := by
  rw [pointedPowerVacuum, ← pointedPowerInsertLinear_operator i 0 (by simp),
    pointedLocalVacuumProjection_apply, pointedLocalVacuum,
    pointedPowerInsertLinear_single]
  congr 1
  ext j
  simp

private theorem pointedPowerVacuumProjection_star (i : ℕ) :
    star (pointedPowerOperator i pointedLocalVacuumProjection) =
      pointedPowerOperator i pointedLocalVacuumProjection := by
  rw [← map_star, pointedLocalVacuumProjection_star]

private theorem vacuum_moment_split
    (i : ℕ) (A : PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
    (B : PointedPowerHilbert →L[ℂ] PointedPowerHilbert)
    (hB : Commute (pointedPowerOperator i pointedLocalVacuumProjection) B) :
    inner ℂ pointedPowerVacuum (pointedPowerOperator i A (B pointedPowerVacuum)) =
      inner ℂ pointedLocalVacuum (A pointedLocalVacuum) *
        inner ℂ pointedPowerVacuum (B pointedPowerVacuum) := by
  let Q := pointedPowerOperator i pointedLocalVacuumProjection
  have hQ : Q pointedPowerVacuum = pointedPowerVacuum := pointedPowerVacuumProjection_fixes i
  have hQs : star Q = Q := pointedPowerVacuumProjection_star i
  have hQB : Q (B pointedPowerVacuum) = B pointedPowerVacuum := by
    rw [← mul_apply_eq_comp, hB.eq, mul_apply_eq_comp, hQ]
  have hinner (x : PointedPowerHilbert) :
      inner ℂ pointedPowerVacuum (Q x) = inner ℂ pointedPowerVacuum x := by
    have h := ContinuousLinearMap.adjoint_inner_right Q pointedPowerVacuum x
    rw [← ContinuousLinearMap.star_eq_adjoint, hQs, hQ] at h
    exact h
  have hcorner : Q * pointedPowerOperator i A * Q =
      (inner ℂ pointedLocalVacuum (A pointedLocalVacuum)) • Q := by
    dsimp only [Q]
    rw [← map_mul, ← map_mul, pointedLocalVacuumProjection_corner, map_smul]
  calc
    _ = inner ℂ pointedPowerVacuum (Q (pointedPowerOperator i A (Q (B pointedPowerVacuum)))) := by
      rw [hQB, hinner]
    _ = inner ℂ pointedPowerVacuum ((Q * pointedPowerOperator i A * Q) (B pointedPowerVacuum)) := rfl
    _ = _ := by
      rw [hcorner]
      simp only [smul_apply, inner_smul_right, hQB]

/-- The vacuum factors on every finite family of distinct sites. -/
theorem pointedPower_product_moment
    (A : ℕ → PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
    (l : List ℕ) (hl : l.Nodup) :
    inner ℂ pointedPowerVacuum
      (((l.map fun i => pointedPowerOperator i (A i)).prod) pointedPowerVacuum) =
      (l.map fun i => inner ℂ pointedLocalVacuum (A i pointedLocalVacuum)).prod := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, norm_pointedPowerVacuum]
    norm_num
  | cons i l ih =>
    have hnot : i ∉ l := (List.nodup_cons.mp hl).1
    have htail : l.Nodup := (List.nodup_cons.mp hl).2
    have hcomm : Commute (pointedPowerOperator i pointedLocalVacuumProjection)
        ((l.map fun j => pointedPowerOperator j (A j)).prod) := by
      apply Commute.list_prod_right
      intro T hT
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hT
      exact pointedPowerOperator_commute (i := i) (j := j)
        (by intro h; subst j; exact hnot hj) _ _
    simpa only [List.map_cons, List.prod_cons, mul_apply_eq_comp, ih htail] using
      vacuum_moment_split i (A i) ((l.map fun j => pointedPowerOperator j (A j)).prod) hcomm

/-- The configuration representation has exactly the prescribed matrix-state moments. -/
theorem pointedPower_moments {ν : ℝ} (d : PointedLocalMatrixData ν)
    (l : List ℕ) (hl : l.Nodup) (r c : ℕ → Fin 2) :
    inner ℂ pointedPowerVacuum
      (((l.map fun i => (pointedPowerSite d.left i).entry (r i) (c i)).prod)
        pointedPowerVacuum) =
      (l.map fun i => if r i = c i then (twoSiteWeight ν (r i) : ℂ) else 0).prod := by
  simpa only [pointedPowerSite, MatrixUnitSystem.map_entry, d.moment] using
    pointedPower_product_moment (fun i => d.left.entry (r i) (c i)) l hl

theorem pointedPowerSite_commuting
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (i j : ℕ) (hij : i ≠ j) (a b c d : Fin 2) :
    Commute ((pointedPowerSite E i).entry a b) ((pointedPowerSite E j).entry c d) :=
  pointedPowerOperator_commute hij _ _

end

end KadisonKastler

end OAI
