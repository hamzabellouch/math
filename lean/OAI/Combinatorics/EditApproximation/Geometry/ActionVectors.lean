import OAI.Combinatorics.EditApproximation.Numerics.Numerics
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The actual fixed-block action hull

Coordinates are precisely the child/state pairs occurring in a finite band.
Each action assigns its fixed rational child mass to one state per child.
This verifies the probability, coverage and block-mass hypotheses used by
the numerical optimizer and optimistic entropy regret.
-/

namespace EditApproximation

open Finset





theorem action_coordinate_mem {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) {action : β → σ} (haction : action ∈ band) (child : β) :
    (child, action child) ∈ bandCoordinates band := by
  apply mem_biUnion.mpr
  exact ⟨action, haction, mem_image.mpr ⟨child, mem_univ _, rfl⟩⟩

theorem actionVector_probability {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    {action : β → σ} (haction : action ∈ band) :
    (∀ coordinate ∈ bandCoordinates band, (0 : ℝ) ≤ actionVector mass action coordinate) ∧
      (∑ coordinate ∈ bandCoordinates band, (actionVector mass action coordinate : ℝ)) = 1 := by
  have htotal : (0 : ℚ) < ∑ child, mass child := sum_pos (fun child _ => hpos child) univ_nonempty
  constructor
  · intro coordinate _
    unfold actionVector
    split_ifs
    · exact_mod_cast (div_pos (hpos _) htotal).le
    · norm_num
  · have hsubset : (univ.image fun child => (child, action child)) ⊆ bandCoordinates band := by
      intro coordinate hc
      obtain ⟨child, _, rfl⟩ := mem_image.mp hc
      exact action_coordinate_mem band haction child
    have hsum : (∑ coordinate ∈ bandCoordinates band, (actionVector mass action coordinate : ℝ)) =
        ∑ coordinate ∈ univ.image (fun child => (child, action child)),
          (actionVector mass action coordinate : ℝ) := by
      symm
      apply sum_subset hsubset
      intro coordinate _ hnot
      have hne : coordinate.2 ≠ action coordinate.1 := by
        intro heq
        exact hnot (mem_image.mpr ⟨coordinate.1, mem_univ _, Prod.ext rfl heq.symm⟩)
      simp only [actionVector, ite_eq_right hne, Rat.cast_zero]
    rw [hsum, sum_image]
    · simp only [actionVector, ite_true, Rat.cast_div]
      rw [← sum_div]
      have hcast : (∑ child, (mass child : ℝ)) = ((∑ child, mass child : ℚ) : ℝ) := by
        norm_cast
      rw [hcast]
      exact div_self (by exact_mod_cast htotal.ne')
    · intro i _ j _ hij
      exact congrArg Prod.fst hij

theorem actionVector_coordinate_coverage {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child) :
    ∀ coordinate ∈ bandCoordinates band, ∃ action ∈ band,
      (0 : ℝ) < actionVector mass action coordinate := by
  intro coordinate hcoordinate
  obtain ⟨action, ha, hcoordinate⟩ := mem_biUnion.mp hcoordinate
  obtain ⟨child, _, heq⟩ := mem_image.mp hcoordinate
  subst coordinate
  refine ⟨action, ha, ?_⟩
  simp only [actionVector, ite_true]
  have htotal : (0 : ℚ) < ∑ child, mass child := sum_pos (fun child _ => hpos child) univ_nonempty
  exact_mod_cast div_pos (hpos child) htotal

theorem actionVector_block_mass {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) (mass : β → ℚ)
    {action : β → σ} (haction : action ∈ band) (child : β) :
    (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child,
      (actionVector mass action coordinate : ℝ)) =
        (mass child / (∑ i, mass i) : ℚ) := by
  rw [sum_eq_single (child, action child)]
  · simp only [actionVector, ite_true]
  · intro coordinate hc hne
    have hchild : coordinate.1 = child := (mem_filter.mp hc).2
    have hstate : coordinate.2 ≠ action child := by
      intro hstate
      exact hne (Prod.ext hchild hstate)
    simp only [actionVector, hchild, ite_eq_right hstate, Rat.cast_zero]
  · intro hnot
    exact False.elim (hnot (mem_filter.mpr ⟨action_coordinate_mem band haction child, rfl⟩))

theorem actionVector_inner_product {β σ : Type*} [Fintype β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (gain : β × σ → ℝ)
    {action : β → σ} (haction : action ∈ band) :
    (∑ coordinate ∈ bandCoordinates band, gain coordinate * (actionVector mass action coordinate : ℝ)) =
      ∑ child, gain (child, action child) * (mass child / (∑ i, mass i) : ℚ) := by
  have hsubset : (univ.image fun child => (child, action child)) ⊆ bandCoordinates band := by
    intro coordinate hc
    obtain ⟨child, _, rfl⟩ := mem_image.mp hc
    exact action_coordinate_mem band haction child
  have hsum : (∑ coordinate ∈ bandCoordinates band,
      gain coordinate * (actionVector mass action coordinate : ℝ)) =
        ∑ coordinate ∈ univ.image (fun child => (child, action child)),
          gain coordinate * (actionVector mass action coordinate : ℝ) := by
    symm
    apply sum_subset hsubset
    intro coordinate _ hnot
    have hne : coordinate.2 ≠ action coordinate.1 := by
      intro heq
      exact hnot (mem_image.mpr ⟨coordinate.1, mem_univ _, Prod.ext rfl heq.symm⟩)
    simp only [actionVector, ite_eq_right hne, Rat.cast_zero, mul_zero]
  rw [hsum, sum_image]
  · simp only [actionVector, ite_true]
  · intro i _ j _ hij
    exact congrArg Prod.fst hij

/-- The coordinate normalization translates entropy gains exactly into
the unnormalized costs of a band action. -/
theorem actionVector_cost_identity {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child) (cost : β × σ → ℝ)
    {action : β → σ} (haction : action ∈ band) :
    -((∑ child, mass child : ℚ) : ℝ) *
      (∑ coordinate ∈ bandCoordinates band,
        (-cost coordinate / (mass coordinate.1 : ℝ)) * (actionVector mass action coordinate : ℝ)) =
          ∑ child, cost (child, action child) := by
  rw [actionVector_inner_product band mass _ haction, mul_sum]
  apply sum_congr rfl
  intro child _
  have hmass : (mass child : ℝ) ≠ 0 := by exact_mod_cast (hpos child).ne'
  have htotal : ((∑ child, mass child : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (sum_pos (fun child _ => hpos child) univ_nonempty).ne'
  rw [Rat.cast_div]
  field_simp

theorem band_block_nonempty {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) (hband : band.Nonempty) (child : β) :
    ((bandCoordinates band).filter fun coordinate => coordinate.1 = child).Nonempty := by
  obtain ⟨action, ha⟩ := hband
  exact ⟨(child, action child), mem_filter.mpr ⟨action_coordinate_mem band ha child, rfl⟩⟩

theorem band_hull_block_mass {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) (mass : β → ℚ) (child : β)
    (p : β × σ → ℝ)
    (hp : p ∈ convexHull ℝ (rationalVertexSet (band.toList.map (actionVector mass)))) :
    (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child, p coordinate) =
      (mass child / (∑ i, mass i) : ℚ) := by
  let targetMass : ℝ := (mass child / (∑ i, mass i) : ℚ)
  have hconvex : Convex ℝ {q : β × σ → ℝ |
      (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child, q coordinate) =
        targetMass} := by
    intro x hx y hy a b _ _ hab
    change (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child,
      (a * x coordinate + b * y coordinate)) = targetMass
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hx, hy]
    calc
      a * targetMass + b * targetMass = (a + b) * targetMass := by ring
      _ = targetMass := by rw [hab, one_mul]
  have hsubset : rationalVertexSet (band.toList.map (actionVector mass)) ⊆
      {q : β × σ → ℝ |
        (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child, q coordinate) =
          targetMass} := by
    rintro _ ⟨vertex, hv, rfl⟩
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact actionVector_block_mass band mass (mem_toList.mp ha) child
  exact convexHull_min hsubset hconvex hp

theorem band_entropy_optimizer {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ)) (hband : band.Nonempty)
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (linear : β × σ → ℚ) (H : ℕ) (hH : 4 ≤ H) :
    let coordinates := bandCoordinates band
    let vertices := band.toList.map (actionVector mass)
    ∃ maximizer ∈ convexHull ℝ (rationalVertexSet vertices),
      IsMaxOn (entropyValue coordinates 1 (fun i => (linear i : ℝ)))
        (convexHull ℝ (rationalVertexSet vertices)) maximizer ∧
      (∑ i ∈ coordinates, |(finiteRationalOptimizer coordinates vertices linear
        (H + coordinates.card + 2) ((H + coordinates.card + 2) ^ 80) i : ℝ) - maximizer i|) ≤
          1 / (H : ℝ) ^ 3 := by
  dsimp only
  have hvertices : band.toList.map (actionVector mass) ≠ [] := by
    obtain ⟨action, ha⟩ := hband
    intro hnil
    have hmem : actionVector mass action ∈ band.toList.map (actionVector mass) :=
      List.mem_map.mpr ⟨action, mem_toList.mpr ha, rfl⟩
    simp only [hnil, List.not_mem_nil] at hmem
  apply finite_entropy_optimizer _ _ _ _ hvertices hH
  · intro p hp
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hp
    exact actionVector_probability band mass hpos (mem_toList.mp ha)
  · intro coordinate hc
    obtain ⟨action, ha, hpositive⟩ := actionVector_coordinate_coverage band mass hpos coordinate hc
    exact ⟨actionVector mass action, List.mem_map.mpr ⟨action, mem_toList.mpr ha, rfl⟩, hpositive⟩

end EditApproximation

end OAI
