import OAI.Combinatorics.HoneycombCorridor.Bridges

namespace OAI

namespace PolynomialVacuumBridge.Corridor

def window (h : ℕ) (r : ℝ) : Set Vertex :=
  {v | 0 ≤ layer v ∧ layer v < (h : ℤ) ∧ |(position v).1| ≤ r}

theorem window_finite (h : ℕ) (r : ℝ) : (window h r).Finite := by
  let B : ℤ := ⌈|r| + (h : ℝ) + 1⌉
  have hB : |r| + (h : ℝ) + 1 ≤ (B : ℝ) := Int.le_ceil _
  have hrect : (Set.Icc (-B) B ×ˢ Set.Ico (0 : ℤ) (h : ℤ)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Ico _ _)
  have hf := (hrect.image (fun z => Vertex.up z.1 z.2)).union
    (hrect.image (fun z => Vertex.down z.1 z.2))
  apply hf.subset
  intro v hv
  obtain ⟨hj0, hjh, hr⟩ := hv
  have hr' : r ≤ |r| := le_abs_self r
  cases v with
  | up i j =>
      simp only [layer] at hj0 hjh
      simp only [position] at hr
      have hj0' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
      have hjh' : (j : ℝ) < (h : ℝ) := by exact_mod_cast hjh
      have hi : -B ≤ i ∧ i ≤ B := by
        obtain ⟨hrl, hru⟩ := abs_le.mp hr
        constructor
        · have : -(B : ℝ) ≤ (i : ℝ) := by linarith
          exact_mod_cast this
        · have : (i : ℝ) ≤ (B : ℝ) := by linarith
          exact_mod_cast this
      exact Or.inl ⟨(i, j), ⟨hi, hj0, hjh⟩, rfl⟩
  | down i j =>
      simp only [layer] at hj0 hjh
      simp only [position] at hr
      have hj0' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
      have hjh' : (j : ℝ) < (h : ℝ) := by exact_mod_cast hjh
      have hi : -B ≤ i ∧ i ≤ B := by
        obtain ⟨hrl, hru⟩ := abs_le.mp hr
        constructor
        · have : -(B : ℝ) ≤ (i : ℝ) := by linarith
          exact_mod_cast this
        · have : (i : ℝ) ≤ (B : ℝ) := by linarith
          exact_mod_cast this
      exact Or.inr ⟨(i, j), ⟨hi, hj0, hjh⟩, rfl⟩

abbrev CorridorVertex (h : ℕ) :=
  {v : Vertex // v ∈ window h ((h : ℝ) * (Real.log (h : ℝ)) ^ 2)}

noncomputable def corridorList {h : ℕ} (p : ConfinedBridgePath h) :
    List (CorridorVertex h) :=
  p.val.vertices.attach.map fun v =>
    ⟨v.val, (p.val.inStrip v.val v.property).1,
      (p.val.inStrip v.val v.property).2, p.property v.val v.property⟩

theorem corridorList_val {h : ℕ} (p : ConfinedBridgePath h) :
    (corridorList p).map Subtype.val = p.val.vertices := by
  simp only [corridorList, List.map_map, Function.comp_def]
  exact List.attach_map_subtype_val _

theorem corridorList_nodup {h : ℕ} (p : ConfinedBridgePath h) :
    (corridorList p).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [corridorList_val]
  exact p.val.distinct

theorem confined_paths_finite (h : ℕ) : Finite (ConfinedBridgePath h) := by
  let : Finite (CorridorVertex h) := (window_finite h _).to_subtype
  let : Fintype (CorridorVertex h) := Fintype.ofFinite _
  apply Finite.of_injective
    (fun p : ConfinedBridgePath h =>
      (⟨corridorList p, corridorList_nodup p⟩ : {l : List (CorridorVertex h) // l.Nodup}))
  intro p q hpq
  have hl : corridorList p = corridorList q := congrArg Subtype.val hpq
  have hv : p.val.vertices = q.val.vertices := by
    simpa only [corridorList_val] using congrArg (List.map Subtype.val) hl
  apply Subtype.ext
  cases p with | mk p hp =>
    cases q with | mk q hq =>
      cases p
      cases q
      cases hv
      rfl

theorem confined_finite_sums (h : ℕ) :
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h =>
      firstLengthWeight p.val / confinedMass h) := by
  let := confined_paths_finite h
  exact ⟨summable_of_hasFiniteSupport (Set.toFinite _),
    summable_of_hasFiniteSupport (Set.toFinite _),
    summable_of_hasFiniteSupport (Set.toFinite _)⟩

end PolynomialVacuumBridge.Corridor

end OAI
