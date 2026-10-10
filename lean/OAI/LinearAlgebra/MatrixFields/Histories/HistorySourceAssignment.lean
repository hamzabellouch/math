import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryGroupCore
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryRecovery

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.GroupOrbitProjection

open PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

section UniformRestriction

variable {H S : Type*} [Fintype H] [Fintype S] [DecidableEq H] [DecidableEq S]

def curryFamily (X : H × S → Type*) : (∀ c, X c) ≃ (∀ h s, X (h, s)) where
  toFun x h s := x (h, s)
  invFun x c := x c.1 c.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem average_subtype_restrict {X : H → Type*} [∀ h, Fintype (X h)]
    [∀ h, Nonempty (X h)] (p : H → Prop) [DecidablePred p]
    (f : (∀ h : {h // p h}, X h.val) → ℝ) :
    average (fun x : ∀ h, X h => f (fun h => x h.val)) = average f := by
  change average (fun x =>
    (fun z : (∀ h : {h // p h}, X h.val) × (∀ h : {h // ¬p h}, X h.val) => f z.1)
      ((Equiv.piEquivPiSubtypeProd p X) x)) = average f
  rw [average_equiv (Equiv.piEquivPiSubtypeProd p X)
    (fun z : (∀ h : {h // p h}, X h.val) × (∀ h : {h // ¬p h}, X h.val) => f z.1),
    average_prod_fst]

theorem average_history_restrict {X : H × S → Type*} [∀ c, Fintype (X c)]
    [∀ c, Nonempty (X c)] (p : H → Prop) [DecidablePred p]
    (f : (∀ c : {h // p h} × S, X (c.1.val, c.2)) → ℝ) :
    average (fun x : ∀ c, X c => f (fun c => x (c.1.val, c.2))) = average f := by
  calc
    _ = average (fun x : ∀ h s, X (h, s) => f (fun c => x c.1.val c.2)) :=
      average_equiv (curryFamily X) _
    _ = average (fun x : ∀ h : {h // p h}, ∀ s, X (h.val, s) =>
        f (fun c => x c.1 c.2)) :=
      average_subtype_restrict (X := fun h => ∀ s, X (h, s)) p
        (fun x => f (fun c => x c.1 c.2))
    _ = average f :=
      average_equiv (curryFamily (fun c : {h // p h} × S => X (c.1.val, c.2))).symm f

theorem average_half_history_restrict {X : H × S → Type*} [∀ c, Fintype (X c)]
    [∀ c, Nonempty (X c)] (p : H → Prop) [DecidablePred p]
    (f : ((∀ c : {h // p h} × S, X (c.1.val, c.2)) ×
      (∀ c : {h // p h} × S, X (c.1.val, c.2))) → ℝ) :
    average (fun g : (∀ c, X c) × (∀ c, X c) =>
      f ((fun c => g.1 (c.1.val, c.2)), (fun c => g.2 (c.1.val, c.2)))) =
        average f := by
  rw [average_prod_average]
  calc
    _ = average (fun x : ∀ c, X c =>
        average (fun y : ∀ c : {h // p h} × S, X (c.1.val, c.2) =>
          f ((fun c => x (c.1.val, c.2)), y))) := by
      apply average_congr
      intro x
      exact average_history_restrict (X := X) p
        (fun y => f ((fun c => x (c.1.val, c.2)), y))
    _ = average (fun x : ∀ c : {h // p h} × S, X (c.1.val, c.2) =>
        average (fun y => f (x, y))) :=
      average_history_restrict (X := X) p (fun x => average (fun y => f (x, y)))
    _ = average f := (average_prod_average f).symm

end UniformRestriction

section OrbitFraction

variable {G H X Y : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [MulAction G X] [MulAction H Y]

theorem orbit_fraction_of_uniform_projection (project : X → Y) (shift : G → H)
    (hsmul : ∀ g x, project (g • x) = shift g • project x)
    (huniform : ∀ f : H → ℝ, average (fun g => f (shift g)) = average f)
    (x : X) (bad : Y → Prop) :
    (((OrbitCounting.orbitSet (G := G) x).filter (fun v => bad (project v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card =
      (((OrbitCounting.orbitSet (G := H) (project x)).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := H) (project x)).card := by
  rw [← OrbitCounting.bad_shift_fraction (G := G) x (fun v => bad (project v)),
    ← OrbitCounting.bad_shift_fraction (G := H) (project x) bad]
  rw [← average_indicator_eq, ← average_indicator_eq]
  simp_rw [hsmul]
  exact huniform (fun g => if bad (g • project x) then (1 : ℝ) else 0)

theorem rejected_fraction_of_uniform_projection (project : X → Y) (shift : G → H)
    (hsmul : ∀ g x, project (g • x) = shift g • project x)
    (huniform : ∀ f : H → ℝ, average (fun g => f (shift g)) = average f)
    (x : X) (bad : Y → Prop) :
    ((rejectedFilter (OrbitCounting.orbitSet (G := G) x)
      (fun v => bad (project v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card =
      ((rejectedFilter (OrbitCounting.orbitSet (G := H) (project x)) bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := H) (project x)).card := by
  simpa only [rejectedFilter, Finset.filter_congr_decidable] using
    orbit_fraction_of_uniform_projection project shift hsmul huniform x bad

end OrbitFraction

section ConjugatedProjection

variable {G H RX RY CX CY : Type*} [Group G] [Group H]
  [MulAction G CX] [MulAction H CY]

theorem conjugated_projection_smul (ex : RX ≃ CX) (ey : RY ≃ CY)
    (raw : RX → RY) (canonical : CX → CY) (shift : G → H)
    (hc : ∀ x, ey (raw x) = canonical (ex x))
    (hs : ∀ g x, canonical (g • x) = shift g • canonical x) :
    letI : MulAction G RX := EquivOrbitTransport.action ex
    letI : MulAction H RY := EquivOrbitTransport.action ey
    ∀ g x, raw (g • x) = shift g • raw x := by
  let : MulAction G RX := EquivOrbitTransport.action ex
  let : MulAction H RY := EquivOrbitTransport.action ey
  intro g x
  apply ey.injective
  rw [hc, EquivOrbitTransport.equiv_smul ex, hs,
    EquivOrbitTransport.equiv_smul ey, hc]

end ConjugatedProjection

def transportedOrbit {G RX CX : Type*} [Group G] [Fintype G] [MulAction G CX]
    (ex : RX ≃ CX) (x : RX) : Finset RX :=
  @OrbitCounting.orbitSet G RX _ (EquivOrbitTransport.action ex) _ _ x

theorem transported_projection_fraction {G H RX RY CX CY : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [MulAction G CX] [MulAction H CY]
    (ex : RX ≃ CX) (ey : RY ≃ CY)
    (raw : RX → RY) (canonical : CX → CY) (shift : G → H)
    (hc : ∀ x, ey (raw x) = canonical (ex x))
    (hs : ∀ g x, canonical (g • x) = shift g • canonical x)
    (huniform : ∀ f : H → ℝ, average (fun g => f (shift g)) = average f)
    (x : RX) (bad : RY → Prop) :
    ((rejectedFilter (transportedOrbit (G := G) ex x)
      (fun v => bad (raw v))).card : ℝ) / (transportedOrbit (G := G) ex x).card =
      ((rejectedFilter (transportedOrbit (G := H) ey (raw x)) bad).card : ℝ) /
        (transportedOrbit (G := H) ey (raw x)).card :=
  @rejected_fraction_of_uniform_projection G H RX RY _ _ _ _
    (EquivOrbitTransport.action ex) (EquivOrbitTransport.action ey)
    raw shift (conjugated_projection_smul ex ey raw canonical shift hc hs) huniform x bad

section CompleteHistories

variable {H S : Type*} [Fintype H] [Fintype S] [DecidableEq H] [DecidableEq S]
  (P X Y : H × S → Type*) [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

def projectPair (p : H → Prop) (w : CompleteWordPair P X Y) :
    CompleteWordPair (fun c : {h // p h} × S => P (c.1.val, c.2))
      (fun c => X (c.1.val, c.2)) (fun c => Y (c.1.val, c.2)) where
  left c i := w.left (c.1.val, c.2) i
  right c i := w.right (c.1.val, c.2) i

def projectShifts (p : H → Prop) (g : HalfClassPermutations P) :
    HalfClassPermutations (fun c : {h // p h} × S => P (c.1.val, c.2)) :=
  ((fun c => g.1 (c.1.val, c.2)), (fun c => g.2 (c.1.val, c.2)))

omit [Fintype H] [Fintype S] [DecidableEq H] [DecidableEq S]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)] in
theorem projectPair_smul (p : H → Prop) (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) :
    projectPair P X Y p (g • w) = projectShifts P p g • projectPair P X Y p w := rfl

theorem complete_orbit_projection_fraction (p : H → Prop) [DecidablePred p]
    (w : CompleteWordPair P X Y)
    (bad : CompleteWordPair (fun c : {h // p h} × S => P (c.1.val, c.2))
      (fun c => X (c.1.val, c.2)) (fun c => Y (c.1.val, c.2)) → Prop) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
      (fun v => bad (projectPair P X Y p v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card =
      (((OrbitCounting.orbitSet
        (G := HalfClassPermutations (fun c : {h // p h} × S => P (c.1.val, c.2)))
        (projectPair P X Y p w)).filter bad).card : ℝ) /
          (OrbitCounting.orbitSet
            (G := HalfClassPermutations (fun c : {h // p h} × S => P (c.1.val, c.2)))
            (projectPair P X Y p w)).card := by
  apply orbit_fraction_of_uniform_projection (projectPair P X Y p) (projectShifts P p)
  · exact projectPair_smul P X Y p
  · intro f
    exact average_half_history_restrict (X := fun c => Equiv.Perm (P c)) p f

end CompleteHistories

section UnionBound

variable {G X I : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype I]

theorem orbit_union_fraction_le (x : X) (bad : I → X → Prop) (bound : I → ℝ)
    (hbound : ∀ i,
      (((OrbitCounting.orbitSet (G := G) x).filter (bad i)).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card ≤ bound i) :
    (((OrbitCounting.orbitSet (G := G) x).filter (fun v => ∃ i, bad i v)).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ ∑ i, bound i := by
  rw [← OrbitCounting.bad_shift_fraction (G := G) x (fun v => ∃ i, bad i v),
    ← average_indicator_eq]
  calc
    _ ≤ average (fun g : G => ∑ i, if bad i (g • x) then (1 : ℝ) else 0) := by
      apply average_mono
      intro g
      split_ifs with hex
      · obtain ⟨i, hi⟩ := hex
        have hterm : (if bad i (g • x) then (1 : ℝ) else 0) = 1 := ite_eq_left hi
        exact hterm.symm.le.trans (Finset.single_le_sum
          (f := fun j : I => if bad j (g • x) then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i))
      · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
    _ = ∑ i, average (fun g : G => if bad i (g • x) then (1 : ℝ) else 0) :=
      average_sum _ _
    _ ≤ ∑ i, bound i := by
      apply Finset.sum_le_sum
      intro i _
      rw [average_indicator_eq, OrbitCounting.bad_shift_fraction (G := G) x (bad i)]
      exact hbound i

end UnionBound

section FinsetUnion

variable {X I : Type*} [Fintype I]

theorem finset_union_fraction_le (samples : Finset X) (bad : I → X → Prop)
    (bound : I → ℝ)
    (hbound : ∀ i, (((samples.filter (bad i)).card : ℝ) / samples.card) ≤ bound i) :
    (((samples.filter (fun v => ∃ i, bad i v)).card : ℝ) / samples.card) ≤
      ∑ i, bound i := by
  have hset : samples.filter (fun v => ∃ i, bad i v) =
      Finset.univ.biUnion (fun i => samples.filter (bad i)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hv, i, hi⟩ => ⟨i, hv, hi⟩, fun ⟨i, hv, hi⟩ => ⟨hv, i, hi⟩⟩
  have hcard : ((samples.filter (fun v => ∃ i, bad i v)).card : ℝ) ≤
      ∑ i, ((samples.filter (bad i)).card : ℝ) := by
    rw [hset, ← Nat.cast_sum]
    exact Nat.cast_le.mpr Finset.card_biUnion_le
  calc
    _ ≤ (∑ i, ((samples.filter (bad i)).card : ℝ)) / samples.card :=
      div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = ∑ i, ((samples.filter (bad i)).card : ℝ) / samples.card := Finset.sum_div _ _ _
    _ ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => hbound i)

theorem rejected_union_fraction_le (samples : Finset X) (bad : I → X → Prop)
    (bound : I → ℝ)
    (hbound : ∀ i, ((rejectedFilter samples (bad i)).card : ℝ) / samples.card ≤ bound i) :
    ((rejectedFilter samples (fun v => ∃ i, bad i v)).card : ℝ) / samples.card ≤
      ∑ i, bound i := by
  have hh (i : I) : ((samples.filter (bad i)).card : ℝ) / samples.card ≤ bound i := by
    simpa only [rejectedFilter, Finset.filter_congr_decidable] using hbound i
  have heq : samples.filter (fun v => ∃ i, bad i v) =
      rejectedFilter samples (fun v => ∃ i, bad i v) := by
    ext v
    simp only [rejectedFilter, Finset.mem_filter]
  rw [← heq]
  exact finset_union_fraction_le samples bad bound hh

end FinsetUnion

section GroupedHistories

variable {H S I : Type*} [Fintype H] [Fintype S] [Fintype I]
  [DecidableEq H] [DecidableEq S] [DecidableEq I]
  (P X Y : H × S → Type*) [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

theorem complete_group_union_fraction_le (group : H → I)
    (w : CompleteWordPair P X Y)
    (bad : ∀ i, CompleteWordPair
      (fun c : {h // group h = i} × S => P (c.1.val, c.2))
      (fun c => X (c.1.val, c.2)) (fun c => Y (c.1.val, c.2)) → Prop)
    (bound : I → ℝ)
    (hbound : ∀ i,
      (((OrbitCounting.orbitSet
        (G := HalfClassPermutations (fun c : {h // group h = i} × S => P (c.1.val, c.2)))
        (projectPair P X Y (fun h => group h = i) w)).filter (bad i)).card : ℝ) /
          (OrbitCounting.orbitSet
            (G := HalfClassPermutations (fun c : {h // group h = i} × S => P (c.1.val, c.2)))
            (projectPair P X Y (fun h => group h = i) w)).card ≤ bound i) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
      (fun v => ∃ i, bad i (projectPair P X Y (fun h => group h = i) v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤ ∑ i, bound i := by
  apply orbit_union_fraction_le
  intro i
  rw [complete_orbit_projection_fraction]
  exact hbound i

end GroupedHistories

section RawHistories

open JointPopulation JointCanonicalization

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ) (L R : H → Type*)

def groupCounts (p : H → Prop) : {h // p h} → Shape → ℕ := fun h => counts h.val

def projectTarget (p : H → Prop) (e : Target counts) : Target (groupCounts counts p) :=
  fun h => e h.val

def projectRaw (p : H → Prop) (w : RawPairs counts L R) :
    RawPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val) :=
  fun h => w h.val

omit [Fintype H] [DecidableEq H] in
theorem pairEquiv_projectRaw (p : H → Prop) [DecidablePred p] (e : Target counts)
    (w : RawPairs counts L R) :
    pairEquiv (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
      (projectTarget counts p e) (projectRaw counts L R p w) =
      projectPair (ClassPositions counts) (fun c => L c.1) (fun c => R c.1) p
        (pairEquiv counts L R e w) := rfl

omit [Fintype H] [DecidableEq H] in
theorem projectRaw_pairEquiv_symm (p : H → Prop) [DecidablePred p] (e : Target counts)
    (v : CanonicalPairs counts L R) :
    projectRaw counts L R p ((pairEquiv counts L R e).symm v) =
      (pairEquiv (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
        (projectTarget counts p e)).symm
        (projectPair (ClassPositions counts) (fun c => L c.1) (fun c => R c.1) p v) := by
  apply (pairEquiv (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
    (projectTarget counts p e)).eq_symm_apply.mpr
  exact (pairEquiv_projectRaw counts L R p e _).trans
    (congrArg (projectPair (ClassPositions counts) (fun c => L c.1) (fun c => R c.1) p)
      ((pairEquiv counts L R e).apply_symm_apply v))

def rawOrbit (e : Target counts) (w : RawPairs counts L R) :
    Finset (RawPairs counts L R) :=
  transportedOrbit (G := HalfClassPermutations (ClassPositions counts))
    (pairEquiv counts L R e) w

theorem raw_orbit_projection_fraction (p : H → Prop) [DecidablePred p] (e : Target counts)
    (w : RawPairs counts L R)
    (bad : RawPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val) → Prop) :
    ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => bad (projectRaw counts L R p v))).card : ℝ) /
        (rawOrbit counts L R e w).card =
      ((rejectedFilter (rawOrbit (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
        (projectTarget counts p e) (projectRaw counts L R p w)) bad).card : ℝ) /
        (rawOrbit (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
          (projectTarget counts p e) (projectRaw counts L R p w)).card := by
  exact transported_projection_fraction
    (G := HalfClassPermutations (ClassPositions counts))
    (H := HalfClassPermutations (ClassPositions (groupCounts counts p)))
    (RX := RawPairs counts L R)
    (RY := RawPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val))
    (CX := CanonicalPairs counts L R)
    (CY := CanonicalPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val))
    (pairEquiv counts L R e)
    (pairEquiv (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
      (projectTarget counts p e))
    (projectRaw counts L R p)
    (projectPair (ClassPositions counts) (fun c => L c.1) (fun c => R c.1) p)
    (projectShifts (ClassPositions counts) p)
    (pairEquiv_projectRaw counts L R p e)
    (projectPair_smul (H := H) (S := Shape) (ClassPositions counts)
      (fun c => L c.1) (fun c => R c.1) p)
    (fun f => average_half_history_restrict (H := H) (S := Shape)
      (X := fun c => Equiv.Perm (ClassPositions counts c)) p f) w bad

theorem raw_group_passing_rejection_fraction_le {I : Type*} [Fintype I] [DecidableEq I]
    (group : H → I) (e : Target counts) (w : RawPairs counts L R)
    (keep : RawPairs counts L R → Prop)
    (localKeep assigned : ∀ i : I, RawPairs (groupCounts counts (fun h => group h = i))
      (fun h => L h.val) (fun h => R h.val) → Prop)
    (hkeep : ∀ v, keep v → ∀ i,
      localKeep i (projectRaw counts L R (fun h => group h = i) v))
    (bound : I → ℝ)
    (hbound : ∀ i,
      ((rejectedFilter (rawOrbit (groupCounts counts (fun h => group h = i))
        (fun h => L h.val) (fun h => R h.val)
        (projectTarget counts (fun h => group h = i) e)
        (projectRaw counts L R (fun h => group h = i) w))
          (fun v => localKeep i v ∧ ¬assigned i v)).card : ℝ) /
        (rawOrbit (groupCounts counts (fun h => group h = i))
          (fun h => L h.val) (fun h => R h.val)
          (projectTarget counts (fun h => group h = i) e)
          (projectRaw counts L R (fun h => group h = i) w)).card ≤ bound i) :
    ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => keep v ∧ ¬∀ i, assigned i
        (projectRaw counts L R (fun h => group h = i) v))).card : ℝ) /
      (rawOrbit counts L R e w).card ≤ ∑ i, bound i := by
  let bad : I → RawPairs counts L R → Prop := fun i v =>
    localKeep i (projectRaw counts L R (fun h => group h = i) v) ∧
      ¬assigned i (projectRaw counts L R (fun h => group h = i) v)
  have hsub : rejectedFilter (rawOrbit counts L R e w)
      (fun v => keep v ∧ ¬∀ i, assigned i
        (projectRaw counts L R (fun h => group h = i) v)) ⊆
      rejectedFilter (rawOrbit counts L R e w) (fun v => ∃ i, bad i v) := by
    intro v hv
    simp only [rejectedFilter, Finset.mem_filter] at hv ⊢
    obtain ⟨hmem, hk, ha⟩ := hv
    obtain ⟨i, hi⟩ := not_forall.mp ha
    exact ⟨hmem, i, hkeep v hk i, hi⟩
  have hlocal (i : I) :
      ((rejectedFilter (rawOrbit counts L R e w) (bad i)).card : ℝ) /
        (rawOrbit counts L R e w).card ≤ bound i :=
    (raw_orbit_projection_fraction counts L R (fun h => group h = i) e w
      (fun v => localKeep i v ∧ ¬assigned i v)).le.trans (hbound i)
  have hunion : ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => ∃ i, bad i v)).card : ℝ) /
      (rawOrbit counts L R e w).card ≤ ∑ i, bound i :=
    rejected_union_fraction_le (rawOrbit counts L R e w) bad bound hlocal
  have hcard : ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => keep v ∧ ¬∀ i, assigned i
        (projectRaw counts L R (fun h => group h = i) v))).card : ℝ) ≤
      ((rejectedFilter (rawOrbit counts L R e w) (fun v => ∃ i, bad i v)).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  exact (div_le_div_of_nonneg_right hcard
    (Nat.cast_nonneg (rawOrbit counts L R e w).card)).trans hunion

end RawHistories

end MatrixMultiplication.GroupOrbitProjection

end
end




section
namespace MatrixMultiplication.RecoveryOrbitDecisions

theorem orbitSet_instances {G X : Type*} [Group G] [MulAction G X]
    (f₁ f₂ : Fintype G) (d₁ d₂ : DecidableEq X) (x : X) :
    @OrbitCounting.orbitSet G X _ _ f₁ d₁ x =
      @OrbitCounting.orbitSet G X _ _ f₂ d₂ x := by
  apply Finset.ext
  intro y
  simp only [OrbitCounting.orbitSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem orbitSet_eq_transportedOrbit {G X Y : Type*} [Group G] [MulAction G Y]
    (fRaw fCanonical : Fintype G) (d : DecidableEq X) (e : X ≃ Y) (x : X) :
    @OrbitCounting.orbitSet G X _ (EquivOrbitTransport.action e) fRaw d x =
      @GroupOrbitProjection.transportedOrbit G X Y _ fCanonical _ e x := by
  unfold GroupOrbitProjection.transportedOrbit
  exact @orbitSet_instances G X _ (EquivOrbitTransport.action e)
    fRaw fCanonical d _ x

theorem transportedOrbit_eq_orbitSet {G X Y : Type*} [Group G] [MulAction G Y]
    (fCanonical fRaw : Fintype G) (d : DecidableEq X) (e : X ≃ Y) (x : X) :
    @GroupOrbitProjection.transportedOrbit G X Y _ fCanonical _ e x =
      @OrbitCounting.orbitSet G X _ (EquivOrbitTransport.action e) fRaw d x :=
  (orbitSet_eq_transportedOrbit fRaw fCanonical d e x).symm

end MatrixMultiplication.RecoveryOrbitDecisions





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem coordinates_project (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    GroupOrbitProjection.projectPair
      (ClassPositions (activeCounts allocation m))
      AllFieldHistoryMasks.Letters AllFieldHistoryMasks.Letters
      (fun h : Active K tick => h.val.physicalOrder = sigma)
      (AllFieldHistoryRecovery.coordinates allocation m e w) =
    groupCoordinates allocation m sigma (projectTarget allocation m sigma e)
      (projectRaw allocation m sigma w) := rfl

theorem idealSide_iff_all_groups (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.idealSide allocation m ε side e w ↔
      ∀ sigma, groupIdealSide allocation m ε side sigma
        (projectTarget allocation m sigma e) (projectRaw allocation m sigma w) := by
  constructor
  · intro hw sigma
    exact ⟨fun h j => hw.1 h.val j, fun h u hu => hw.2 h.val u hu⟩
  · intro hw
    exact ⟨fun h j => (hw h.val.physicalOrder).1 ⟨h, rfl⟩ j,
      fun h u hu => (hw h.val.physicalOrder).2 ⟨h, rfl⟩ u hu⟩

theorem project_joinGroupTargets (allocation : Allocation) (m : ℕ)
    (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (sigma : Placement) :
    projectTarget allocation m sigma (joinGroupTargets (activeCounts allocation m) e) =
      e sigma := by
  funext h
  rcases h with ⟨h, hh⟩
  cases hh
  rfl

def groupedAssignment (allocation : Allocation) (m : ℕ) (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma)) :
    JointExtraction.Assignment (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
      (∀ sigma, E sigma) where
  x w := GroupAssignment.collect (fun sigma => (a sigma).x)
    (fun sigma => projectRaw allocation m sigma w)
  y w := GroupAssignment.collect (fun sigma => (a sigma).y)
    (fun sigma => projectRaw allocation m sigma w)
  z w := GroupAssignment.collect (fun sigma => (a sigma).z)
    (fun sigma => projectRaw allocation m sigma w)

theorem groupedAssignment_sound (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (hx : ∀ sigma w, (a sigma).x w = some (i sigma) →
      groupIdealSide allocation m ε 0 sigma (e sigma) w)
    (hy : ∀ sigma w, (a sigma).y w = some (i sigma) →
      groupIdealSide allocation m ε 1 sigma (e sigma) w)
    (hz : ∀ sigma w, (a sigma).z w = some (i sigma) →
      groupIdealSide allocation m ε 2 sigma (e sigma) w) :
    (∀ w, (groupedAssignment allocation m E a).x w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 0
        (joinGroupTargets (activeCounts allocation m) e) w) ∧
    (∀ w, (groupedAssignment allocation m E a).y w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 1
        (joinGroupTargets (activeCounts allocation m) e) w) ∧
    (∀ w, (groupedAssignment allocation m E a).z w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 2
        (joinGroupTargets (activeCounts allocation m) e) w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 0 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hx sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 1 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hy sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 2 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hz sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)

def localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : GroupTarget (K := K) (tick := tick) allocation m sigma)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Finset (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  GroupOrbitProjection.rawOrbit (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7) e w

def localAssigned (allocation : Allocation) (m : ℕ) (sigma : Placement) {E : Type*}
    (a : JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) E)
    (i : E) (side : Fin 3) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  AllFieldHistoryRecovery.sideVariable side (a.x w = some i) (a.y w = some i) (a.z w = some i)

theorem grouped_assigned_iff (allocation : Allocation) (m : ℕ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.sideVariable side
      ((groupedAssignment allocation m E a).x w = some i)
      ((groupedAssignment allocation m E a).y w = some i)
      ((groupedAssignment allocation m E a).z w = some i) ↔
      ∀ sigma, localAssigned allocation m sigma (a sigma) (i sigma) side
        (projectRaw allocation m sigma w) := by
  fin_cases side <;> exact GroupAssignment.collect_eq_some _ _ _

theorem filter_eq_rejected {V : Type*} (orbit : Finset V)
    (bad : V → Prop) (d : DecidablePred bad) :
    @Finset.filter V bad d orbit = rejectedFilter orbit bad := by
  ext v
  simp only [rejectedFilter, Finset.mem_filter]

theorem grouped_collision_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hbound : ∀ sigma,
      (((localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).filter
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).card ≤ 1 / m) :
    letI : MulAction (AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :=
        AllFieldHistoryRecovery.rawAction allocation m (joinGroupTargets (activeCounts allocation m) e)
    (((OrbitCounting.orbitSet (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => AllFieldHistoryRecovery.completeKeep allocation m ε side v ∧
        ¬AllFieldHistoryRecovery.sideVariable side
          ((groupedAssignment allocation m E a).x v = some i)
          ((groupedAssignment allocation m E a).y v = some i)
          ((groupedAssignment allocation m E a).z v = some i))).card : ℝ) /
      (OrbitCounting.orbitSet (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m := by
  let target := joinGroupTargets (activeCounts allocation m) e
  let : MulAction (AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) := AllFieldHistoryRecovery.rawAction allocation m target
  have hb (sigma : Placement) :
      ((rejectedFilter (GroupOrbitProjection.rawOrbit
        (GroupOrbitProjection.groupCounts (activeCounts allocation m)
          (fun h : Active K tick => h.val.physicalOrder = sigma))
        (fun h => Left activeHalfLength h.val) (fun h => Right activeHalfLength h.val)
        (GroupOrbitProjection.projectTarget (activeCounts allocation m)
          (fun h => h.val.physicalOrder = sigma) target)
        (projectRaw allocation m sigma w))
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (GroupOrbitProjection.rawOrbit
          (GroupOrbitProjection.groupCounts (activeCounts allocation m)
            (fun h : Active K tick => h.val.physicalOrder = sigma))
          (fun h => Left activeHalfLength h.val) (fun h => Right activeHalfLength h.val)
          (GroupOrbitProjection.projectTarget (activeCounts allocation m)
            (fun h => h.val.physicalOrder = sigma) target)
          (projectRaw allocation m sigma w)).card ≤ 1 / m := by
    change ((rejectedFilter
      (localOrbit allocation m sigma (projectTarget allocation m sigma target)
        (projectRaw allocation m sigma w))
      (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
        ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
      (localOrbit allocation m sigma (projectTarget allocation m sigma target)
        (projectRaw allocation m sigma w)).card ≤ 1 / m
    dsimp only [target]
    rw [project_joinGroupTargets]
    have hb0 := hbound sigma
    rw [filter_eq_rejected] at hb0
    exact hb0
  have hh := GroupOrbitProjection.raw_group_passing_rejection_fraction_le
    (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
    (fun h : Active K tick => h.val.physicalOrder) target w
    (AllFieldHistoryRecovery.completeKeep allocation m ε side)
    (fun sigma => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma)
    (fun sigma => localAssigned allocation m sigma (a sigma) (i sigma) side)
    (fun v hv sigma => completeKeep_project allocation m ε side v hv sigma)
    (fun _ => (1 : ℝ) / m) hb
  have hcard : Fintype.card Placement = 6 := by
    norm_num [Placement, Fintype.card_perm, Nat.factorial]
  have horbit :
      OrbitCounting.orbitSet
        (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w =
      GroupOrbitProjection.rawOrbit (activeCounts allocation m)
        (Left activeHalfLength) (Right activeHalfLength) target w := by
    exact RecoveryOrbitDecisions.orbitSet_eq_transportedOrbit
      (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      _ _ _ (AllFieldHistoryRecovery.coordinates allocation m target) w
  rw [filter_eq_rejected, horbit]
  simp only [target, grouped_assigned_iff, Finset.sum_const, Finset.card_univ,
    hcard, nsmul_eq_mul, Nat.cast_ofNat, mul_one_div] at hh ⊢
  exact hh

theorem repair_grouped (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (hx : ∀ sigma w, (a sigma).x w = some (i sigma) →
      groupIdealSide allocation m ε 0 sigma (e sigma) w)
    (hy : ∀ sigma w, (a sigma).y w = some (i sigma) →
      groupIdealSide allocation m ε 1 sigma (e sigma) w)
    (hz : ∀ sigma w, (a sigma).z w = some (i sigma) →
      groupIdealSide allocation m ε 2 sigma (e sigma) w)
    (hbound : ∀ side w,
      AllFieldHistoryRecovery.Used F allocation m ε
        (joinGroupTargets (activeCounts allocation m) e) side w → ∀ sigma,
      (((localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).filter
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).card ≤ 1 / m) :
    InverseLinearRecovery.RecoveredBy
      (AllFieldHistoryRecovery.ideal F allocation m ε (joinGroupTargets (activeCounts allocation m) e))
      (JointExtraction.branch
        (ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F allocation m)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 2))
        (groupedAssignment allocation m E a) i)
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  have hs := groupedAssignment_sound allocation m ε E a i e hx hy hz
  apply AllFieldHistoryRecovery.repair_selected_branch F allocation hε hm
    (groupedAssignment allocation m E a) i (joinGroupTargets (activeCounts allocation m) e)
    hs.1 hs.2.1 hs.2.2
  intro side w hw
  exact grouped_collision_le allocation m ε E a i e side w (hbound side w hw)

end MatrixMultiplication.AllFieldHistoryGroupedRecovery






namespace MatrixMultiplication.AllFieldHistorySource

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

theorem groupedAssignment_coherent (F : Type*) [Field F] (ε : ℝ)
    (E : Placement → Type)
    (a : ∀ sigma, JointExtraction.Assignment
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma)
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma)
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (ha : ∀ sigma, JointExtraction.Coherent
      (AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma) (a sigma)) :
    JointExtraction.Coherent (preparedSource (K := K) (tick := tick) allocation m F ε)
      (AllFieldHistoryGroupedRecovery.groupedAssignment allocation m E a) := by
  intro x y z i j k hT hx hy hz
  have hprod : CommonDimensions.familyProduct
      (fun sigma => AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma x)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma y)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma z) ≠ 0 := by
    rw [preparedSource_eq_delete] at hT
    exact fun hzero => hT ((AllFieldHistoryGroupMasks.preparedSource_factor
      F allocation m ε x y z).trans hzero)
  exact GroupAssignment.product_coherent _ a ha _ _ _ i j k hprod hx hy hz

end MatrixMultiplication.AllFieldHistorySource

end
end

end MatrixAllFields

end OAI
