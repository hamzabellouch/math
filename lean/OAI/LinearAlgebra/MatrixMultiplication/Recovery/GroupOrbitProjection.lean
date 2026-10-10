import OAI.LinearAlgebra.MatrixMultiplication.Tensor.CompleteWordPair
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.FiniteAverage
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.OrbitCounting
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Canonicalization
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.EquivOrbitTransport
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskOrbitFilter
import Mathlib.Data.Fintype.Perm

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

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
  exact (Equiv.eq_symm_apply
    (pairEquiv (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
      (projectTarget counts p e))).mpr
    ((pairEquiv_projectRaw counts L R p e ((pairEquiv counts L R e).symm v)).trans
      (congrArg
        (projectPair (ClassPositions counts) (fun c => L c.1) (fun c => R c.1) p)
        ((pairEquiv counts L R e).apply_symm_apply v)))

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

end MatrixMultiplication.GroupOrbitProjection

end

end OAI
