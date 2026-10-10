import OAI.GroupTheory.ArtinCAT0.Braids

namespace OAI

namespace ArtinCAT0

section Presentations

variable {S H : Type*} [Group H]

lemma lift_alternating_constant (c : H) (s t : S) (n : ℕ) :
    FreeGroup.lift (fun _ : S => c) (alternating s t n) = c^n := by
  induction n generalizing s t with
  | zero => simp [alternating]
  | succ n ih => simp [alternating, ih, pow_succ']

/-- Exponent sum, valid for every Artin matrix (including infinity labels). -/
def artinExponent (M : S → S → Label) : ArtinGroup M →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := fun _ : S => Multiplicative.ofAdd (1 : ℤ)) (by
    rintro r ⟨s, t, n, _, rfl⟩
    simp only [map_mul, map_inv, lift_alternating_constant, mul_inv_cancel])

@[simp] lemma artinExponent_of (M : S → S → Label) (s : S) :
    artinExponent M (PresentedGroup.of s) = Multiplicative.ofAdd (1 : ℤ) :=
  PresentedGroup.toGroup.of _

lemma artin_generator_infinite_order (M : S → S → Label) (s : S) :
    ¬ IsOfFinOrder (PresentedGroup.of (rels := artinRelators M) s) := by
  intro hf
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hf
  have hh := congrArg (artinExponent M) he
  have hz : (n : ℤ) = 0 := by
    simpa using congrArg Multiplicative.toAdd hh
  exact (Nat.ne_of_gt hn) (Int.natCast_eq_zero.mp hz)

/-- Positive braid presentation on n generators, i.e. the group B_(n+1). -/
def braidRelators (n : ℕ) : Set (FreeGroup (Fin n)) :=
  {w | ∃ (i : ℕ) (hi : i+1 < n),
    w = (FreeGroup.of ⟨i, by omega⟩ * FreeGroup.of ⟨i+1, hi⟩ * FreeGroup.of ⟨i, by omega⟩) *
      (FreeGroup.of ⟨i+1, hi⟩ * FreeGroup.of ⟨i, by omega⟩ * FreeGroup.of ⟨i+1, hi⟩)⁻¹} ∪
  {w | ∃ (i j : Fin n), i.val+2 ≤ j.val ∧
    w = (FreeGroup.of i * FreeGroup.of j) * (FreeGroup.of j * FreeGroup.of i)⁻¹}

abbrev BraidGroup (n : ℕ) := PresentedGroup (braidRelators n)

def braidGen (n i : ℕ) : BraidGroup n :=
  if hi : i < n then PresentedGroup.of ⟨i, hi⟩ else 1

lemma braidGroup_relation (n i : ℕ) (hi : i+1 < n) :
    braidGen n i * braidGen n (i+1) * braidGen n i =
      braidGen n (i+1) * braidGen n i * braidGen n (i+1) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := braidRelators n)
    (Or.inl ⟨i, hi, rfl⟩)
  simpa [braidGen, show i < n by omega, hi, PresentedGroup.of, map_mul] using h

lemma braidGroup_commute (n i j : ℕ) (hij : i+2 ≤ j) (hj : j < n) :
    Commute (braidGen n i) (braidGen n j) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := braidRelators n)
    (Or.inr ⟨⟨i, by omega⟩, ⟨j, hj⟩, hij, rfl⟩)
  change _ * _ = _ * _
  simpa [braidGen, show i < n by omega, hj, PresentedGroup.of, map_mul] using h

lemma braidGroup_relations (n : ℕ) : BraidRelations n (braidGen n) :=
  ⟨fun i hi => braidGroup_relation n i (by omega), fun i j _ hj hij =>
    braidGroup_commute n i j hij hj⟩

/-- Universal property, with equations rather than escaped relator words. -/
def braidLift {n : ℕ} (s : Fin n → H)
    (hb : ∀ (i : ℕ) (hi : i+1 < n),
      s ⟨i, by omega⟩ * s ⟨i+1, hi⟩ * s ⟨i, by omega⟩ =
        s ⟨i+1, hi⟩ * s ⟨i, by omega⟩ * s ⟨i+1, hi⟩)
    (hc : ∀ i j : Fin n, i.val+2 ≤ j.val → Commute (s i) (s j)) : BraidGroup n →* H :=
  PresentedGroup.toGroup (f := s) (by
    rintro r (⟨i, hi, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] using hb i hi
    · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] using (hc i j hij).eq)

@[simp] lemma braidLift_of {n : ℕ} (s : Fin n → H) (hb hc) (i : Fin n) :
    braidLift s hb hc (PresentedGroup.of i) = s i := PresentedGroup.toGroup.of _

@[simp] lemma braidLift_gen {n : ℕ} (s : Fin n → H) (hb hc) (i : ℕ) (hi : i < n) :
    braidLift s hb hc (braidGen n i) = s ⟨i, hi⟩ := by simp [braidGen, hi]

/-- Token representation. Unlike naive strand deletion, it is defined on every
selected-position state, so respects arbitrary signed prefixes and suffixes. -/
def braidTokenRepresentation (n : ℕ) : BraidGroup n →* Equiv.Perm (TokenState (BraidGroup 2)) :=
  braidLift (fun i => tokenPerm (braidGen 2 0) (braidGen 2 1) i.val)
    (fun i _ => tokenPerm_braid _ _ (braidGroup_relation 2 0 (by omega)) i)
    (fun i j hij => tokenPerm_distant _ _ i.val j.val hij)

def initialSelected : SelectedPositions := ⟨{0, 1, 2}, by decide⟩

lemma tokenPerm_initial (i : Fin 2) (q : BraidGroup 2) :
    tokenPerm (braidGen 2 0) (braidGen 2 1) i.val (initialSelected, q) =
      (initialSelected, PresentedGroup.of i * q) := by
  fin_cases i <;> apply Prod.ext
  all_goals simp [tokenPerm, initialSelected, tokenRecord, swapPositions, selectedPrefix, braidGen,
    Equiv.swap_apply_def, Finset.insert_comm] <;> decide

lemma braidTokenRepresentation_initial (g q : BraidGroup 2) :
    braidTokenRepresentation 2 g (initialSelected, q) = (initialSelected, g*q) := by
  let K : Subgroup (BraidGroup 2) :=
    { carrier := {g | ∀ q, braidTokenRepresentation 2 g (initialSelected, q) =
        (initialSelected, g*q)}
      one_mem' := by intro q; simp
      mul_mem' := by
        intro g h hg hh q
        change ∀ t, braidTokenRepresentation 2 g (initialSelected, t) = _ at hg
        change ∀ t, braidTokenRepresentation 2 h (initialSelected, t) = _ at hh
        simp only [map_mul, Equiv.Perm.mul_apply, hh, hg, mul_assoc]
      inv_mem' := by
        intro g hg q
        apply (braidTokenRepresentation 2 g).injective
        change ∀ t, braidTokenRepresentation 2 g (initialSelected, t) = _ at hg
        simp only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply, hg, mul_inv_cancel_left] }
  exact PresentedGroup.generated_by (braidRelators 2) K
    (fun i q => by simpa [braidTokenRepresentation] using tokenPerm_initial i q) g q

lemma braidTokenRepresentation_two_injective : Function.Injective (braidTokenRepresentation 2) := by
  intro g h he
  have hh := congrArg (fun f : Equiv.Perm (TokenState (BraidGroup 2)) => f (initialSelected, 1)) he
  simpa [braidTokenRepresentation_initial] using congrArg Prod.snd hh

/-- Initial B3 inclusion in every B_(n+1), for n≥2. -/
def initialBraidInclusion (n : ℕ) (hn : 2 ≤ n) : BraidGroup 2 →* BraidGroup n :=
  braidLift (fun i => braidGen n i.val)
    (fun i hi => braidGroup_relation n i (by omega))
    (fun i j hij => by omega)

lemma initialBraidInclusion_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (initialBraidInclusion n hn) := by
  have he : (braidTokenRepresentation n).comp (initialBraidInclusion n hn) =
      braidTokenRepresentation 2 := by
    apply PresentedGroup.ext
    intro i
    simp [initialBraidInclusion, braidTokenRepresentation, braidGen, show i.val < n by omega]
  apply Function.Injective.of_comp (f := braidTokenRepresentation n)
  rw [← MonoidHom.coe_comp, he]
  exact braidTokenRepresentation_two_injective

end Presentations

section TrianglePresentation

def triangleRelators : Set (FreeGroup (Fin 3)) :=
  {w | ∃ i : Fin 3,
    w = (FreeGroup.of i * FreeGroup.of (i+1) * FreeGroup.of i) *
      (FreeGroup.of (i+1) * FreeGroup.of i * FreeGroup.of (i+1))⁻¹}

abbrev TriangleGroup := PresentedGroup triangleRelators

def triangleGen (i : Fin 3) : TriangleGroup := PresentedGroup.of i

lemma triangle_braid (i : Fin 3) :
    triangleGen i * triangleGen (i+1) * triangleGen i =
      triangleGen (i+1) * triangleGen i * triangleGen (i+1) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := triangleRelators) ⟨i, rfl⟩
  simpa [triangleGen, PresentedGroup.of, map_mul] using h

def triangleLift {H : Type*} [Group H] (s : Fin 3 → H)
    (hb : ∀ i : Fin 3, s i * s (i+1) * s i = s (i+1) * s i * s (i+1)) :
    TriangleGroup →* H :=
  PresentedGroup.toGroup (f := s) (by
    rintro r ⟨i, rfl⟩
    simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] using hb i)

@[simp] lemma triangleLift_gen {H : Type*} [Group H] (s : Fin 3 → H) (hb) (i : Fin 3) :
    triangleLift s hb (triangleGen i) = s i := PresentedGroup.toGroup.of _

def trianglePair (i : Fin 3) : BraidGroup 2 →* TriangleGroup :=
  braidLift (fun j => if j.val = 0 then triangleGen i else triangleGen (i+1))
    (fun j hj => by
      have : j = 0 := by omega
      subst j
      simpa using triangle_braid i)
    (fun j k h => by omega)

def trianglePairRetraction (i : Fin 3) : TriangleGroup →* BraidGroup 2 :=
  triangleLift (fun j => if j = i+1 then braidGen 2 1 else braidGen 2 0) (by
    have hb := braidGroup_relation 2 0 (by omega)
    intro j
    fin_cases i <;> fin_cases j <;> simp_all)

lemma trianglePair_leftInverse (i : Fin 3) :
    (trianglePairRetraction i).comp (trianglePair i) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro j
  fin_cases j <;> fin_cases i <;>
    simp [trianglePair, trianglePairRetraction, braidGen]

lemma trianglePair_injective (i : Fin 3) : Function.Injective (trianglePair i) := by
  apply Function.Injective.of_comp (f := trianglePairRetraction i)
  rw [← MonoidHom.coe_comp, trianglePair_leftInverse]
  exact Function.injective_id

def triangleExponent : TriangleGroup →* Multiplicative ℤ :=
  triangleLift (fun _ => Multiplicative.ofAdd (1 : ℤ)) (by intro i; rfl)

@[simp] lemma triangleExponent_gen (i : Fin 3) :
    triangleExponent (triangleGen i) = Multiplicative.ofAdd (1 : ℤ) := triangleLift_gen _ _ _

lemma triangle_generator_infinite_order (i : Fin 3) : ¬ IsOfFinOrder (triangleGen i) := by
  intro hf
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hf
  have hh := congrArg triangleExponent he
  have hz : (n : ℤ) = 0 := by simpa using congrArg Multiplicative.toAdd hh
  exact (Nat.ne_of_gt hn) (Int.natCast_eq_zero.mp hz)

def triangleX (b i : Fin 3) : TriangleGroup :=
  if i = 0 then triangleGen b else if i = 1 then triangleGen (b+1)
  else (triangleGen (b+1))⁻¹ * triangleGen b * triangleGen (b+1)

def triangleH (b : Fin 3) : TriangleGroup := triangleGen b * triangleGen (b+1)

lemma triangular_relation (b i : Fin 3) : triangleX b i * triangleX b (i+1) = triangleH b := by
  fin_cases i
  · simp [triangleX, triangleH]
  · simp [triangleX, triangleH, mul_assoc]
  · simp only [triangleX]
    unfold triangleH
    have hb := triangle_braid b
    calc
      (triangleGen (b+1))⁻¹ * triangleGen b * triangleGen (b+1) * triangleGen b =
          (triangleGen (b+1))⁻¹ * (triangleGen b * triangleGen (b+1) * triangleGen b) := by group
      _ = _ := by rw [hb]; group

@[simp] lemma triangleExponent_X (b i : Fin 3) :
    triangleExponent (triangleX b i) = Multiplicative.ofAdd (1 : ℤ) := by
  fin_cases i <;> simp [triangleX]

@[simp] lemma triangleExponent_H (b : Fin 3) :
    triangleExponent (triangleH b) = Multiplicative.ofAdd (2 : ℤ) := by
  simp only [triangleH, map_mul, triangleExponent_gen]
  rfl

end TrianglePresentation

/-- Signed edge directions in the nine-letter triangular presentation.
Indices 0..8 are positive; indices 9..17 are negative. -/
abbrev LinkDirection := Fin 18

/-- The three theta graphs, glued at a±, b±, c±, with cell identities retained. -/
def linkNeighbors (d : LinkDirection) : Finset LinkDirection :=
  match d.val with
  | 0 => {6,12,8,11}
  | 1 => {6,9,7,13}
  | 2 => {7,10,8,14}
  | 3 => {6,10}
  | 4 => {7,11}
  | 5 => {8,9}
  | 6 => {0,1,3}
  | 7 => {1,2,4}
  | 8 => {2,0,5}
  | 9 => {1,15,5,17}
  | 10 => {3,15,2,16}
  | 11 => {4,16,0,17}
  | 12 => {0,15}
  | 13 => {1,16}
  | 14 => {2,17}
  | 15 => {10,12,9}
  | 16 => {11,13,10}
  | _ => {9,14,11}

lemma linkNeighbors_symm : ∀ p q : LinkDirection, p ∈ linkNeighbors q ↔ q ∈ linkNeighbors p := by
  decide

lemma linkNeighbors_irrefl : ∀ p : LinkDirection, p ∉ linkNeighbors p := by decide

/-- Endpoints of nonbacktracking walks with a prescribed first oriented edge. -/
def linkEnds : ℕ → LinkDirection → LinkDirection → Finset LinkDirection
  | 0, _, q => {q}
  | n+1, p, q => ((linkNeighbors q).erase p).biUnion (fun r => linkEnds n q r)

lemma link_girth0 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 0 p q := by decide
lemma link_girth1 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 1 p q := by decide
lemma link_girth2 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 2 p q := by decide
lemma link_girth3 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 3 p q := by decide
lemma link_girth4 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 4 p q := by decide

lemma link_girth (n : ℕ) (hn : n < 5) (p q : LinkDirection) (h : q ∈ linkNeighbors p) :
    p ∉ linkEnds n p q := by
  interval_cases n
  · exact link_girth0 p q h
  · exact link_girth1 p q h
  · exact link_girth2 p q h
  · exact link_girth3 p q h
  · exact link_girth4 p q h

lemma mem_linkEnds_of_path (n : ℕ) (v : ℕ → LinkDirection)
    (hadj : ∀ i < n+1, v (i+1) ∈ linkNeighbors (v i))
    (hnob : ∀ i < n, v (i+2) ≠ v i) :
    v (n+1) ∈ linkEnds n (v 0) (v 1) := by
  induction n generalizing v with
  | zero => simp [linkEnds]
  | succ n ih =>
    simp only [linkEnds, Finset.mem_biUnion, Finset.mem_erase]
    refine ⟨v 2, ⟨hnob 0 (by omega), hadj 1 (by omega)⟩, ?_⟩
    simpa [Nat.add_assoc] using ih (fun i => v (i+1))
      (fun i hi => hadj (i+1) (by omega)) (fun i hi => hnob (i+1) (by omega))

/-- Every nonempty closed nonbacktracking walk in the exact link has at least six edges. -/
lemma link_closed_walk_length (n : ℕ) (hn : 0 < n) (v : ℕ → LinkDirection)
    (hadj : ∀ i < n, v (i+1) ∈ linkNeighbors (v i))
    (hnob : ∀ i, i+2 ≤ n → v (i+2) ≠ v i) (hclosed : v n = v 0) : 6 ≤ n := by
  by_contra h
  have he := mem_linkEnds_of_path (n-1) v (by simpa [Nat.sub_add_cancel hn] using hadj)
    (fun i hi => hnob i (by omega))
  rw [Nat.sub_add_cancel hn, hclosed] at he
  exact link_girth (n-1) (by omega) (v 0) (v 1) (hadj 0 hn) he

end ArtinCAT0

end OAI
