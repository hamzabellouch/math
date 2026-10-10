import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayRepresentation

namespace OAI

namespace EditApproximation
namespace BinaryFraction

private theorem coarseMin_result (a b : BinaryFraction) :
    (minWithWork a b).1 = a ∨ (minWithWork a b).1 = b := by
  unfold minWithWork
  dsimp only
  split_ifs <;> simp only [true_or, or_true]

 theorem coarseGridScan_den (two previous : BinaryFraction) (source : List BinaryFraction)
    (hp : previous.representation.den = two.representation.den)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    ∀ a ∈ (coarseGridScanWithWork two previous source).1,
      a.representation.den = two.representation.den := by
  induction source generalizing previous with
  | nil => simpa only [coarseGridScanWithWork, List.mem_singleton] using
      (fun a (ha : a = previous) => ha ▸ hp)
  | cons head rest ih =>
    have hh := hs head List.mem_cons_self
    have ha := (coarseGridAddWithWork_den previous two).trans hp
    have hn : (minWithWork head (coarseGridAddWithWork previous two).1).1.representation.den =
        two.representation.den := by
      rcases coarseMin_result head (coarseGridAddWithWork previous two).1 with h | h
      · simpa only [h] using hh
      · simpa only [h] using ha
    intro a hmem
    change a ∈ previous :: _ at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hp
    · exact ih _ hn (fun a ha => hs a (List.mem_cons_of_mem _ ha)) a hmem

 theorem coarseGridLeft_den (two : BinaryFraction) (source : List BinaryFraction)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    ∀ a ∈ (coarseGridLeftWithWork two source).1,
      a.representation.den = two.representation.den := by
  cases source with
  | nil => simp only [coarseGridLeftWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons head rest =>
      exact coarseGridScan_den two head rest (hs head List.mem_cons_self)
        (fun a ha => hs a (List.mem_cons_of_mem _ ha))

 theorem coarseGridZipMinimum_den (left right : List BinaryFraction) (D : ℕ)
    (hl : ∀ a ∈ left, a.representation.den = D)
    (hr : ∀ a ∈ right, a.representation.den = D) :
    ∀ a ∈ (coarseGridZipMinimumWithWork left right).1, a.representation.den = D := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipMinimumWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipMinimumWithWork, List.not_mem_nil, false_implies, implies_true]
    | cons b right =>
      intro c hc
      change c ∈ (minWithWork a b).1 :: _ at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rcases coarseMin_result a b with h | h
        · simpa only [h] using hl a List.mem_cons_self
        · simpa only [h] using hr b List.mem_cons_self
      · exact ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
          (fun b hb => hr b (List.mem_cons_of_mem _ hb)) c hc

 theorem coarseGridPenalty_den (two : BinaryFraction) (source : List BinaryFraction)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    ∀ a ∈ (coarseGridPenaltyWithWork two source).1,
      a.representation.den = two.representation.den := by
  apply coarseGridZipMinimum_den
  · exact coarseGridLeft_den two source hs
  · intro a ha
    exact coarseGridLeft_den two source.reverse
      (fun b hb => hs b (List.mem_reverse.mp hb)) a (List.mem_reverse.mp ha)

 theorem coarseGridZipAdd_den (left right : List BinaryFraction) (D : ℕ)
    (hl : ∀ a ∈ left, a.representation.den = D) :
    ∀ a ∈ (coarseGridZipAddWithWork left right).1, a.representation.den = D := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipAddWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipAddWithWork, List.not_mem_nil, false_implies, implies_true]
    | cons b right =>
      intro c hc
      change c ∈ (coarseGridAddWithWork a b).1 :: _ at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (coarseGridAddWithWork_den a b).trans (hl a List.mem_cons_self)
      · exact ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha)) c hc

/-- The array relation ignores proof fields and keeps exact stored values. -/
def CoarseArrayRep {n : ℕ} (actual : CoarseBinaryArray) (spec : CoarseStoredArray n) : Prop :=
  coarseBinaryContents actual = coarseRationalContents spec

def CoarseArrayOnGrid (D : ℕ) (actual : CoarseBinaryArray) : Prop :=
  ∀ values, actual = some values → ∀ a ∈ values, a.representation.den = D

 theorem coarseBinaryAdd_grid (a b : CoarseBinaryArray) (D : ℕ)
    (ha : CoarseArrayOnGrid D a) (hb : CoarseArrayOnGrid D b) :
    CoarseArrayOnGrid D (coarseBinaryAddWithWork a b).1 := by
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      intro values hv
      have heq : (coarseGridZipAddWithWork a b).1 = values := Option.some.inj hv
      rw [← heq]
      exact coarseGridZipAdd_den a b D (ha a rfl)

 theorem coarseBinaryPenalty_grid (two : BinaryFraction) (a : CoarseBinaryArray)
    (ha : CoarseArrayOnGrid two.representation.den a) :
    CoarseArrayOnGrid two.representation.den (coarseBinaryPenaltyWithWork two a).1 := by
  cases a with
  | none => intro values hv; cases hv
  | some a =>
    intro values hv
    have heq : (coarseGridPenaltyWithWork two a).1 = values := Option.some.inj hv
    rw [← heq]
    exact coarseGridPenalty_den two a (ha a rfl)

 theorem coarseBinaryMap_grid (f : BinaryFraction → BinaryFraction × ℕ) (a : CoarseBinaryArray)
    (D : ℕ) (ha : CoarseArrayOnGrid D a)
    (hf : ∀ z, z.representation.den = D → (f z).1.representation.den = D) :
    CoarseArrayOnGrid D (coarseBinaryMapWithWork f a).1 := by
  cases a with
  | none => intro values hv; cases hv
  | some a =>
    intro values hv z hz
    have heq : (arithmeticMapWithWork f a).1 = values := Option.some.inj hv
    rw [← heq, arithmeticMapWithWork_value] at hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact hf x (ha a rfl x hx)

def coarseContentsAdd : Option (List ℚ) → Option (List ℚ) → Option (List ℚ)
  | none, b => b
  | a, none => a
  | some a, some b => some (List.zipWith (· + ·) a b)

 theorem coarseStoredAdd_contents {n : ℕ} (a b : CoarseStoredArray n) :
    coarseRationalContents (coarseStoredAdd a b).1 =
      coarseContentsAdd (coarseRationalContents a) (coarseRationalContents b) := by
  cases a <;> cases b <;> rfl

 theorem coarseBinaryAdd_contents (a b : CoarseBinaryArray) (D : ℕ)
    (ha : ∀ values, a = some values → ∀ x ∈ values, x.representation.den = D)
    (hb : ∀ values, b = some values → ∀ x ∈ values, x.representation.den = D) :
    coarseBinaryContents (coarseBinaryAddWithWork a b).1 =
      coarseContentsAdd (coarseBinaryContents a) (coarseBinaryContents b) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      exact congrArg some (coarseGridZipAddWithWork_value a b
        (fun x hx y hy => (ha a rfl x hx).trans (hb b rfl y hy).symm))

 theorem coarseBinaryAdd_rep {n : ℕ} (a b : CoarseBinaryArray) (x y : CoarseStoredArray n)
    (D : ℕ) (hx : CoarseArrayRep a x) (hy : CoarseArrayRep b y)
    (ha : ∀ values, a = some values → ∀ z ∈ values, z.representation.den = D)
    (hb : ∀ values, b = some values → ∀ z ∈ values, z.representation.den = D) :
    CoarseArrayRep (coarseBinaryAddWithWork a b).1 (coarseStoredAdd x y).1 := by
  change coarseBinaryContents _ = coarseRationalContents _
  rw [coarseBinaryAdd_contents a b D ha hb, coarseStoredAdd_contents, hx, hy]

 theorem coarseStoredPenalty_contents {n : ℕ} (a : CoarseStoredArray n) :
    coarseRationalContents (coarseStoredPenalty a).1 =
      (coarseRationalContents a).map coarsePenaltyTransform := by
  cases a with
  | none => rfl
  | some a =>
    exact congrArg some (coarseCostedPenaltyTransform_result a.1).1

 theorem coarseBinaryPenalty_rep {n : ℕ} (two : BinaryFraction) (a : CoarseBinaryArray)
    (x : CoarseStoredArray n) (htwo : two.value = 2) (hx : CoarseArrayRep a x)
    (ha : ∀ values, a = some values → ∀ z ∈ values, z.representation.den = two.representation.den) :
    CoarseArrayRep (coarseBinaryPenaltyWithWork two a).1 (coarseStoredPenalty x).1 := by
  change coarseBinaryContents _ = coarseRationalContents _
  rw [coarseStoredPenalty_contents, ← hx]
  cases a with
  | none => rfl
  | some a => exact coarseBinaryPenaltyWithWork_value two a htwo (ha a rfl)

 theorem coarseStoredMap_contents {n : ℕ} (f : ℚ → ℚ) (a : CoarseStoredArray n) :
    coarseRationalContents (coarseStoredMap f a).1 = (coarseRationalContents a).map (List.map f) := by
  cases a <;> rfl

 theorem coarseBinaryMap_rep {n : ℕ} (f : BinaryFraction → BinaryFraction × ℕ) (g : ℚ → ℚ)
    (hf : ∀ a, (f a).1.value = g a.value) (a : CoarseBinaryArray) (x : CoarseStoredArray n)
    (hx : CoarseArrayRep a x) :
    CoarseArrayRep (coarseBinaryMapWithWork f a).1 (coarseStoredMap g x).1 := by
  change coarseBinaryContents _ = coarseRationalContents _
  rw [coarseBinaryMapWithWork_value f g hf, coarseStoredMap_contents, hx]

end BinaryFraction
end EditApproximation

end OAI
