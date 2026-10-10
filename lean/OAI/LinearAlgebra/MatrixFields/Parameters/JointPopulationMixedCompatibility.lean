import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointCanonicalMixed
import OAI.LinearAlgebra.MatrixFields.Construction.JointCompatibilityIncidence
import OAI.LinearAlgebra.MatrixFields.Tensors.CWStrandCompatibility

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationCompatibility

open MatrixMultiplication.Foundation JointPopulation JointTypeCounts InheritedMasks
open JointCompatibilityIncidence
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

abbrev ClassKey := H × Fin 17

abbrev ClassPos (b : Position counts → Fin 17) (c : ClassKey (H := H)) :=
  {i : Positions counts c.1 // b ⟨c.1, i⟩ = c.2}

def classCounts (s : Fin 3) (c : ClassKey (H := H)) (u : Shape) : ℕ :=
  if shapeSide s u = c.2 then counts c.1 u else 0

abbrev FixedSideTargets (s : Fin 3) (b : Position counts → Fin 17) :=
  {e : Target counts // ∀ h i, shapeSide s ((e h).val i) = b ⟨h, i⟩}

def candidateEquiv (s : Fin 3) (b : Position counts → Fin 17) :
    FixedSideTargets counts s b ≃
      FixedClassWords (ClassPos counts b) (fun _ => Shape) (classCounts counts s) := by
  let split : FixedSideTargets counts s b ≃
      (∀ h, FixedCoarseWords (counts h) (shapeSide s) (fun i => b ⟨h, i⟩)) :=
    { toFun := fun e h => ⟨(e.val h).val, (e.val h).property, e.property h⟩
      invFun := fun v =>
        ⟨fun h => ⟨(v h).val, (v h).property.1⟩, fun h => (v h).property.2⟩
      left_inv := by
        intro e
        apply Subtype.ext
        funext h
        apply Subtype.ext
        rfl
      right_inv := by
        intro v
        funext h
        apply Subtype.ext
        rfl }
  let perHistory (h : H) :=
    (fixedCoarseWordsEquiv (counts h) (shapeSide s) (fun i => b ⟨h, i⟩)).trans
      (conditionalWordsEquiv (fun i : Positions counts h => b ⟨h, i⟩)
        (fun a u => if shapeSide s u = a then counts h u else 0))
  refine split.trans ((Equiv.piCongrRight perHistory).trans ?_)
  exact
    { toFun := fun v c => v c.1 c.2
      invFun := fun v h a => v (h, a)
      left_inv := by intro v; rfl
      right_inv := by
        intro v
        funext c
        rcases c with ⟨h, a⟩
        rfl }

omit [Fintype H] [DecidableEq H] in
@[simp] theorem candidateEquiv_apply (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) (c : ClassKey (H := H)) (i : ClassPos counts b c) :
    ((candidateEquiv counts s b e) c).val i = (e.val c.1).val i.val := rfl

omit [Fintype H] [DecidableEq H] in
theorem classCounts_size (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) (c : ClassKey (H := H)) :
    Fintype.card (ClassPos counts b c) = ∑ u, classCounts counts s c u := by
  calc
    Fintype.card (ClassPos counts b c) =
        ∑ u, wordPopulation ((candidateEquiv counts s b e) c).val u :=
      (wordPopulation_sum _).symm
    _ = ∑ u, classCounts counts s c u :=
      Finset.sum_congr rfl fun u _ => ((candidateEquiv counts s b e) c).property u

theorem fixedSideTargets_card (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) :
    Fintype.card (FixedSideTargets counts s b) =
      ∏ c : ClassKey (H := H), Nat.multinomial Finset.univ (classCounts counts s c) := by
  rw [Fintype.card_congr (candidateEquiv counts s b)]
  exact fixedClassWords_card _ _ _ (classCounts_size counts s b e)

def shapeStatisticCount {A : Type*} [Fintype A] [DecidableEq A]
    (e : Target counts) (h : H) (u : Shape) (f : Positions counts h → A) (a : A) : ℕ :=
  wordPopulation (fun i : Class counts e h u => f i.val) a

theorem scaled_count_window {x n p χ : ℝ} (hn : 0 < n)
    (hw : |x / n - p| ≤ χ) : |x - n * p| ≤ n * χ := by
  calc
    |x - n * p| = |(x / n - p) * n| := by
      rw [sub_mul, div_mul_cancel₀ _ hn.ne', mul_comm p n]
    _ = |x / n - p| * n := by rw [abs_mul, abs_of_pos hn]
    _ ≤ χ * n := mul_le_mul_of_nonneg_right hw hn.le
    _ = n * χ := mul_comm _ _

omit [Fintype H] [DecidableEq H] in
theorem shape_count_window_of_typeWindow {A : Type*} [Fintype A] [DecidableEq A]
    (e : Target counts) (h : H) (u : Shape) (f : Positions counts h → A)
    (law : A → ℝ) (χ : ℝ)
    (hw : 0 < counts h u → typeWindow law χ (fun i : Class counts e h u => f i.val)) :
    ∀ a, |(shapeStatisticCount counts e h u f a : ℝ) -
      (counts h u : ℝ) * law a| ≤ (counts h u : ℝ) * χ := by
  intro a
  by_cases hn : 0 < counts h u
  · apply scaled_count_window (Nat.cast_pos.mpr hn)
    simpa only [empiricalLaw, class_card, shapeStatisticCount] using hw hn a
  · have hn0 : counts h u = 0 := Nat.eq_zero_of_not_pos hn
    have hc : shapeStatisticCount counts e h u f a = 0 := by
      apply Nat.eq_zero_of_le_zero
      let forget : {i : Class counts e h u // f i.val = a} → Class counts e h u :=
        Subtype.val
      have hinj : Function.Injective forget := Subtype.val_injective
      have hbound := Fintype.card_le_of_injective forget hinj
      calc
        shapeStatisticCount counts e h u f a ≤ Fintype.card (Class counts e h u) :=
          hbound
        _ = 0 := (class_card counts e h u).trans hn0
    simp only [hc, hn0, Nat.cast_zero, zero_mul, sub_zero, abs_zero, le_refl]

theorem jointCount_le_population {P U Z A : Type*}
    [Fintype P] [Fintype U] [DecidableEq U] [DecidableEq A]
    (w : P → U) (z : P → Z) (part : Z → A) (u : U) (a : A) :
    jointCount w z part u a ≤ wordPopulation w u := by
  exact Fintype.card_le_of_injective
    (fun i : {i : P // w i = u ∧ part (z i) = a} =>
      (⟨i.val, i.property.1⟩ : {i : P // w i = u}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun j : {i : P // w i = u} => j.val) h))

omit [Fintype H] [DecidableEq H] in
theorem class_jointCount_eq {A : Type*} [Fintype A] [DecidableEq A]
    (s : Fin 3) (b : Position counts → Fin 17) (e : FixedSideTargets counts s b)
    (c : ClassKey (H := H)) (u : Shape) (hu : shapeSide s u = c.2)
    (f : Positions counts c.1 → A) (a : A) :
    jointCount ((candidateEquiv counts s b e) c).val
      (fun i => f i.val) id u a = shapeStatisticCount counts (A := A) e.val c.1 u f a := by
  let eFiber : {i : ClassPos counts b c //
      ((candidateEquiv counts s b e) c).val i = u ∧ f i.val = a} ≃
      {i : Class counts e.val c.1 u // f i.val = a} :=
    { toFun := fun i => ⟨⟨i.val.val, by
        simpa only [candidateEquiv_apply] using i.property.1⟩, i.property.2⟩
      invFun := fun i =>
        ⟨⟨i.val.val, by
          calc
            b ⟨c.1, i.val.val⟩ = shapeSide s ((e.val c.1).val i.val.val) :=
              (e.property c.1 i.val.val).symm
            _ = shapeSide s u := congrArg (shapeSide s) i.val.property
            _ = c.2 := hu⟩,
          by simpa only [candidateEquiv_apply] using i.val.property, i.property⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  unfold jointCount shapeStatisticCount wordPopulation
  exact Fintype.card_congr eFiber

omit [Fintype H] [DecidableEq H] in
theorem class_jointCount_zero {A : Type*} [DecidableEq A]
    (s : Fin 3) (b : Position counts → Fin 17) (e : FixedSideTargets counts s b)
    (c : ClassKey (H := H)) (u : Shape) (hu : shapeSide s u ≠ c.2)
    (f : ClassPos counts b c → A) (a : A) :
    jointCount ((candidateEquiv counts s b e) c).val f id u a = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    jointCount ((candidateEquiv counts s b e) c).val f id u a ≤
        wordPopulation ((candidateEquiv counts s b e) c).val u :=
      jointCount_le_population _ _ _ _ _
    _ = classCounts counts s c u := ((candidateEquiv counts s b e) c).property u
    _ = 0 := ite_eq_right hu

omit [Fintype H] [DecidableEq H] in
theorem side_compatibility_iff_class_counts
    (A : ClassKey (H := H) → Type*)
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (s : Fin 3) (b : Position counts → Fin 17) (e : FixedSideTargets counts s b)
    (f : ∀ h k, Positions counts h → A (h, k))
    (designated : ClassKey (H := H) → Shape → Prop)
    (law : ∀ c, Shape → A c → ℝ) (χ : ℝ) :
    (∀ h u, designated (h, shapeSide s u) u → ∀ a : A (h, shapeSide s u),
      |(shapeStatisticCount counts (A := A (h, shapeSide s u))
          e.val h u (f h (shapeSide s u)) a : ℝ) -
        (counts h u : ℝ) * law (h, shapeSide s u) u a| ≤ (counts h u : ℝ) * χ) ↔
    (∀ c u, designated c u → ∀ a : A c,
      |(jointCount ((candidateEquiv counts s b e) c).val
          (fun i => f c.1 c.2 i.val) id u a : ℝ) -
        (classCounts counts s c u : ℝ) * law c u a| ≤
          (classCounts counts s c u : ℝ) * χ) := by
  constructor
  · intro h c u hd a
    by_cases hu : shapeSide s u = c.2
    · rw [class_jointCount_eq counts s b e c u hu]
      rcases c with ⟨h₀, k⟩
      dsimp at hu
      subst k
      simpa only [classCounts, ite_eq_left rfl, ite_true] using h h₀ u hd a
    · rw [class_jointCount_zero counts s b e c u hu]
      simp only [classCounts, ite_eq_right hu, Nat.cast_zero, zero_mul, sub_zero, abs_zero, le_refl]
  · intro h h₀ u hd a
    have hh := h (h₀, shapeSide s u) u hd a
    rw [class_jointCount_eq counts s b e (h₀, shapeSide s u) u rfl] at hh
    simpa only [classCounts, ite_eq_left rfl, ite_true] using hh

section Statistics

variable (L R : H → Type*)
  (SL SR : ClassKey (H := H) → Type*)
  [∀ c, Fintype (SL c)] [∀ c, DecidableEq (SL c)]
  [∀ c, Fintype (SR c)] [∀ c, DecidableEq (SR c)]
  (leftStatistic : ∀ c, L c.1 → SL c)
  (rightStatistic : ∀ c, R c.1 → SR c)

def statisticWord (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) (c : ClassKey (H := H)) :
    ClassPos counts b c → SL c × SR c :=
  fun i => (leftStatistic c (w c.1 i.val).1, rightStatistic c (w c.1 i.val).2)

def statisticCounts (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) (c : ClassKey (H := H)) :
    SL c × SR c → ℕ :=
  wordPopulation (statisticWord counts L R SL SR leftStatistic rightStatistic b w c)

def statisticElement (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) :
    FixedClassWords (ClassPos counts b) (fun c => SL c × SR c)
      (statisticCounts counts L R SL SR leftStatistic rightStatistic b w) :=
  fun c => ⟨statisticWord counts L R SL SR leftStatistic rightStatistic b w c, fun _ => rfl⟩

variable (designatedLeft designatedRight : ClassKey (H := H) → Shape → Prop)
  (leftLaw : ∀ c, Shape → SL c → ℝ) (rightLaw : ∀ c, Shape → SR c → ℝ) (χ : ℝ)

def Compatible (s : Fin 3) (e : Target counts)
    (w : JointCanonicalization.RawPairs counts L R) : Prop :=
  (∀ h u, designatedLeft (h, shapeSide s u) u → ∀ a,
    |(shapeStatisticCount counts e h u
        (fun i => leftStatistic (h, shapeSide s u) (w h i).1) a : ℝ) -
      (counts h u : ℝ) * leftLaw (h, shapeSide s u) u a| ≤ (counts h u : ℝ) * χ) ∧
  (∀ h u, designatedRight (h, shapeSide s u) u → ∀ a,
    |(shapeStatisticCount counts e h u
        (fun i => rightStatistic (h, shapeSide s u) (w h i).2) a : ℝ) -
      (counts h u : ℝ) * rightLaw (h, shapeSide s u) u a| ≤ (counts h u : ℝ) * χ)

omit [Fintype H] [DecidableEq H] in
theorem compatible_of_designated_windows (s : Fin 3) (e : Target counts)
    (w : JointCanonicalization.RawPairs counts L R)
    (hl : ∀ h u, 0 < counts h u → designatedLeft (h, shapeSide s u) u →
      typeWindow (leftLaw (h, shapeSide s u) u) χ
        (fun i : Class counts e h u => leftStatistic (h, shapeSide s u) (w h i.val).1))
    (hr : ∀ h u, 0 < counts h u → designatedRight (h, shapeSide s u) u →
      typeWindow (rightLaw (h, shapeSide s u) u) χ
        (fun i : Class counts e h u => rightStatistic (h, shapeSide s u) (w h i.val).2)) :
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e w := by
  constructor
  · intro h u hd
    exact shape_count_window_of_typeWindow counts e h u _ _ χ (fun hn => hl h u hn hd)
  · intro h u hd
    exact shape_count_window_of_typeWindow counts e h u _ _ χ (fun hn => hr h u hn hd)

omit [Fintype H] [DecidableEq H] in
theorem compatible_iff_kernel (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) (w : JointCanonicalization.RawPairs counts L R) :
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e.val w ↔
    DesignatedCompatibility (ClassPos counts b) (fun _ => Shape) (fun c => SL c × SR c)
      SL SR (classCounts counts s)
      (statisticCounts counts L R SL SR leftStatistic rightStatistic b w)
      (fun _ p => p.1) (fun _ p => p.2) designatedLeft designatedRight leftLaw rightLaw χ
      (candidateEquiv counts s b e)
      (statisticElement counts L R SL SR leftStatistic rightStatistic b w) := by
  exact and_congr
    (side_compatibility_iff_class_counts counts SL s b e
      (fun h k i => leftStatistic (h, k) (w h i).1) designatedLeft leftLaw χ)
    (side_compatibility_iff_class_counts counts SR s b e
      (fun h k i => rightStatistic (h, k) (w h i).2) designatedRight rightLaw χ)

def compatibleTargetCount (s : Fin 3) (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) : ℕ :=
  Fintype.card {e : FixedSideTargets counts s b //
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e.val w}

theorem compatibleTargetCount_eq_kernel (s : Fin 3) (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) :
    compatibleTargetCount counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s b w =
    compatibleCandidateCount (ClassPos counts b) (fun _ => Shape) (fun c => SL c × SR c)
      SL SR (classCounts counts s)
      (statisticCounts counts L R SL SR leftStatistic rightStatistic b w)
      (fun _ p => p.1) (fun _ p => p.2) designatedLeft designatedRight leftLaw rightLaw χ
      (statisticElement counts L R SL SR leftStatistic rightStatistic b w) := by
  exact Fintype.card_congr ((candidateEquiv counts s b).subtypeEquiv
    (fun e => compatible_iff_kernel counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s b e w))

theorem compatibleTarget_incidence (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) (w : JointCanonicalization.RawPairs counts L R) :
    Fintype.card (FixedSideTargets counts s b) *
      compatibleStatisticCount (ClassPos counts b) (fun _ => Shape) (fun c => SL c × SR c)
        SL SR (classCounts counts s)
        (statisticCounts counts L R SL SR leftStatistic rightStatistic b w)
        (fun _ p => p.1) (fun _ p => p.2) designatedLeft designatedRight leftLaw rightLaw χ
        (candidateEquiv counts s b e) =
    Fintype.card (FixedClassWords (ClassPos counts b) (fun c => SL c × SR c)
      (statisticCounts counts L R SL SR leftStatistic rightStatistic b w)) *
      compatibleTargetCount counts L R SL SR leftStatistic rightStatistic
        designatedLeft designatedRight leftLaw rightLaw χ s b w := by
  rw [compatibleTargetCount_eq_kernel,
    Fintype.card_congr (candidateEquiv counts s b)]
  exact designated_incidence_count _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (candidateEquiv counts s b e)
    (statisticElement counts L R SL SR leftStatistic rightStatistic b w)

def compatibleByTriple (s : Fin 3)
    (t : JointCoarseHashing.Triple (Position counts))
    (w : JointCanonicalization.RawPairs counts L R) : Prop :=
  ∃ e : Target counts, triple counts e = t ∧
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e w

omit [Fintype H] [DecidableEq H] in
theorem compatibleByTriple_target (s : Fin 3) (e : Target counts)
    (w : JointCanonicalization.RawPairs counts L R) :
    compatibleByTriple counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s (triple counts e) w ↔
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e w := by
  constructor
  · rintro ⟨f, hf, hw⟩
    have he : f = e := triple_injective counts hf
    subst f
    exact hw
  · intro hw
    exact ⟨e, rfl, hw⟩

def compatibleWithCoarse
    (ownCoarse : JointCanonicalization.RawPairs counts L R → Position counts → Fin 17)
    (s : Fin 3) (t : JointCoarseHashing.Triple (Position counts))
    (w : JointCanonicalization.RawPairs counts L R) : Prop :=
  (∀ h i, sideWord counts s t h i = ownCoarse w ⟨h, i⟩) ∧
    compatibleByTriple counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s t w

omit [Fintype H] [DecidableEq H] in
theorem compatibleWithCoarse_target
    (ownCoarse : JointCanonicalization.RawPairs counts L R → Position counts → Fin 17)
    (s : Fin 3) (e : Target counts) (w : JointCanonicalization.RawPairs counts L R) :
    compatibleWithCoarse counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ ownCoarse s (triple counts e) w ↔
    (∀ h i, shapeSide s ((e h).val i) = ownCoarse w ⟨h, i⟩) ∧
      Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
        leftLaw rightLaw χ s e w := by
  exact and_congr Iff.rfl (compatibleByTriple_target counts L R SL SR leftStatistic
    rightStatistic designatedLeft designatedRight leftLaw rightLaw χ s e w)

omit [Fintype H] [DecidableEq H] in
theorem compatibleWithCoarse_shares_side
    (ownCoarse : JointCanonicalization.RawPairs counts L R → Position counts → Fin 17)
    (s : Fin 3) (t t' : JointCoarseHashing.Triple (Position counts))
    (w : JointCanonicalization.RawPairs counts L R)
    (ht : compatibleWithCoarse counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ ownCoarse s t w)
    (ht' : compatibleWithCoarse counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ ownCoarse s t' w) :
    ∀ h, sideWord counts s t h = sideWord counts s t' h := by
  intro h
  funext i
  exact (ht.1 h i).trans (ht'.1 h i).symm

theorem compatibleWithCoarse_target_count
    (ownCoarse : JointCanonicalization.RawPairs counts L R → Position counts → Fin 17)
    (s : Fin 3) (w : JointCanonicalization.RawPairs counts L R) :
    Fintype.card {e : Target counts //
      compatibleWithCoarse counts L R SL SR leftStatistic rightStatistic
        designatedLeft designatedRight leftLaw rightLaw χ ownCoarse s (triple counts e) w} =
    compatibleTargetCount counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s (ownCoarse w) w := by
  apply Fintype.card_congr
  exact (Equiv.subtypeEquivRight (fun e => compatibleWithCoarse_target counts L R SL SR
    leftStatistic rightStatistic designatedLeft designatedRight leftLaw rightLaw χ
      ownCoarse s e w)).trans (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun e : Target counts => ∀ h i, shapeSide s ((e h).val i) = ownCoarse w ⟨h, i⟩)
        (fun e => Compatible counts L R SL SR leftStatistic rightStatistic
          designatedLeft designatedRight leftLaw rightLaw χ s e w)).symm

end Statistics

def designatedYLeft (_ : ClassKey (H := H)) (u : Shape) : Prop :=
  (shapeSide 2 u).val = 0

def designatedYRight (parentShape : H → Fin 3 → ℕ)
    (c : ClassKey (H := H)) (u : Shape) : Prop :=
  parentShape c.1 2 - (shapeSide 2 u).val = 0

def designatedZLeft (_ : ClassKey (H := H)) (u : Shape) : Prop :=
  (shapeSide 0 u).val * (shapeSide 1 u).val = 0

def designatedZRight (parentShape : H → Fin 3 → ℕ)
    (c : ClassKey (H := H)) (u : Shape) : Prop :=
  (parentShape c.1 0 - (shapeSide 0 u).val) *
    (parentShape c.1 1 - (shapeSide 1 u).val) = 0

end MatrixMultiplication.JointPopulationCompatibility






namespace MatrixMultiplication.JointPopulationMixedNonzero

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open JointCanonicalMixed CWStrands InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [Field F]

omit [DecidableEq H] in
theorem class_half_products_nonzero
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool)
    (hleft : ∀ h, leftLength h ≤ 8)
    (hsupp : ∀ h u, 0 < counts h u → sharing h = true →
      ∀ s, shapeNat u s ≤ parentShape h s)
    (e : Target counts)
    (x y z : RawPairs counts (Left leftLength) (Right rightLength))
    (hsource : sourceTensor counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing) x y z ≠ 0)
    (hx : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 0 e x)
    (hy : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 1 e y)
    (hz : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 2 e z)
    (h : H) (u : Shape) (hn : 0 < counts h u) (hh : sharing h = true) :
    (∏ i : Class counts e h u,
      shapeTensor (F := F) (Fin (leftLength h)) (shapeNat u)
        (x h i.val).1 (y h i.val).1 (z h i.val).1) ≠ 0 ∧
    (∏ i : Class counts e h u,
      shapeTensor (F := F) (Fin (rightLength h)) (parentShape h - shapeNat u)
        (x h i.val).2 (y h i.val).2 (z h i.val).2) ≠ 0 := by
  change (∏ h' : H, ∏ i : Positions counts h',
    inputTensor (F := F) leftLength rightLength parentShape sharing h'
      (x h' i) (y h' i) (z h' i)) ≠ 0 at hsource
  have hparent (i : Positions counts h) :
      inputTensor (F := F) leftLength rightLength parentShape sharing h
        (x h i) (y h i) (z h i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp hsource h (Finset.mem_univ h)) i (Finset.mem_univ i)
  have hhalves (i : Class counts e h u) :
      shapeTensor (F := F) (Fin (leftLength h)) (shapeNat u)
          (x h i.val).1 (y h i.val).1 (z h i.val).1 *
        shapeTensor (F := F) (Fin (rightLength h)) (parentShape h - shapeNat u)
          (x h i.val).2 (y h i.val).2 (z h i.val).2 ≠ 0 := by
    have hx' : coarse leftLength rightLength hleft 0 h (x h i.val) = u.1 := by
      simpa [shapeSide, i.property] using hx h i.val
    have hy' : coarse leftLength rightLength hleft 1 h (y h i.val) = u.2.1 := by
      simpa [shapeSide, i.property] using hy h i.val
    have hz' : coarse leftLength rightLength hleft 2 h (z h i.val) = u.2.2 := by
      simpa [shapeSide, i.property] using hz h i.val
    have hblock : block (Left leftLength) (Right rightLength)
        (inputTensor (F := F) leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) (h, u)
        (x h i.val) (y h i.val) (z h i.val) ≠ 0 := by
      simpa [block, hx', hy', hz'] using hparent i.val
    rw [block_eq_children leftLength rightLength parentShape sharing hleft h u
      (hsupp h u hn)] at hblock
    simpa only [Tensor.product, leftTensor, childRight, hh, ↓reduceIte, rightTensor]
      using hblock
  constructor
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (mul_ne_zero_iff.mp (hhalves i)).1
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (mul_ne_zero_iff.mp (hhalves i)).2

end MatrixMultiplication.JointPopulationMixedNonzero






namespace MatrixMultiplication.JointPopulationMixedCompatibility

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open JointPopulationCompatibility JointPopulationMixedNonzero CWStrands InheritedMasks
open CWStrandCompatibility
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def sharingDesignated {H : Type*} (sharing : H → Bool)
    (d : JointPopulationCompatibility.ClassKey (H := H) → Shape → Prop)
    (c : JointPopulationCompatibility.ClassKey (H := H)) (u : Shape) : Prop :=
  sharing c.1 = true ∧ d c u

variable {H F : Type*} [Fintype H] [DecidableEq H] [Field F]
  (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
  (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool) (hleft : ∀ h, leftLength h ≤ 8)
  (hsupport : ∀ h u, 0 < counts h u → sharing h = true → ∀ s, shapeNat u s ≤ parentShape h s)
  (e : Target counts)
  (x y z : RawPairs counts (Left leftLength) (Right rightLength))
  (hsource : sourceTensor counts (Left leftLength) (Right rightLength)
    (JointCanonicalMixed.inputTensor (F := F) leftLength rightLength parentShape sharing) x y z ≠ 0)
  (hx : coarseMask counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 0 e x)
  (hy : coarseMask counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 1 e y)
  (hz : coarseMask counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 2 e z)

variable (SL SR : H → Type*)
  [∀ h, Fintype (SL h)] [∀ h, DecidableEq (SL h)]
  [∀ h, Fintype (SR h)] [∀ h, DecidableEq (SR h)]
  (leftStatistic : ∀ h, Left leftLength h → SL h)
  (rightStatistic : ∀ h, Right rightLength h → SR h)
  (κLeft : ∀ h, SL h ≃ SL h) (κRight : ∀ h, SR h ≃ SR h)
  (hstatLeft : ∀ h w, leftStatistic h (CWCompatibilityTransfer.wordComplement w) =
    κLeft h (leftStatistic h w))
  (hstatRight : ∀ h w, rightStatistic h (CWCompatibilityTransfer.wordComplement w) =
    κRight h (rightStatistic h w))
  (xLeftLaw yLeftLaw : ∀ c : JointCanonicalization.ClassKey (H := H), SL c.1 → ℝ)
  (xRightLaw yRightLaw : ∀ c : JointCanonicalization.ClassKey (H := H), SR c.1 → ℝ)
  (χ : ℝ)

include hsource hx hy hz hsupport hstatLeft hstatRight

omit [DecidableEq H] in
theorem source_implies_compatibleY
    (leftLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SL c.1 → ℝ)
    (rightLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SR c.1 → ℝ)
    (hlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedYLeft (h, shapeSide 1 u) u →
      leftLaw (h, shapeSide 1 u) u = xLeftLaw (h, u) ∘ (κLeft h).symm)
    (hrlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedYRight parentShape (h, shapeSide 1 u) u →
      rightLaw (h, shapeSide 1 u) u = xRightLaw (h, u) ∘ (κRight h).symm)
    (huseX : ∀ h u, 0 < counts h u → sharing h = true →
      typeWindow (xLeftLaw (h, u)) χ
        (fun i : Class counts e h u => leftStatistic h (x h i.val).1) ∧
      typeWindow (xRightLaw (h, u)) χ
        (fun i : Class counts e h u => rightStatistic h (x h i.val).2)) :
    Compatible counts (Left leftLength) (Right rightLength)
      (fun c => SL c.1) (fun c => SR c.1)
      (fun c => leftStatistic c.1) (fun c => rightStatistic c.1)
      (sharingDesignated sharing designatedYLeft)
      (sharingDesignated sharing (designatedYRight parentShape)) leftLaw rightLaw χ 1 e y := by
  apply compatible_of_designated_windows
  · intro h u hn hd
    rw [hlaw h u hn hd.1 hd.2]
    exact zeroZ_transfer (fun _ : Class counts e h u => shapeNat u)
      (fun i => (x h i.val).1) (fun i => (y h i.val).1) (fun i => (z h i.val).1)
      (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
        hsupport e x y z hsource hx hy hz h u hn hd.1).1
      (leftStatistic h) (κLeft h) (hstatLeft h) (xLeftLaw (h, u)) χ
      (fun _ => hd.2) (huseX h u hn hd.1).1
  · intro h u hn hd
    rw [hrlaw h u hn hd.1 hd.2]
    exact zeroZ_transfer (fun _ : Class counts e h u => parentShape h - shapeNat u)
      (fun i => (x h i.val).2) (fun i => (y h i.val).2) (fun i => (z h i.val).2)
      (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
        hsupport e x y z hsource hx hy hz h u hn hd.1).2
      (rightStatistic h) (κRight h) (hstatRight h) (xRightLaw (h, u)) χ
      (fun _ => hd.2) (huseX h u hn hd.1).2

omit [DecidableEq H] in
theorem source_implies_compatibleZ
    (leftLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SL c.1 → ℝ)
    (rightLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SR c.1 → ℝ)
    (hlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedZLeft (h, shapeSide 2 u) u →
      leftLaw (h, shapeSide 2 u) u =
        (if shapeNat u 1 = 0 then xLeftLaw (h, u) else yLeftLaw (h, u)) ∘
          (κLeft h).symm)
    (hrlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedZRight parentShape (h, shapeSide 2 u) u →
      rightLaw (h, shapeSide 2 u) u =
        (if (parentShape h - shapeNat u) 1 = 0 then xRightLaw (h, u)
          else yRightLaw (h, u)) ∘ (κRight h).symm)
    (huseX : ∀ h u, 0 < counts h u → sharing h = true →
      typeWindow (xLeftLaw (h, u)) χ
        (fun i : Class counts e h u => leftStatistic h (x h i.val).1) ∧
      typeWindow (xRightLaw (h, u)) χ
        (fun i : Class counts e h u => rightStatistic h (x h i.val).2))
    (huseY : ∀ h u, 0 < counts h u → sharing h = true →
      typeWindow (yLeftLaw (h, u)) χ
        (fun i : Class counts e h u => leftStatistic h (y h i.val).1) ∧
      typeWindow (yRightLaw (h, u)) χ
        (fun i : Class counts e h u => rightStatistic h (y h i.val).2)) :
    Compatible counts (Left leftLength) (Right rightLength)
      (fun c => SL c.1) (fun c => SR c.1)
      (fun c => leftStatistic c.1) (fun c => rightStatistic c.1)
      (sharingDesignated sharing designatedZLeft)
      (sharingDesignated sharing (designatedZRight parentShape)) leftLaw rightLaw χ 2 e z := by
  apply compatible_of_designated_windows
  · intro h u hn hd
    rw [hlaw h u hn hd.1 hd.2]
    have hp := (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
      hsupport e x y z hsource hx hy hz h u hn hd.1).1
    by_cases hzeroY : shapeNat u 1 = 0
    · rw [ite_eq_left hzeroY]
      exact zeroY_transfer (fun _ : Class counts e h u => shapeNat u)
        (fun i => (x h i.val).1) (fun i => (y h i.val).1) (fun i => (z h i.val).1) hp
        (leftStatistic h) (κLeft h) (hstatLeft h) (xLeftLaw (h, u)) χ
        (fun _ => hzeroY) (huseX h u hn hd.1).1
    · rw [ite_eq_right hzeroY]
      have hzeroX : shapeNat u 0 = 0 :=
        (Nat.mul_eq_zero.mp hd.2).resolve_right hzeroY
      exact zeroX_transfer (fun _ : Class counts e h u => shapeNat u)
        (fun i => (x h i.val).1) (fun i => (y h i.val).1) (fun i => (z h i.val).1) hp
        (leftStatistic h) (κLeft h) (hstatLeft h) (yLeftLaw (h, u)) χ
        (fun _ => hzeroX) (huseY h u hn hd.1).1
  · intro h u hn hd
    rw [hrlaw h u hn hd.1 hd.2]
    have hp := (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
      hsupport e x y z hsource hx hy hz h u hn hd.1).2
    by_cases hzeroY : (parentShape h - shapeNat u) 1 = 0
    · rw [ite_eq_left hzeroY]
      exact zeroY_transfer (fun _ : Class counts e h u => parentShape h - shapeNat u)
        (fun i => (x h i.val).2) (fun i => (y h i.val).2) (fun i => (z h i.val).2) hp
        (rightStatistic h) (κRight h) (hstatRight h) (xRightLaw (h, u)) χ
        (fun _ => hzeroY) (huseX h u hn hd.1).2
    · rw [ite_eq_right hzeroY]
      have hzeroX : (parentShape h - shapeNat u) 0 = 0 :=
        (Nat.mul_eq_zero.mp hd.2).resolve_right hzeroY
      exact zeroX_transfer (fun _ : Class counts e h u => parentShape h - shapeNat u)
        (fun i => (x h i.val).2) (fun i => (y h i.val).2) (fun i => (z h i.val).2) hp
        (rightStatistic h) (κRight h) (hstatRight h) (yRightLaw (h, u)) χ
        (fun _ => hzeroX) (huseY h u hn hd.1).2

end MatrixMultiplication.JointPopulationMixedCompatibility

end
end

end MatrixAllFields

end OAI
