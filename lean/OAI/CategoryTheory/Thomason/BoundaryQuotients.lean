import Mathlib
import OAI.CategoryTheory.Thomason.GlobularComplexes

namespace OAI

/-! Boundary Quotients. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def boundarySetoid (C : OmegaCategory.{u}) (n : ℕ) : Setoid C.Cell where
  r x y := C.source n x = C.source n y ∧ C.target n x = C.target n y
  iseqv := ⟨fun _ => ⟨rfl,rfl⟩, fun h => ⟨h.1.symm,h.2.symm⟩,
    fun h h' => ⟨h.1.trans h'.1,h.2.trans h'.2⟩⟩

namespace BoundaryQuotient
variable (C : OmegaCategory.{u}) (n : ℕ)
abbrev Cell := Quotient (boundarySetoid C n)
def map (x : C.Cell) : Cell C n := Quotient.mk _ x
lemma map_eq_iff (x y : C.Cell) : map C n x = map C n y ↔
    C.source n x = C.source n y ∧ C.target n x = C.target n y := Quotient.eq
lemma surjective : Function.Surjective (map C n) := Quotient.mk_surjective

lemma source_respects (k : ℕ) {x y : C.Cell}
    (h : C.source n x = C.source n y ∧ C.target n x = C.target n y) :
    C.source n (C.source k x) = C.source n (C.source k y) ∧
      C.target n (C.source k x) = C.target n (C.source k y) := by
  by_cases hk : n < k
  · simpa [C.source_source, C.target_source, hk, min_eq_left (le_of_lt hk)] using h
  · have hs : C.source k x = C.source k y := by
      simpa [C.source_source, min_eq_left (Nat.le_of_not_gt hk)] using congrArg (C.source k) h.1
    exact ⟨congrArg (C.source n) hs, congrArg (C.target n) hs⟩

lemma target_respects (k : ℕ) {x y : C.Cell}
    (h : C.source n x = C.source n y ∧ C.target n x = C.target n y) :
    C.source n (C.target k x) = C.source n (C.target k y) ∧
      C.target n (C.target k x) = C.target n (C.target k y) := by
  by_cases hk : n < k
  · simpa [C.source_target, C.target_target, hk, min_eq_left (le_of_lt hk)] using h
  · have ht : C.target k x = C.target k y := by
      simpa [C.target_target, min_eq_left (Nat.le_of_not_gt hk)] using congrArg (C.target k) h.2
    exact ⟨congrArg (C.source n) ht, congrArg (C.target n) ht⟩

def source (k : ℕ) : Cell C n → Cell C n := Quotient.map (C.source k) (fun _ _ h => source_respects C n k h)
def target (k : ℕ) : Cell C n → Cell C n := Quotient.map (C.target k) (fun _ _ h => target_respects C n k h)
@[simp] lemma source_map (k : ℕ) (x : C.Cell) : source C n k (map C n x) = map C n (C.source k x) := rfl
@[simp] lemma target_map (k : ℕ) (x : C.Cell) : target C n k (map C n x) = map C n (C.target k x) := rfl

lemma source_high (k : ℕ) (hk : n < k) (x : Cell C n) : source C n k x = x := by
  induction x using Quotient.inductionOn with | h x =>
    apply (map_eq_iff C n _ _).mpr
    simp [C.source_source, C.target_source, hk, min_eq_left (le_of_lt hk)]
lemma target_high (k : ℕ) (hk : n < k) (x : Cell C n) : target C n k x = x := by
  induction x using Quotient.inductionOn with | h x =>
    apply (map_eq_iff C n _ _).mpr
    simp [C.source_target, C.target_target, hk, min_eq_left (le_of_lt hk)]

lemma injective_on_lower {x y : C.Cell} (hx : C.source n x = x)
    (hy : C.source n y = y) (h : map C n x = map C n y) : x = y := by
  simpa only [hx,hy] using ((map_eq_iff C n x y).mp h).1

lemma composable_low {k : ℕ} (hk : k ≤ n) {x y : C.Cell}
    (h : target C n k (map C n x) = source C n k (map C n y)) :
    C.target k x = C.source k y := by
  apply injective_on_lower C n _ _ h
  · exact C.source_fixed_upwards hk (C.source_target_self k x)
  · exact C.source_fixed_upwards hk (C.source_source_self k y)

def comp (k : ℕ) (x y : Cell C n) (h : target C n k x = source C n k y) : Cell C n :=
  if hk : k ≤ n then
    map C n (C.comp k x.out y.out (composable_low C n hk (by simpa [map] using h)))
  else x

lemma comp_map (k : ℕ) (x y : C.Cell) (h : C.target k x = C.source k y)
    (h' : target C n k (map C n x) = source C n k (map C n y)) :
    comp C n k (map C n x) (map C n y) h' = map C n (C.comp k x y h) := by
  by_cases hk : k ≤ n
  · simp only [comp, dite_eq_left hk]
    apply (map_eq_iff C n _ _).mpr
    have hx := (map_eq_iff C n _ _).mp (Quotient.out_eq (map C n x))
    have hy := (map_eq_iff C n _ _).mp (Quotient.out_eq (map C n y))
    have hr : C.target k (map C n x).out = C.source k (map C n y).out :=
      composable_low C n hk (by simpa [map] using h')
    by_cases hnk : n ≤ k
    · simpa only [C.source_comp_le n k hnk, C.target_comp_le n k hnk] using And.intro hx.1 hy.2
    · have hlt : k < n := Nat.lt_of_not_ge hnk
      constructor
      · rw [C.source_comp_gt n k hlt _ _ _ (C.source_composable hlt hr),
          C.source_comp_gt n k hlt _ _ _ (C.source_composable hlt h)]
        congr 1
        · exact hx.1
        · exact hy.1
      · rw [C.target_comp_gt n k hlt _ _ _ (C.target_composable hlt hr),
          C.target_comp_gt n k hlt _ _ _ (C.target_composable hlt h)]
        congr 1
        · exact hx.2
        · exact hy.2
  · simp only [comp, dite_eq_right hk]
    apply (map_eq_iff C n _ _).mpr
    have hn : n ≤ k := le_of_lt (Nat.lt_of_not_ge hk)
    rw [C.source_comp_le n k hn, C.target_comp_le n k hn]
    refine ⟨rfl, ?_⟩
    have he := congrArg (C.target n) h
    simpa [C.target_target, C.target_source, Nat.lt_of_not_ge hk, min_eq_left hn] using he

lemma comp_map_low (k : ℕ) (hk : k ≤ n) (x y : C.Cell)
    (h : target C n k (map C n x) = source C n k (map C n y)) :
    comp C n k (map C n x) (map C n y) h =
      map C n (C.comp k x y (composable_low C n hk h)) :=
  comp_map C n k x y _ h

lemma comp_high (k : ℕ) (hk : n < k) (x y : Cell C n)
    (h : target C n k x = source C n k y) : comp C n k x y h = x := by
  simp only [comp, dite_eq_right (Nat.not_le.mpr hk)]

lemma high_composable {k : ℕ} (hk : n < k) {x y : Cell C n}
    (h : target C n k x = source C n k y) : x = y := by
  simpa only [target_high C n k hk, source_high C n k hk] using h

lemma source_source (i j : ℕ) (x : Cell C n) :
    source C n i (source C n j x) = source C n (min i j) x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  simp only [source_map,C.source_source]
lemma target_target (i j : ℕ) (x : Cell C n) :
    target C n i (target C n j x) = target C n (min i j) x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  simp only [target_map,C.target_target]
lemma source_target (i j : ℕ) (x : Cell C n) :
    source C n i (target C n j x) = if i < j then source C n i x else target C n j x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  by_cases h : i < j <;> simp [source_map,target_map,C.source_target,h]
lemma target_source (i j : ℕ) (x : Cell C n) :
    target C n i (source C n j x) = if i < j then target C n i x else source C n j x := by
  obtain ⟨x,rfl⟩ := surjective C n x
  by_cases h : i < j <;> simp [source_map,target_map,C.target_source,h]

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell C n)
    (h : target C n k x = source C n k y) :
    source C n i (comp C n k x y h) = source C n i x := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,source_map,C.source_comp_le i k hik]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk)]
lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell C n)
    (h : target C n k x = source C n k y) :
    target C n i (comp C n k x y h) = target C n i y := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,target_map,C.target_comp_le i k hik]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk), high_composable C n (Nat.lt_of_not_ge hk) h]

lemma source_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell C n)
    (h : target C n k x = source C n k y)
    (hs : target C n k (source C n i x) = source C n k (source C n i y)) :
    source C n i (comp C n k x y h) = comp C n k (source C n i x) (source C n i y) hs := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,source_map]
    exact congrArg (map C n) (C.source_comp_gt i k hki x y _ _)
  · rw [comp_high C n k (Nat.lt_of_not_ge hk), comp_high C n k (Nat.lt_of_not_ge hk)]
lemma target_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell C n)
    (h : target C n k x = source C n k y)
    (ht : target C n k (target C n i x) = source C n k (target C n i y)) :
    target C n i (comp C n k x y h) = comp C n k (target C n i x) (target C n i y) ht := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    simp only [comp_map_low C n k hk,target_map]
    exact congrArg (map C n) (C.target_comp_gt i k hki x y _ _)
  · rw [comp_high C n k (Nat.lt_of_not_ge hk), comp_high C n k (Nat.lt_of_not_ge hk)]

lemma unit_left (k : ℕ) (x : Cell C n)
    (h : target C n k (source C n k x) = source C n k x) :
    comp C n k (source C n k x) x h = x := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    simp only [source_map,comp_map_low C n k hk,C.unit_left]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk),source_high C n k (Nat.lt_of_not_ge hk)]
lemma unit_right (k : ℕ) (x : Cell C n)
    (h : target C n k x = source C n k (target C n k x)) :
    comp C n k x (target C n k x) h = x := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    simp only [target_map,comp_map_low C n k hk,C.unit_right]
  · rw [comp_high C n k (Nat.lt_of_not_ge hk)]

lemma assoc (k : ℕ) (x y z : Cell C n)
    (hxy : target C n k x = source C n k y) (hyz : target C n k y = source C n k z)
    (hxy_z : target C n k (comp C n k x y hxy) = source C n k z)
    (hx_yz : target C n k x = source C n k (comp C n k y z hyz)) :
    comp C n k (comp C n k x y hxy) z hxy_z = comp C n k x (comp C n k y z hyz) hx_yz := by
  by_cases hk : k ≤ n
  · obtain ⟨x,rfl⟩ := surjective C n x
    obtain ⟨y,rfl⟩ := surjective C n y
    obtain ⟨z,rfl⟩ := surjective C n z
    simp only [comp_map_low C n k hk]
    exact congrArg (map C n) (C.assoc k x y z _ _ _ _)
  · simp only [comp_high C n k (Nat.lt_of_not_ge hk)]

lemma interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell C n)
    (hab : target C n l a = source C n l b) (hcd : target C n l c = source C n l d)
    (hac : target C n k a = source C n k c) (hbd : target C n k b = source C n k d)
    (hab_cd : target C n k (comp C n l a b hab) = source C n k (comp C n l c d hcd))
    (hac_bd : target C n l (comp C n k a c hac) = source C n l (comp C n k b d hbd)) :
    comp C n k (comp C n l a b hab) (comp C n l c d hcd) hab_cd =
      comp C n l (comp C n k a c hac) (comp C n k b d hbd) hac_bd := by
  by_cases hl : l ≤ n
  · have hk : k ≤ n := (le_of_lt hkl).trans hl
    obtain ⟨a,rfl⟩ := surjective C n a
    obtain ⟨b,rfl⟩ := surjective C n b
    obtain ⟨c,rfl⟩ := surjective C n c
    obtain ⟨d,rfl⟩ := surjective C n d
    simp only [comp_map_low C n k hk,comp_map_low C n l hl]
    exact congrArg (map C n) (C.interchange k l hkl a b c d _ _ _ _ _ _)
  · simp only [comp_high C n l (Nat.lt_of_not_ge hl)]

def category : OmegaCategory.{u} where
  Cell := Cell C n
  source := source C n
  target := target C n
  comp := comp C n
  source_source := source_source C n
  target_target := target_target C n
  source_target := source_target C n
  target_source := target_source C n
  source_comp_le := source_comp_le C n
  target_comp_le := target_comp_le C n
  source_comp_gt := source_comp_gt C n
  target_comp_gt := target_comp_gt C n
  unit_left := unit_left C n
  unit_right := unit_right C n
  assoc := assoc C n
  interchange := interchange C n
  finite_dimension x := ⟨n+1, source_high C n (n+1) (by omega) x⟩

lemma truncated : (category C n).IsTruncated (n+1) :=
  source_high C n (n+1) (by omega)

def projection : Functor C (category C n) where
  map := map C n
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp k x y h h' := (comp_map C n k x y h h').symm

end BoundaryQuotient

lemma truncationUnit_injective_below (C : OmegaCategory.{u}) (n k : ℕ)
    (hk : k < n) {x y : C.Cell} (hx : C.source k x = x)
    (hy : C.source k y = y)
    (h : (truncationUnit n C).map x = (truncationUnit n C).map y) : x = y := by
  let D : NCategory.{u} n := ⟨BoundaryQuotient.category C k, fun z =>
    (BoundaryQuotient.category C k).source_fixed_upwards (by omega)
      (BoundaryQuotient.truncated C k z)⟩
  let F := truncationLift D (BoundaryQuotient.projection C k)
  exact BoundaryQuotient.injective_on_lower C k hx hy (congrArg F.map h)

lemma truncationUnit_surjective (C : OmegaCategory.{u}) (n : ℕ) :
    Function.Surjective (truncationUnit n C).map := by
  intro z
  induction z using Quotient.inductionOn with | h z =>
    rcases z with ⟨z,hz⟩
    induction hz with
    | gen x => exact ⟨x,rfl⟩
    | source k z hz ih =>
      obtain ⟨x,hx⟩ := ih
      refine ⟨C.source k x, ?_⟩
      rw [(truncationUnit n C).map_source, hx]
      rfl
    | target k z hz ih =>
      obtain ⟨x,hx⟩ := ih
      refine ⟨C.target k x, ?_⟩
      rw [(truncationUnit n C).map_target, hx]
      rfl
    | comp k z w hz hw hm ihz ihw =>
      obtain ⟨x,hx⟩ := ihz
      obtain ⟨y,hy⟩ := ihw
      have he : (truncationPresentation n C).category.target k (Quotient.mk _ ⟨z,hz⟩) =
          (truncationPresentation n C).category.source k (Quotient.mk _ ⟨w,hw⟩) :=
        Quotient.sound hm
      rw [← (truncationPresentation n C).mk_comp k ⟨z,hz⟩ ⟨w,hw⟩ hm he]
      change ∃ a, (truncationUnit n C).map a =
        (truncationPresentation n C).category.comp k _ _ he
      by_cases hk : k < n
      · have he' : (truncationUnit n C).map (C.target k x) =
            (truncationUnit n C).map (C.source k y) := by
          rw [(truncationUnit n C).map_target, (truncationUnit n C).map_source, hx, hy]
          exact he
        have hc := truncationUnit_injective_below C n k hk
          (C.source_target_self k x) (C.source_source_self k y) he'
        refine ⟨C.comp k x y hc, ?_⟩
        rw [(truncationUnit n C).map_comp k x y hc ((truncationUnit n C).map_composable hc)]
        congr 1
      · refine ⟨y, ?_⟩
        rw [(truncationPresentation n C).category.comp_of_left_source_fixed k _ _ he
          ((truncationPresentation n C).category.source_fixed_upwards
            (Nat.le_of_not_gt hk) (truncation_isTruncated n C _))]
        exact hy

lemma truncationUnit_surjective_nCells (C : OmegaCategory.{u}) (n : ℕ)
    (z : (truncation n C).val.Cell) :
    ∃ x : C.Cell, C.source n x = x ∧ (truncationUnit n C).map x = z := by
  obtain ⟨x,rfl⟩ := truncationUnit_surjective C n z
  refine ⟨C.source n x, C.source_source_self n x, ?_⟩
  rw [(truncationUnit n C).map_source]
  exact truncation_isTruncated n C _

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma truncationUnit_onCells_surjective (C : OmegaCategory.{u}) (n p : ℕ) :
    Function.Surjective ((truncationUnit n C).onCells p) := by
  intro z
  obtain ⟨x,hx⟩ := truncationUnit_surjective C n z.val
  refine ⟨C.sourceCell p x, ?_⟩
  apply Subtype.ext
  change (truncationUnit n C).map (C.source p x) = z.val
  rw [(truncationUnit n C).map_source, hx, z.property]

def truncationCellLift (C : OmegaCategory.{u}) (n p : ℕ)
    (z : (truncation n C).val.Cells p) : C.Cells p :=
  (truncationUnit_onCells_surjective C n p z).choose

@[simp] lemma truncationCellLift_unit (C : OmegaCategory.{u}) (n p : ℕ)
    (z : (truncation n C).val.Cells p) :
    (truncationUnit n C).onCells p (truncationCellLift C n p z) = z :=
  (truncationUnit_onCells_surjective C n p z).choose_spec

@[simp] lemma truncationCellLift_map (C : OmegaCategory.{u}) (n p : ℕ)
    (z : (truncation n C).val.Cells p) :
    (truncationUnit n C).map (truncationCellLift C n p z).val = z.val :=
  congrArg Subtype.val (truncationCellLift_unit C n p z)

lemma truncationUnit_onCells_injective (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    Function.Injective ((truncationUnit n C).onCells p) := by
  intro x y h
  exact Subtype.ext (truncationUnit_injective_below C n p hp x.property y.property
    (congrArg Subtype.val h))

@[simp] lemma truncationCellLift_of_unit (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x : C.Cells p) : truncationCellLift C n p ((truncationUnit n C).onCells p x) = x :=
  truncationUnit_onCells_injective C n p hp (truncationCellLift_unit C n p _)

lemma truncationCellLift_source_fixed (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x : (truncation n C).val.Cells p) (k : ℕ) (hk : k ≤ p)
    (hx : (truncation n C).val.source k x.val = x.val) :
    C.source k (truncationCellLift C n p x).val = (truncationCellLift C n p x).val := by
  apply truncationUnit_injective_below C n p hp
    (C.source_fixed_upwards hk (C.source_source_self k _)) (truncationCellLift C n p x).property
  rw [(truncationUnit n C).map_source, truncationCellLift_map]
  exact hx

lemma truncationCellLift_composable (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x y : (truncation n C).val.Cells p) (k : ℕ) (hk : k < p)
    (h : (truncation n C).val.target k x.val = (truncation n C).val.source k y.val) :
    C.target k (truncationCellLift C n p x).val = C.source k (truncationCellLift C n p y).val := by
  apply truncationUnit_injective_below C n k (lt_trans hk hp)
    (C.source_target_self k _) (C.source_source_self k _)
  rw [(truncationUnit n C).map_source, (truncationUnit n C).map_target,
    truncationCellLift_map, truncationCellLift_map]
  exact h

lemma truncationCellLift_comp (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x y : (truncation n C).val.Cells p) (k : ℕ) (hk : k < p)
    (h : (truncation n C).val.target k x.val = (truncation n C).val.source k y.val) :
    truncationCellLift C n p ((truncation n C).val.gradedComp hk x y h) =
      C.gradedComp hk (truncationCellLift C n p x) (truncationCellLift C n p y)
        (truncationCellLift_composable C n p hp x y k hk h) := by
  apply truncationUnit_onCells_injective C n p hp
  rw [truncationCellLift_unit, (truncationUnit n C).onCells_comp]
  simp only [truncationCellLift_unit]
  rfl

def truncationLambdaRawRetraction (C : OmegaCategory.{u}) (n p : ℕ) :
    (truncation n C).val.LambdaRaw p →ₗ[ℤ] C.LambdaChain p :=
  Finsupp.linearCombination ℤ (fun x => C.lambdaGen (truncationCellLift C n p x))

@[simp] lemma truncationLambdaRawRetraction_single (C : OmegaCategory.{u}) (n p : ℕ)
    (x : (truncation n C).val.Cells p) :
    truncationLambdaRawRetraction C n p (Finsupp.single x 1) =
      C.lambdaGen (truncationCellLift C n p x) := by
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma truncationLambdaRawRetraction_relations (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    (truncation n C).val.lambdaRelations p ≤ LinearMap.ker (truncationLambdaRawRetraction C n p) := by
  apply Submodule.span_le.mpr
  intro z hz
  change truncationLambdaRawRetraction C n p z = 0
  rcases hz with ⟨x,k,hk,hx,rfl⟩ | ⟨k,hk,x,y,h,rfl⟩
  · rw [truncationLambdaRawRetraction_single]
    exact C.lambdaGen_degenerate hk _ (truncationCellLift_source_fixed C n p hp x k hk.le hx)
  · simp only [map_sub,truncationLambdaRawRetraction_single]
    rw [truncationCellLift_comp C n p hp x y k hk h, C.lambdaGen_comp hk]
    abel

def truncationLambdaRetraction (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    (truncation n C).val.LambdaChain p →ₗ[ℤ] C.LambdaChain p :=
  ((truncation n C).val.lambdaRelations p).liftQ (truncationLambdaRawRetraction C n p)
    (truncationLambdaRawRetraction_relations C n p hp)

@[simp] lemma truncationLambdaRetraction_gen (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n)
    (x : (truncation n C).val.Cells p) :
    truncationLambdaRetraction C n p hp ((truncation n C).val.lambdaGen x) =
      C.lambdaGen (truncationCellLift C n p x) :=
  truncationLambdaRawRetraction_single C n p x

lemma truncationLambdaRetraction_leftInverse (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    (truncationLambdaRetraction C n p hp).comp ((truncationUnit n C).lambdaMap p) = LinearMap.id := by
  apply C.lambda_linear_ext
  intro x
  change truncationLambdaRetraction C n p hp
    ((truncationUnit n C).lambdaMap p (C.lambdaGen x)) = C.lambdaGen x
  rw [Functor.lambdaMap_gen]
  exact (truncationLambdaRetraction_gen C n p hp ((truncationUnit n C).onCells p x)).trans
    (congrArg C.lambdaGen (truncationCellLift_of_unit C n p hp x))

lemma truncationUnit_lambdaMap_injective (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    Function.Injective ((truncationUnit n C).lambdaMap p) := by
  intro x y h
  have hx := LinearMap.congr_fun (truncationLambdaRetraction_leftInverse C n p hp) x
  have hy := LinearMap.congr_fun (truncationLambdaRetraction_leftInverse C n p hp) y
  exact hx.symm.trans ((congrArg (truncationLambdaRetraction C n p hp) h).trans hy)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory

variable {C : OmegaCategory.{u}} {n N : ℕ}

def liftedBasis (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) : C.LambdaChain p := by
  classical
  by_cases h : w.val.length = p+1
  · rcases w with ⟨w,hw⟩
    cases w with
    | nil => simp at h
    | cons a l =>
      let A := simplexAtom a l (hw.imp le_of_lt)
      have he : (a::l).length-1 = p := by simp only [List.length_cons] at h ⊢; omega
      exact C.lambdaGen (truncationCellLift C n p (F.onCells p ⟨A.table, he ▸ A.dimension⟩))
  · exact 0

lemma liftedBasis_cons (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (h : l.length = p)
    (hd : truncate p false (simplexAtom a l (ha.imp le_of_lt)).table =
      (simplexAtom a l (ha.imp le_of_lt)).table) :
    liftedBasis F p ⟨a::l,ha⟩ = C.lambdaGen
      (truncationCellLift C n p (F.onCells p ⟨_,hd⟩)) := by
  simp [liftedBasis,h]

lemma liftedBasis_unit (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) :
    (truncationUnit n C).lambdaMap p (liftedBasis F p w) = F.lambdaMap p (basisLambda p w) := by
  classical
  unfold liftedBasis basisLambda
  split_ifs with h
  · rcases w with ⟨w,hw⟩
    cases w with
    | nil => simp at h
    | cons a l =>
      erw [OmegaCategory.Functor.lambdaMap_gen, OmegaCategory.Functor.lambdaMap_gen]
      congr 1
      exact truncationCellLift_unit C n p _
  · exact (map_zero ((truncationUnit n C).lambdaMap p)).trans (map_zero (F.lambdaMap p)).symm

def liftedChainMap (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) : (complex (Fin (N+1))).Chain p →ₗ[ℤ] C.LambdaChain p :=
  (Finsupp.linearCombination ℤ (liftedBasis F p)).comp (grade (p+1)).subtype

lemma liftedChainMap_bracket (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) (h : w.val.length = p+1) :
    liftedChainMap F p ⟨bracket w.val, h ▸ bracket_mem_grade w.val⟩ = liftedBasis F p w := by
  change Finsupp.linearCombination ℤ (liftedBasis F p) (bracket w.val) = _
  rw [bracket_of_pairwise w.property,Finsupp.linearCombination_single,one_smul]

lemma liftedChainMap_unit (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (x : (complex (Fin (N+1))).Chain p) :
    (truncationUnit n C).lambdaMap p (liftedChainMap F p x) =
      F.lambdaMap p (atomCounitInverse p x) := by
  change ((truncationUnit n C).lambdaMap p).comp
      (Finsupp.linearCombination ℤ (liftedBasis F p)) x.val =
    (F.lambdaMap p).comp (Finsupp.linearCombination ℤ (basisLambda p)) x.val
  congr 1
  apply Finsupp.lhom_ext
  intro w z
  change (truncationUnit n C).lambdaMap p
    (Finsupp.linearCombination ℤ (liftedBasis F p) (Finsupp.single w z)) =
    F.lambdaMap p (Finsupp.linearCombination ℤ (basisLambda p) (Finsupp.single w z))
  erw [Finsupp.linearCombination_single,Finsupp.linearCombination_single,map_smul,map_smul,
    liftedBasis_unit]
  rfl

lemma liftedChainMap_d (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (hN : N ≤ n) (p : ℕ) (x : (complex (Fin (N+1))).Chain (p+1)) :
    liftedChainMap F p ((complex (Fin (N+1))).d p x) =
      C.lambdaD p (liftedChainMap F (p+1) x) := by
  by_cases hp : p < n
  · apply truncationUnit_lambdaMap_injective C n p hp
    rw [liftedChainMap_unit]
    have hd := (simplexCounitInverse N).map_d p x
    change atomCounitInverse p ((complex (Fin (N+1))).d p x) =
      (Oriental N).lambdaD p (atomCounitInverse (p+1) x) at hd
    rw [hd]
    exact (LinearMap.congr_fun (F.lambdaMap_d p) _).trans
      ((congrArg ((truncation n C).val.lambdaD p) (liftedChainMap_unit F (p+1) x).symm).trans
        (LinearMap.congr_fun ((truncationUnit n C).lambdaMap_d p) _).symm)
  · have hx : x = 0 := by
      apply Subtype.ext
      exact grade_eq_zero_of_card_lt x.property (by simp only [Fintype.card_fin]; omega)
    rw [hx,map_zero,map_zero,map_zero,map_zero]

lemma liftedChainMap_aug (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (x : (complex (Fin (N+1))).Chain 0) :
    C.lambdaAug (liftedChainMap F 0 x) = (complex (Fin (N+1))).augmentation x := by
  calc
    _ = (truncation n C).val.lambdaAug
        ((truncationUnit n C).lambdaMap 0 (liftedChainMap F 0 x)) :=
      (LinearMap.congr_fun ((truncationUnit n C).lambdaMap_aug) _).symm
    _ = (truncation n C).val.lambdaAug (F.lambdaMap 0 (atomCounitInverse 0 x)) :=
      congrArg _ (liftedChainMap_unit F 0 x)
    _ = (Oriental N).lambdaAug (atomCounitInverse 0 x) :=
      LinearMap.congr_fun F.lambdaMap_aug _
    _ = _ := (simplexCounitInverse N).map_augmentation x

lemma liftedBasis_positive (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) : liftedBasis F p w ∈ C.lambdaPositive p := by
  classical
  unfold liftedBasis
  split_ifs with h
  · rcases w with ⟨w,hw⟩
    cases w with
    | nil => simp at h
    | cons a l => exact C.lambdaGen_positive _
  · exact AddSubmonoid.zero_mem _

lemma liftedChainMap_positive (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (x : (complex (Fin (N+1))).Chain p) (hx : x ∈ (complex (Fin (N+1))).positive p) :
    liftedChainMap F p x ∈ C.lambdaPositive p := by
  classical
  change Finsupp.linearCombination ℤ (liftedBasis F p) x.val ∈ _
  rw [Finsupp.linearCombination_apply,Finsupp.sum]
  apply AddSubmonoid.sum_mem
  intro w _
  have hw : 0 ≤ x.val w := hx w
  have he : x.val w = (x.val w).toNat := (Int.toNat_of_nonneg hw).symm
  rw [he,Nat.cast_smul_eq_nsmul]
  exact AddSubmonoid.nsmul_mem _ (liftedBasis_positive F p w) _

def liftedChainHom (F : OmegaCategory.Functor (Oriental N) (truncation n C).val) (hN : N ≤ n) :
    Hom (complex (Fin (N+1))) C.linearization where
  map p := (liftedChainMap F p).toAddMonoidHom
  map_d := liftedChainMap_d F hN
  map_augmentation := liftedChainMap_aug F
  map_positive := liftedChainMap_positive F

lemma atomCounitInverse_row (p : ℕ) (y : Table (complex (Fin (N+1)))) (b : Bool) :
    atomCounitInverse p (y.row p b) = (Oriental N).lambdaGen
      (if b then (Oriental N).targetCell p y else (Oriental N).sourceCell p y) := by
  have h := atomCounitInverse_top (p := p) (truncate p b y) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])
  rw [truncate_top_row] at h
  cases b <;> exact h

variable {K : DirectedComplex.{u}}

def boundedOrientalLift (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (hN : N ≤ n) : OmegaCategory.Functor (Oriental N) K.nu :=
  (Hom.comp (liftedChainHom F hN) K.lambdaCounit).nu

lemma boundedOrientalLift_atom
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val) (hN : N ≤ n)
    (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·)) :
    (boundedOrientalLift F hN).map (simplexAtom a l (ha.imp le_of_lt)).table =
      (truncationCellLift K.nu n l.length
        (F.onCells l.length ⟨(simplexAtom a l (ha.imp le_of_lt)).table,
          by
            change @Eq (Table (complex (Fin (N+1)))) (truncate l.length false _) _
            simpa only [List.length_cons,Nat.add_sub_cancel] using
              (simplexAtom a l (ha.imp le_of_lt)).dimension⟩)).val := by
  let A := simplexAtom a l (ha.imp le_of_lt)
  have hd : truncate l.length false A.table = A.table := by
    simpa only [List.length_cons,Nat.add_sub_cancel] using A.dimension
  let L := truncationCellLift K.nu n l.length (F.onCells l.length ⟨A.table,hd⟩)
  have hL : (truncationUnit n K.nu).map L.val = F.map A.table :=
    truncationCellLift_map K.nu n l.length _
  have hlen : l.length ≤ N := by
    have h := ha.nodup.length_le_card
    simp only [List.length_cons,Fintype.card_fin] at h
    omega
  apply Table.ext
  funext p b
  change K.lambdaCounitMap p (liftedChainMap F p (A.table.row p b)) = L.val.row p b
  by_cases hp : p < l.length
  · have hl : liftedChainMap F p (A.table.row p b) = K.nu.lambdaGen
        (if b then K.nu.targetCell p L.val else K.nu.sourceCell p L.val) := by
      apply truncationUnit_lambdaMap_injective K.nu n p (by omega)
      rw [liftedChainMap_unit,atomCounitInverse_row]
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
      · erw [OmegaCategory.Functor.lambdaMap_gen,OmegaCategory.Functor.lambdaMap_gen]
        congr 1
        apply Subtype.ext
        change F.map (truncate p false A.table) =
          (truncationUnit n K.nu).map (truncate p false L.val)
        exact (F.map_source p A.table).trans
          ((congrArg ((truncation n K.nu).val.source p) hL.symm).trans
            ((truncationUnit n K.nu).map_source p L.val).symm)
      · erw [OmegaCategory.Functor.lambdaMap_gen,OmegaCategory.Functor.lambdaMap_gen]
        congr 1
        apply Subtype.ext
        change F.map (truncate p true A.table) =
          (truncationUnit n K.nu).map (truncate p true L.val)
        exact (F.map_target p A.table).trans
          ((congrArg ((truncation n K.nu).val.target p) hL.symm).trans
            ((truncationUnit n K.nu).map_target p L.val).symm)
    rw [hl]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · rw [K.lambdaCounitMap_gen]
      exact truncate_top_row p false L.val false
    · rw [K.lambdaCounitMap_gen]
      exact truncate_top_row p true L.val false
  · by_cases he : p = l.length
    · subst p
      have ht : A.table.row l.length b =
          (⟨bracket (a::l),bracket_mem_grade (a::l)⟩ : (complex (Fin (N+1))).Chain l.length) := by
        apply Subtype.ext
        have ht := A.top b
        have he : (a::l).length-1 = l.length := by simp
        rw [he] at ht
        exact ht
      rw [ht,liftedChainMap_bracket F l.length ⟨a::l,ha⟩ rfl,
        liftedBasis_cons F l.length a l ha rfl hd]
      rw [K.lambdaCounitMap_gen]
      change L.val.row l.length false = L.val.row l.length b
      have h := congrArg (fun t : Table K => t.row l.length b) L.property
      change (truncate l.length false L.val).row l.length b = L.val.row l.length b at h
      erw [truncate_top_row] at h
      exact h
    · have hlt : l.length < p := by omega
      rw [row_above_fixed A.table hd hlt b,map_zero,map_zero,
        row_above_fixed L.val L.property hlt b]

lemma boundedOrientalLift_unit
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val) (hN : N ≤ n) :
    OmegaCategory.Functor.comp (boundedOrientalLift F hN) (truncationUnit n K.nu) = F := by
  apply oriental_functor_ext
  intro a l ha
  change (truncationUnit n K.nu).map
    ((boundedOrientalLift F hN).map (simplexAtom a l (ha.imp le_of_lt)).table) = _
  rw [boundedOrientalLift_atom F hN a l ha]
  exact truncationCellLift_map K.nu n l.length _

lemma truncation_oriental_surjective (K : DirectedComplex.{u}) (n N : ℕ) (hN : N ≤ n) :
    Function.Surjective (fun G : OmegaCategory.Functor (Oriental N) K.nu =>
      OmegaCategory.Functor.comp G (truncationUnit n K.nu)) := by
  intro F
  exact ⟨boundedOrientalLift F hN,boundedOrientalLift_unit F hN⟩

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table OmegaCategory

structure PartialHom (K : DirectedComplex.{u}) (L : DirectedComplex.{v}) (n : ℕ) where
  map : (p : ℕ) → K.Chain p →+ L.Chain p
  map_d (p : ℕ) (hp : p < n) (x : K.Chain (p+1)) :
    map p (K.d p x) = L.d p (map (p+1) x)
  map_augmentation (x : K.Chain 0) : L.augmentation (map 0 x) = K.augmentation x
  map_positive (p : ℕ) (x : K.Chain p) :
    x ∈ K.positive p → map p x ∈ L.positive p

namespace PartialHom
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def table (f : PartialHom K L n) (x : Table K) : Table L where
  row p b := if p < n then f.map p (x.row p b) else
    if p = n then f.map p (x.row p false) else 0
  positive p b := by
    split_ifs with h h
    · exact f.map_positive p _ (x.positive p b)
    · exact f.map_positive p _ (x.positive p false)
    · exact (L.positive p).zero_mem
  boundary p b := by
    by_cases hp : p < n
    · by_cases hp' : p+1 < n
      · simp only [hp,hp',ite_true]
        rw [← f.map_d p hp,x.boundary,map_sub]
      · have he : p+1 = n := by omega
        simp only [hp,ite_true,ite_false,he,lt_self_iff_false]
        rw [← f.map_d p hp,x.boundary,map_sub]
    · have hp' : ¬p+1 < n := by omega
      have he' : p+1 ≠ n := by omega
      simp only [hp,hp',he',ite_false,map_zero]
      split <;> simp
  augmentation b := by
    by_cases hn : 0 < n
    · simp only [hn,ite_true]; rw [f.map_augmentation,x.augmentation]
    · have he : n = 0 := by omega
      simp only [he,lt_self_iff_false,ite_false,ite_true]
      rw [f.map_augmentation,x.augmentation]
  bounded := ⟨n,fun p hp b => by simp [show ¬p<n by omega,show p ≠ n by omega]⟩

lemma table_bounded (f : PartialHom K L n) (x : Table K) :
    truncate n false (f.table x) = f.table x := by
  apply dimension_of_rows_above_zero
  intro p hp b
  simp [table,show ¬p<n by omega,show p≠n by omega]

lemma table_source (f : PartialHom K L n) (k : ℕ) (x : Table K) :
    f.table (truncate k false x) = truncate k false (f.table x) := by
  ext p b
  simp only [table,truncate_row]
  split_ifs <;> simp_all only [map_zero]

lemma table_target_lt (f : PartialHom K L n) (k : ℕ) (hk : k<n) (x : Table K) :
    f.table (truncate k true x) = truncate k true (f.table x) := by
  ext p b
  simp only [table,truncate_row]
  split_ifs <;> simp_all only [map_zero, not_true_eq_false]

lemma table_composable (f : PartialHom K L n) {k : ℕ} (hk : k<n) {x y : Table K}
    (h : truncate k true x = truncate k false y) :
    truncate k true (f.table x) = truncate k false (f.table y) := by
  rw [← f.table_target_lt k hk,← f.table_source,h]

lemma table_comp_lt (f : PartialHom K L n) {k : ℕ} (hk : k<n) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    f.table (comp k x y h) = comp k (f.table x) (f.table y) (f.table_composable hk h) := by
  ext p b
  simp only [table,comp_row]
  cases b <;> split_ifs <;> simp_all only [map_add, add_zero, not_true_eq_false]

lemma table_source_n (f : PartialHom K L n) (x : Table K) :
    f.table (truncate n false x) = f.table x := by
  rw [f.table_source,f.table_bounded]

end PartialHom
end Thomason.DirectedComplex

end

end OAI
