import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I]

/- Oriented edges crossing a two-color cut. -/
def cutEdges (R : I → I → Prop) (c : I → Bool) : Finset (I × I) :=
  Finset.univ.filter (fun p => R p.1 p.2 ∧ c p.1 ≠ c p.2)

omit [DecidableEq I] in
@[simp] theorem mem_cutEdges (R : I → I → Prop) (c : I → Bool) (i j : I) :
    (i,j) ∈ cutEdges R c ↔ R i j ∧ c i ≠ c j := by simp [cutEdges]

/- A maximum cut has an opposite-color neighbor at every nonisolated vertex.
Only symmetry and absence of loops are used. -/
theorem exists_crossing_cut (R : I → I → Prop)
    (hsym : ∀ ⦃left right⦄, R left right → R right left) (hirr : ∀ vertex, ¬ R vertex vertex) :
    ∃ c : I → Bool, ∀ i, (∃ j, R i j) → ∃ j, R i j ∧ c i ≠ c j := by
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image
    (Finset.univ : Finset (I → Bool)) (fun c => (cutEdges R c).card) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  intro i hi
  by_contra hh
  have hn : ∀ j, R i j → c i = c j := by
    intro j hij
    by_contra hne
    exact hh ⟨j,hij,hne⟩
  let c' := Function.update c i (!(c i))
  have hsub : cutEdges R c ⊆ cutEdges R c' := by
    intro p hp
    obtain ⟨hpR,hpne⟩ := (mem_cutEdges R c p.1 p.2).mp hp
    have hpi : p.1 ≠ i := by
      intro he; subst he
      exact hpne (hn _ hpR)
    have hpj : p.2 ≠ i := by
      intro he
      have heq := hn p.1 (hsym (he ▸ hpR))
      exact hpne (he ▸ heq.symm)
    apply (mem_cutEdges R c' p.1 p.2).mpr
    exact ⟨hpR, by simpa [c', Function.update_of_ne hpi, Function.update_of_ne hpj] using hpne⟩
  obtain ⟨j,hij⟩ := hi
  have hji : j ≠ i := by intro he; subst j; exact hirr i hij
  have hnew : (i,j) ∈ cutEdges R c' := by
    rw [mem_cutEdges]
    refine ⟨hij, ?_⟩
    simp only [c', Function.update_self, Function.update_of_ne hji]
    rw [← hn j hij]
    cases c i <;> decide
  have hold : (i,j) ∉ cutEdges R c := by simp [hn j hij]
  have hlt : (cutEdges R c).card < (cutEdges R c').card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro he; rw [he] at hold; exact hold hnew⟩)
  exact (not_lt_of_ge (hc c' (Finset.mem_univ _))) hlt

/- Particles incident to a particle-sharing edge or a fixed hole. -/
def covered (R : I → I → Prop) (T : I → H → Prop) : Finset I :=
  Finset.univ.filter (fun i => (∃ j, R i j) ∨ (∃ l, T i l))

omit [DecidableEq I] in
@[simp] theorem mem_covered (R : I → I → Prop) (T : I → H → Prop) (i : I) :
    i ∈ covered R T ↔ (∃ j, R i j) ∨ (∃ l, T i l) := by simp [covered]

/- A star forest supplies at least half as many distinct particle tails as
there are covered particles, with all parents outside the chosen tails. -/
theorem exists_star_forest (R : I → I → Prop) (T : I → H → Prop)
    (hsym : ∀ ⦃left right⦄, R left right → R right left) (hirr : ∀ vertex, ¬ R vertex vertex) :
    ∃ A : Finset I, A ⊆ covered R T ∧ (covered R T).card ≤ 2*A.card ∧
      ∀ i ∈ A, (∃ j, j ∉ A ∧ R i j) ∨ (∃ l, T i l) := by
  obtain ⟨c,hc⟩ := exists_crossing_cut R hsym hirr
  let A := (covered R T).filter (fun i => c i = false)
  let B := (covered R T).filter (fun i => c i = true)
  have hAB : (covered R T).card = A.card + B.card := by
    have hpart := Finset.card_filter_add_card_filter_not (s := covered R T)
      (p := fun i => c i = false)
    have he : B = (covered R T).filter (fun i => ¬ c i = false) := by
      ext i
      simp only [B, Finset.mem_filter]
      cases c i <;> simp
    rw [he]
    exact hpart.symm
  have hA : ∀ i ∈ A, (∃ j, j ∉ A ∧ R i j) ∨ (∃ l, T i l) := by
    intro i hi
    obtain ⟨hcov,hci⟩ := Finset.mem_filter.mp hi
    rcases (mem_covered R T i).mp hcov with h | h
    · obtain ⟨j,hij,hne⟩ := hc i h
      left
      refine ⟨j,?_,hij⟩
      intro hj
      have hcj := (Finset.mem_filter.mp hj).2
      exact hne (hci.trans hcj.symm)
    · exact Or.inr h
  have hB : ∀ i ∈ B, (∃ j, j ∉ B ∧ R i j) ∨ (∃ l, T i l) := by
    intro i hi
    obtain ⟨hcov,hci⟩ := Finset.mem_filter.mp hi
    rcases (mem_covered R T i).mp hcov with h | h
    · obtain ⟨j,hij,hne⟩ := hc i h
      left
      refine ⟨j,?_,hij⟩
      intro hj
      have hcj := (Finset.mem_filter.mp hj).2
      exact hne (hci.trans hcj.symm)
    · exact Or.inr h
  by_cases hle : A.card ≤ B.card
  · exact ⟨B, Finset.filter_subset _ _, by omega, hB⟩
  · exact ⟨A, Finset.filter_subset _ _, by omega, hA⟩

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/- Product mass of independent particle data. -/
def productMass (w : X → ℝ) (x : I → X) : ℝ := ∏ i, w (x i)

/- Finite event probability, with the product law on the full endpoint array. -/
def probability (w : X → ℝ) (P : (I → X) → Prop) : ℝ :=
  ∑ x : I → X, if P x then productMass w x else 0

def glue (A : Finset I) (x : A → X) (y : {i : I // i ∉ A} → X) : I → X :=
  (Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) (fun _ => X)).symm (x,y)

omit [Fintype I] [Fintype X] in
@[simp] theorem glue_mem (A : Finset I) (x : A → X) (y : {i : I // i ∉ A} → X)
    (i : A) : glue A x y i = x i := by
  simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

omit [Fintype I] [Fintype X] in
@[simp] theorem glue_not_mem (A : Finset I) (x : A → X) (y : {i : I // i ∉ A} → X)
    (i : {i : I // i ∉ A}) : glue A x y i = y i := by
  simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

omit [Fintype X] in
theorem productMass_glue (A : Finset I) (w : X → ℝ)
    (x : A → X) (y : {i : I // i ∉ A} → X) :
    productMass w (glue A x y) = (∏ i, w (x i)) * ∏ j, w (y j) := by
  unfold productMass
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ A)]
  simp only [glue_mem, glue_not_mem]
  congr!

/- Reused elementary finite independence identity, inline. -/
theorem sum_prod_ite_all {J : Type*} [Fintype J] [DecidableEq J]
    {Y : J → Type*} [∀ j, Fintype (Y j)]
    (w : ∀ j, Y j → ℝ) (P : ∀ j, Y j → Prop) :
    (∑ x : ∀ j, Y j, if ∀ j, P j (x j) then ∏ j, w j (x j) else 0) =
      ∏ j, ∑ y, if P j y then w j y else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ j, P j (x j)
  · simp [hx]
  · obtain ⟨j,hj⟩ := not_forall.mp hx
    rw [ite_eq_right hx]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

/- Conditional on all roots, different star tails involve independent data.
This is a factorization of the actual finite sum, not an independence axiom. -/
theorem probability_star_factorization (A : Finset I) (w : X → ℝ)
    (P : ({i : I // i ∉ A} → X) → A → X → Prop) :
    probability w (fun x : I → X => ∀ i : A, P (fun j => x j) i (x i)) =
      ∑ y : {i : I // i ∉ A} → X,
        (∏ j, w (y j)) * ∏ i : A, ∑ t : X, if P y i t then w t else 0 := by
  unfold probability
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) (fun _ => X)
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hg : ∀ x : A → X,
      (if ∀ i : A, P (fun j => e.symm (x,y) j) i (e.symm (x,y) i)
        then productMass w (e.symm (x,y)) else 0) =
      (∏ j, w (y j)) * (if ∀ i : A, P y i (x i) then ∏ i, w (x i) else 0) := by
    intro x
    change (if ∀ i : A, P (fun j => glue A x y j) i (glue A x y i)
      then productMass w (glue A x y) else 0) = _
    simp only [glue_mem, glue_not_mem, productMass_glue]
    split_ifs <;> ring
  calc
    _ = ∑ x : A → X, (∏ j, w (y j)) *
        (if ∀ i : A, P y i (x i) then ∏ i, w (x i) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      convert hg x using 1
      congr!
    _ = (∏ j, w (y j)) * (∑ x : A → X,
        if ∀ i : A, P y i (x i) then ∏ i, w (x i) else 0) := by rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      exact sum_prod_ite_all (fun (_ : A) t => w t) (P y)

/- The source's leaf elimination bound for the star witnesses selected above. -/
theorem probability_star_le (A : Finset I) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) (ω : ℝ) (hω : 0 ≤ ω)
    (P : ({i : I // i ∉ A} → X) → A → X → Prop)
    (hP : ∀ y i, (∑ t : X, if P y i t then w t else 0) ≤ ω) :
    probability w (fun x : I → X => ∀ i : A, P (fun j => x j) i (x i)) ≤ ω^A.card := by
  rw [probability_star_factorization]
  have hprod : ∀ y : {i : I // i ∉ A} → X,
      (∏ i : A, ∑ t : X, if P y i t then w t else 0) ≤ ω^A.card := by
    intro y
    calc
      _ ≤ ∏ _i : A, ω := by
        apply Finset.prod_le_prod₀
        · intro i _; exact Finset.sum_nonneg (fun t _ => by split_ifs; exact hw t; exact le_rfl)
        · intro i _; exact hP y i
      _ = _ := by simp
  calc
    _ ≤ ∑ y : {i : I // i ∉ A} → X, (∏ j, w (y j)) * ω^A.card := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hprod y) (Finset.prod_nonneg (fun j _ => hw _))
    _ ≤ 1 * ω^A.card := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hω _)
      rw [← Fintype.prod_sum]
      simp [hs]
    _ = ω^A.card := one_mul _

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I]

/- A finite directed star system. Distinct tails are indexed by the subtype A;
the parent lies outside A or is a hole. -/
def starSystem (R : I → I → Prop) (T : I → H → Prop)
    (A : Finset I) (p : A → I ⊕ H) : Prop :=
  ∀ i : A, match p i with
    | .inl j => j ∉ A ∧ R i j
    | .inr l => T i l

/- The witness can be trimmed to any requested number of tails up to half
(rounded up) of the number of covered particles. -/
theorem exists_star_system (R : I → I → Prop) (T : I → H → Prop)
    (hsym : ∀ ⦃left right⦄, R left right → R right left) (hirr : ∀ vertex, ¬ R vertex vertex) (j : ℕ)
    (hj : j ≤ ((covered R T).card + 1)/2) :
    ∃ A : Finset I, A.card = j ∧ ∃ p : A → I ⊕ H, starSystem R T A p := by
  obtain ⟨B,_,hB,hpar⟩ := exists_star_forest R T hsym hirr
  have hjB : j ≤ B.card := by omega
  obtain ⟨A,hAB,hAc⟩ := Finset.exists_subset_card_eq hjB
  have hp : ∀ i : A, ∃ r : I ⊕ H, match r with
      | .inl l => l ∉ A ∧ R i l
      | .inr l => T i l := by
    intro i
    rcases hpar i (hAB i.property) with ⟨l,hl,hR⟩ | ⟨l,hT⟩
    · exact ⟨.inl l, fun hm => hl (hAB hm), hR⟩
    · exact ⟨.inr l, hT⟩
  choose p hp using hp
  exact ⟨A,hAc,p,hp⟩

variable {X : Type*} [Fintype X]

/- The sharing event of one directed system under the full independent data.
Forbidden parent choices simply give an empty event. -/
def starEvent (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H) (x : I → X) : Prop :=
  starSystem (fun i j => S (x i) (x j)) (fun i l => S (x i) (holes l)) A p

/- A tail predicate with the values at all its possible roots fixed. -/
def rootPredicate (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H)
    (y : {i : I // i ∉ A} → X) (i : A) (t : X) : Prop :=
  match p i with
  | .inl j => if hj : j ∉ A then S t (y ⟨j,hj⟩) else False
  | .inr l => S t (holes l)

omit [Fintype I] [Fintype X] in
theorem starEvent_iff_root (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H) (x : I → X) :
    starEvent S holes A p x ↔
      ∀ i : A, rootPredicate S holes A p (fun j => x j) i (x i) := by
  unfold starEvent starSystem rootPredicate
  apply forall_congr'
  intro i
  cases p i with
  | inl j => by_cases hj : j ∉ A <;> simp [hj]
  | inr l => rfl

/- For every particular system of j distinct tails toward non-tail parents,
the sharing probability is at most ω^j, with no layer independence premise. -/
theorem probability_starEvent_le (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω) :
    probability w (starEvent S holes A p) ≤ ω^A.card := by
  have he : starEvent S holes A p =
      (fun x : I → X => ∀ i : A, rootPredicate S holes A p (fun j => x j) i (x i)) := by
    funext x
    exact propext (starEvent_iff_root S holes A p x)
  rw [he]
  apply probability_star_le A w hw hs ω hω
  intro y i
  unfold rootPredicate
  cases hp : p i with
  | inl j =>
    by_cases hj : j ∉ A
    · simpa only [dite_eq_left hj] using hS (y ⟨j,hj⟩)
    · simpa [hj] using hω
  | inr l => exact hS (holes l)

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

omit [DecidableEq I] [Fintype X] in
theorem productMass_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x : I → X) :
    0 ≤ productMass w x := Finset.prod_nonneg (fun i _ => hw (x i))

theorem probability_mono (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {P Q : (I → X) → Prop} (hPQ : ∀ x, P x → Q x) :
    probability w P ≤ probability w Q := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x
  · simp only [ite_eq_left hp, ite_eq_left (hPQ x hp)]
    exact le_rfl
  · simp only [ite_eq_right hp]
    split_ifs
    · exact productMass_nonneg w hw x
    · exact le_rfl

theorem probability_exists_le {J : Type*} [Fintype J]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (P : J → (I → X) → Prop) :
    probability w (fun x => ∃ j, P j x) ≤ ∑ j, probability w (P j) := by
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hpj : ∀ j, 0 ≤ (if P j x then productMass w x else 0) := by
    intro j; split_ifs; exact productMass_nonneg w hw x; exact le_rfl
  by_cases he : ∃ j, P j x
  · obtain ⟨j,hj⟩ := he
    rw [ite_eq_left ⟨j,hj⟩]
    have hh := Finset.single_le_sum (fun j _ => hpj j) (Finset.mem_univ j)
    simpa only [ite_eq_left hj] using hh
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun j _ => hpj j)

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]

/- Data encoding exactly j distinct tails and one arbitrary parent per tail.
The sub-event enforces the star/root restrictions. -/
abbrev Witness (I H : Type*) [Fintype I] (j : ℕ) :=
  Σ A : {A : Finset I // A.card = j}, (A.val → I ⊕ H)

theorem card_witness_le (j : ℕ) :
    Fintype.card (Witness I H j) ≤
      2^Fintype.card I * (Fintype.card I + Fintype.card H)^j := by
  have hc : ∀ A : {A : Finset I // A.card = j},
      Fintype.card (A.val → I ⊕ H) = (Fintype.card I + Fintype.card H)^j := by
    intro A
    simp [A.property]
  have hA : Fintype.card {A : Finset I // A.card = j} ≤ 2^Fintype.card I := by
    simpa using Fintype.card_le_of_injective
      (fun A : {A : Finset I // A.card = j} => A.val) Subtype.val_injective
  calc
    _ = Fintype.card {A : Finset I // A.card = j} *
        (Fintype.card I + Fintype.card H)^j := by
      rw [Fintype.card_sigma]
      simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hA

variable {X : Type*} [Fintype X]

/- Covered particles for the actual symmetric sharing relation on path data. -/
def sharingCoverage (S : X → X → Prop) (holes : H → X) (x : I → X) : Finset I :=
  covered (fun i j => i ≠ j ∧ S (x i) (x j)) (fun i l => S (x i) (holes l))

omit [Fintype H] [Fintype X] in
theorem sharingCoverage_witness (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (x : I → X) (n : ℕ)
    (hn : n ≤ (sharingCoverage S holes x).card) :
    ∃ W : Witness I H ((n+1)/2), starEvent S holes W.1.val W.2 x := by
  let R : I → I → Prop := fun i j => i ≠ j ∧ S (x i) (x j)
  let T : I → H → Prop := fun i l => S (x i) (holes l)
  have hsym : ∀ ⦃left right⦄, R left right → R right left := fun i j h => ⟨h.1.symm, hSsym h.2⟩
  have hirr : ∀ vertex, ¬ R vertex vertex := fun i h => h.1 rfl
  have hc : n ≤ (covered R T).card := hn
  obtain ⟨A,hAc,p,hp⟩ := exists_star_system R T hsym hirr ((n+1)/2) (by omega)
  refine ⟨⟨⟨A,hAc⟩,p⟩,?_⟩
  intro i
  have hi := hp i
  cases hpi : p i with
  | inl j =>
    simp only [hpi] at hi ⊢
    exact ⟨hi.1,hi.2.2⟩
  | inr l =>
    simpa only [hpi] using hi

/- Source coverage bound with the slightly stronger integer exponent ceil(n/2).
There is no independence assumption between different path layers. -/
theorem probability_coverage_le_nat (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω) (n : ℕ) :
    probability w (fun x : I → X => n ≤ (sharingCoverage S holes x).card) ≤
      (2 : ℝ)^Fintype.card I *
        (((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω)^((n+1)/2) := by
  let j := (n+1)/2
  let P : Witness I H j → (I → X) → Prop :=
    fun W => starEvent S holes W.1.val W.2
  calc
    _ ≤ probability w (fun x : I → X => ∃ W : Witness I H j, P W x) :=
      probability_mono w hw (fun x hx => sharingCoverage_witness S hSsym holes x n hx)
    _ ≤ ∑ W : Witness I H j, probability w (P W) := probability_exists_le w hw P
    _ ≤ ∑ _W : Witness I H j, ω^j := by
      apply Finset.sum_le_sum
      intro W _
      simpa only [W.1.property] using
        probability_starEvent_le S holes W.1.val W.2 w hw hs ω hω hS
    _ = (Fintype.card (Witness I H j) : ℝ) * ω^j := by simp
    _ ≤ (2 : ℝ)^Fintype.card I *
        (((Fintype.card I + Fintype.card H : ℕ) : ℝ)^j) * ω^j := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hω _)
      exact_mod_cast (card_witness_le (I := I) (H := H) j)
    _ = _ := by rw [mul_assoc, ← mul_pow]

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H X : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype X]

/- The literal source's coverage estimate (04:eq9), including zero sharing
rate and zero requested coverage, with the real exponent n/2. -/
theorem probability_coverage_le (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω)
    (hsmall : ((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω ≤ 1) (n : ℕ) :
    probability w (fun x : I → X => n ≤ (sharingCoverage S holes x).card) ≤
      (2 : ℝ)^Fintype.card I *
        ((((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω) ^ ((n : ℝ)/2)) := by
  have hn : n ≤ 2*((n+1)/2) := by omega
  have hn' : (n : ℝ) ≤ 2 * (((n+1)/2 : ℕ) : ℝ) := by exact_mod_cast hn
  have hr :
      ((((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω) ^ ((n+1)/2 : ℕ)) ≤
      ((((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω) ^ ((n : ℝ)/2)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge' (by positivity) hsmall (by positivity) (by linarith)
  exact (probability_coverage_le_nat S hSsym holes w hw hs ω hω hS n).trans
    (mul_le_mul_of_nonneg_left hr (by positivity))

end CoordinateSweeps.Coverage
end
end
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/- Independent occupancy of a fixed measurable subset. The set is fixed
BEFORE taking probability, exactly as required in source04:eq12. -/
theorem probability_many_hits_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (P : X → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hP : (∑ x, if P x then w x else 0) ≤ p) (n : ℕ) :
    probability w (fun x : I → X => n ≤ (Finset.univ.filter (fun i => P (x i))).card) ≤
      (2 : ℝ)^Fintype.card I * p^n := by
  let W := {A : Finset I // A.card = n}
  have hcover (x : I → X) (hx : n ≤ (Finset.univ.filter (fun i => P (x i))).card) :
      ∃ A : W, ∀ i : A.val, P (x i) := by
    obtain ⟨A,hA,hAc⟩ := Finset.exists_subset_card_eq hx
    exact ⟨⟨A,hAc⟩, fun i => (Finset.mem_filter.mp (hA i.property)).2⟩
  have hprob (A : W) : probability w (fun x : I → X => ∀ i : A.val, P (x i)) ≤ p^n := by
    simpa only [A.property] using probability_star_le A.val w hw hs p hp
      (fun _ _ x => P x) (fun _ _ => hP)
  calc
    _ ≤ probability w (fun x : I → X => ∃ A : W, ∀ i : A.val, P (x i)) :=
      probability_mono w hw hcover
    _ ≤ ∑ A : W, probability w (fun x : I → X => ∀ i : A.val, P (x i)) :=
      probability_exists_le w hw _
    _ ≤ ∑ _A : W, p^n := Finset.sum_le_sum (fun A _ => hprob A)
    _ = (Fintype.card W : ℝ)*p^n := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
      exact_mod_cast (Fintype.card_subtype_le (fun A : Finset I => A.card = n)).trans_eq
        (Fintype.card_finset (α := I))

theorem probability_many_hits_le_rpow (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (P : X → Prop) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hP : (∑ x, if P x then w x else 0) ≤ p) (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X => u ≤ ((Finset.univ.filter (fun i => P (x i))).card : ℝ)) ≤
      (2 : ℝ)^Fintype.card I * p^u := by
  have he := probability_many_hits_le (I := I) w hw hs P p hp hP ⌈u⌉₊
  have hconv : (fun x : I → X => u ≤ ((Finset.univ.filter (fun i => P (x i))).card : ℝ)) =
      (fun x => ⌈u⌉₊ ≤ (Finset.univ.filter (fun i => P (x i))).card) := by
    funext x
    exact propext Nat.ceil_le.symm
  rw [hconv]
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge' hp hp1 hu (Nat.le_ceil u)

/- Canonical padded enumeration encodes a subset of size at most r in r
optional entries. This supplies the source's (number-of-lines+1)^r union count. -/
def encodeSmallSet {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ)
    (S : {S : Finset L // S.card ≤ r}) : Fin r → Option L := fun i =>
  if hi : i.val < S.val.card then
    some (((Fintype.equivFinOfCardEq (Fintype.card_coe S.val)).symm ⟨i.val,hi⟩).val)
  else none

theorem mem_iff_encodeSmallSet {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ)
    (S : {S : Finset L // S.card ≤ r}) (a : L) :
    a ∈ S.val ↔ ∃ i, encodeSmallSet r S i = some a := by
  constructor
  · intro ha
    let e := Fintype.equivFinOfCardEq (Fintype.card_coe S.val)
    let j := e ⟨a,ha⟩
    let i : Fin r := ⟨j.val, lt_of_lt_of_le j.isLt S.property⟩
    refine ⟨i, ?_⟩
    simp only [encodeSmallSet, i, dite_eq_left j.isLt]
    change some ((e.symm j).val) = some a
    simp [j]
  · rintro ⟨i,hi⟩
    unfold encodeSmallSet at hi
    split_ifs at hi with hlt
    · have he := Option.some.inj hi
      rw [← he]
      exact ((Fintype.equivFinOfCardEq (Fintype.card_coe S.val)).symm ⟨i.val,hlt⟩).property

theorem encodeSmallSet_injective {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ) :
    Function.Injective (encodeSmallSet (L := L) r) := by
  intro S T he
  apply Subtype.ext
  ext a
  rw [mem_iff_encodeSmallSet, mem_iff_encodeSmallSet]
  simp only [he]

theorem card_smallSets_le {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ) :
    Fintype.card {S : Finset L // S.card ≤ r} ≤ (Fintype.card L+1)^r := by
  have he := Fintype.card_le_of_injective _ (encodeSmallSet_injective (L := L) r)
  simpa using he

/- Uniform union bound over small sets of lines, without conditioning on a
set chosen from the particle array. -/
theorem probability_smallSet_hits_le {L : Type*} [Fintype L] [DecidableEq L]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) (line : X → L)
    (r : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hprob : ∀ S : Finset L, S.card ≤ r → (∑ x, if line x ∈ S then w x else 0) ≤ p)
    (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X => ∃ S : Finset L, S.card ≤ r ∧
      u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S)).card : ℝ)) ≤
      ((Fintype.card L+1 : ℕ) : ℝ)^r * (2 : ℝ)^Fintype.card I * p^u := by
  let W := {S : Finset L // S.card ≤ r}
  have he (x : I → X) :
      (∃ S : Finset L, S.card ≤ r ∧ u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S)).card : ℝ)) ↔
      ∃ S : W, u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S.val)).card : ℝ) := by
    constructor
    · rintro ⟨S,hS,hc⟩; exact ⟨⟨S,hS⟩,hc⟩
    · rintro ⟨S,hc⟩; exact ⟨S.val,S.property,hc⟩
  simp only [he]
  calc
    _ ≤ ∑ S : W, probability w (fun x : I → X =>
          u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S.val)).card : ℝ)) :=
      probability_exists_le w hw _
    _ ≤ ∑ _S : W, (2 : ℝ)^Fintype.card I*p^u := by
      apply Finset.sum_le_sum
      intro S _
      convert probability_many_hits_le_rpow (I := I) w hw hs (fun x => line x ∈ S.val) p hp hp1
        (by convert hprob S.val S.property using 1; congr!) u hu using 1
      congr!
    _ = (Fintype.card W : ℝ)*((2 : ℝ)^Fintype.card I*p^u) := by simp
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_smallSets_le (L := L) r

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X L : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype L] [DecidableEq L]

omit [Fintype L] in
theorem sum_lineSet (w : X → ℝ) (line : X → L) (S : Finset L) :
    (∑ x, if line x ∈ S then w x else 0) =
      ∑ l ∈ S, ∑ x, if line x = l then w x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [Fintype L] in
theorem probability_lineSet_le (w : X → ℝ) (line : X → L) (S : Finset L)
    (δ : ℝ) (hδ : ∀ l, (∑ x, if line x = l then w x else 0) ≤ δ) :
    (∑ x, if line x ∈ S then w x else 0) ≤ (S.card : ℝ)*δ := by
  rw [sum_lineSet]
  calc
    _ ≤ ∑ _l ∈ S, δ := Finset.sum_le_sum (fun l _ => hδ l)
    _ = _ := by simp

def heavySet (t : L → ℕ) (v : ℝ) : Finset L := Finset.univ.filter (fun l => v < t l)

omit [DecidableEq L] in
theorem heavySet_card_mul_le (t : L → ℕ) (v : ℝ) :
    ((heavySet t v).card : ℝ)*v ≤ ∑ l, (t l : ℝ) := by
  calc
    _ = ∑ _l ∈ heavySet t v, v := by simp
    _ ≤ ∑ l ∈ heavySet t v, (t l : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      exact (Finset.mem_filter.mp hl).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.cast_nonneg _)

omit [DecidableEq L] in
theorem heavySet_card_le_floor (t : L → ℕ) {v : ℝ} (hv : 0 < v) :
    (heavySet t v).card ≤ ⌊(∑ l, (t l : ℝ))/v⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ hv).mpr
  exact heavySet_card_mul_le t v

def occupancy (line : X → L) (x : I → X) (l : L) : ℕ :=
  (Finset.univ.filter (fun i => line (x i) = l)).card

omit [DecidableEq I] [Fintype X] in
theorem sum_occupancy (line : X → L) (x : I → X) :
    ∑ l, occupancy line x l = Fintype.card I := by
  unfold occupancy
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/- Heavy line sets are small by deterministic occupancy counting. -/
omit [DecidableEq I] [Fintype X] in
theorem heavy_occupancy_card_le (line : X → L) (x : I → X) {v : ℝ} (hv : 0 < v) :
    (heavySet (occupancy line x) v).card ≤ ⌊(Fintype.card I : ℝ)/v⌋₊ := by
  have hh := heavySet_card_le_floor (occupancy line x) hv
  simpa only [← Nat.cast_sum, sum_occupancy] using hh

/- Probability of many particles in particle-heavy lines. The random line
set is controlled by a union over ALL small deterministic sets. -/
theorem probability_heavy_occupancy_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (line : X → L) {v : ℝ} (hv : 0 < v)
    (p δ : ℝ) (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hline : ∀ l, (∑ x, if line x = l then w x else 0) ≤ δ)
    (hrp : (⌊(Fintype.card I : ℝ)/v⌋₊ : ℝ)*δ ≤ p)
    (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X =>
      u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ heavySet (occupancy line x) v)).card : ℝ)) ≤
      ((Fintype.card L+1 : ℕ) : ℝ)^⌊(Fintype.card I : ℝ)/v⌋₊ *
        (2 : ℝ)^Fintype.card I * p^u := by
  apply le_trans (probability_mono w hw (Q := fun x : I → X =>
    ∃ S : Finset L, S.card ≤ ⌊(Fintype.card I : ℝ)/v⌋₊ ∧
      u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S)).card : ℝ)) (fun x hx =>
    ⟨heavySet (occupancy line x) v, heavy_occupancy_card_le line x hv, hx⟩))
  apply probability_smallSet_hits_le w hw hs line _ p hp hp1 _ u hu
  intro S hS
  have hle := probability_lineSet_le w line S δ hline
  apply hle.trans
  apply le_trans _ hrp
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hδ

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H X : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype X]

theorem probability_or_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (P Q : (I → X) → Prop) :
    probability w (fun x => P x ∨ Q x) ≤ probability w P + probability w Q := by
  simp only [probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hx := productMass_nonneg w hw x
  split_ifs <;> simp_all

theorem probability_coverage_le_real (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω)
    (hsmall : ((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω ≤ 1)
    (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X => u ≤ ((sharingCoverage S holes x).card : ℝ)) ≤
      (2 : ℝ)^Fintype.card I *
      ((((Fintype.card I + Fintype.card H : ℕ) : ℝ)*ω)^(u/2)) := by
  have hc : (fun x : I → X => u ≤ ((sharingCoverage S holes x).card : ℝ)) =
      (fun x => ⌈u⌉₊ ≤ (sharingCoverage S holes x).card) := by
    funext x
    exact propext Nat.ceil_le.symm
  rw [hc]
  apply (probability_coverage_le S hSsym holes w hw hs ω hω hS hsmall ⌈u⌉₊).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_ge' (by positivity) hsmall (by positivity)
    (div_le_div_of_nonneg_right (Nat.le_ceil u) (by norm_num))
end CoordinateSweeps.Coverage

end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
