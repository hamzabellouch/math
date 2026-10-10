import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace IndependentCoordinates

/-- The uniform average on a finite type, with value zero on an empty type. -/
def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α


/-- Uniform finite averages are unchanged by relabeling. -/
theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, e.sum_comp, Fintype.card_congr e]

/-- Independent coordinates factor the average of a product. -/
theorem average_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) :
    average (fun x : ∀ i, α i => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  classical
  simp only [average, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]
  congr 1
  exact (Fintype.prod_sum f).symm

/-- Reorganize coordinates into the fibers of a grouping function. -/
def fiberAssignmentEquiv {σ ι α : Type*} (group : σ → ι) :
    (σ → α) ≃ (∀ i, {s // group s = i} → α) :=
  (Equiv.piCongrLeft (fun _ : σ => α) (Equiv.sigmaFiberEquiv group)).symm.trans
    (Equiv.piCurry (fun _ _ => α))

@[simp] theorem fiberAssignmentEquiv_apply {σ ι α : Type*} (group : σ → ι)
    (x : σ → α) (i : ι) (s : {s // group s = i}) :
    fiberAssignmentEquiv group x i s = x s := rfl

/-- Factors on disjoint groups of coordinates have independent uniform averages.
An unused group can be included with its factor set equal to one. -/
theorem average_grouped_prod {σ ι α : Type*}
    [Fintype σ] [Fintype ι] [Fintype α] [DecidableEq σ] [DecidableEq ι]
    (group : σ → ι) (f : ∀ i, ({s // group s = i} → α) → ℝ) :
    average (fun x : σ → α => ∏ i, f i (fun s => x s)) =
      ∏ i, average (f i) := by
  calc
    _ = average (fun x : ∀ i, ({s // group s = i} → α) => ∏ i, f i (x i)) :=
      average_equiv (fiberAssignmentEquiv group) _
    _ = _ := average_prod f

/-- One independent pair of uniform labels agrees with probability `1 / card α`. -/
theorem average_pair_eq {α : Type*} [Fintype α] [DecidableEq α] :
    average (fun x : α × α => if x.1 = x.2 then (1 : ℝ) else 0) =
      (Fintype.card α : ℝ)⁻¹ := by
  rw [average, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod, Nat.cast_mul]
  by_cases h : (Fintype.card α : ℝ) = 0
  · simp [h]
  · field_simp

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average, Fintype.card_ne_zero]

theorem average_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp [average, ← Finset.mul_sum, mul_div_assoc]

/-- The indicator that two labels agree. -/
def pairEq {α : Type*} [DecidableEq α] (x : α × α) : ℝ :=
  if x.1 = x.2 then 1 else 0

/-- Simultaneous agreement of `card κ` independent label pairs. -/
def allPairsEq {κ α : Type*} [Fintype κ] [DecidableEq α]
    (x : κ → α × α) : ℝ := ∏ i, pairEq (x i)

theorem average_allPairsEq {κ α : Type*} [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] :
    average (allPairsEq (κ := κ) (α := α)) =
      (Fintype.card α : ℝ)⁻¹ ^ Fintype.card κ := by
  rw [show allPairsEq (κ := κ) (α := α) =
    (fun x : κ → α × α => ∏ i, pairEq (x i)) from rfl, average_prod]
  simp only [Finset.prod_const, Finset.card_univ]
  exact congrArg (fun z : ℝ => z ^ Fintype.card κ) (average_pair_eq (α := α))

theorem average_equality_correction {κ α : Type*} [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] [Nonempty α] (c : ℝ) :
    average (fun x : κ → α × α => 1 + c * allPairsEq x) =
      1 + c * (Fintype.card α : ℝ)⁻¹ ^ Fintype.card κ := by
  rw [average_add, average_const, average_const_mul, average_allPairsEq]

/-- The precise independence identity used for nonadjacent derivative layers.
The fibers of `group` are the disjoint sets of free endpoints of those layers. -/
theorem average_grouped_equality_corrections {σ ι α : Type*}
    [Fintype σ] [Fintype ι] [Fintype α]
    [DecidableEq σ] [DecidableEq ι] [DecidableEq α] [Nonempty α]
    (group : σ → ι) (c : ι → ℝ) :
    average (fun x : σ → α × α =>
      ∏ i, (1 + c i * allPairsEq (fun s : {s // group s = i} => x s))) =
    ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^ Fintype.card {s // group s = i}) := by
  rw [average_grouped_prod group
    (fun i x => 1 + c i * allPairsEq x)]
  congr 1
  ext i
  exact average_equality_correction (c i)

/-- Coordinates assigned to `none` are unused and integrate out. -/
theorem average_selected_grouped_prod {σ ι α : Type*}
    [Fintype σ] [Fintype ι] [Fintype α] [Nonempty α]
    [DecidableEq σ] [DecidableEq ι]
    (group : σ → Option ι)
    (f : ∀ i, ({s // group s = some i} → α) → ℝ) :
    average (fun x : σ → α => ∏ i, f i (fun s => x s)) =
      ∏ i, average (f i) := by
  let F : ∀ o : Option ι, ({s // group s = o} → α) → ℝ := fun o =>
    match o with
    | none => fun _ => 1
    | some i => f i
  have h := average_grouped_prod group F
  simpa only [Fintype.prod_option, F, one_mul, average_const] using h

/-- Equality corrections for selected disjoint endpoint groups.  Other vertices
may be assigned to `none`, and their choices do not affect the expectation. -/
theorem average_selected_equality_corrections {σ ι α : Type*}
    [Fintype σ] [Fintype ι] [Fintype α]
    [DecidableEq σ] [DecidableEq ι] [DecidableEq α] [Nonempty α]
    (group : σ → Option ι) (c : ι → ℝ) :
    average (fun x : σ → α × α =>
      ∏ i, (1 + c i * allPairsEq (fun s : {s // group s = some i} => x s))) =
    ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^
      Fintype.card {s // group s = some i}) := by
  rw [average_selected_grouped_prod group
    (fun i x => 1 + c i * allPairsEq x)]
  congr 1
  ext i
  exact average_equality_correction (c i)

/-- Extra independent coordinates that do not appear in the integrand cancel. -/
theorem average_ignore_right {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    average (fun x : α × β => f x.1) = average f := by
  rw [average, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul, average]
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hα : (Fintype.card α : ℝ) = 0
  · simp [hα]
  · field_simp

/-- Split all assignments into their values on an embedded coordinate set and
on its complement. -/
def restrictAssignmentEquiv {σ τ α : Type*} (j : τ → σ)
    (hj : Function.Injective j) :
    (σ → α) ≃ (τ → α) × ({s // s ∉ Set.range j} → α) := by
  classical
  let e : τ ⊕ {s // s ∉ Set.range j} ≃ σ :=
    ((Equiv.ofInjective j hj).sumCongr (Equiv.refl _)).trans
      (Equiv.sumCompl (fun s => s ∈ Set.range j))
  exact (Equiv.piCongrLeft (fun _ : σ => α) e).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ => α))

@[simp] theorem restrictAssignmentEquiv_fst {σ τ α : Type*} (j : τ → σ)
    (hj : Function.Injective j) (x : σ → α) (t : τ) :
    (restrictAssignmentEquiv j hj x).1 t = x (j t) := rfl

/-- Uniform assignments restrict uniformly to any subset of coordinates. -/
theorem average_precomp_injective {σ τ α : Type*}
    [Fintype σ] [Fintype τ] [Fintype α] [Nonempty α]
    [DecidableEq σ] [DecidableEq τ]
    (j : τ → σ) (hj : Function.Injective j) (f : (τ → α) → ℝ) :
    average (fun x : σ → α => f (fun t => x (j t))) = average f := by
  classical
  calc
    _ = average (fun x : (τ → α) × ({s // s ∉ Set.range j} → α) => f x.1) :=
      average_equiv (restrictAssignmentEquiv j hj) _
    _ = _ := average_ignore_right f

/-- A sigma-indexed family of labels is the product of its fiber families. -/
theorem average_sigma_prod {ι α : Type*} {κ : ι → Type*}
    [Fintype ι] [Fintype α] [∀ i, Fintype (κ i)]
    [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (f : ∀ i, (κ i → α) → ℝ) :
    average (fun x : (Σ i, κ i) → α => ∏ i, f i (fun t => x ⟨i, t⟩)) =
      ∏ i, average (f i) := by
  let e := Equiv.piCurry (α := ι) (β := κ) (fun _ _ => α)
  have h := average_equiv e (fun x : ∀ i, κ i → α => ∏ i, f i (x i))
  change average (fun x : (Σ i, κ i) → α => ∏ i, f i (fun t => x ⟨i, t⟩)) = _ at h
  exact h.trans (average_prod f)

/-- Finite factors on an injectively embedded disjoint family of coordinates
factor under uniform averaging. -/
theorem average_embedded_prod {σ ι α : Type*} {κ : ι → Type*}
    [Fintype σ] [Fintype ι] [Fintype α] [∀ i, Fintype (κ i)] [Nonempty α]
    [DecidableEq σ] [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (j : ∀ i, κ i → σ) (hj : Function.Injective (Sigma.uncurry j))
    (f : ∀ i, (κ i → α) → ℝ) :
    average (fun x : σ → α => ∏ i, f i (fun t => x (j i t))) =
      ∏ i, average (f i) := by
  have h := average_precomp_injective (Sigma.uncurry j) hj
    (fun x : (Σ i, κ i) → α => ∏ i, f i (fun t => x ⟨i, t⟩))
  exact h.trans (average_sigma_prod f)

/-- Pairwise disjoint subsets give an injective family of coordinate inclusions. -/
theorem sigma_val_injective {σ ι : Type*} (s : ι → Finset σ)
    (hs : Pairwise (fun i j => Disjoint (s i) (s j))) :
    Function.Injective (fun x : Σ i, s i => (x.2 : σ)) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  change (x : σ) = (y : σ) at hxy
  have hij : i = j := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hs hne)) x.property (hxy.symm ▸ y.property)
  subst j
  have h : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Factors depending on pairwise disjoint finite coordinate sets are independent. -/
theorem average_disjoint_finset_prod {σ ι α : Type*}
    [Fintype σ] [Fintype ι] [Fintype α] [Nonempty α]
    [DecidableEq σ] [DecidableEq ι]
    (s : ι → Finset σ) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : ∀ i, (s i → α) → ℝ) :
    average (fun x : σ → α => ∏ i, f i (fun t => x t)) =
      ∏ i, average (f i) := by
  exact average_embedded_prod (fun i (t : s i) => (t : σ))
    (sigma_val_injective s hs) f

/-- The endpoint-coincidence average for pairwise disjoint free-endpoint sets. -/
theorem average_disjoint_equality_corrections {σ ι α : Type*}
    [Fintype σ] [Fintype ι] [Fintype α]
    [DecidableEq σ] [DecidableEq ι] [DecidableEq α] [Nonempty α]
    (s : ι → Finset σ) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (c : ι → ℝ) :
    average (fun x : σ → α × α =>
      ∏ i, (1 + c i * allPairsEq (fun t : s i => x t))) =
    ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^ (s i).card) := by
  rw [average_disjoint_finset_prod s hs
    (fun i x => 1 + c i * allPairsEq x)]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Fintype.card_coe] using
    (average_equality_correction (κ := s i) (α := α) (c i))

/-- Dependent-coordinate version of restriction to an embedded coordinate set. -/
def restrictDependentAssignmentEquiv {σ τ : Type*} (β : σ → Type*)
    (j : τ → σ) (hj : Function.Injective j) :
    (∀ s, β s) ≃ (∀ t, β (j t)) × (∀ s : {s // s ∉ Set.range j}, β s) := by
  classical
  let e : τ ⊕ {s // s ∉ Set.range j} ≃ σ :=
    ((Equiv.ofInjective j hj).sumCongr (Equiv.refl _)).trans
      (Equiv.sumCompl (fun s => s ∈ Set.range j))
  exact (Equiv.piCongrLeft β e).symm.trans
    (Equiv.sumPiEquivProdPi (fun z => β (e z)))

@[simp] theorem restrictDependentAssignmentEquiv_fst {σ τ : Type*}
    (β : σ → Type*) (j : τ → σ) (hj : Function.Injective j)
    (x : ∀ s, β s) (t : τ) :
    (restrictDependentAssignmentEquiv β j hj x).1 t = x (j t) := rfl

/-- Marginals of a uniform finite product are uniform, allowing different
coordinate types at different vertices. -/
theorem average_precomp_injective_dependent {σ τ : Type*} {β : σ → Type*}
    [Fintype σ] [Fintype τ] [∀ s, Fintype (β s)] [∀ s, Nonempty (β s)]
    [DecidableEq σ] [DecidableEq τ]
    (j : τ → σ) (hj : Function.Injective j) (f : (∀ t, β (j t)) → ℝ) :
    average (fun x : ∀ s, β s => f (fun t => x (j t))) = average f := by
  classical
  calc
    _ = average (fun x : (∀ t, β (j t)) ×
        (∀ s : {s // s ∉ Set.range j}, β s) => f x.1) :=
      average_equiv (restrictDependentAssignmentEquiv β j hj) _
    _ = _ := average_ignore_right f

theorem average_sigma_prod_dependent {ι : Type*} {κ : ι → Type*}
    {β : (Σ i, κ i) → Type*}
    [Fintype ι] [∀ i, Fintype (κ i)] [∀ s, Fintype (β s)]
    [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (f : ∀ i, (∀ t : κ i, β ⟨i,t⟩) → ℝ) :
    average (fun x : ∀ s, β s => ∏ i, f i (fun t => x ⟨i,t⟩)) =
      ∏ i, average (f i) := by
  let e := Equiv.piCurry (fun i (t : κ i) => β ⟨i,t⟩)
  have h := average_equiv e (fun x : ∀ i, ∀ t : κ i, β ⟨i,t⟩ => ∏ i, f i (x i))
  change average (fun x : ∀ s, β s => ∏ i, f i (fun t => x ⟨i,t⟩)) = _ at h
  exact h.trans (average_prod f)

theorem average_embedded_prod_dependent {σ ι : Type*} {κ : ι → Type*}
    {β : σ → Type*}
    [Fintype σ] [Fintype ι] [∀ i, Fintype (κ i)]
    [∀ s, Fintype (β s)] [∀ s, Nonempty (β s)]
    [DecidableEq σ] [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (j : ∀ i, κ i → σ) (hj : Function.Injective (Sigma.uncurry j))
    (f : ∀ i, (∀ t : κ i, β (j i t)) → ℝ) :
    average (fun x : ∀ s, β s => ∏ i, f i (fun t => x (j i t))) =
      ∏ i, average (f i) := by
  have h := average_precomp_injective_dependent (β := β) (Sigma.uncurry j) hj
    (fun x : ∀ s : Σ i, κ i, β (j s.1 s.2) => ∏ i, f i (fun t => x ⟨i,t⟩))
  exact h.trans (average_sigma_prod_dependent
    (β := fun s : Σ i, κ i => β (j s.1 s.2)) f)

/-- Disjoint coordinate families remain independent when vertex alphabets vary. -/
theorem average_disjoint_finset_prod_dependent {σ ι : Type*} {β : σ → Type*}
    [Fintype σ] [Fintype ι] [∀ s, Fintype (β s)] [∀ s, Nonempty (β s)]
    [DecidableEq σ] [DecidableEq ι]
    (s : ι → Finset σ) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : ∀ i, (∀ t : s i, β t) → ℝ) :
    average (fun x : ∀ s, β s => ∏ i, f i (fun t => x t)) =
      ∏ i, average (f i) := by
  exact average_embedded_prod_dependent (fun i (t : s i) => (t : σ))
    (sigma_val_injective s hs) f

end IndependentCoordinates
end Problem335

end

end OAI
