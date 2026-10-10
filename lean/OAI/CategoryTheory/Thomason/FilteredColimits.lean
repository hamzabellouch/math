import Mathlib
import OAI.CategoryTheory.Thomason.SimplexAtoms

namespace OAI

/-! Filtered Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

variable {K : DirectedComplex.{u}}

def verticalRow (x : Table K) : (p : ℕ) → Bool → K.cylinder.Chain p
  | 0, b => if b then (0, x.row 0 b) else (x.row 0 b, 0)
  | p+1, b => if Even (p+1) then
      (if b then (0, x.row (p+1) b, x.row p b)
        else (x.row (p+1) b, 0, x.row p b))
    else (if b then (x.row (p+1) b, 0, x.row p b)
        else (0, x.row (p+1) b, x.row p b))

lemma verticalRow_boundary (x : Table K) (p : ℕ) (b : Bool) :
    K.cylinder.d p (verticalRow x (p+1) b) =
      verticalRow x p true - verticalRow x p false := by
  cases p with
  | zero =>
    cases b <;> simp [verticalRow, cylinder, cylinderDifferential, x.boundary]
  | succ p =>
    by_cases hp : Even (p+1)
    · have hp' : ¬Even (p+1+1) := by rw [Nat.even_add_one]; exact not_not_intro hp
      have hs : (-1 : ℤ)^(p+1) = 1 := hp.neg_one_pow
      cases b <;>
        simp [verticalRow, hp, hp', cylinder, cylinderDifferential, hs, x.boundary]
    · have hp' : Even (p+1+1) := by rw [Nat.even_add_one]; exact hp
      have hs : (-1 : ℤ)^(p+1) = -1 := (Nat.not_even_iff_odd.mp hp).neg_one_pow
      cases b
      · simp [verticalRow, hp, hp', cylinder, cylinderDifferential, hs, x.boundary]
      · simp [verticalRow, hp, hp', cylinder, cylinderDifferential, hs, x.boundary]
        abel

def verticalTable (x : Table K) : Table K.cylinder where
  row := verticalRow x
  positive p b := by
    cases p with
    | zero => cases b <;> exact ⟨by first | exact x.positive _ _ | exact (K.positive _).zero_mem,
        by first | exact x.positive _ _ | exact (K.positive _).zero_mem⟩
    | succ p =>
      dsimp only [verticalRow]
      split <;> cases b <;> exact ⟨by first | exact x.positive _ _ | exact (K.positive _).zero_mem,
        ⟨by first | exact x.positive _ _ | exact (K.positive _).zero_mem, x.positive _ _⟩⟩
  boundary := verticalRow_boundary x
  augmentation b := by
    cases b <;> simp [verticalRow, cylinder, x.augmentation]
  bounded := by
    obtain ⟨n, hn⟩ := x.bounded
    refine ⟨n+1, ?_⟩
    intro p hp b
    cases p with
    | zero => omega
    | succ p =>
      have hnp : n < p := by omega
      have hnp' : n < p+1 := by omega
      simp [verticalRow, hn p hnp, hn (p+1) hnp']

lemma verticalTable_natural {L : DirectedComplex.{v}} (f : Hom K L) (x : Table K) :
    f.cylinder.nu.map (verticalTable x) = verticalTable (f.nu.map x) := by
  change f.cylinder.table (verticalTable x) = verticalTable (f.table x)
  ext p b
  cases p with
  | zero => cases b <;> simp [verticalTable, verticalRow, Hom.table,
      Hom.cylinder, Hom.cylinderMap]
  | succ p =>
    by_cases hp : Even (p+1) <;> cases b <;>
      simp [verticalTable, verticalRow, hp, Hom.table,
        Hom.cylinder, Hom.cylinderMap]

end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [LinearOrder E] [Finite E]

instance finiteWord : Finite (Word E) := by
  classical
  apply Finite.of_injective (fun w : Word E => w.val.toFinset)
  intro x y h
  apply Subtype.ext
  apply x.property.eq_of_mem_iff y.property
  intro a
  have he := Finset.ext_iff.mp h a
  simpa using he

lemma finite_positive_fillings (p : ℕ) (b : Chains E) :
    {c : Chains E | c ∈ grade (p+2) ∧ Positive c ∧ boundary c = b}.Finite := by
  classical
  let S : Set (Chains E) := {c | c ∈ grade (p+2) ∧ Positive c ∧ boundary c = b}
  let f : Chains E → Word E → ℕ := fun c w => (c w).toNat
  have hi : Set.InjOn f S := by
    intro c hc d hd h
    ext w
    have he := congrFun h w
    have hcc := Int.toNat_of_nonneg (hc.2.1 w)
    have hdd := Int.toNat_of_nonneg (hd.2.1 w)
    dsimp only [f] at he
    omega
  have ha : IsAntichain (· ≤ ·) (f '' S) := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hne hle
    have hone : Positive (d-c) := by
      intro w
      change 0 ≤ d w - c w
      have hh := hle w
      have hcc := Int.toNat_of_nonneg (hc.2.1 w)
      have hdd := Int.toNat_of_nonneg (hd.2.1 w)
      dsimp only [f] at hh
      omega
    have hz : d-c = 0 := positive_cycle_zero ((grade (p+2)).sub_mem hd.1 hc.1)
      hone (by rw [map_sub, hd.2.2, hc.2.2, sub_self])
    exact hne (congrArg f (sub_eq_zero.mp hz).symm)
  exact (WellQuasiOrderedLE.finite_of_isAntichain ha).of_finite_image hi

def possibleRows : ℕ → Set (Chains E)
  | 0 => Set.range (fun a : E => bracket [a])
  | p+1 => ⋃ s ∈ possibleRows p, ⋃ t ∈ possibleRows p,
      {c | c ∈ grade (p+2) ∧ Positive c ∧ boundary c = t-s}

lemma possibleRows_finite (p : ℕ) : (possibleRows (E := E) p).Finite := by
  induction p with
  | zero => exact Set.finite_range _
  | succ p ih =>
    exact ih.biUnion (fun s _ => ih.biUnion (fun t _ => finite_positive_fillings p (t-s)))

omit [Finite E] in
lemma table_row_possible (x : Table (complex E)) (p : ℕ) (b : Bool) :
    (x.row p b).val ∈ possibleRows p := by
  induction p generalizing b with
  | zero =>
    obtain ⟨a, ha⟩ := table_zero_row_vertex x b
    exact ⟨a, ha.symm⟩
  | succ p ih =>
    simp only [possibleRows, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨(x.row p false).val, ih false, (x.row p true).val, ih true,
      (x.row (p+1) b).property, x.positive (p+1) b, ?_⟩
    exact congrArg Subtype.val (x.boundary p b)

omit [Finite E] in
lemma grade_eq_zero_of_card_lt [Fintype E] {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) (hk : Fintype.card E < k) : c = 0 := by
  ext w
  change c w = 0
  by_contra hw
  have he := (mem_grade_iff k c).mp hc w hw
  have hb := w.property.nodup.length_le_card
  omega

instance finiteTables : Finite (Table (complex E)) := by
  classical
  let := Fintype.ofFinite E
  let (p : Fin (Fintype.card E+1)) : Finite {c : Chains E // c ∈ possibleRows p.val} :=
    (possibleRows_finite p.val).to_subtype
  let f : Table (complex E) →
      ((p : Fin (Fintype.card E+1)) → Bool → {c : Chains E // c ∈ possibleRows p.val}) :=
    fun x p b => ⟨(x.row p.val b).val, table_row_possible x p.val b⟩
  apply Finite.of_injective f
  intro x y h
  ext p b
  apply Subtype.ext
  by_cases hp : p < Fintype.card E+1
  · exact congrArg (fun c : {c : Chains E // c ∈ possibleRows p} => c.val)
      (congrFun (congrFun h ⟨p, hp⟩) b)
  · have hn : Fintype.card E < p+1 := by omega
    rw [grade_eq_zero_of_card_lt (x.row p b).property hn,
      grade_eq_zero_of_card_lt (y.row p b).property hn]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

instance orientalFiniteCells (m : ℕ) : Finite (Oriental m).Cell :=
  NormalizedChains.finiteTables

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.FilteredTypes

open CategoryTheory Limits ConcreteCategory

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ Type u)

lemma finite_representatives {α : Type v} [Finite α] (x : α → colimit F) :
    ∃ j, ∃ y : α → F.obj j, ∀ a, (colimit.ι F j) (y a) = x a := by
  classical
  let := Fintype.ofFinite α
  choose j y hy using fun a => Types.jointly_surjective_of_isColimit (colimit.isColimit F) (x a)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (a : α) : j a ⟶ k := Classical.choice (hk (Finset.mem_image.mpr ⟨a, by simp, rfl⟩))
  refine ⟨k, fun a => F.map (f a) (y a), ?_⟩
  intro a
  calc
    (colimit.ι F k) (F.map (f a) (y a)) = (colimit.ι F (j a)) (y a) :=
      congr_hom (colimit.w F (f a)) (y a)
    _ = x a := hy a

lemma finite_equalities {α : Type v} [Finite α] {i : J} (x y : α → F.obj i)
    (h : ∀ a, (colimit.ι F i) (x a) = (colimit.ι F i) (y a)) :
    ∃ (j : J) (f : i ⟶ j), ∀ a, F.map f (x a) = F.map f (y a) := by
  classical
  let := Fintype.ofFinite α
  have aux (s : Finset α) : ∃ (j : J) (f : i ⟶ j),
      ∀ a ∈ s, F.map f (x a) = F.map f (y a) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨j, f, hf⟩ := ih
      have he : (colimit.ι F j) (F.map f (x a)) = (colimit.ι F j) (F.map f (y a)) := by
        simpa only [← CategoryTheory.comp_apply, colimit.w] using h a
      obtain ⟨k, g, hg⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit F) _ _).mp he
      refine ⟨k, f ≫ g, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa only [F.map_comp, CategoryTheory.comp_apply] using hg
      · simpa only [F.map_comp, CategoryTheory.comp_apply] using congrArg (F.map g) (hf b hb)
  obtain ⟨j, f, hf⟩ := aux Finset.univ
  exact ⟨j, f, fun a => hf a (by simp)⟩

lemma compare_finite {α : Type v} [Finite α] {i j : J}
    (x : α → F.obj i) (y : α → F.obj j)
    (h : ∀ a, (colimit.ι F i) (x a) = (colimit.ι F j) (y a)) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), ∀ a, F.map f (x a) = F.map g (y a) := by
  let k := IsFiltered.max i j
  let f := IsFiltered.leftToMax i j
  let g := IsFiltered.rightToMax i j
  have he (a : α) : (colimit.ι F k) (F.map f (x a)) =
      (colimit.ι F k) (F.map g (y a)) := by
    calc
      _ = (colimit.ι F i) (x a) := congr_hom (colimit.w F f) (x a)
      _ = (colimit.ι F j) (y a) := h a
      _ = _ := (congr_hom (colimit.w F g) (y a)).symm
  obtain ⟨l, t, ht⟩ := finite_equalities F (fun a => F.map f (x a))
    (fun a => F.map g (y a)) he
  exact ⟨l, f ≫ t, g ≫ t, fun a => by
    simpa only [F.map_comp, CategoryTheory.comp_apply] using ht a⟩

end Thomason.FilteredTypes

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits ConcreteCategory

def cellFunctor : OmegaCategory.{u} ⥤ Type u where
  obj C := C.Cell
  map F := ↾F.map

def cellSourceNat (n : ℕ) : cellFunctor.{u} ⟶ cellFunctor where
  app C := ↾C.source n
  naturality C D F := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (F.map_source n x).symm

def cellTargetNat (n : ℕ) : cellFunctor.{u} ⟶ cellFunctor where
  app C := ↾C.target n
  naturality C D F := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (F.map_target n x).symm

namespace FilteredColimit

variable {J : Type u} [Category.{u} J] (F : J ⥤ OmegaCategory.{u})

abbrev CellDiagram := F ⋙ cellFunctor
abbrev Cell := colimit (CellDiagram F)
abbrev ι (j : J) : (F.obj j).Cell → Cell F := colimit.ι (CellDiagram F) j

def source (n : ℕ) : Cell F → Cell F :=
  colimMap (CategoryTheory.Functor.whiskerLeft F (cellSourceNat n))

def target (n : ℕ) : Cell F → Cell F :=
  colimMap (CategoryTheory.Functor.whiskerLeft F (cellTargetNat n))

@[simp] lemma source_ι (n : ℕ) (j : J) (x : (F.obj j).Cell) :
    source F n (ι F j x) = ι F j ((F.obj j).source n x) :=
  congr_hom (ι_colimMap (CategoryTheory.Functor.whiskerLeft F (cellSourceNat n)) j) x

@[simp] lemma target_ι (n : ℕ) (j : J) (x : (F.obj j).Cell) :
    target F n (ι F j x) = ι F j ((F.obj j).target n x) :=
  congr_hom (ι_colimMap (CategoryTheory.Functor.whiskerLeft F (cellTargetNat n)) j) x

@[simp] lemma ι_map {i j : J} (f : i ⟶ j) (x : (F.obj i).Cell) :
    ι F j ((F.map f).map x) = ι F i x :=
  congr_hom (colimit.w (CellDiagram F) f) x

lemma exists_rep (x : Cell F) : ∃ j, ∃ y : (F.obj j).Cell, ι F j y = x :=
  Types.jointly_surjective_of_isColimit (colimit.isColimit (CellDiagram F)) x

lemma source_source (i j : ℕ) (x : Cell F) :
    source F i (source F j x) = source F (min i j) x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  simp only [source_ι, (F.obj k).source_source]

lemma target_target (i j : ℕ) (x : Cell F) :
    target F i (target F j x) = target F (min i j) x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  simp only [target_ι, (F.obj k).target_target]

lemma source_target (i j : ℕ) (x : Cell F) :
    source F i (target F j x) = if i < j then source F i x else target F j x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  by_cases h : i < j <;> simp only [source_ι, target_ι, (F.obj k).source_target, h, ite_true, ite_false]

lemma target_source (i j : ℕ) (x : Cell F) :
    target F i (source F j x) = if i < j then target F i x else source F j x := by
  obtain ⟨k, y, rfl⟩ := exists_rep F x
  by_cases h : i < j <;> simp only [source_ι, target_ι, (F.obj k).target_source, h, ite_true, ite_false]

lemma finite_dimension (x : Cell F) : ∃ n, source F n x = x := by
  obtain ⟨j, y, rfl⟩ := exists_rep F x
  obtain ⟨n, hn⟩ := (F.obj j).finite_dimension y
  exact ⟨n, by rw [source_ι, hn]⟩

variable [IsFiltered J]

lemma lift_matches {α : Type v} {β : Type w} [Finite α] [Finite β]
    (x : α → Cell F) (s t : β → α) (d : β → ℕ)
    (h : ∀ b, target F (d b) (x (s b)) = source F (d b) (x (t b))) :
    ∃ j, ∃ y : α → (F.obj j).Cell,
      (∀ a, ι F j (y a) = x a) ∧
      (∀ b, (F.obj j).target (d b) (y (s b)) = (F.obj j).source (d b) (y (t b))) := by
  obtain ⟨i, y, hy⟩ := Thomason.FilteredTypes.finite_representatives (CellDiagram F) x
  change α → (F.obj i).Cell at y
  change ∀ a, ι F i (y a) = x a at hy
  have he b : ι F i ((F.obj i).target (d b) (y (s b))) =
      ι F i ((F.obj i).source (d b) (y (t b))) := by
    rw [← target_ι, ← source_ι, hy, hy]
    exact h b
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F)
    (fun b => (F.obj i).target (d b) (y (s b)))
    (fun b => (F.obj i).source (d b) (y (t b))) he
  refine ⟨j, fun a => (F.map f).map (y a), ?_, ?_⟩
  · intro a
    rw [ι_map, hy]
  · intro b
    rw [← (F.map f).map_target, ← (F.map f).map_source]
    exact hf b

lemma lift_pair (k : ℕ) (x y : Cell F) (h : target F k x = source F k y) :
    ∃ j, ∃ a b : (F.obj j).Cell, ι F j a = x ∧ ι F j b = y ∧
      (F.obj j).target k a = (F.obj j).source k b := by
  obtain ⟨j, z, hz, he⟩ := lift_matches F (fun b : Bool => if b then y else x)
    (fun _ : Unit => false) (fun _ : Unit => true) (fun _ => k) (fun _ => h)
  exact ⟨j, z false, z true, hz false, hz true, he ()⟩

structure PairWitness (k : ℕ) (x y : Cell F) where
  stage : J
  left : (F.obj stage).Cell
  right : (F.obj stage).Cell
  left_eq : ι F stage left = x
  right_eq : ι F stage right = y
  matching : (F.obj stage).target k left = (F.obj stage).source k right

noncomputable def pairWitness (k : ℕ) (x y : Cell F)
    (h : target F k x = source F k y) : PairWitness F k x y := by
  have : Nonempty (PairWitness F k x y) := by
    obtain ⟨j, a, b, ha, hb, hab⟩ := lift_pair F k x y h
    exact ⟨⟨j, a, b, ha, hb, hab⟩⟩
  exact Classical.choice this

noncomputable def comp (k : ℕ) (x y : Cell F)
    (h : target F k x = source F k y) : Cell F :=
  let w := pairWitness F k x y h
  ι F w.stage ((F.obj w.stage).comp k w.left w.right w.matching)

lemma comp_ι (k : ℕ) (j : J) (a b : (F.obj j).Cell)
    (h : (F.obj j).target k a = (F.obj j).source k b)
    (h' : target F k (ι F j a) = source F k (ι F j b)) :
    comp F k (ι F j a) (ι F j b) h' = ι F j ((F.obj j).comp k a b h) := by
  let w := pairWitness F k (ι F j a) (ι F j b) h'
  have he (e : Bool) : ι F w.stage (if e then w.right else w.left) =
      ι F j (if e then b else a) := by
    cases e
    · exact w.left_eq
    · exact w.right_eq
  obtain ⟨l, f, g, hfg⟩ := Thomason.FilteredTypes.compare_finite (CellDiagram F)
    (fun e : Bool => if e then w.right else w.left)
    (fun e : Bool => if e then b else a) he
  change ∀ e : Bool, (F.map f).map (if e then w.right else w.left) =
    (F.map g).map (if e then b else a) at hfg
  have hl := hfg false
  have hr := hfg true
  dsimp at hl hr
  change ι F w.stage ((F.obj w.stage).comp k w.left w.right w.matching) = _
  calc
    _ = ι F l ((F.map f).map ((F.obj w.stage).comp k w.left w.right w.matching)) :=
      (ι_map F f _).symm
    _ = ι F l ((F.map g).map ((F.obj j).comp k a b h)) := by
      rw [(F.map f).map_comp k _ _ _ ((F.map f).map_composable w.matching),
        (F.map g).map_comp k _ _ _ ((F.map g).map_composable h)]
      simp only [hl, hr]
    _ = _ := ι_map F g _

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell F)
    (h : target F k x = source F k y) :
    source F i (comp F k x y h) = source F i x := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  rw [comp_ι F k j a b hab, source_ι, source_ι, (F.obj j).source_comp_le i k hik]

lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell F)
    (h : target F k x = source F k y) :
    target F i (comp F k x y h) = target F i y := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  rw [comp_ι F k j a b hab, target_ι, target_ι, (F.obj j).target_comp_le i k hik]

lemma source_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell F)
    (h : target F k x = source F k y)
    (hs : target F k (source F i x) = source F k (source F i y)) :
    source F i (comp F k x y h) = comp F k (source F i x) (source F i y) hs := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  simp only [source_ι] at hs ⊢
  rw [comp_ι F k j a b hab, source_ι,
    (F.obj j).source_comp_gt i k hki a b hab ((F.obj j).source_composable hki hab),
    comp_ι F k j _ _ ((F.obj j).source_composable hki hab)]

lemma target_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell F)
    (h : target F k x = source F k y)
    (ht : target F k (target F i x) = source F k (target F i y)) :
    target F i (comp F k x y h) = comp F k (target F i x) (target F i y) ht := by
  obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
  simp only [target_ι] at ht ⊢
  rw [comp_ι F k j a b hab, target_ι,
    (F.obj j).target_comp_gt i k hki a b hab ((F.obj j).target_composable hki hab),
    comp_ι F k j _ _ ((F.obj j).target_composable hki hab)]

lemma unit_left (k : ℕ) (x : Cell F)
    (h : target F k (source F k x) = source F k x) :
    comp F k (source F k x) x h = x := by
  obtain ⟨j, a, rfl⟩ := exists_rep F x
  simp only [source_ι] at h ⊢
  rw [comp_ι F k j _ _ ((F.obj j).target_source_self k a), (F.obj j).unit_left]

lemma unit_right (k : ℕ) (x : Cell F)
    (h : target F k x = source F k (target F k x)) :
    comp F k x (target F k x) h = x := by
  obtain ⟨j, a, rfl⟩ := exists_rep F x
  simp only [target_ι] at h ⊢
  rw [comp_ι F k j _ _ ((F.obj j).source_target_self k a).symm, (F.obj j).unit_right]

lemma assoc (k : ℕ) (x y z : Cell F)
    (hxy : target F k x = source F k y) (hyz : target F k y = source F k z)
    (hxy_z : target F k (comp F k x y hxy) = source F k z)
    (hx_yz : target F k x = source F k (comp F k y z hyz)) :
    comp F k (comp F k x y hxy) z hxy_z = comp F k x (comp F k y z hyz) hx_yz := by
  obtain ⟨j, a, ha, he⟩ := lift_matches F ![x,y,z]
    (fun e : Bool => if e then (1 : Fin 3) else 0)
    (fun e : Bool => if e then (2 : Fin 3) else 1) (fun _ => k)
    (by intro e; cases e <;> assumption)
  have h0 : ι F j (a 0) = x := ha 0
  have h1 : ι F j (a 1) = y := ha 1
  have h2 : ι F j (a 2) = z := ha 2
  have h01 : (F.obj j).target k (a 0) = (F.obj j).source k (a 1) := he false
  have h12 : (F.obj j).target k (a 1) = (F.obj j).source k (a 2) := he true
  subst x y z
  simp only [comp_ι F k j _ _ h01, comp_ι F k j _ _ h12,
    comp_ι F k j _ _ ((F.obj j).assoc_composable_left h01 h12),
    comp_ι F k j _ _ ((F.obj j).assoc_composable_right h01 h12)]
  rw [(F.obj j).assoc]

lemma interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell F)
    (hab : target F l a = source F l b) (hcd : target F l c = source F l d)
    (hac : target F k a = source F k c) (hbd : target F k b = source F k d)
    (hab_cd : target F k (comp F l a b hab) = source F k (comp F l c d hcd))
    (hac_bd : target F l (comp F k a c hac) = source F l (comp F k b d hbd)) :
    comp F k (comp F l a b hab) (comp F l c d hcd) hab_cd =
      comp F l (comp F k a c hac) (comp F k b d hbd) hac_bd := by
  obtain ⟨j, x, hx, he⟩ := lift_matches F ![a,b,c,d]
    ![(0 : Fin 4),2,0,1] ![(1 : Fin 4),3,2,3] ![l,l,k,k]
    (by intro e; fin_cases e <;> assumption)
  have h0 : ι F j (x 0) = a := hx 0
  have h1 : ι F j (x 1) = b := hx 1
  have h2 : ι F j (x 2) = c := hx 2
  have h3 : ι F j (x 3) = d := hx 3
  have h01 : (F.obj j).target l (x 0) = (F.obj j).source l (x 1) := he 0
  have h23 : (F.obj j).target l (x 2) = (F.obj j).source l (x 3) := he 1
  have h02 : (F.obj j).target k (x 0) = (F.obj j).source k (x 2) := he 2
  have h13 : (F.obj j).target k (x 1) = (F.obj j).source k (x 3) := he 3
  have hlower : (F.obj j).target k (x 1) = (F.obj j).target k (x 0) := by
    have h := congrArg ((F.obj j).target k) h01
    simpa only [(F.obj j).target_target, (F.obj j).target_source,
      min_eq_left (le_of_lt hkl), ite_eq_left hkl] using h.symm
  have hm1 : (F.obj j).target k ((F.obj j).comp l (x 0) (x 1) h01) =
      (F.obj j).source k ((F.obj j).comp l (x 2) (x 3) h23) := by
    rw [(F.obj j).target_comp_le k l (le_of_lt hkl),
      (F.obj j).source_comp_le k l (le_of_lt hkl), hlower, h02]
  have hm2 : (F.obj j).target l ((F.obj j).comp k (x 0) (x 2) h02) =
      (F.obj j).source l ((F.obj j).comp k (x 1) (x 3) h13) := by
    rw [(F.obj j).target_comp_gt l k hkl _ _ _ ((F.obj j).target_composable hkl h02),
      (F.obj j).source_comp_gt l k hkl _ _ _ ((F.obj j).source_composable hkl h13)]
    simp only [h01, h23]
  subst a b c d
  simp only [comp_ι F l j _ _ h01, comp_ι F l j _ _ h23,
    comp_ι F k j _ _ h02, comp_ι F k j _ _ h13,
    comp_ι F k j _ _ hm1, comp_ι F l j _ _ hm2]
  rw [(F.obj j).interchange k l hkl]

noncomputable def omega : OmegaCategory.{u} where
  Cell := Cell F
  source := source F
  target := target F
  source_source := source_source F
  target_target := target_target F
  source_target := source_target F
  target_source := target_source F
  comp := comp F
  source_comp_le := source_comp_le F
  target_comp_le := target_comp_le F
  source_comp_gt := source_comp_gt F
  target_comp_gt := target_comp_gt F
  unit_left := unit_left F
  unit_right := unit_right F
  assoc := assoc F
  interchange := interchange F
  finite_dimension := finite_dimension F

noncomputable def cocone : Cocone F where
  pt := omega F
  ι := {
    app := fun j => {
      map := ι F j
      map_source := fun k x => (source_ι F k j x).symm
      map_target := fun k x => (target_ι F k j x).symm
      map_comp := fun k x y h h' => (comp_ι F k j x y h h').symm }
    naturality := by
      intro i j f
      apply Functor.ext
      funext x
      exact ι_map F f x }

omit [IsFiltered J] in
lemma desc_cell_ι (s : Cocone F) (j : J) (a : (F.obj j).Cell) :
    (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s)) (ι F j a) =
      (s.ι.app j).map a :=
  congr_hom (colimit.ι_desc (cellFunctor.mapCocone s) j) a

noncomputable def desc (s : Cocone F) : omega F ⟶ s.pt where
  map := colimit.desc (CellDiagram F) (cellFunctor.mapCocone s)
  map_source k x := by
    obtain ⟨j, a, rfl⟩ := exists_rep F x
    change (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s))
      (source F k (ι F j a)) = _
    rw [source_ι]
    rw [desc_cell_ι, desc_cell_ι]
    exact (s.ι.app j).map_source k a
  map_target k x := by
    obtain ⟨j, a, rfl⟩ := exists_rep F x
    change (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s))
      (target F k (ι F j a)) = _
    rw [target_ι]
    rw [desc_cell_ι, desc_cell_ι]
    exact (s.ι.app j).map_target k a
  map_comp k x y h h' := by
    obtain ⟨j, a, b, rfl, rfl, hab⟩ := lift_pair F k x y h
    change target F k (ι F j a) = source F k (ι F j b) at h
    change (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s))
      (comp F k (ι F j a) (ι F j b) h) = _
    rw [comp_ι F k j a b hab]
    simp only [desc_cell_ι] at h' ⊢
    exact (s.ι.app j).map_comp k a b hab h'

noncomputable def isColimit : IsColimit (cocone F) where
  desc := desc F
  fac s j := by
    apply Functor.ext
    funext x
    exact desc_cell_ι F s j x
  uniq s m h := by
    apply Functor.ext
    funext x
    obtain ⟨j, a, rfl⟩ := exists_rep F x
    have hm : m.map (ι F j a) = (s.ι.app j).map a := congrArg (fun G => G.map a) (h j)
    change m.map (ι F j a) = (colimit.desc (CellDiagram F) (cellFunctor.mapCocone s)) (ι F j a)
    rw [hm]
    exact (congr_hom (colimit.ι_desc (cellFunctor.mapCocone s) j) a).symm

end FilteredColimit
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma comp_of_left_source_fixed (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) (hx : C.source k x = x) :
    C.comp k x y h = y := by
  have hx' : x = C.source k y := (C.target_eq_self_of_source_eq_self hx).symm.trans h
  simpa only [← hx'] using C.unit_left k y (C.target_source_self k y)

lemma finite_truncation (C : OmegaCategory.{u}) [Finite C.Cell] :
    ∃ n, C.IsTruncated n := by
  classical
  let := Fintype.ofFinite C.Cell
  choose n hn using C.finite_dimension
  exact ⟨Finset.univ.sup n, fun x => C.source_fixed_upwards
    (Finset.le_sup (Finset.mem_univ x)) (hn x)⟩

structure GlobularMap (C : OmegaCategory.{u}) (D : OmegaCategory.{v}) where
  map : C.Cell → D.Cell
  map_source (k : ℕ) (x : C.Cell) : map (C.source k x) = D.source k (map x)
  map_target (k : ℕ) (x : C.Cell) : map (C.target k x) = D.target k (map x)

namespace FilteredColimit

open CategoryTheory Limits ConcreteCategory

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ OmegaCategory.{u})

lemma finite_globular_lift {C : OmegaCategory.{v}} [Finite C.Cell]
    (G : Functor C (omega F)) :
    ∃ j, ∃ H : GlobularMap C (F.obj j), ∀ x, ι F j (H.map x) = G.map x := by
  obtain ⟨n, hn⟩ := finite_truncation C
  obtain ⟨i, y, hy⟩ := Thomason.FilteredTypes.finite_representatives (CellDiagram F) G.map
  change C.Cell → (F.obj i).Cell at y
  change ∀ x, ι F i (y x) = G.map x at hy
  let z (x : C.Cell) := (F.obj i).source n (y x)
  have hz x : ι F i (z x) = G.map x := by
    change ι F i ((F.obj i).source n (y x)) = _
    rw [← source_ι, hy]
    exact (G.map_source n x).symm.trans (congrArg G.map (hn x))
  let p : (Fin (n+1) × Bool × C.Cell) → (F.obj i).Cell :=
    fun a => if a.2.1 then (F.obj i).target a.1.val (z a.2.2)
      else (F.obj i).source a.1.val (z a.2.2)
  let q : (Fin (n+1) × Bool × C.Cell) → (F.obj i).Cell :=
    fun a => z (if a.2.1 then C.target a.1.val a.2.2 else C.source a.1.val a.2.2)
  have he a : ι F i (p a) = ι F i (q a) := by
    rcases a with ⟨k, b, x⟩
    cases b
    · change ι F i ((F.obj i).source k.val (z x)) = ι F i (z (C.source k.val x))
      rw [← source_ι, hz, hz]
      exact (G.map_source k.val x).symm
    · change ι F i ((F.obj i).target k.val (z x)) = ι F i (z (C.target k.val x))
      rw [← target_ι, hz, hz]
      exact (G.map_target k.val x).symm
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F) p q he
  change ∀ a, (F.map f).map (p a) = (F.map f).map (q a) at hf
  let w (x : C.Cell) := (F.map f).map (z x)
  have hw x : (F.obj j).source n (w x) = w x := by
    dsimp [w, z]
    rw [← (F.map f).map_source, (F.obj i).source_source_self]
  refine ⟨j, ⟨w, ?_, ?_⟩, fun x => (ι_map F f (z x)).trans (hz x)⟩
  · intro k x
    by_cases hk : k ≤ n
    · have hh := hf ⟨⟨k, by omega⟩, false, x⟩
      change (F.map f).map ((F.obj i).source k (z x)) = w (C.source k x) at hh
      rw [(F.map f).map_source] at hh
      exact hh.symm
    · rw [C.source_fixed_upwards (by omega : n ≤ k) (hn x)]
      exact ((F.obj j).source_fixed_upwards (by omega) (hw x)).symm
  · intro k x
    by_cases hk : k ≤ n
    · have hh := hf ⟨⟨k, by omega⟩, true, x⟩
      change (F.map f).map ((F.obj i).target k (z x)) = w (C.target k x) at hh
      rw [(F.map f).map_target] at hh
      exact hh.symm
    · rw [C.target_eq_self_of_source_eq_self (C.source_fixed_upwards (by omega : n ≤ k) (hn x))]
      exact ((F.obj j).target_eq_self_of_source_eq_self
        ((F.obj j).source_fixed_upwards (by omega) (hw x))).symm

lemma finite_functor_lift {C : OmegaCategory.{v}} [Finite C.Cell]
    (G : Functor C (omega F)) :
    ∃ j, ∃ H : Functor C (F.obj j), ∀ x, ι F j (H.map x) = G.map x := by
  obtain ⟨n, hn⟩ := finite_truncation C
  obtain ⟨i, H, hH⟩ := finite_globular_lift F G
  let A := (k : Fin (n+1)) × {p : C.Cell × C.Cell // C.target k.val p.1 = C.source k.val p.2}
  let hm (a : A) : (F.obj i).target a.1.val (H.map a.2.val.1) =
      (F.obj i).source a.1.val (H.map a.2.val.2) := by
    rw [← H.map_target, ← H.map_source, a.2.property]
  let p (a : A) : (F.obj i).Cell :=
    (F.obj i).comp a.1.val (H.map a.2.val.1) (H.map a.2.val.2) (hm a)
  let q (a : A) : (F.obj i).Cell := H.map (C.comp a.1.val a.2.val.1 a.2.val.2 a.2.property)
  have he (a : A) : ι F i (p a) = ι F i (q a) := by
    have hh : target F a.1.val (ι F i (H.map a.2.val.1)) =
        source F a.1.val (ι F i (H.map a.2.val.2)) := by
      rw [hH, hH]
      exact G.map_composable a.2.property
    change ι F i ((F.obj i).comp a.1.val (H.map a.2.val.1) (H.map a.2.val.2) (hm a)) = _
    rw [← comp_ι F a.1.val i _ _ (hm a) hh]
    simp only [q, hH]
    exact (G.map_comp a.1.val _ _ a.2.property (G.map_composable a.2.property)).symm
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F) p q he
  change ∀ a, (F.map f).map (p a) = (F.map f).map (q a) at hf
  let w (x : C.Cell) := (F.map f).map (H.map x)
  have ws k x : w (C.source k x) = (F.obj j).source k (w x) := by
    dsimp [w]
    rw [H.map_source, (F.map f).map_source]
  have wt k x : w (C.target k x) = (F.obj j).target k (w x) := by
    dsimp [w]
    rw [H.map_target, (F.map f).map_target]
  refine ⟨j, ⟨w, ws, wt, ?_⟩, fun x => (ι_map F f (H.map x)).trans (hH x)⟩
  intro k x y h h'
  by_cases hk : k ≤ n
  · let a : A := ⟨⟨k, by omega⟩, ⟨⟨x,y⟩, h⟩⟩
    have hh := hf a
    change (F.map f).map ((F.obj i).comp k (H.map x) (H.map y) (hm a)) =
      w (C.comp k x y h) at hh
    rw [(F.map f).map_comp k _ _ _ h'] at hh
    exact hh.symm
  · have hx : C.source k x = x := C.source_fixed_upwards (by omega) (hn x)
    have hwx : (F.obj j).source k (w x) = w x := (ws k x).symm.trans (congrArg w hx)
    rw [C.comp_of_left_source_fixed k x y h hx,
      (F.obj j).comp_of_left_source_fixed k (w x) (w y) h' hwx]

lemma finite_functor_equality {C : OmegaCategory.{v}} [Finite C.Cell]
    {i : J} (G H : Functor C (F.obj i))
    (h : Functor.comp G ((cocone F).ι.app i) = Functor.comp H ((cocone F).ι.app i)) :
    ∃ (j : J) (f : i ⟶ j), Functor.comp G (F.map f) = Functor.comp H (F.map f) := by
  have he x : ι F i (G.map x) = ι F i (H.map x) :=
    congrArg (fun H : Functor C (omega F) => H.map x) h
  obtain ⟨j, f, hf⟩ := Thomason.FilteredTypes.finite_equalities (CellDiagram F) G.map H.map he
  refine ⟨j, f, ?_⟩
  apply Functor.ext
  funext x
  exact hf x

end FilteredColimit
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.FilteredColimit

open CategoryTheory Limits Opposite ConcreteCategory

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ OmegaCategory.{u})

noncomputable def finiteHomIsColimit (C : OmegaCategory.{u}) [Finite C.Cell] :
    IsColimit ((coyoneda.obj (Opposite.op C)).mapCocone (cocone F)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro G
    obtain ⟨j, H, hH⟩ := finite_functor_lift F G
    refine ⟨j, H, ?_⟩
    apply Functor.ext
    funext x
    exact (hH x).symm
  · intro i G H h
    exact finite_functor_equality F G H h

instance finiteHomPreservesColimit (C : OmegaCategory.{u}) [Finite C.Cell] :
    PreservesColimit F (coyoneda.obj (Opposite.op C)) :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (finiteHomIsColimit F C)

noncomputable def streetIsColimit :
    IsColimit (streetNerveFunctor.mapCocone (cocone F)) := by
  apply evaluationJointlyReflectsColimits
  intro m
  letI : Finite (orientals.obj m.unop).Cell := NormalizedChains.finiteTables
  apply Types.FilteredColimit.isColimitOf'
  · intro G
    change Functor (orientals.obj m.unop) (omega F) at G
    obtain ⟨j, H, hH⟩ := finite_functor_lift F G
    refine ⟨j, H, ?_⟩
    apply Functor.ext
    funext x
    exact (hH x).symm
  · intro i G H h
    exact finite_functor_equality F G H h

instance streetPreservesColimit : PreservesColimit F streetNerveFunctor :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (streetIsColimit F)

end Thomason.OmegaCategory.FilteredColimit

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance streetPreservesFilteredShape {J : Type u} [Category.{u} J] [IsFiltered J] :
    PreservesColimitsOfShape J streetNerveFunctor.{u} where
  preservesColimit {K} := OmegaCategory.FilteredColimit.streetPreservesColimit K

end Thomason

end

end OAI
