import Mathlib
import OAI.CategoryTheory.Thomason.SubdivisionFaces
import OAI.CategoryTheory.Thomason.SubdivisionWeak

namespace OAI

/-! Generators. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

instance thomasonBoundary_smallCardinal :
    IsCardinalForSmallObjectArgument (boundaryImages thomasonLeft.{u}) Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨n⟩ := hi
      infer_instance
    infer_instance

instance thomasonHorn_smallCardinal :
    IsCardinalForSmallObjectArgument (hornImages thomasonLeft.{u}) Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [hornImages, iSup_iff] at hi
      obtain ⟨n, ⟨j⟩⟩ := hi
      infer_instance
    infer_instance

instance thomasonBoundaryFinite_smallCardinal (n : ℕ) :
    IsCardinalForSmallObjectArgument (boundaryImages (thomasonLeftFinite.{u} n))
      Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨m⟩ := hi
      infer_instance
    infer_instance

instance thomasonHornFinite_smallCardinal (n : ℕ) :
    IsCardinalForSmallObjectArgument (hornImages (thomasonLeftFinite.{u} n))
      Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [hornImages, iSup_iff] at hi
      obtain ⟨m, ⟨j⟩⟩ := hi
      infer_instance
    infer_instance

lemma boundaryImages_right_fib_and_weak {C : Type v} [Category.{u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    (boundaryImages L).rlp ≤
      (simplicialFibrations.inverseImage R ⊓ simplicialWeakEquivalences.inverseImage R) := by
  rw [boundaryImages_rlp adj]
  intro X Y f hf
  exact ⟨KanQuillen.boundary_right_fibrations _ hf, KanQuillen.boundary_right_weak _ hf⟩

lemma thomasonBoundary_right_fib_and_weak :
    (boundaryImages thomasonLeft.{u}).rlp ≤ thomasonFibrations ⊓ thomasonWeakEquivalences :=
  boundaryImages_right_fib_and_weak thomasonAdjunction

lemma thomasonBoundaryFinite_right_fib_and_weak (n : ℕ) :
    (boundaryImages (thomasonLeftFinite.{u} n)).rlp ≤
      thomasonFibrationsFinite n ⊓ thomasonWeakEquivalencesFinite n :=
  boundaryImages_right_fib_and_weak (thomasonFiniteAdjunction n)

lemma thomasonCofibrations_le_boundaryGenerated :
    thomasonCofibrations.{u} ≤ (boundaryImages thomasonLeft).rlp.llp :=
  antitone_llp thomasonBoundary_right_fib_and_weak

lemma thomasonCofibrationsFinite_le_boundaryGenerated (n : ℕ) :
    thomasonCofibrationsFinite.{u} n ≤ (boundaryImages (thomasonLeftFinite n)).rlp.llp :=
  antitone_llp (thomasonBoundaryFinite_right_fib_and_weak n)

lemma hornGenerated_le_thomasonCofibrations :
    (hornImages thomasonLeft.{u}).rlp.llp ≤ thomasonCofibrations := by
  rw [hornImages_rlp thomasonAdjunction]
  exact antitone_llp inf_le_left

lemma hornGeneratedFinite_le_thomasonCofibrations (n : ℕ) :
    (hornImages (thomasonLeftFinite.{u} n)).rlp.llp ≤ thomasonCofibrationsFinite n := by
  rw [hornImages_rlp (thomasonFiniteAdjunction n)]
  exact antitone_llp inf_le_left

noncomputable def thomasonBoundaryFactorization {X Y : OmegaCategory.{u}} (f : X ⟶ Y) :
    MapFactorizationData (boundaryImages thomasonLeft).rlp.llp
      (thomasonFibrations ⊓ thomasonWeakEquivalences) f := by
  let d := factorizationData (boundaryImages thomasonLeft.{u}).rlp.llp
    (boundaryImages thomasonLeft).rlp f
  exact { d with hp := thomasonBoundary_right_fib_and_weak _ d.hp }

noncomputable def thomasonBoundaryFiniteFactorization (n : ℕ)
    {X Y : OmegaCategory.NCategory.{u} n} (f : X ⟶ Y) :
    MapFactorizationData (boundaryImages (thomasonLeftFinite n)).rlp.llp
      (thomasonFibrationsFinite n ⊓ thomasonWeakEquivalencesFinite n) f := by
  let d := factorizationData (boundaryImages (thomasonLeftFinite.{u} n)).rlp.llp
    (boundaryImages (thomasonLeftFinite n)).rlp f
  exact { d with hp := thomasonBoundaryFinite_right_fib_and_weak n _ d.hp }

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

def injectiveWordMap (f : E →o D) (hf : Function.Injective f) : Word E ↪ Word D where
  toFun w := ⟨w.val.map f,
    List.pairwise_map.mpr (w.property.imp fun h => f.monotone.strictMono_of_injective hf h)⟩
  inj' x y h := by
    apply Subtype.ext
    exact List.map_injective_iff.mpr hf (congrArg Subtype.val h)

lemma map_injectiveOrderHom (f : E →o D) (hf : Function.Injective f) (c : Chains E) :
    map f c = Finsupp.mapDomain (injectiveWordMap f hf) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, Finsupp.mapDomain_add, ih]
    congr 1
    rw [map, Finsupp.linearCombination_single, Finsupp.mapDomain_single]
    change z • bracket (injectiveWordMap f hf l).val =
      Finsupp.single (injectiveWordMap f hf l) z
    rw [bracket_of_pairwise (injectiveWordMap f hf l).property]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

lemma map_injectiveOrderHom_apply (f : E →o D) (hf : Function.Injective f)
    (c : Chains E) (w : Word E) : map f c (injectiveWordMap f hf w) = c w := by
  rw [map_injectiveOrderHom]
  exact Finsupp.mapDomain_apply_of_injective (injectiveWordMap f hf).injective c w

lemma map_injectiveOrderHom_injective (f : E →o D) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro a b h
  apply Finsupp.mapDomain_injective (injectiveWordMap f hf).injective
  simpa only [← map_injectiveOrderHom] using h

lemma map_supportedOn (f : E →o D) {S : Set E} {T : Set D}
    (hf : Set.MapsTo f S T) {c : Chains E} (hc : c ∈ supportedOn S) :
    map f c ∈ supportedOn T := by
  classical
  rw [map, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (supportedOn T).sum_mem
  intro w hw
  apply (supportedOn T).smul_mem
  apply bracket_mem_supportedOn
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hf ((mem_supportedOn_iff S c).mp hc w (Finsupp.mem_support_iff.mp hw) b hb)

lemma supportedOn_of_injective_map (f : E →o D) (hf : Function.Injective f)
    {T : Set D} {c : Chains E} (hc : map f c ∈ supportedOn T) :
    c ∈ supportedOn (f ⁻¹' T) := by
  rw [mem_supportedOn_iff]
  intro w hw a ha
  exact (mem_supportedOn_iff T _).mp hc (injectiveWordMap f hf w)
    (by simpa only [map_injectiveOrderHom_apply] using hw) (f a)
    (List.mem_map.mpr ⟨a, ha, rfl⟩)

noncomputable def upperCutLinearExtension (S : Set E) (hS : IsUpperSet S) :
    E →o Fin 2 ×ₗ LinearExtension E := by
  classical
  exact {
  toFun x := toLex (if x ∈ S then 1 else 0, toLinearExtension x)
  monotone' := by
    classical
    intro a b hab
    by_cases ha : a ∈ S
    · have hb := hS hab ha
      simp only [ha, hb, ite_true]
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, toLinearExtension.monotone hab⟩)
    · by_cases hb : b ∈ S
      · simp only [ha, hb, ite_false, ite_true]
        exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (show (0 : Fin 2) < 1 from by decide))
      · simp only [ha, hb, ite_false]
        exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, toLinearExtension.monotone hab⟩) }

lemma upperCutLinearExtension_injective (S : Set E) (hS : IsUpperSet S) :
    Function.Injective (upperCutLinearExtension S hS) := by
  intro a b h
  exact congrArg (fun z : Fin 2 ×ₗ LinearExtension E => (ofLex z).2) h

lemma positive_supportedOn_of_boundary_upper_partial {S : Set E} (hS : IsUpperSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  classical
  let f := upperCutLinearExtension S hS
  let T : Set (Fin 2 ×ₗ LinearExtension E) := {z | 1 ≤ (ofLex z).1}
  have hT : IsUpperSet T := by
    intro a b hab ha
    exact le_trans ha (Prod.Lex.monotone_fst_ofLex hab)
  have hpre : f ⁻¹' T = S := by
    ext x
    change (1 ≤ (if x ∈ S then 1 else 0 : Fin 2)) ↔ x ∈ S
    by_cases hx : x ∈ S <;> simp [hx]
  have hm : map f c ∈ supportedOn T := by
    apply positive_supportedOn_of_boundary_upper hT (map_mem_grade f hc) (map_positive f hp)
    rw [← map_boundary]
    apply map_supportedOn f _ hd
    intro a ha
    change 1 ≤ (if a ∈ S then 1 else 0 : Fin 2)
    simp [ha]
  rw [← hpre]
  exact supportedOn_of_injective_map f (upperCutLinearExtension_injective S hS) hm

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma positive_supportedOn_of_boundary_partial {S : Set E} (hS : IsLowerSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  apply supportedOn_of_reverseChain
  apply positive_supportedOn_of_boundary_upper_partial (E := Eᵒᵈ) hS
    (reverseChain_mem_grade hc) (reverseChain_positive hp)
  rw [boundary_reverseChain hc]
  exact (supportedOn (E := Eᵒᵈ) S).smul_mem _ (reverseChain_supportedOn hd)

lemma table_supportedOn_upper_partial {S : Set E} (hS : IsUpperSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  intro p
  induction p with
  | zero => exact hx
  | succ p ih =>
    intro b
    apply positive_supportedOn_of_boundary_upper_partial hS
      (x.row (p+1) b).property (x.positive _ _)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [hb]
    exact (supportedOn S).sub_mem (ih true) (ih false)

lemma table_supportedOn_lower_partial {S : Set E} (hS : IsLowerSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  intro p
  induction p with
  | zero => exact hx
  | succ p ih =>
    intro b
    apply positive_supportedOn_of_boundary_partial hS
      (x.row (p+1) b).property (x.positive _ _)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [hb]
    exact (supportedOn S).sub_mem (ih true) (ih false)

lemma table_segment_unique_lift_partial {S : Set E} (hS : IsUpperSet S ∨ IsLowerSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∃! y : Table (complex S),
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table y = x := by
  have h : ∀ p b, (x.row p b).val ∈ supportedOn S := hS.elim
    (fun hu => table_supportedOn_upper_partial hu x hx)
    (fun hl => table_supportedOn_lower_partial hl x hx)
  refine ⟨restrictTable S x h, table_map_restrictTable S x h, ?_⟩
  intro y hy
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S)
  exact hy.trans (table_map_restrictTable S x h).symm

lemma table_source_le_target_partial (x : Table (complex E)) (s t : E)
    (hs : (x.row 0 false).val = bracket [s])
    (ht : (x.row 0 true).val = bracket [t]) : s ≤ t := by
  classical
  let f : E →o Fin 2 :=
    { toFun := fun a => if s ≤ a then 1 else 0
      monotone' := by
        intro a b hab
        by_cases ha : s ≤ a
        · simp [ha, le_trans ha hab]
        · simp only [ha, ite_false]
          split <;> decide }
  have hh := table_source_le_target ((complexMap f).table x) (f s) (f t)
    (by change map f (x.row 0 false).val = bracket [f s]; rw [hs, map_bracket f (by simp)]; rfl)
    (by change map f (x.row 0 true).val = bracket [f t]; rw [ht, map_bracket f (by simp)]; rfl)
  by_contra hn
  change (if s ≤ s then 1 else 0 : Fin 2) ≤ (if s ≤ t then 1 else 0) at hh
  simp [hn] at hh

lemma map_table_injectiveOrderHom {D : Type v} [PartialOrder D] (f : E →o D)
    (hf : Function.Injective f) : Function.Injective (complexMap f).table := by
  intro x y h
  ext p b
  apply Subtype.ext
  apply map_injectiveOrderHom_injective f hf
  exact congrArg (fun z : Table (complex D) => (z.row p b).val) h

lemma positive_cycle_zero_partial {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2))
    (hp : Positive c) (hd : boundary c = 0) : c = 0 := by
  let f := toLinearExtension (α := E)
  apply map_injectiveOrderHom_injective f (fun _ _ h => h)
  rw [map_zero]
  apply positive_cycle_zero (map_mem_grade f hc) (map_positive f hp)
  rw [← map_boundary, hd, map_zero]

lemma table_endomorphism_identity_partial (x : Table (complex E))
    (hx : x.row 0 false = x.row 0 true) : Table.truncate 0 false x = x := by
  let f := toLinearExtension (α := E)
  apply map_table_injectiveOrderHom f (fun _ _ h => h)
  rw [DirectedComplex.Hom.table_truncate]
  exact table_endomorphism_identity ((complexMap f).table x)
    (congrArg (fun z => (complexMap f).map 0 z) hx)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [PartialOrder E]

lemma coneTable_one_source (x : Table (complex E)) (s t : E)
    (hs : (x.row 0 false).val = bracket [s])
    (ht : (x.row 0 true).val = bracket [t])
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici s)) :
    Table.truncate 1 false (coneTable s x hx) =
      edgeTable s t (table_source_le_target_partial x s t hs ht) := by
  ext p b
  cases p with
  | zero =>
    cases b
    · rfl
    · apply Subtype.ext; exact ht
  | succ p =>
    cases p with
    | zero =>
      rw [Table.truncate_top_row]
      apply Subtype.ext
      change prepend s (x.row 0 true).val = bracket [s,t]
      rw [ht, prepend_bracket]
    | succ p => rfl

lemma coneTable_one_target (x : Table (complex E)) (s : E)
    (hs : (x.row 0 false).val = bracket [s])
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici s)) :
    Table.truncate 1 true (coneTable s x hx) = Table.truncate 1 true x := by
  ext p b
  cases p with
  | zero =>
    cases b
    · apply Subtype.ext; exact hs.symm
    · rfl
  | succ p =>
    cases p with
    | zero =>
      rw [Table.truncate_top_row, Table.truncate_top_row]
      apply Subtype.ext
      change (x.row 1 true).val + prepend s (x.row 0 false).val = (x.row 1 true).val
      rw [hs, prepend_bracket, bracket_of_not_pairwise (by simp), add_zero]
    | succ p => rfl

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [PartialOrder E]

def tableStart (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.sourceObject x)

def tableFinish (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.targetObject x)

lemma tableStart_row (x : Table (complex E)) :
    (x.row 0 false).val = bracket [tableStart x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.sourceObject x))
  exact he.symm

lemma tableFinish_row (x : Table (complex E)) :
    (x.row 0 true).val = bracket [tableFinish x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.targetObject x))
  exact he.symm

lemma tableStart_le_finish (x : Table (complex E)) : tableStart x ≤ tableFinish x :=
  table_source_le_target_partial x _ _ (tableStart_row x) (tableFinish_row x)

lemma map_table_eq_edge {D : OmegaCategory.{v}} (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) (x : Table (complex E)) :
    F.map x = F.map (edgeTable (tableStart x) (tableFinish x) (tableStart_le_finish x)) := by
  have hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici (tableStart x)) := by
    apply table_supportedOn_upper_partial (by intro a b hab ha; exact le_trans ha hab) x
    intro b
    cases b
    · rw [tableStart_row]; exact bracket_mem_supportedOn (by simp)
    · rw [tableFinish_row]
      exact bracket_mem_supportedOn (by simpa using tableStart_le_finish x)
  let y := coneTable (tableStart x) x hx
  have hs : (complex E).nu.source 1 y =
      edgeTable (tableStart x) (tableFinish x) (tableStart_le_finish x) :=
    coneTable_one_source x _ _ (tableStart_row x) (tableFinish_row x) hx
  have ht : (complex E).nu.target 1 y = (complex E).nu.target 1 x :=
    coneTable_one_target x _ (tableStart_row x) hx
  calc
    F.map x = D.target 1 (F.map x) := (D.target_eq_self_of_source_eq_self (hD _)).symm
    _ = F.map ((complex E).nu.target 1 x) := (F.map_target 1 x).symm
    _ = F.map ((complex E).nu.target 1 y) := congrArg F.map ht.symm
    _ = D.target 1 (F.map y) := F.map_target 1 y
    _ = F.map y := D.target_eq_self_of_source_eq_self (hD _)
    _ = D.source 1 (F.map y) := (hD _).symm
    _ = F.map ((complex E).nu.source 1 y) := (F.map_source 1 y).symm
    _ = _ := congrArg F.map hs

lemma ordered_arrow_ext (f g : Arrow E) (hl : f.left = g.left) (hr : f.right = g.right) :
    f = g := Arrow.ext hl hr (Subsingleton.elim _ _)

def tableEndpoints : OmegaCategory.Functor (complex E).nu (ofCategory E) where
  map x := Arrow.mk (homOfLE (tableStart_le_finish x))
  map_source k x := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.source, tableStart]
    · cases k <;> simp [ofCategory, CategoryCell.source, tableStart, tableFinish]
  map_target k x := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.target, tableStart, tableFinish]
    · cases k <;> simp [ofCategory, CategoryCell.target, tableFinish]
  map_comp k x y h h' := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.comp, tableStart]
    · cases k with
      | zero => simp [ofCategory, CategoryCell.comp, tableFinish]
      | succ k =>
        have he := congrArg (fun z => tableObjectsEquiv ((complex E).nu.targetObject z)) h
        simpa [ofCategory, CategoryCell.comp, tableFinish] using he.symm

@[simp] lemma tableStart_edge (a b : E) (hab : a ≤ b) :
    tableStart (edgeTable a b hab) = a := by
  simp [tableStart, edgeTable_sourceObject]

@[simp] lemma tableFinish_edge (a b : E) (hab : a ≤ b) :
    tableFinish (edgeTable a b hab) = b := by
  simp [tableFinish, edgeTable_targetObject]

lemma edgeTable_diagonal (a : E) : edgeTable a a le_rfl = vertexTable a := by
  ext p b
  cases p with
  | zero => cases b <;> rfl
  | succ p =>
    cases p with
    | zero =>
      apply Subtype.ext
      change bracket [a,a] = 0
      exact bracket_of_not_pairwise (by simp)
    | succ p => rfl

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [PartialOrder E] {D : OmegaCategory.{v}}

def posetOneFunctor (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) : E ⥤ D.OneSkeleton where
  obj a := F.objects (tableObjectsEquiv.symm a)
  map {a b} f := ⟨F.map (edgeTable a b (leOfHom f)), hD _, by
      exact (F.map_source 0 _).symm.trans
        (congrArg F.map (edgeTable_source a b (leOfHom f))), by
      exact (F.map_target 0 _).symm.trans
        (congrArg F.map (edgeTable_target a b (leOfHom f)))⟩
  map_id a := by
    apply Subtype.ext
    exact congrArg F.map (edgeTable_diagonal a)
  map_comp {a b c} f g := by
    apply Subtype.ext
    let x := edgeTable a b (leOfHom f)
    let y := edgeTable b c (leOfHom g)
    have hxy : (complex E).nu.target 0 x = (complex E).nu.source 0 y :=
      (edgeTable_target a b _).trans (edgeTable_source b c _).symm
    let z := (complex E).nu.comp 0 x y hxy
    have hs : tableStart z = a := by
      exact (congrArg tableObjectsEquiv ((complex E).nu.sourceObject_comp 0 x y hxy)).trans
        (tableStart_edge a b _)
    have ht : tableFinish z = c := by
      exact (congrArg tableObjectsEquiv ((complex E).nu.targetObject_comp 0 x y hxy)).trans
        (tableFinish_edge b c _)
    have he := map_table_eq_edge hD F z
    have he' : F.map z = F.map (edgeTable a c (leOfHom (f ≫ g))) := by
      simpa only [hs, ht] using he
    exact he'.symm.trans (F.map_comp 0 x y hxy _)

def posetDiagramFunctor (G : E ⥤ D.OneSkeleton) :
    OmegaCategory.Functor (complex E).nu D :=
  OmegaCategory.Functor.comp tableEndpoints
    (OmegaCategory.Functor.comp (ofCategoryMap G) D.oneSkeletonEvaluation)

lemma posetDiagramFunctor_posetOneFunctor (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) :
    posetDiagramFunctor (posetOneFunctor hD F) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact (map_table_eq_edge hD F x).symm

@[simp] lemma tableStart_vertex (a : E) : tableStart (vertexTable a) = a := by
  have he := tableStart_edge a a le_rfl
  rwa [edgeTable_diagonal] at he

@[simp] lemma tableFinish_vertex (a : E) : tableFinish (vertexTable a) = a := by
  have he := tableFinish_edge a a le_rfl
  rwa [edgeTable_diagonal] at he

lemma tableEndpoints_vertex (a : E) : tableEndpoints.map (vertexTable a) = Arrow.mk (𝟙 a) := by
  apply ordered_arrow_ext
  · exact tableStart_vertex a
  · exact tableFinish_vertex a

lemma tableEndpoints_edge (a b : E) (hab : a ≤ b) :
    tableEndpoints.map (edgeTable a b hab) = Arrow.mk (homOfLE hab) := by
  apply ordered_arrow_ext
  · exact tableStart_edge a b hab
  · exact tableFinish_edge a b hab

lemma posetOneFunctor_posetDiagramFunctor_obj (hD : D.IsTruncated 1)
    (G : E ⥤ D.OneSkeleton) (a : E) :
    (posetOneFunctor hD (posetDiagramFunctor G)).obj a = G.obj a := by
  apply Subtype.ext
  change D.oneSkeletonEvaluation.map
    ((ofCategoryMap G).map (tableEndpoints.map (vertexTable a))) = _
  rw [tableEndpoints_vertex]
  change (G.map (𝟙 a)).val = _
  rw [G.map_id]
  rfl

lemma posetOneFunctor_posetDiagramFunctor (hD : D.IsTruncated 1)
    (G : E ⥤ D.OneSkeleton) : posetOneFunctor hD (posetDiagramFunctor G) = G := by
  refine CategoryTheory.Functor.ext
    (posetOneFunctor_posetDiagramFunctor_obj hD G) ?_
  intro a b f
  apply Subtype.ext
  change D.oneSkeletonEvaluation.map
    ((ofCategoryMap G).map (tableEndpoints.map (edgeTable a b (leOfHom f)))) = _
  rw [tableEndpoints_edge]
  change (G.map (homOfLE (leOfHom f))).val = _
  have he : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  rw [he]
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]

def posetOneEquiv (hD : D.IsTruncated 1) :
    OmegaCategory.Functor (complex E).nu D ≃ (E ⥤ D.OneSkeleton) where
  toFun := posetOneFunctor hD
  invFun := posetDiagramFunctor
  left_inv := posetDiagramFunctor_posetOneFunctor hD
  right_inv := posetOneFunctor_posetDiagramFunctor hD

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [PartialOrder E] {B : Type v} [PartialOrder B]
  {D : OmegaCategory.{w}}

lemma complexMap_vertex (f : E →o B) (a : E) :
    (complexMap f).nu.map (vertexTable a) = vertexTable (f a) := by
  change (complexMap f).table (vertexTable a) = _
  ext p b
  apply Subtype.ext
  cases p with
  | zero =>
    change map f (bracket [a]) = bracket [f a]
    simpa using map_bracket f (by simp : [a].Pairwise (· ≤ ·))
  | succ p => exact map_zero (map f)

lemma complexMap_edge (f : E →o B) (a b : E) (hab : a ≤ b) :
    (complexMap f).nu.map (edgeTable a b hab) = edgeTable (f a) (f b) (f.monotone hab) := by
  change (complexMap f).table (edgeTable a b hab) = _
  ext p e
  apply Subtype.ext
  cases p with
  | zero =>
    cases e <;>
      change map f (bracket [_]) = bracket [f _] <;>
      simpa using map_bracket f (by simp : [_].Pairwise (· ≤ ·))
  | succ p =>
    cases p with
    | zero =>
      change map f (bracket [a,b]) = bracket [f a, f b]
      simpa using map_bracket f (by simpa using hab : [a,b].Pairwise (· ≤ ·))
    | succ p => exact map_zero (map f)

lemma posetOneFunctor_naturality_obj (hD : D.IsTruncated 1) (f : E →o B)
    (F : OmegaCategory.Functor (complex B).nu D) (a : E) :
    (posetOneFunctor hD (OmegaCategory.Functor.comp (complexMap f).nu F)).obj a =
      (f.monotone.functor ⋙ posetOneFunctor hD F).obj a := by
  apply Subtype.ext
  exact congrArg F.map (complexMap_vertex f a)

lemma posetOneFunctor_naturality (hD : D.IsTruncated 1) (f : E →o B)
    (F : OmegaCategory.Functor (complex B).nu D) :
    posetOneFunctor hD (OmegaCategory.Functor.comp (complexMap f).nu F) =
      f.monotone.functor ⋙ posetOneFunctor hD F := by
  refine CategoryTheory.Functor.ext (posetOneFunctor_naturality_obj hD f F) ?_
  intro a b g
  apply Subtype.ext
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]
  exact congrArg F.map (complexMap_edge f a b (leOfHom g))

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Simplicial Opposite OmegaCategory NormalizedChains KanQuillen

lemma tableObjects_map {E : Type u} [PartialOrder E] {B : Type v} [PartialOrder B]
    (f : E →o B) (a : (complex E).nu.Objects) :
    tableObjectsEquiv ((complexMap f).nu.objects a) = f (tableObjectsEquiv a) := by
  obtain ⟨i, rfl⟩ := tableObjectsEquiv.symm.surjective a
  have he : (complexMap f).nu.objects (tableObjectsEquiv.symm i) =
      tableObjectsEquiv.symm (f i) := by
    apply Subtype.ext
    exact PosetTables.complexMap_vertex f i
  rw [he]
  simp

def chaoticNerveLift (X : SSet.{u}) (S : Type u) (f : X _⦋0⦌ → S) :
    X ⟶ streetNerve (chaotic S) where
  app n := TypeCat.ofHom (fun x => chaoticLift (fun a => f (vertexOf (n := n.unop) x (tableObjectsEquiv a))))
  naturality n m g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (chaoticHomEquiv (orientals.obj m.unop) S).symm.injective
    funext a
    change (complex (Fin (m.unop.len+1))).nu.Objects at a
    change f (vertexOf (X.map g x) (tableObjectsEquiv a)) =
      f (vertexOf x (tableObjectsEquiv ((complexMap g.unop.toOrderHom).nu.objects a)))
    rw [tableObjects_map]
    exact congrArg f (vertexOf_map g.unop x _)

def chaoticNerveRestrict (X : SSet.{u}) (S : Type u)
    (f : X ⟶ streetNerve (chaotic S)) : X _⦋0⦌ → S :=
  fun x => chaoticRestrict (f.app _ x) (tableObjectsEquiv.symm 0)

lemma chaoticNerveRestrict_lift (X : SSet.{u}) (S : Type u) (f : X _⦋0⦌ → S) :
    chaoticNerveRestrict X S (chaoticNerveLift X S f) = f := by
  funext x
  change f (vertexOf x (tableObjectsEquiv (tableObjectsEquiv.symm 0))) = f x
  simp only [Equiv.apply_symm_apply, vertexOf_zero]

lemma chaoticNerveLift_restrict (X : SSet.{u}) (S : Type u)
    (f : X ⟶ streetNerve (chaotic S)) :
    chaoticNerveLift X S (chaoticNerveRestrict X S f) = f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply (chaoticHomEquiv (orientals.obj n.unop) S).symm.injective
  funext a
  obtain ⟨i, rfl⟩ := tableObjectsEquiv.symm.surjective a
  have hn := NatTrans.naturality_apply f (SimplexCategory.const ⦋0⦌ n.unop i).op x
  have he := congrArg (fun F => chaoticRestrict F (tableObjectsEquiv.symm 0)) hn
  change chaoticNerveRestrict X S f
      (vertexOf x (tableObjectsEquiv (tableObjectsEquiv.symm i))) =
    chaoticRestrict (f.app n x) (tableObjectsEquiv.symm i)
  rw [Equiv.apply_symm_apply]
  change chaoticRestrict (f.app _ (vertexOf x i)) (tableObjectsEquiv.symm 0) = _ at he
  apply he.trans
  change ((f.app n x).map ((complexMap
    (SimplexCategory.const ⦋0⦌ n.unop i).toOrderHom).nu.map (vertexTable 0))).left = _
  rw [PosetTables.complexMap_vertex]
  rfl

def verticesChaoticHomEquiv (X : SSet.{u}) (S : Type u) :
    (X _⦋0⦌ → S) ≃ (X ⟶ streetNerve (chaotic S)) where
  toFun := chaoticNerveLift X S
  invFun := chaoticNerveRestrict X S
  left_inv := chaoticNerveRestrict_lift X S
  right_inv := chaoticNerveLift_restrict X S

def verticesChaoticAdjunction :
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌) ⊣
      chaoticFunctor ⋙ streetNerveFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X S => TypeCat.homEquiv.trans (verticesChaoticHomEquiv X S)
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by
      intro X S T f g
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro x
      rfl }

noncomputable def categorificationObjectsIso :
    categorification.{u} ⋙ objectsFunctor ≅
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌) :=
  Adjunction.leftAdjointUniq (categorificationAdjunction.comp objectsChaoticAdjunction)
    verticesChaoticAdjunction

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def objectsFiniteFunctor (n : ℕ) : NCategory.{u} n ⥤ Type u :=
  nCategoryInclusion n ⋙ objectsFunctor

def chaoticFiniteFunctor (n : ℕ) (hn : 1 ≤ n) : Type u ⥤ NCategory.{u} n where
  obj S := ⟨chaotic S, fun x => (chaotic S).source_fixed_upwards hn rfl⟩
  map f := chaoticFunctor.map f

def objectsFiniteChaoticAdjunction (n : ℕ) (hn : 1 ≤ n) :
    objectsFiniteFunctor.{u} n ⊣ chaoticFiniteFunctor n hn :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun C S => TypeCat.homEquiv.trans (chaoticHomEquiv C.val S)
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; rfl }

lemma objectsFinite_preservesColimits (n : ℕ) (hn : 1 ≤ n) :
    Limits.PreservesColimitsOfSize.{v,w} (objectsFiniteFunctor.{u} n) :=
  (objectsFiniteChaoticAdjunction n hn).leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Simplicial Opposite OmegaCategory

noncomputable def categorificationFiniteObjectsIso (n : ℕ) (hn : 1 ≤ n) :
    categorificationFinite.{u} n ⋙ objectsFiniteFunctor n ≅
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌) :=
  Adjunction.leftAdjointUniq
    ((categorificationFiniteAdjunction n).comp (objectsFiniteChaoticAdjunction n hn))
    verticesChaoticAdjunction

noncomputable def posetCategorificationObjectsIso (P : Type u) [PartialOrder P] :
    (categorification.obj (nerve P)).Objects ≅ P :=
  categorificationObjectsIso.app (nerve P) ≪≫ nerveEquiv.toIso

noncomputable def posetCategorificationFiniteObjectsIso (n : ℕ) (hn : 1 ≤ n)
    (P : Type u) [PartialOrder P] :
    ((categorificationFinite n).obj (nerve P)).val.Objects ≅ P :=
  (categorificationFiniteObjectsIso n hn).app (nerve P) ≪≫ nerveEquiv.toIso

lemma posetCategorificationObjectsIso_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) :
    objectsFunctor.map (categorification.map (nerveMap f.monotone.functor)) ≫
        (posetCategorificationObjectsIso Q).hom =
      (posetCategorificationObjectsIso P).hom ≫ TypeCat.ofHom f := by
  dsimp only [posetCategorificationObjectsIso, Iso.trans_hom]
  generalize he : categorificationObjectsIso = e
  exact congrArg (fun k : (categorification.obj (nerve P)).Objects ⟶ (nerve Q) _⦋0⦌ =>
    k ≫ nerveEquiv.toIso.hom) (e.hom.naturality (nerveMap f.monotone.functor))

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def finiteInterval (n : ℕ) (hn : 1 ≤ n) : NCategory.{u} n :=
  ⟨interval, fun x => interval.source_fixed_upwards hn (show interval.source 1 x = x from rfl)⟩

def fiberFiniteFunctor (n : ℕ) (hn : 1 ≤ n) (i : Fin 2) :
    CategoryTheory.Functor (Over (finiteInterval.{u} n hn)) (NCategory.{u} n) where
  obj p := ⟨(p.hom.fiber (intervalVertex i)).category, fun x =>
    Subtype.ext (p.left.property x.val)⟩
  map F := Functor.fiberMap _ _ F.left (Over.w F) (intervalVertex i)

def terminalConeFiniteObj (n : ℕ) (hn : 1 ≤ n) (C : NCategory.{u} n) :
    Over (finiteInterval.{u} n hn) :=
  Over.mk (X := finiteInterval n hn)
    (Y := ⟨C.val.terminalCone, terminalCone_truncated C.val hn C.property⟩) (coneLabel C.val)

def terminalConeFiniteFunctor (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.Functor (NCategory.{u} n) (Over (finiteInterval.{u} n hn)) where
  obj := terminalConeFiniteObj n hn
  map {C D} F := Over.homMk
    (U := terminalConeFiniteObj n hn C) (V := terminalConeFiniteObj n hn D)
    (coneMap F) (by
      apply Functor.ext
      funext x
      cases x <;> rfl)
  map_id C := by
    apply Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl
  map_comp F G := by
    apply Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl

def zeroFiberFiniteConeAdjunction (n : ℕ) (hn : 1 ≤ n) :
    fiberFiniteFunctor.{u} n hn 0 ⊣ terminalConeFiniteFunctor n hn :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun p B => {
      toFun F := Over.homMk (coneExtend p.hom F) (coneExtend_label p.hom F)
      invFun H := coneRestrict p.hom H.left (Over.w H)
      left_inv := coneRestrict_extend p.hom
      right_inv H := by
        apply Over.OverMorphism.ext
        exact coneExtend_restrict p.hom H.left (Over.w H) }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by
      intro p B D F G
      apply Over.OverMorphism.ext
      apply Functor.ext
      funext x
      change coneExtendMap p.hom (Functor.comp F G) x =
        (coneMap G).map (coneExtendMap p.hom F x)
      rcases interval_cases (p.hom.map x) with hx | hx | hx
      · rw [coneExtendMap_zero p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_zero p.hom F x hx)).symm
      · rw [coneExtendMap_arrow p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_arrow p.hom F x hx)).symm
      · rw [coneExtendMap_one p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_one p.hom F x hx)).symm }

instance zeroFiberFinite_preservesColimits (n : ℕ) (hn : 1 ≤ n) :
    Limits.PreservesColimitsOfSize.{v,w} (fiberFiniteFunctor.{u} n hn 0) :=
  (zeroFiberFiniteConeAdjunction n hn).leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

end OAI
