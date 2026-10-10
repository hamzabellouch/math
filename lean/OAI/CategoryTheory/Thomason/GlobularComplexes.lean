import Mathlib
import OAI.CategoryTheory.Thomason.OrientalCounit
import OAI.CategoryTheory.Thomason.SubdivisionNerves

namespace OAI

/-! Globular Complexes. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {X : Type u} [PartialOrder X]

noncomputable def chainsSubtypeOrderIso (A : Set X) :
    NonemptyFiniteChains A ≃o OldChains A := by
  classical
  let f : A →o X := ⟨Subtype.val, fun _ _ h => h⟩
  let forward : NonemptyFiniteChains A → OldChains A := fun s =>
    ⟨s.map f, by
      intro x hx
      obtain ⟨a, _, rfl⟩ := (s.mem_map_iff f x).mp hx
      exact a.property⟩
  let backward : OldChains A → NonemptyFiniteChains A := fun s => {
    finset := s.val.finset.subtype (· ∈ A)
    nonempty := by
      obtain ⟨a, ha⟩ := s.val.nonempty
      exact ⟨⟨a, s.property a ha⟩, Finset.mem_subtype.mpr ha⟩
    comparable := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      exact s.val.comparable ⟨a.val, Finset.mem_subtype.mp ha⟩
        ⟨b.val, Finset.mem_subtype.mp hb⟩ }
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro s
    apply NonemptyFiniteChains.ext
    ext a
    change a ∈ (s.map f).finset.subtype (· ∈ A) ↔ a ∈ s.finset
    rw [Finset.mem_subtype, NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨b, hb, hba⟩
      exact (Subtype.ext hba : b = a) ▸ hb
    · exact fun h => ⟨a, h, rfl⟩
  · intro s
    apply Subtype.ext
    apply NonemptyFiniteChains.ext
    ext a
    change a ∈ ((backward s).map f).finset ↔ a ∈ s.val.finset
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Finset.mem_subtype.mp hb
    · intro ha
      exact ⟨⟨a, s.property a ha⟩, Finset.mem_subtype.mpr ha, rfl⟩
  · intro s t
    constructor
    · intro h a ha
      have hh := h ((s.mem_map_iff f a.val).mpr ⟨a, ha, rfl⟩)
      obtain ⟨b, hb, hba⟩ := (t.mem_map_iff f a.val).mp hh
      exact (Subtype.ext hba : b = a) ▸ hb
    · exact fun h => (NonemptyFiniteChains.orderHomMap f).monotone h

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

noncomputable def sdTwiceSubcomplexIso :
    (SSet.sd ⋙ SSet.sd).obj (K : SSet.{u}) ≅
      nerve (NonemptyFiniteChains (AllowedChains K)) :=
  SSet.sd.mapIso (sdSubcomplexIso K) ≪≫ sdNerveIso

noncomputable def sdTwiceNerveIso :
    (SSet.sd ⋙ SSet.sd).obj (nerve E) ≅
      nerve (NonemptyFiniteChains (NonemptyFiniteChains E)) :=
  SSet.sd.mapIso sdNerveIso ≪≫ sdNerveIso

lemma sdTwiceSubcomplexIso_naturality :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ (sdTwiceNerveIso (E := E)).hom =
      (sdTwiceSubcomplexIso K).hom ≫ PartOrd.nerveFunctor.map
        (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap
          (⟨Subtype.val, fun _ _ h => h⟩ : AllowedChains K →o NonemptyFiniteChains E))) := by
  change SSet.sd.map (SSet.sd.map K.ι) ≫ (SSet.sd.map sdNerveMap ≫ sdNerveMap) =
    (SSet.sd.map (sdSubcomplexMap K) ≫ sdNerveMap) ≫ _
  rw [← Category.assoc, ← SSet.sd.map_comp, sdSubcomplexMap_naturality,
    SSet.sd.map_comp, Category.assoc]
  change SSet.sd.map (sdSubcomplexMap K) ≫
      (SSet.sd.map (nerveMap (⟨Subtype.val, fun _ _ h => h⟩ :
        AllowedChains K →o NonemptyFiniteChains E).monotone.functor) ≫ sdNerveMap) = _
  rw [sdNerveMap_naturality]
  erw [← Category.assoc]

noncomputable def orderedSimplexSubcomplex {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (nerve (ULift.{u} (Fin (m+1)))).Subcomplex :=
  SSet.Subcomplex.range (K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom)

noncomputable def orderedSimplexSubcomplexIso {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (K : SSet.{u}) ≅ (orderedSimplexSubcomplex K : SSet) :=
  by
  let f : (K : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (m+1))) :=
    K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom
  haveI : Mono f := mono_comp _ _
  let t : (K : SSet.{u}) ⟶ (SSet.Subcomplex.range f : SSet.{u}) := SSet.Subcomplex.toRange f
  haveI : Mono t := mono_of_mono_fac (SSet.Subcomplex.toRange_ι f)
  haveI : Epi t := inferInstanceAs (Epi (Subfunctor.toRange f))
  haveI : IsIso t := isIso_of_mono_of_epi t
  exact @asIso SSet.{u} (inferInstance) _ _ t ‹IsIso t›

noncomputable def sdTwiceSimplexSubcomplexIso {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).obj (K : SSet.{u}) ≅
      nerve (NonemptyFiniteChains (AllowedChains (orderedSimplexSubcomplex K))) :=
  (SSet.sd ⋙ SSet.sd).mapIso (orderedSimplexSubcomplexIso K) ≪≫
    sdTwiceSubcomplexIso (orderedSimplexSubcomplex K)

noncomputable def sdTwiceSimplexIso (m : ℕ) :
    (SSet.sd ⋙ SSet.sd).obj (SSet.stdSimplex.{u}.obj ⦋m⦌) ≅
      nerve (NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+1))))) :=
  (SSet.sd ⋙ SSet.sd).mapIso (SSet.stdSimplex.isoNerve.{u} m) ≪≫ sdTwiceNerveIso

lemma sdTwiceSimplexSubcomplexIso_naturality {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ (sdTwiceSimplexIso m).hom =
      (sdTwiceSimplexSubcomplexIso K).hom ≫ PartOrd.nerveFunctor.map
        (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap
          (⟨Subtype.val, fun _ _ h => h⟩ : AllowedChains (orderedSimplexSubcomplex K) →o
            NonemptyFiniteChains (ULift.{u} (Fin (m+1)))))) := by
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  simp only [Functor.mapIso_hom]
  erw [← Category.assoc, ← Functor.map_comp]
  have h : K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom =
      (orderedSimplexSubcomplexIso K).hom ≫ (orderedSimplexSubcomplex K).ι := rfl
  erw [h, Functor.map_comp, Category.assoc, sdTwiceSubcomplexIso_naturality, ← Category.assoc]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

open DirectedComplex

def chainModule (n p : ℕ) : Submodule ℤ (ULift.{u} Bool → ℤ) where
  carrier := {x | ∀ b, (n < p ∨ (p = n ∧ b.down = true)) → x b = 0}
  zero_mem' := by simp
  add_mem' hx hy b hb := by simp [hx b hb, hy b hb]
  smul_mem' a x hx b hb := by simp [hx b hb]

abbrev Chain (n p : ℕ) : Type u := ↥(chainModule.{u} n p)

def mass (n p : ℕ) : Chain.{u} n p →+ ℤ where
  toFun x := x.val ⟨false⟩ + x.val ⟨true⟩
  map_zero' := by simp
  map_add' x y := by simp; ring

lemma chain_zero {n p : ℕ} (h : n < p) (x : Chain.{u} n p) : x = 0 := by
  apply Subtype.ext
  funext b
  exact x.property b (Or.inl h)

lemma top_target_zero (n : ℕ) (x : Chain.{u} n n) : x.val ⟨true⟩ = 0 :=
  x.property ⟨true⟩ (Or.inr ⟨rfl, rfl⟩)

def delta (n p : ℕ) : Chain.{u} n p :=
  if h : p < n then ⟨fun b => if b.down then 1 else -1, by
    intro b hb
    rcases hb with hb | ⟨hb, _⟩ <;> omega⟩ else 0

@[simp] lemma mass_delta (n p : ℕ) : mass n p (delta.{u} n p) = 0 := by
  by_cases h : p < n <;> simp [delta, mass, h]

def differential (n p : ℕ) : Chain.{u} n (p+1) →+ Chain.{u} n p where
  toFun x := mass n (p+1) x • delta n p
  map_zero' := by simp
  map_add' x y := by rw [map_add, add_zsmul]

lemma differential_coordinate (n p : ℕ) (x : Chain.{u} n (p+1)) (b : Bool) :
    (differential n p x).val ⟨b⟩ = if b then mass n (p+1) x else -mass n (p+1) x := by
  by_cases h : p < n
  · cases b <;> simp [differential, delta, h]
  · have hx := chain_zero (show n < p+1 by omega) x
    subst x
    simp [differential]

def positive (n p : ℕ) : AddSubmonoid (Chain.{u} n p) where
  carrier := {x | ∀ b, 0 ≤ x.val ⟨b⟩}
  zero_mem' _ := le_rfl
  add_mem' hx hy b := add_nonneg (hx b) (hy b)

def complex (n : ℕ) : DirectedComplex.{u} where
  Chain := Chain n
  group _ := inferInstance
  d := differential n
  d_d p x := by
    change mass n (p+1) (mass n (p+2) x • delta n (p+1)) • delta n p = 0
    rw [map_zsmul, mass_delta, smul_zero, zero_smul]
  augmentation := mass n 0
  augmentation_d x := by
    change mass n 0 (mass n 1 x • delta n 0) = 0
    rw [map_zsmul, mass_delta, smul_zero]
  positive := positive n

lemma complex_d_coordinate (n p : ℕ) (x : (complex.{u} n).Chain (p+1)) (b : Bool) :
    ((complex n).d p x).val ⟨b⟩ = if b then mass n (p+1) x else -mass n (p+1) x :=
  differential_coordinate n p x b

lemma mass_nonneg {n p : ℕ} {x : (complex.{u} n).Chain p}
    (hx : x ∈ (complex n).positive p) : 0 ≤ mass n p x :=
  add_nonneg (hx false) (hx true)

lemma coordinate_le_mass {n p : ℕ} {x : (complex.{u} n).Chain p}
    (hx : x ∈ (complex n).positive p) (b : Bool) : x.val ⟨b⟩ ≤ mass n p x := by
  change x.val ⟨b⟩ ≤ x.val ⟨false⟩ + x.val ⟨true⟩
  cases b
  · linarith [hx true]
  · linarith [hx false]

lemma mass_eq_zero_iff {n p : ℕ} {x : (complex.{u} n).Chain p}
    (hx : x ∈ (complex n).positive p) : mass n p x = 0 ↔ x = 0 := by
  constructor
  · intro hm
    apply Subtype.ext
    funext ⟨b⟩
    have h := coordinate_le_mass hx b
    rw [hm] at h
    exact le_antisymm h (hx b)
  · rintro rfl
    exact map_zero _

def basis (n p : ℕ) (b : Bool) (hb : p < n ∨ (p = n ∧ b = false)) :
    (complex.{u} n).Chain p :=
  ⟨fun i => if i.down = b then 1 else 0, by
    intro ⟨i⟩ hi
    dsimp
    split_ifs with h
    · subst i
      rcases hb with hb | ⟨hb, hb'⟩
      · rcases hi with hi | ⟨hi, _⟩ <;> omega
      · rcases hi with hi | ⟨_, hi⟩
        · omega
        · simp [hb'] at hi
    · rfl⟩

@[simp] lemma basis_coordinate (n p : ℕ) (b : Bool)
    (hb : p < n ∨ (p = n ∧ b = false)) (i : Bool) :
    (basis.{u} n p b hb).val ⟨i⟩ = if i = b then 1 else 0 := rfl

@[simp] lemma mass_basis (n p : ℕ) (b : Bool)
    (hb : p < n ∨ (p = n ∧ b = false)) : mass n p (basis.{u} n p b hb) = 1 := by
  cases b <;> simp [mass]

lemma basis_positive (n p : ℕ) (b : Bool)
    (hb : p < n ∨ (p = n ∧ b = false)) : basis.{u} n p b hb ∈ (complex n).positive p := by
  intro i
  simp only [basis_coordinate]
  split_ifs <;> omega

lemma differential_basis (n p : ℕ) (b : Bool)
    (hb : p+1 < n ∨ (p+1 = n ∧ b = false)) :
    (complex.{u} n).d p (basis n (p+1) b hb) =
      basis n p true (Or.inl (by rcases hb with hb | ⟨hb, _⟩ <;> omega)) -
      basis n p false (Or.inl (by rcases hb with hb | ⟨hb, _⟩ <;> omega)) := by
  apply Subtype.ext
  funext ⟨i⟩
  change ((complex n).d p _).val ⟨i⟩ = _
  rw [complex_d_coordinate, mass_basis]
  change (if i then (1 : ℤ) else -1) = (if i = true then 1 else 0) -
    (if i = false then 1 else 0)
  cases i <;> norm_num

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

open DirectedComplex DirectedComplex.Table

def topRow (n p : ℕ) (b : Bool) : (complex.{u} n).Chain p :=
  if h : p < n then basis n p b (Or.inl h)
  else if h : p = n then basis n p false (Or.inr ⟨h, rfl⟩) else 0

lemma topRow_lt (n p : ℕ) (b : Bool) (h : p < n) :
    topRow.{u} n p b = basis n p b (Or.inl h) := by simp [topRow, h]

lemma topRow_eq (n : ℕ) (b : Bool) :
    topRow.{u} n n b = basis n n false (Or.inr ⟨rfl, rfl⟩) := by simp [topRow]

lemma topRow_gt (n p : ℕ) (b : Bool) (h : n < p) : topRow.{u} n p b = 0 := by
  simp [topRow, show ¬p < n by omega, show p ≠ n by omega]

def topTable (n : ℕ) : Table (complex.{u} n) where
  row := topRow n
  positive p b := by
    unfold topRow
    split_ifs <;> first | exact basis_positive _ _ _ _ | exact (positive.{u} n p).zero_mem
  boundary p b := by
    by_cases hp : p < n
    · rw [topRow_lt n p true hp, topRow_lt n p false hp]
      by_cases hp' : p+1 < n
      · rw [topRow_lt n (p+1) b hp', differential_basis]
      · have he : p+1 = n := by omega
        rw [show topRow n (p+1) b = basis n (p+1) false (Or.inr ⟨he, rfl⟩) by
          unfold topRow; rw [dite_eq_right hp', dite_eq_left he]]
        exact differential_basis n p false (Or.inr ⟨he, rfl⟩)
    · rw [topRow_gt n (p+1) b (by omega), map_zero]
      by_cases he : p = n
      · subst p; rw [topRow_eq, topRow_eq, sub_self]
      · rw [topRow_gt n p true (by omega), topRow_gt n p false (by omega), sub_self]
  augmentation b := by
    change mass n 0 (topRow n 0 b) = 1
    unfold topRow
    split_ifs with h he
    · exact mass_basis _ _ _ _
    · exact mass_basis _ _ _ _
    · omega
  bounded := ⟨n, fun p hp b => topRow_gt n p b hp⟩

lemma topTable_bounded (n : ℕ) : truncate n false (topTable.{u} n) = topTable n := by
  ext p b
  rw [truncate_row]
  change (if p < n then topRow n p b else if p = n then topRow n p false else 0) = topRow n p b
  split_ifs with h he
  · rfl
  · subst p; rw [topRow_eq, topRow_eq]
  · exact (topRow_gt n p b (by omega)).symm

variable {n : ℕ} (x : Table (complex.{u} n))

lemma table_boundary_coordinate (p : ℕ) (b i : Bool) :
    (if i then mass n (p+1) (x.row (p+1) b) else -mass n (p+1) (x.row (p+1) b)) =
      (x.row p true).val ⟨i⟩ - (x.row p false).val ⟨i⟩ := by
  have h := congrArg (fun z : (complex n).Chain p => z.val ⟨i⟩) (x.boundary p b)
  rw [complex_d_coordinate] at h
  exact h

lemma table_mass_eq (p : ℕ) : mass n p (x.row p true) = mass n p (x.row p false) := by
  have h := congrArg (mass n p) (x.boundary p false)
  change mass n p (mass n (p+1) (x.row (p+1) false) • delta n p) = _ at h
  erw [map_sub, map_zsmul, mass_delta, smul_zero] at h
  omega

lemma table_mass_zero (b : Bool) : mass n 0 (x.row 0 b) = 1 := x.augmentation b

lemma table_mass_step (p : ℕ) (b : Bool) :
    mass n (p+1) (x.row (p+1) b) ≤ mass n p (x.row p false) := by
  have h := table_boundary_coordinate x p b false
  simp only [Bool.false_eq_true, ite_false] at h
  have hp := x.positive p true false
  have hc := coordinate_le_mass (x.positive p false) false
  omega

lemma table_mass_le_one (p : ℕ) (b : Bool) : mass n p (x.row p b) ≤ 1 := by
  induction p generalizing b with
  | zero => rw [table_mass_zero]
  | succ p ih => exact (table_mass_step x p b).trans (ih false)

lemma table_mass_antitone : Antitone (fun p => mass n p (x.row p false)) := by
  apply antitone_nat_of_succ_le
  intro p
  exact table_mass_step x p false

lemma positive_mass_one {p : ℕ} (z : (complex.{u} n).Chain p)
    (hz : z ∈ (complex n).positive p) (hm : mass n p z = 1) :
    ∃ (b : Bool) (hb : p < n ∨ (p = n ∧ b = false)), z = basis n p b hb := by
  have hp : p ≤ n := by
    by_contra h
    rw [chain_zero (by omega) z, map_zero] at hm
    omega
  have h₀ := hz false
  have h₁ := hz true
  change z.val ⟨false⟩ + z.val ⟨true⟩ = 1 at hm
  by_cases h : z.val ⟨false⟩ = 1
  · have hb : p < n ∨ (p = n ∧ false = false) := by
      by_cases h : p < n
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩
    refine ⟨false, hb, ?_⟩
    apply Subtype.ext
    funext ⟨i⟩
    change z.val ⟨i⟩ = if i = false then 1 else 0
    cases i <;> dsimp <;> omega
  · have ht : z.val ⟨true⟩ = 1 := by omega
    have hpn : p < n := by
      by_contra hpn
      have he : p = n := by omega
      subst p
      have := top_target_zero n z
      omega
    refine ⟨true, Or.inl hpn, ?_⟩
    apply Subtype.ext
    funext ⟨i⟩
    change z.val ⟨i⟩ = if i = true then 1 else 0
    cases i <;> dsimp <;> omega

lemma table_has_top : ∃ p, p ≤ n ∧ mass n p (x.row p false) = 1 ∧
    ∀ q, p < q → ∀ b, x.row q b = 0 := by
  classical
  let s := (Finset.range (n+1)).filter (fun p => mass n p (x.row p false) ≠ 0)
  have he : s.Nonempty := ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), by rw [table_mass_zero]; omega⟩⟩
  let p := s.max' he
  have hp : p ∈ s := Finset.max'_mem s he
  obtain ⟨hpn, hpne⟩ := Finset.mem_filter.mp hp
  have hple : p ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hpn
  have hpmass : mass n p (x.row p false) = 1 := by
    have := table_mass_le_one x p false
    have := mass_nonneg (x.positive p false)
    omega
  refine ⟨p, hple, hpmass, ?_⟩
  intro q hpq b
  have hqzero : mass n q (x.row q false) = 0 := by
    by_contra hq
    have hqn : q ≤ n := by
      by_contra h
      exact hq (by rw [chain_zero (by omega) (x.row q false), map_zero])
    have hqmem : q ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩
    have := Finset.le_max' s q hqmem
    omega
  apply (mass_eq_zero_iff (x.positive q b)).mp
  cases b
  · exact hqzero
  · rw [table_mass_eq, hqzero]

lemma table_lower_row {p : ℕ} (hm : mass n (p+1) (x.row (p+1) false) = 1)
    (hp : p < n) (b : Bool) : x.row p b = basis n p b (Or.inl hp) := by
  have h₀ := table_boundary_coordinate x p false false
  have h₁ := table_boundary_coordinate x p false true
  simp only [Bool.false_eq_true, ite_false, ite_true, hm] at h₀ h₁
  have hs := table_mass_le_one x p false
  have ht := table_mass_le_one x p true
  change (x.row p false).val ⟨false⟩ + (x.row p false).val ⟨true⟩ ≤ 1 at hs
  change (x.row p true).val ⟨false⟩ + (x.row p true).val ⟨true⟩ ≤ 1 at ht
  have hsf := x.positive p false false
  have hst := x.positive p false true
  have htf := x.positive p true false
  have htt := x.positive p true true
  apply Subtype.ext
  funext ⟨i⟩
  change (x.row p b).val ⟨i⟩ = if i = b then 1 else 0
  cases b <;> cases i <;> dsimp <;> omega

lemma topRow_basis {p : ℕ} (b : Bool) (hb : p < n ∨ (p = n ∧ b = false)) :
    topRow.{u} n p b = basis n p b hb := by
  rcases hb with h | ⟨rfl, rfl⟩
  · rw [topRow_lt n p b h]
  · rw [topRow_eq]

lemma table_classification : ∃ (p : ℕ) (b : Bool), p ≤ n ∧
    x = truncate p b (topTable n) := by
  obtain ⟨p, hpn, hmass, hzero⟩ := table_has_top x
  obtain ⟨b, hb, he⟩ := positive_mass_one (x.row p false) (x.positive p false) hmass
  have hpeq : x.row p true = x.row p false := by
    have h := x.boundary p false
    rw [hzero (p+1) (by omega) false, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  refine ⟨p, b, hpn, ?_⟩
  ext q a
  rw [truncate_row]
  by_cases hq : q < p
  · rw [ite_eq_left hq]
    have hm : mass n (q+1) (x.row (q+1) false) = 1 := by
      have hupper := table_mass_le_one x (q+1) false
      have hlower := table_mass_antitone x (show q+1 ≤ p by omega)
      change mass n p (x.row p false) ≤ mass n (q+1) (x.row (q+1) false) at hlower
      rw [hmass] at hlower
      omega
    rw [table_lower_row x hm (by omega)]
    exact (topRow_lt n q a (by omega)).symm
  · rw [ite_eq_right hq]
    by_cases heq : q = p
    · subst q
      rw [ite_eq_left rfl]
      change x.row p a = topRow n p b
      rw [topRow_basis b hb]
      cases a
      · exact he
      · exact hpeq.trans he
    · rw [ite_eq_right heq]
      exact hzero q (by omega) a

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def face (C : OmegaCategory.{u}) (p : ℕ) (b : Bool) (x : C.Cell) : C.Cell :=
  if b then C.target p x else C.source p x

lemma face_face (C : OmegaCategory.{u}) (p q : ℕ) (a b : Bool) (x : C.Cell) :
    C.face p a (C.face q b x) = if p < q then C.face p a x else C.face q b x := by
  cases a <;> cases b <;>
    simp only [face, Bool.false_eq_true, ite_false, ite_true]
  · rw [C.source_source]
    split_ifs with h
    · rw [min_eq_left (Nat.le_of_lt h)]
    · rw [min_eq_right (Nat.le_of_not_gt h)]
  · exact C.source_target p q x
  · exact C.target_source p q x
  · rw [C.target_target]
    split_ifs with h
    · rw [min_eq_left (Nat.le_of_lt h)]
    · rw [min_eq_right (Nat.le_of_not_gt h)]

lemma face_of_fixed (C : OmegaCategory.{u}) {n p : ℕ} {x : C.Cell}
    (hx : C.source n x = x) (hnp : n ≤ p) (b : Bool) : C.face p b x = x := by
  cases b
  · exact C.source_fixed_upwards hnp hx
  · exact C.target_eq_self_of_source_eq_self (C.source_fixed_upwards hnp hx)

lemma Functor.map_face {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (p : ℕ) (b : Bool) (x : C.Cell) :
    F.map (C.face p b x) = D.face p b (F.map x) := by
  cases b
  · exact F.map_source p x
  · exact F.map_target p x

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

open DirectedComplex DirectedComplex.Table OmegaCategory

lemma face_nu (n p : ℕ) (b : Bool) (x : Table (complex.{u} n)) :
    (complex n).nu.face p b x = truncate p b x := by cases b <;> rfl

lemma top_face_mass {n p : ℕ} (hp : p ≤ n) (b : Bool) :
    mass n p ((truncate p b (topTable.{u} n)).row p false) = 1 := by
  rw [truncate_top_row]
  change mass n p (topRow n p b) = 1
  by_cases h : p < n
  · rw [topRow_lt n p b h, mass_basis]
  · have he : p = n := by omega
    subst p; rw [topRow_eq, mass_basis]

lemma top_face_dimension {n p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (a b : Bool)
    (h : truncate p a (topTable.{u} n) = truncate q b (topTable n)) : p = q := by
  by_contra he
  rcases lt_or_gt_of_ne he with hpq | hqp
  · have hh := congrArg (fun t : Table (complex n) => mass n q (t.row q false)) h
    erw [truncate_row, ite_eq_right (by omega), ite_eq_right (by omega), map_zero,
      top_face_mass hq b] at hh
    omega
  · have hh := congrArg (fun t : Table (complex n) => mass n p (t.row p false)) h
    erw [top_face_mass hp a, truncate_row, ite_eq_right (by omega), ite_eq_right (by omega), map_zero] at hh
    omega

lemma top_face_sign {n p : ℕ} (hp : p < n) (a b : Bool)
    (h : truncate p a (topTable.{u} n) = truncate p b (topTable n)) : a = b := by
  have hh := congrArg (fun t : Table (complex n) => (t.row p false).val ⟨a⟩) h
  rw [truncate_top_row, truncate_top_row] at hh
  change (topRow n p a).val ⟨a⟩ = (topRow n p b).val ⟨a⟩ at hh
  rw [topRow_lt n p a hp, topRow_lt n p b hp] at hh
  change (if a = a then (1 : ℤ) else 0) = (if a = b then 1 else 0) at hh
  simp only [ite_true] at hh
  split_ifs at hh with he
  · exact he
  · omega

lemma face_evaluation_well_defined {n p q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (a b : Bool) (h : truncate p a (topTable.{u} n) = truncate q b (topTable n))
    {C : OmegaCategory.{v}} (x : C.Cell) (hx : C.source n x = x) :
    C.face p a x = C.face q b x := by
  have he := top_face_dimension hp hq a b h
  subst q
  by_cases hp' : p < n
  · rw [top_face_sign hp' a b h]
  · have hn : n ≤ p := by omega
    rw [C.face_of_fixed hx hn, C.face_of_fixed hx hn]

noncomputable def evaluate {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (t : Table (complex.{u} n)) : C.Cell :=
  let p := (table_classification t).choose
  let b := (table_classification t).choose_spec.choose
  C.face p b x

lemma evaluate_face {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) (p : ℕ) (b : Bool) :
    evaluate x (truncate p b (topTable.{u} n)) = C.face p b x := by
  by_cases hp : p ≤ n
  · let t := truncate p b (topTable.{u} n)
    obtain ⟨hqn, ht⟩ := (table_classification t).choose_spec.choose_spec
    exact face_evaluation_well_defined hqn hp _ b ht.symm x hx
  · have hnp : n ≤ p := by omega
    have he : truncate p b (topTable.{u} n) = topTable n :=
      (face_nu n p b (topTable n)).symm.trans
        ((complex n).nu.face_of_fixed (topTable_bounded n) hnp b)
    rw [he, C.face_of_fixed hx hnp]
    obtain ⟨hqn, ht⟩ := (table_classification (topTable.{u} n)).choose_spec.choose_spec
    exact (face_evaluation_well_defined hqn (le_refl n) _ false
      (ht.symm.trans (topTable_bounded n).symm) x hx).trans hx

lemma evaluate_top {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) : evaluate x (topTable.{u} n) = x := by
  rw [← topTable_bounded n, evaluate_face x hx]
  exact hx

lemma evaluate_truncate {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) (t : Table (complex.{u} n)) (k : ℕ) (a : Bool) :
    evaluate x (truncate k a t) = C.face k a (evaluate x t) := by
  obtain ⟨p, b, _, rfl⟩ := table_classification t
  rw [truncate_truncate, evaluate_face x hx, C.face_face]
  split_ifs <;> rw [evaluate_face x hx]

lemma composable_has_identity {n : ℕ} (k : ℕ) (x y : Table (complex.{u} n))
    (h : truncate k true x = truncate k false y) :
    truncate k false x = x ∨ truncate k false y = y := by
  obtain ⟨p, a, hpn, rfl⟩ := table_classification x
  obtain ⟨q, b, hqn, rfl⟩ := table_classification y
  by_cases hkp : k < p
  · by_cases hkq : k < q
    · rw [truncate_truncate, truncate_truncate, ite_eq_left hkp, ite_eq_left hkq] at h
      have := top_face_sign (by omega : k < n) true false h
      cases this
    · exact Or.inr (by rw [truncate_truncate, ite_eq_right hkq])
  · exact Or.inl (by rw [truncate_truncate, ite_eq_right hkp])

noncomputable def lift {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) : OmegaCategory.Functor (complex.{u} n).nu C where
  map := evaluate x
  map_source k t := evaluate_truncate x hx t k false
  map_target k t := evaluate_truncate x hx t k true
  map_comp k s t h h' := by
    rcases composable_has_identity k s t h with hs | ht
    · have hs' : s = truncate k false t :=
        ((complex n).nu.target_eq_self_of_source_eq_self hs).symm.trans h
      subst s
      erw [(complex n).nu.unit_left]
      revert h'
      rw [evaluate_truncate x hx t k false]
      intro h'
      exact (C.unit_left k (evaluate x t) h').symm
    · have ht' : t = truncate k true s := ht.symm.trans h.symm
      subst t
      erw [(complex n).nu.unit_right]
      revert h'
      rw [evaluate_truncate x hx s k true]
      intro h'
      exact (C.unit_right k (evaluate x s) h').symm

lemma lift_top {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) : (lift.{u,v} x hx).map (topTable n) = x :=
  evaluate_top x hx

lemma functor_ext {n : ℕ} {C : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (complex.{u} n).nu C}
    (h : F.map (topTable n) = G.map (topTable n)) : F = G := by
  apply OmegaCategory.Functor.ext
  funext t
  obtain ⟨p, b, _, rfl⟩ := table_classification t
  rw [← face_nu]
  erw [F.map_face, G.map_face, h]

noncomputable def globeIso (n : ℕ) : OmegaCategory.globe.{u} n ≅ (complex.{u} n).nu where
  hom := OmegaCategory.globeLift n (topTable n) (topTable_bounded n)
  inv := lift (OmegaCategory.globeGenerator n) (OmegaCategory.globeGenerator_bounded n)
  hom_inv_id := by
    apply OmegaCategory.globe_functor_ext
    change (lift (OmegaCategory.globeGenerator n) (OmegaCategory.globeGenerator_bounded n)).map
      (topTable n) = OmegaCategory.globeGenerator n
    exact lift_top (OmegaCategory.globeGenerator n) (OmegaCategory.globeGenerator_bounded n)
  inv_hom_id := by
    apply functor_ext
    change (OmegaCategory.globeLift n (C := (complex.{u} n).nu) (topTable n) (topTable_bounded n)).map
      ((lift (OmegaCategory.globeGenerator n) (OmegaCategory.globeGenerator_bounded n)).map
        (topTable n)) = topTable n
    erw [lift_top]
    rfl

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex OmegaCategory

lemma basisLambda_positive {E : Type u} [PartialOrder E] (p : ℕ) (w : Word E) :
    basisLambda p w ∈ (complex E).nu.lambdaPositive p := by
  classical
  unfold basisLambda
  split_ifs with h
  · rcases w with ⟨w, hw⟩
    cases w with
    | nil => exact False.elim (by change 0 = p + 1 at h; omega)
    | cons a l => exact (complex E).nu.lambdaGen_positive _
  · exact AddSubmonoid.zero_mem _

lemma atomCounitInverse_positive {E : Type u} [PartialOrder E] (p : ℕ)
    (x : (complex E).Chain p) (hx : x ∈ (complex E).positive p) :
    atomCounitInverse p x ∈ (complex E).nu.lambdaPositive p := by
  classical
  change Finsupp.linearCombination ℤ (basisLambda p) x.val ∈ _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply AddSubmonoid.sum_mem
  intro w _
  have hw : 0 ≤ x.val w := hx w
  have he : x.val w = (x.val w).toNat := (Int.toNat_of_nonneg hw).symm
  rw [he, Nat.cast_smul_eq_nsmul]
  exact AddSubmonoid.nsmul_mem _ (basisLambda_positive p w) _

lemma oriental_lambdaCounit_rightInverse {N : ℕ} (p : ℕ) :
    ((complex (Fin (N+1))).lambdaCounitMap p).comp (atomCounitInverse p) =
      LinearMap.id := by
  ext x
  obtain ⟨y, rfl⟩ := normalized_lambdaCounit_surjective (E := Fin (N+1)) p x
  exact congrArg ((complex (Fin (N+1))).lambdaCounitMap p)
    (LinearMap.congr_fun (oriental_lambdaCounit_leftInverse p) y)

lemma counit_atomInverse {N : ℕ} (p : ℕ) (x : (complex (Fin (N+1))).Chain p) :
    (complex (Fin (N+1))).lambdaCounitMap p (atomCounitInverse p x) = x :=
  LinearMap.congr_fun (oriental_lambdaCounit_rightInverse p) x

noncomputable def simplexCounitInverse (N : ℕ) :
    Hom (complex (Fin (N+1))) (complex (Fin (N+1))).nu.linearization where
  map p := (atomCounitInverse p).toAddMonoidHom
  map_d p x := by
    apply oriental_lambdaCounit_injective p
    calc
      _ = (complex (Fin (N+1))).d p x := counit_atomInverse p _
      _ = (complex (Fin (N+1))).d p
          ((complex (Fin (N+1))).lambdaCounitMap (p+1) (atomCounitInverse (p+1) x)) :=
        congrArg ((complex (Fin (N+1))).d p) (counit_atomInverse (p+1) x).symm
      _ = _ := (DFunLike.congr_fun ((complex (Fin (N+1))).lambdaCounitMap_d p)
        (atomCounitInverse (p+1) x)).symm
  map_augmentation x := by
    exact (DFunLike.congr_fun (complex (Fin (N+1))).lambdaCounitMap_aug
      (atomCounitInverse 0 x)).symm.trans
      (congrArg (complex (Fin (N+1))).augmentation (counit_atomInverse 0 x))
  map_positive := atomCounitInverse_positive

lemma simplexCounitInverse_counit (N : ℕ) :
    Hom.comp (simplexCounitInverse N) (complex (Fin (N+1))).lambdaCounit =
      Hom.id (complex (Fin (N+1))) := by
  ext p x
  exact LinearMap.congr_fun (oriental_lambdaCounit_rightInverse p) x

lemma counit_simplexCounitInverse (N : ℕ) :
    Hom.comp (complex (Fin (N+1))).lambdaCounit (simplexCounitInverse N) =
      Hom.id (complex (Fin (N+1))).nu.linearization := by
  ext p x
  exact LinearMap.congr_fun (oriental_lambdaCounit_leftInverse p) x

noncomputable def simplexCounitIso (N : ℕ) :
    (complex (Fin (N+1))).nu.linearization ≅ complex (Fin (N+1)) where
  hom := (complex (Fin (N+1))).lambdaCounit
  inv := simplexCounitInverse N
  hom_inv_id := counit_simplexCounitInverse N
  inv_hom_id := simplexCounitInverse_counit N

end Thomason.NormalizedChains

end

end OAI
