import OAI.Analysis.DiamondDistortion.FiniteAverage

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

structure SegmentSystem (ι : Type*) where
  IsSegment : Finset ι → Prop
  singleton : ∀ v, IsSegment {v}

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

/-- The represented disjoint families in the definition of the primal segment norm. -/
structure Family where
  n : ℕ
  seg : Fin n → Finset ι
  allowed : ∀ i, T.IsSegment (seg i)
  disjoint : Pairwise (fun i j => Disjoint (seg i) (seg j))

instance : Nonempty T.Family := ⟨{
  n := 0
  seg := Fin.elim0
  allowed := fun i => Fin.elim0 i
  disjoint := fun {i} => Fin.elim0 i }⟩

variable {T}

/-- Segment testing as a Euclidean-valued linear map. -/
def Family.test (F : T.Family) : (ι →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin F.n) where
  toFun u := WithLp.toLp 2 (fun i => ∑ v ∈ F.seg i, u v)
  map_add' u v := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' c u := by
    ext i
    simp [Finset.mul_sum]

@[simp] theorem Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
    F.test u i = ∑ v ∈ F.seg i, u v := rfl

def Family.seminorm (F : T.Family) : Seminorm ℝ (ι →₀ ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ (Fin F.n))).comp F.test

@[simp] theorem Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
    F.seminorm u = ‖F.test u‖ := rfl

lemma Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
    ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
  classical
  rw [EuclideanSpace.norm_eq]
  apply (Real.sqrt_le_left (abs_nonneg r)).2
  by_cases h : ∃ i, v ∈ F.seg i
  · obtain ⟨i, hi⟩ := h
    have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
      intro j hji hj
      exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
    rw [Finset.sum_eq_single i]
    · simp [Family.test, Finsupp.single_apply, hi]
    · intro j _ hji
      simp [Family.test, Finsupp.single_apply, hne j hji]
    · simp
  · have hn : ∀ i, v ∉ F.seg i := by simpa using h
    simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]

lemma Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
    ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
  classical
  calc
    ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
      rw [← map_sum]
      congr 2
      exact (Finsupp.sum_single u).symm
    _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => F.test_single_le v (u v)
    _ = u.sum (fun _ r => |r|) := rfl

variable (T)

lemma families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
  rw [Seminorm.bddAbove_range_iff]
  intro u
  exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact F.test_le_l1 u⟩

def primalSeminorm : Seminorm ℝ (ι →₀ ℝ) := ⨆ F : T.Family, F.seminorm

lemma test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
    ‖F.test u‖ ≤ T.primalSeminorm u := by
  rw [primalSeminorm, Seminorm.iSup_apply T.families_bddAbove]
  exact le_ciSup (⟨u.sum (fun _ r => |r|), by
    rintro _ ⟨G, rfl⟩; exact G.test_le_l1 u⟩ :
    BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F

lemma primal_le_l1 (u : ι →₀ ℝ) :
    T.primalSeminorm u ≤ u.sum (fun _ r => |r|) := by
  rw [primalSeminorm, Seminorm.iSup_apply T.families_bddAbove]
  apply ciSup_le
  intro F
  exact F.test_le_l1 u

/-- Singleton families ensure that the segment seminorm separates points. -/
def singletonFamily (v : ι) : T.Family where
  n := 1
  seg _ := {v}
  allowed _ := T.singleton v
  disjoint := by intro i j h; exact False.elim (h (Subsingleton.elim _ _))

lemma coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
  have h := T.test_le_primal (T.singletonFamily v) u
  rw [EuclideanSpace.norm_eq] at h
  change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
  simpa [Real.sqrt_sq_eq_abs] using h

lemma primal_eq_zero_iff (u : ι →₀ ℝ) : T.primalSeminorm u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext v
    have := T.coordinate_le_primal u v
    simpa [h] using this
  · rintro rfl
    exact map_zero _

/-- Finite families with any finite index type give the same segment tests. -/
def familyOfFintype {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) : T.Family where
  n := Fintype.card κ
  seg i := S ((Fintype.equivFin κ).symm i)
  allowed i := hS _
  disjoint := by
    intro i j hij
    exact hd (fun he => hij ((Fintype.equivFin κ).symm.injective he))

lemma test_energy_le {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ S i, u v) ^ 2) ≤ (T.primalSeminorm u) ^ 2 := by
  let F := T.familyOfFintype S hS hd
  have hb := pow_le_pow_left₀ (norm_nonneg (F.test u)) (T.test_le_primal F u) 2
  rw [EuclideanSpace.norm_sq_eq] at hb
  change (∑ i : Fin (Fintype.card κ),
    ‖∑ v ∈ S ((Fintype.equivFin κ).symm i), u v‖ ^ 2) ≤ _ at hb
  rw [(Fintype.equivFin κ).symm.sum_comp (fun i : κ => ‖∑ v ∈ S i, u v‖ ^ 2)] at hb
  simpa only [Real.norm_eq_abs, sq_abs] using hb

/-- Empty pieces in a partition may be discarded; they contribute no energy. -/
lemma test_energy_le_allow_empty {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ S i, u v) ^ 2) ≤ (T.primalSeminorm u) ^ 2 := by
  classical
  let K := {i : κ // (S i).Nonempty}
  have h := T.test_energy_le (fun i : K => S i.val) (fun i => hS _ i.property)
    (by intro i j hij; exact hd (fun he => hij (Subtype.ext he))) u
  have hz : (∑ i : {i : κ // ¬ (S i).Nonempty}, (∑ v ∈ S i.val, u v) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : S i.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp i.property
    simp [hi]
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun i : κ => (S i).Nonempty) (fun i => (∑ v ∈ S i, u v) ^ 2)
  rw [hz, add_zero] at he
  rwa [← he]

def Primal (_T : SegmentSystem ι) := ι →₀ ℝ

/-- Explicit conversions keep the chosen norm distinct from unrelated Finsupp structures. -/
def ofPrimal (u : T.Primal) : ι →₀ ℝ := u

def toPrimal (u : ι →₀ ℝ) : T.Primal := u

def filterPrimal (p : ι → Prop) (u : T.Primal) : T.Primal :=
  (T.ofPrimal u).filter p

instance : AddCommGroup T.Primal := inferInstanceAs (AddCommGroup (ι →₀ ℝ))
instance : Module ℝ T.Primal := inferInstanceAs (Module ℝ (ι →₀ ℝ))

attribute [-simp] Family.test_apply Family.seminorm_apply in
instance : NormedAddCommGroup T.Primal := by
  have Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
      F.test u i = ∑ v ∈ F.seg i, u v := rfl
  have Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
      F.seminorm u = ‖F.test u‖ := rfl
  have Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
      ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
    classical
    rw [EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_left (abs_nonneg r)).2
    by_cases h : ∃ i, v ∈ F.seg i
    · obtain ⟨i, hi⟩ := h
      have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
        intro j hji hj
        exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
      rw [Finset.sum_eq_single i]
      · simp [Family.test, Finsupp.single_apply, hi]
      · intro j _ hji
        simp [Family.test, Finsupp.single_apply, hne j hji]
      · simp
    · have hn : ∀ i, v ∉ F.seg i := by simpa using h
      simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]
  have Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
    classical
    calc
      ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
        rw [← map_sum]
        congr 2
        exact (Finsupp.sum_single u).symm
      _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => Family.test_single_le F v (u v)
      _ = u.sum (fun _ r => |r|) := rfl
  have families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact Family.test_le_l1 F u⟩
  have test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ T.primalSeminorm u := by
    rw [primalSeminorm, Seminorm.iSup_apply families_bddAbove]
    exact le_ciSup (⟨u.sum (fun _ r => |r|), by
      rintro _ ⟨G, rfl⟩; exact Family.test_le_l1 G u⟩ :
      BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F
  have coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
    have h := test_le_primal (T.singletonFamily v) u
    rw [EuclideanSpace.norm_eq] at h
    change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
    simpa [Real.sqrt_sq_eq_abs] using h
  have primal_eq_zero_iff (u : ι →₀ ℝ) : T.primalSeminorm u = 0 ↔ u = 0 := by
    constructor
    · intro h
      ext v
      have := coordinate_le_primal u v
      simpa [h] using this
    · rintro rfl
      exact map_zero _
  exact AddGroupNorm.toNormedAddCommGroup
    { T.primalSeminorm.toAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun u h => (primal_eq_zero_iff u).mp h }

instance : NormedSpace ℝ T.Primal where
  norm_smul_le c u := le_of_eq (T.primalSeminorm.smul' c u)

@[simp] lemma ofPrimal_sub (u v : T.Primal) :
    T.ofPrimal (u-v) = T.ofPrimal u - T.ofPrimal v := rfl

@[simp] lemma ofPrimal_smul (a : ℝ) (u : T.Primal) :
    T.ofPrimal (a • u) = a • T.ofPrimal u := rfl

@[simp] lemma ofPrimal_sum {κ : Type*} (s : Finset κ) (f : κ → T.Primal) :
    T.ofPrimal (∑ i ∈ s, f i) = ∑ i ∈ s, T.ofPrimal (f i) := rfl

@[simp] lemma ofPrimal_filter (p : ι → Prop) (u : T.Primal) :
    T.ofPrimal (T.filterPrimal p u) = (T.ofPrimal u).filter p := rfl

@[simp] lemma norm_eq_primal (u : T.Primal) :
    ‖u‖ = T.primalSeminorm (T.ofPrimal u) := rfl

lemma sub_filterPrimal (p : ι → Prop) (u : T.Primal) :
    u - T.filterPrimal p u = T.filterPrimal (fun x => ¬ p x) u := by
  apply Finsupp.ext
  intro v
  change T.ofPrimal (u - T.filterPrimal p u) v =
    T.ofPrimal (T.filterPrimal (fun x => ¬ p x) u) v
  simp only [ofPrimal_sub, ofPrimal_filter, Finsupp.sub_apply, Finsupp.filter_apply]
  split_ifs <;> simp_all

abbrev JamesSpace := UniformSpace.Completion T.Primal

/-- Its full real continuous dual. -/
abbrev Dual := StrongDual ℝ T.JamesSpace

/-- Coordinate evaluation on finite arrays, bounded by the singleton test. -/
def coordinateFinite (v : ι) : T.Primal →L[ℝ] ℝ := by
  have Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
      F.test u i = ∑ v ∈ F.seg i, u v := rfl
  have Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
      F.seminorm u = ‖F.test u‖ := rfl
  have Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
      ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
    classical
    rw [EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_left (abs_nonneg r)).2
    by_cases h : ∃ i, v ∈ F.seg i
    · obtain ⟨i, hi⟩ := h
      have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
        intro j hji hj
        exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
      rw [Finset.sum_eq_single i]
      · simp [Family.test, Finsupp.single_apply, hi]
      · intro j _ hji
        simp [Family.test, Finsupp.single_apply, hne j hji]
      · simp
    · have hn : ∀ i, v ∉ F.seg i := by simpa using h
      simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]
  have Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
    classical
    calc
      ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
        rw [← map_sum]
        congr 2
        exact (Finsupp.sum_single u).symm
      _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => Family.test_single_le F v (u v)
      _ = u.sum (fun _ r => |r|) := rfl
  have families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact Family.test_le_l1 F u⟩
  have test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ T.primalSeminorm u := by
    rw [primalSeminorm, Seminorm.iSup_apply families_bddAbove]
    exact le_ciSup (⟨u.sum (fun _ r => |r|), by
      rintro _ ⟨G, rfl⟩; exact Family.test_le_l1 G u⟩ :
      BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F
  have coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
    have h := test_le_primal (T.singletonFamily v) u
    rw [EuclideanSpace.norm_eq] at h
    change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
    simpa [Real.sqrt_sq_eq_abs] using h
  exact (show T.Primal →ₗ[ℝ] ℝ from Finsupp.lapply v).mkContinuous 1 (by
      intro u
      change ‖(show ι →₀ ℝ from u) v‖ ≤ 1 * T.primalSeminorm u
      simpa only [one_mul, Real.norm_eq_abs] using coordinate_le_primal u v)

def coordinate (v : ι) : T.Dual :=
  (T.coordinateFinite v).extend UniformSpace.Completion.toComplL

@[simp] lemma coordinate_coe (v : ι) (u : T.Primal) :
    T.coordinate v (u : T.JamesSpace) = (show ι →₀ ℝ from u) v := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) u

/-- Primal unit coordinate and its canonical image in the completion. -/
def unitFinite (v : ι) : T.Primal := Finsupp.single v 1

def unitVector (v : ι) : T.JamesSpace := (T.unitFinite v : T.JamesSpace)

@[simp] lemma norm_unitFinite (v : ι) : ‖T.unitFinite v‖ = 1 := by
  change T.primalSeminorm (Finsupp.single v 1) = 1
  apply le_antisymm
  · have h := T.primal_le_l1 (Finsupp.single v 1)
    simpa using h
  · have h := T.coordinate_le_primal (Finsupp.single v 1) v
    simpa using h

@[simp] lemma norm_unitVector (v : ι) : ‖T.unitVector v‖ = 1 := by
  rw [unitVector, UniformSpace.Completion.norm_coe, norm_unitFinite]

@[simp] lemma coordinate_unitVector (v w : ι) :
    T.coordinate v (T.unitVector w) = if w = v then 1 else 0 := by
  classical
  rw [unitVector, coordinate_coe]
  exact Finsupp.single_apply

/-- Finite head projection on the completed primal, defined even for nonancestral sets. -/
def headPrimal (H : Finset ι) : T.JamesSpace →L[ℝ] T.JamesSpace :=
  ∑ v ∈ H, (T.coordinate v).smulRight (T.unitVector v)

@[simp] lemma headPrimal_apply (H : Finset ι) (u : T.JamesSpace) :
    T.headPrimal H u = ∑ v ∈ H, T.coordinate v u • T.unitVector v := by
  simp [headPrimal]

lemma sum_units_eq_filter (H : Finset ι) (u : T.Primal) :
    (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) = T.filterPrimal (· ∈ H) u := by
  classical
  apply Finsupp.ext
  intro w
  change T.ofPrimal (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) w =
    T.ofPrimal (T.filterPrimal (· ∈ H) u) w
  simp only [ofPrimal_sum, ofPrimal_smul, ofPrimal_filter, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp [ofPrimal, unitFinite, Finsupp.single_apply,
    mul_ite, Finset.sum_ite_eq']
  convert (Finsupp.filter_apply (· ∈ H) (T.ofPrimal u) w).symm using 1
  all_goals congr

lemma headPrimal_coe (H : Finset ι) (u : T.Primal) :
    T.headPrimal H (u : T.JamesSpace) =
      (T.filterPrimal (· ∈ H) u : T.JamesSpace) := by
  classical
  rw [headPrimal_apply, ← T.sum_units_eq_filter]
  simp only [coordinate_coe, unitVector]
  change (∑ v ∈ H, T.ofPrimal u v •
    (UniformSpace.Completion.toComplL (S := ℝ)) (T.unitFinite v)) =
    (UniformSpace.Completion.toComplL (S := ℝ)) (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v)
  simp only [map_sum, map_smul]

def headDual (H : Finset ι) : T.Dual →L[ℝ] T.Dual :=
  ∑ v ∈ H, (ContinuousLinearMap.apply ℝ ℝ (T.unitVector v)).smulRight (T.coordinate v)

@[simp] lemma headDual_apply (H : Finset ι) (x : T.Dual) :
    T.headDual H x = ∑ v ∈ H, x (T.unitVector v) • T.coordinate v := by
  simp [headDual]

lemma headDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.headDual H x u = x (T.headPrimal H u) := by
  simp [headDual_apply, headPrimal_apply, mul_comm]

/-- Complementary coordinate projection, never assumed contractive without proof. -/
def tailDual (H : Finset ι) : T.Dual →L[ℝ] T.Dual :=
  ContinuousLinearMap.id ℝ T.Dual - T.headDual H

@[simp] lemma tailDual_apply (H : Finset ι) (x : T.Dual) :
    T.tailDual H x = x - T.headDual H x := rfl

lemma tailDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.tailDual H x u = x (u - T.headPrimal H u) := by
  simp [tailDual_apply, mul_comm]

/-- The canonical linear embedding, presented on actual finitely supported arrays. -/
def finiteEmbedding : (ι →₀ ℝ) →ₗ[ℝ] T.JamesSpace :=
  (UniformSpace.Completion.toComplL (S := ℝ) (α := T.Primal)).toLinearMap

@[simp] lemma finiteEmbedding_apply (u : ι →₀ ℝ) :
    T.finiteEmbedding u = (T.toPrimal u : T.JamesSpace) := rfl

@[simp] lemma finiteEmbedding_single (v : ι) (a : ℝ) :
    T.finiteEmbedding (Finsupp.single v a) = a • T.unitVector v := by
  have he : Finsupp.single v a = a • (Finsupp.single v 1 : ι →₀ ℝ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he, map_smul]
  rfl

lemma dual_coe_apply (x : T.Dual) (u : T.Primal) :
    x (u : T.JamesSpace) = ∑ v ∈ (T.ofPrimal u).support, T.ofPrimal u v * x (T.unitVector v) := by
  have hu := Finsupp.sum_single (T.ofPrimal u)
  have he := congrArg (fun z => x (T.finiteEmbedding z)) hu
  simp only [Finsupp.sum, map_sum, finiteEmbedding_single, map_smul, smul_eq_mul] at he
  change (∑ v ∈ (T.ofPrimal u).support, T.ofPrimal u v * x (T.unitVector v)) =
    x (u : T.JamesSpace) at he
  exact he.symm

/-- Full dual functionals are determined by all coordinate unit vectors. -/
lemma dual_ext {x y : T.Dual} (h : ∀ v, x (T.unitVector v) = y (T.unitVector v)) : x = y := by
  apply ContinuousLinearMap.ext
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u => simp only [dual_coe_apply, h]

def segmentFunctional (S : Finset ι) : T.Dual := ∑ v ∈ S, T.coordinate v

@[simp] lemma segmentFunctional_coe (S : Finset ι) (u : T.Primal) :
    T.segmentFunctional S (u : T.JamesSpace) = ∑ v ∈ S, T.ofPrimal u v := by
  simp only [segmentFunctional, sum_apply, coordinate_coe, ofPrimal]

@[simp] lemma segmentFunctional_unit (S : Finset ι) (v : ι) :
    T.segmentFunctional S (T.unitVector v) = if v ∈ S then 1 else 0 := by
  classical
  simp [segmentFunctional, coordinate_unitVector]

/-- Finite represented vectors retain their segment families as data. -/
def combine {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ) : T.Dual :=
  ∑ i, a i • T.segmentFunctional (S i)

@[simp] lemma combine_coe {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (a : κ → ℝ) (u : T.Primal) :
    T.combine S a (u : T.JamesSpace) = ∑ i, a i * (∑ v ∈ S i, T.ofPrimal u v) := by
  simp only [combine, sum_apply, smul_apply,
    segmentFunctional_coe, smul_eq_mul]

@[simp] lemma combine_unit {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (a : κ → ℝ) (v : ι) :
    T.combine S a (T.unitVector v) = ∑ i, if v ∈ S i then a i else 0 := by
  simp only [combine, sum_apply, smul_apply,
    segmentFunctional_unit, smul_eq_mul, mul_ite, mul_one, mul_zero]

lemma combine_add {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a b : κ → ℝ) :
    T.combine S (a+b) = T.combine S a + T.combine S b := by
  simp [combine, add_smul, Finset.sum_add_distrib]

lemma combine_sub {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a b : κ → ℝ) :
    T.combine S (a-b) = T.combine S a - T.combine S b := by
  unfold combine
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact sub_smul (a i) (b i) (T.segmentFunctional (S i))

lemma combine_unit_of_mem (F : T.Family) (a : Fin F.n → ℝ)
    (i : Fin F.n) {v : ι} (hv : v ∈ F.seg i) :
    T.combine F.seg a (T.unitVector v) = a i := by
  classical
  rw [combine_unit, Finset.sum_eq_single i]
  · simp only [ite_eq_left hv]
  · intro j _ hji
    rw [ite_eq_right (fun h => Finset.disjoint_left.mp (F.disjoint hji) h hv)]
  · simp

/-- Cauchy--Schwarz for represented disjoint segment coefficients, with empty
    pieces permitted after a projection. -/
lemma norm_combine_le {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ‖T.combine S a‖ ≤ Real.sqrt (∑ i, (a i) ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [combine_coe, Real.norm_eq_abs, UniformSpace.Completion.norm_coe, norm_eq_primal]
    have htest : Real.sqrt (∑ i, (∑ v ∈ S i, T.ofPrimal u v) ^ 2) ≤
        T.primalSeminorm (T.ofPrimal u) := by
      exact (Real.sqrt_le_left (apply_nonneg _ _)).mpr
        (T.test_energy_le_allow_empty S hS hd (T.ofPrimal u))
    calc
      |∑ i, a i * (∑ v ∈ S i, T.ofPrimal u v)| ≤
          ∑ i, |a i * (∑ v ∈ S i, T.ofPrimal u v)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |a i| * |∑ v ∈ S i, T.ofPrimal u v| := by simp only [abs_mul]
      _ ≤ Real.sqrt (∑ i, (a i) ^ 2) *
          Real.sqrt (∑ i, (∑ v ∈ S i, T.ofPrimal u v) ^ 2) := by
        simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun i => |a i|) (fun i => |∑ v ∈ S i, T.ofPrimal u v|)
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (Real.sqrt_nonneg _)

/-- A finite family of disjoint cones can be tested by independently maximizing
    each cone's represented segment. This is the finite dual reconstruction bound. -/
lemma norm_cone_mean_le {Ω κ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ]
    (S : Ω → κ → Finset ι) (a : Ω → κ → ℝ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hS : ∀ ω g, (S ω g).Nonempty → T.IsSegment (S ω g))
    (hd : ∀ g h, g ≠ h → ∀ ω ν, Disjoint (S ω g) (S ν h)) :
    ‖∑ ω, w ω • T.combine (S ω) (a ω)‖ ≤
      Real.sqrt (∑ g, (∑ ω, w ω * |a ω g|) ^ 2) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [sum_apply]
    simp only [smul_apply, smul_eq_mul, combine_coe, Real.norm_eq_abs,
      UniformSpace.Completion.norm_coe, norm_eq_primal]
    choose idx hidx hmax using fun g : κ => Finset.exists_max_image Finset.univ
      (fun ω => |∑ v ∈ S ω g, T.ofPrimal u v|) Finset.univ_nonempty
    let t : κ → ℝ := fun g => |∑ v ∈ S (idx g) g, T.ofPrimal u v|
    have ht (ω : Ω) (g : κ) : |∑ v ∈ S ω g, T.ofPrimal u v| ≤ t g :=
      hmax g ω (Finset.mem_univ _)
    have htest : Real.sqrt (∑ g, t g ^ 2) ≤ T.primalSeminorm (T.ofPrimal u) := by
      apply (Real.sqrt_le_left (apply_nonneg _ _)).2
      simpa only [t, sq_abs] using T.test_energy_le_allow_empty
        (fun g => S (idx g) g) (fun g => hS (idx g) g)
        (fun {g h} hgh => hd g h hgh (idx g) (idx h)) (T.ofPrimal u)
    calc
      |∑ ω, w ω * ∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| ≤
          ∑ ω, |w ω * ∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ω, w ω * |∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| := by
        simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ ω, w ω * (∑ g, |a ω g| * t g) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        calc
          _ ≤ ∑ g, |a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro g _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (ht ω g) (abs_nonneg _)
      _ = ∑ g, (∑ ω, w ω * |a ω g|) * t g := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ Real.sqrt (∑ g, (∑ ω, w ω * |a ω g|) ^ 2) * Real.sqrt (∑ g, t g ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (Real.sqrt_nonneg _)

lemma combine_smul {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ) (c : ℝ) :
    T.combine S (fun i => c * a i) = c • T.combine S a := by
  simp only [combine, mul_smul, Finset.smul_sum]

lemma headDual_unit (H : Finset ι) (x : T.Dual) (v : ι) :
    T.headDual H x (T.unitVector v) = if v ∈ H then x (T.unitVector v) else 0 := by
  classical
  simp [headDual_apply, coordinate_unitVector, mul_ite, Finset.sum_ite_eq]

lemma headDual_eq_self {H : Finset ι} {x : T.Dual}
    (hx : ∀ v, v ∉ H → x (T.unitVector v) = 0) : T.headDual H x = x := by
  apply T.dual_ext
  intro v
  rw [headDual_unit]
  split_ifs with hv
  · rfl
  · exact (hx v hv).symm

lemma headDual_finite_apply {H : Finset ι} (x : T.Dual) (u : T.Primal)
    (hu : (T.ofPrimal u).support ⊆ H) :
    T.headDual H x (u : T.JamesSpace) = x (u : T.JamesSpace) := by
  rw [dual_coe_apply, dual_coe_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rw [headDual_unit, ite_eq_left (hu hv)]

lemma headDual_commute (H K : Finset ι) (x : T.Dual) :
    T.headDual H (T.headDual K x) = T.headDual K (T.headDual H x) := by
  apply T.dual_ext
  intro v
  simp only [headDual_unit]
  split_ifs <;> rfl

lemma tailDual_headDual (H K : Finset ι) (x : T.Dual) :
    T.tailDual H (T.headDual K x) = T.headDual K (T.tailDual H x) := by
  rw [tailDual_apply, tailDual_apply, map_sub, headDual_commute]

/-- The array representing an arbitrary completed vector's finite head. -/
def headArray (H : Finset ι) (u : T.JamesSpace) : ι →₀ ℝ :=
  ∑ v ∈ H, T.coordinate v u • Finsupp.single v 1

lemma headArray_outside (H : Finset ι) (u : T.JamesSpace) {v : ι} (hv : v ∉ H) :
    T.headArray H u v = 0 := by
  classical
  simp [headArray, Finsupp.finsetSum_apply, Finsupp.single_apply, hv,
    Finset.sum_ite_eq']

lemma finiteEmbedding_headArray (H : Finset ι) (u : T.JamesSpace) :
    T.finiteEmbedding (T.headArray H u) = T.headPrimal H u := by
  simp only [headArray, map_sum, map_smul, finiteEmbedding_single, one_smul,
    headPrimal_apply]

lemma headDual_segment (H S : Finset ι) :
    T.headDual H (T.segmentFunctional S) = T.segmentFunctional (S.filter (· ∈ H)) := by
  apply T.dual_ext
  intro v
  rw [headDual_unit, segmentFunctional_unit, segmentFunctional_unit]
  simp only [Finset.mem_filter]
  split_ifs <;> simp_all

lemma tailDual_segment (H S : Finset ι) :
    T.tailDual H (T.segmentFunctional S) = T.segmentFunctional (S.filter (· ∉ H)) := by
  apply T.dual_ext
  intro v
  simp only [tailDual_apply, sub_apply, headDual_unit,
    segmentFunctional_unit, Finset.mem_filter]
  split_ifs <;> simp_all

lemma headDual_combine {κ : Type*} [Fintype κ] (H : Finset ι) (S : κ → Finset ι) (a : κ → ℝ) :
    T.headDual H (T.combine S a) = T.combine (fun i => (S i).filter (· ∈ H)) a := by
  simp only [combine, map_sum, map_smul, headDual_segment]

lemma tailDual_combine {κ : Type*} [Fintype κ] (H : Finset ι) (S : κ → Finset ι) (a : κ → ℝ) :
    T.tailDual H (T.combine S a) = T.combine (fun i => (S i).filter (· ∉ H)) a := by
  simp only [combine, map_sum, map_smul, tailDual_segment]

abbrev Coordinates (_T : SegmentSystem ι) (K : Finset ι) := K → ℝ

def coordinateTest (K : Finset ι) (a : T.Coordinates K) : ι →₀ ℝ :=
  Finsupp.onFinset K (fun v => if h : v ∈ K then a ⟨v, h⟩ else 0) (by
    intro v hv
    by_contra h
    simp only [dite_eq_right h] at hv
    exact hv rfl)

@[simp] lemma coordinateTest_mem (K : Finset ι) (a : T.Coordinates K) (v : K) :
    T.coordinateTest K a v.val = a v := by simp [coordinateTest]

lemma coordinateTest_not_mem (K : Finset ι) (a : T.Coordinates K)
    {v : ι} (hv : v ∉ K) : T.coordinateTest K a v = 0 := by simp [coordinateTest, hv]

lemma coordinateTest_sum (K S : Finset ι) (a : T.Coordinates K) (hSK : S ⊆ K) :
    (∑ v ∈ S, T.coordinateTest K a v) =
      ∑ v : K, if v.val ∈ S then a v else 0 := by
  classical
  have hfilter : K.filter (· ∈ S) = S := by ext v; simp; exact fun h => hSK h
  calc
    _ = ∑ v ∈ K, if v ∈ S then T.coordinateTest K a v else 0 := by
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ v : K, if v.val ∈ S then T.coordinateTest K a v.val else 0 :=
      (Finset.sum_coe_sort K _).symm
    _ = _ := by simp only [coordinateTest_mem]

lemma functional_pi_formula (K : Finset ι) (f : T.Coordinates K →L[ℝ] ℝ)
    (z : T.Coordinates K) : f z = ∑ v : K, z v * f (Pi.single v 1) := by
  classical
  have hz : z = ∑ v : K, z v • (Pi.single v 1 : T.Coordinates K) := by
    ext w
    simp [Pi.single_apply, Finset.sum_apply, mul_ite, Finset.sum_ite_eq]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- All local disjoint families. This type is finite even when the tree branches
    countably, because each member is a family of subsets of the fixed head K. -/
def LocalFamily (K : Finset ι) := {F : Finset (Finset ι) //
  F ∈ K.powerset.powerset ∧ (∀ S ∈ F, T.IsSegment S) ∧ (F : Set (Finset ι)).Pairwise Disjoint}

instance localFamilyFintype (K : Finset ι) : Fintype (T.LocalFamily K) :=
  Fintype.subtype (K.powerset.powerset.filter
    (fun F => (∀ S ∈ F, T.IsSegment S) ∧ (F : Set (Finset ι)).Pairwise Disjoint)) (by intro F; simp)

abbrev LocalIndex {K : Finset ι} (F : T.LocalFamily K) := ↥F.val

lemma localFamily_subset {K : Finset ι} (F : T.LocalFamily K) (S : T.LocalIndex F) :
    S.val ⊆ K :=
  Finset.mem_powerset.mp ((Finset.mem_powerset.mp F.property.1) S.property)

lemma localFamily_allowed {K : Finset ι} (F : T.LocalFamily K) (S : T.LocalIndex F) :
    T.IsSegment S.val := F.property.2.1 _ S.property

lemma localFamily_disjoint {K : Finset ι} (F : T.LocalFamily K) :
    Pairwise (fun S U : T.LocalIndex F => Disjoint S.val U.val) := by
  intro S U hne
  exact F.property.2.2 S.property U.property (fun h => hne (Subtype.ext h))

variable {T}

def LocalFamily.asFamily {K : Finset ι} (F : T.LocalFamily K) : T.Family where
  n := Fintype.card (T.LocalIndex F)
  seg i := ((Fintype.equivFin (T.LocalIndex F)).symm i).val
  allowed i := T.localFamily_allowed F _
  disjoint := by
    intro i j hij
    apply T.localFamily_disjoint F
    exact fun h => hij ((Fintype.equivFin (T.LocalIndex F)).symm.injective h)

def LocalFamily.reindex {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) : Fin F.asFamily.n → ℝ :=
  fun i => a ((Fintype.equivFin (T.LocalIndex F)).symm i)

lemma LocalFamily.reindex_energy {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    (∑ i, F.reindex a i ^ 2) = ‖a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  exact (Fintype.equivFin (T.LocalIndex F)).symm.sum_comp (fun i => a i ^ 2)

lemma LocalFamily.reindex_combine {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    T.combine F.asFamily.seg (F.reindex a) = T.combine (fun S : T.LocalIndex F => S.val) a := by
  unfold combine
  exact (Fintype.equivFin (T.LocalIndex F)).symm.sum_comp
    (fun S => a S • T.segmentFunctional S.val)

lemma LocalFamily.asFamily_subset {K : Finset ι} (F : T.LocalFamily K)
    (i : Fin F.asFamily.n) : F.asFamily.seg i ⊆ K :=
  T.localFamily_subset F _

variable (T)

/-- Local atoms as linear images of Euclidean blocks. -/
def localMap {K : Finset ι} (F : T.LocalFamily K) :
    EuclideanSpace ℝ (T.LocalIndex F) →ₗ[ℝ] T.Coordinates K where
  toFun a v := ∑ S : T.LocalIndex F, if v.val ∈ S.val then a S else 0
  map_add' a b := by
    ext v
    simp only [Pi.add_apply, PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp
  map_smul' a b := by
    ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp

lemma localMap_combine {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) (v : K) :
    T.localMap F a v = T.combine (fun S : T.LocalIndex F => S.val) a (T.unitVector v.val) := by
  simp [localMap, combine_unit]

lemma functional_localMap {K : Finset ι} (F : T.LocalFamily K)
    (f : T.Coordinates K →L[ℝ] ℝ) (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    f (T.localMap F a) = ∑ S : T.LocalIndex F, a S *
      (∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v) := by
  classical
  rw [T.functional_pi_formula]
  simp only [localMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [T.coordinateTest_sum K S.val _ (T.localFamily_subset F S), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

lemma finiteEmbedding_norm (p : ι →₀ ℝ) :
    ‖T.finiteEmbedding p‖ = T.primalSeminorm p := by
  rw [finiteEmbedding_apply, UniformSpace.Completion.norm_coe]
  rfl

lemma coordinateTest_pairing (K : Finset ι) (a : T.Coordinates K) (x : T.Dual) :
    x (T.finiteEmbedding (T.coordinateTest K a)) =
      ∑ v : K, a v * x (T.unitVector v.val) := by
  classical
  rw [finiteEmbedding_apply, dual_coe_apply]
  change (∑ v ∈ (T.coordinateTest K a).support,
    T.coordinateTest K a v * x (T.unitVector v)) = _
  have hs : (T.coordinateTest K a).support ⊆ K := by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv (T.coordinateTest_not_mem K a hn)
  calc
    _ = ∑ v ∈ K, T.coordinateTest K a v * x (T.unitVector v) := by
      apply Finset.sum_subset hs
      intro v _ hv
      rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
    _ = ∑ v : K, T.coordinateTest K a v.val * x (T.unitVector v.val) :=
      (Finset.sum_coe_sort K _).symm
    _ = _ := by simp only [coordinateTest_mem]

lemma local_energy_le_of_functional_bound {K : Finset ι} (F : T.LocalFamily K)
    (f : T.Coordinates K →L[ℝ] ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hf : ∀ a : EuclideanSpace ℝ (T.LocalIndex F), ‖a‖ ≤ 1 →
      f (T.localMap F a) ≤ u) :
    (∑ S : T.LocalIndex F, (∑ v ∈ S.val,
      T.coordinateTest K (fun w => f (Pi.single w 1)) v) ^ 2) ≤ u ^ 2 := by
  classical
  let b : EuclideanSpace ℝ (T.LocalIndex F) := WithLp.toLp 2
    (fun S => ∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v)
  have he : (∑ S : T.LocalIndex F, (∑ v ∈ S.val,
      T.coordinateTest K (fun w => f (Pi.single w 1)) v) ^ 2) = ‖b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [b, Real.norm_eq_abs, sq_abs]
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) hu).2
  by_cases hb : b = 0
  · simpa only [hb, norm_zero] using hu
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hbn : ‖‖b‖⁻¹ • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  have h := hf (‖b‖⁻¹ • b) hbn
  rw [T.functional_localMap] at h
  have hsum : (∑ S : T.LocalIndex F, (‖b‖⁻¹ • b) S *
      (∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v)) = ‖b‖ := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    change (∑ S, ‖b‖⁻¹ * b S * b S) = ‖b‖
    simp_rw [mul_assoc, ← sq]
    rw [← Finset.mul_sum]
    have hb2 : (∑ S, b S ^ 2) = ‖b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [hb2, sq, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rwa [hsum] at h

/-- An l1-of-Euclidean-block ball gives a compact convex parameter space for all
    finite atomic combinations. No Caratheodory theorem is assumed. -/
abbrev Coefficients (K : Finset ι) :=
  (F : T.LocalFamily K) → EuclideanSpace ℝ (T.LocalIndex F)

def totalMap (K : Finset ι) : T.Coefficients K →ₗ[ℝ] T.Coordinates K where
  toFun c := ∑ F, T.localMap F (c F)
  map_add' c d := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

def coefficientBall (K : Finset ι) (R : ℝ) : Set (T.Coefficients K) :=
  {c | ∑ F, ‖c F‖ ≤ R}

lemma coefficientBall_compact (K : Finset ι) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (T.coefficientBall K R) := by
  apply (isCompact_closedBall (0 : T.Coefficients K) R).of_isClosed_subset
  · exact isClosed_le (by fun_prop) continuous_const
  · intro c hc
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro F
    exact (Finset.single_le_sum (fun G _ => norm_nonneg (c G)) (Finset.mem_univ F)).trans hc

lemma coefficientBall_convex (K : Finset ι) (R : ℝ) :
    Convex ℝ (T.coefficientBall K R) := by
  intro c hc d hd a b ha hb hab
  change ∑ F, ‖a • c F + b • d F‖ ≤ R
  calc
    _ ≤ ∑ F, (a * ‖c F‖ + b * ‖d F‖) := by
      apply Finset.sum_le_sum
      intro F _
      calc
        ‖a • c F + b • d F‖ ≤ ‖a • c F‖ + ‖b • d F‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * (∑ F, ‖c F‖) + b * (∑ F, ‖d F‖) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hc ha)
      (mul_le_mul_of_nonneg_left hd hb)
    _ = R := by rw [← add_mul, hab, one_mul]

lemma totalMap_single (K : Finset ι) (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    T.totalMap K (Pi.single F a) = T.localMap F a := by
  classical
  rw [totalMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_eq_single F]
  · rw [Pi.single_eq_same]
  · intro G _ hGF
    rw [Pi.single_eq_of_ne hGF, map_zero]
  · simp

lemma single_mem_coefficientBall (K : Finset ι) (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (ha : ‖a‖ ≤ R) :
    Pi.single F a ∈ T.coefficientBall K R := by
  classical
  change ∑ G, ‖(Pi.single F a : T.Coefficients K) G‖ ≤ R
  rw [Finset.sum_eq_single F]
  · simpa only [Pi.single_eq_same] using ha
  · intro G _ hGF
    rw [Pi.single_eq_of_ne hGF, norm_zero]
  · simp

/-- A represented atom includes its coefficients, rather than just its value. -/
structure Atom (R : ℝ) where
  family : T.Family
  coeff : Fin family.n → ℝ
  energy_le : (∑ i, coeff i ^ 2) ≤ R ^ 2

def Atom.value {T : SegmentSystem ι} {R : ℝ} (a : T.Atom R) : T.Dual :=
  T.combine a.family.seg a.coeff

/-- Finite convex atom laws, with explicit probabilities and mean. -/
structure AtomLaw (Ω : Type*) [Fintype Ω] (R : ℝ) (x : T.Dual) where
  atom : Ω → T.Atom R
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  sum_one : ∑ ω, weight ω = 1
  mean : (∑ ω, weight ω • (atom ω).value) = x

def zeroAtom (R : ℝ) : T.Atom R where
  family := {
    n := 0
    seg := Fin.elim0
    allowed := fun i => Fin.elim0 i
    disjoint := fun {i} => Fin.elim0 i }
  coeff := Fin.elim0
  energy_le := by simpa using sq_nonneg R

@[simp] lemma zeroAtom_value (R : ℝ) : (T.zeroAtom R).value = 0 := by
  change (∑ i : Fin 0, (Fin.elim0 i : ℝ) • T.segmentFunctional (Fin.elim0 i)) = 0
  exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)

/-- Normalize a local block to radius R. A zero block stays zero. -/
def blockAtom {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (hR : 0 ≤ R) : T.Atom R where
  family := F.asFamily
  coeff := F.reindex ((R / ‖a‖) • a)
  energy_le := by
    rw [F.reindex_energy, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR (norm_nonneg _))]
    by_cases ha : a = 0
    · simp [ha, sq_nonneg]
    · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
      rw [div_mul_cancel₀ _ hn]

lemma blockAtom_value {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (hR : 0 ≤ R) :
    (T.blockAtom F a hR).value = (R / ‖a‖) • T.combine (fun S : T.LocalIndex F => S.val) a := by
  rw [Atom.value, blockAtom, F.reindex_combine]
  simp only [combine, PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma weighted_blockAtom {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (hR : 0 < R) :
    (‖a‖ / R) • (T.blockAtom F a hR.le).value =
      T.combine (fun S : T.LocalIndex F => S.val) a := by
  rw [T.blockAtom_value, smul_smul]
  by_cases ha : a = 0
  · simp [ha, combine]
  · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have he : ‖a‖ / R * (R / ‖a‖) = 1 := by field_simp
    rw [he, one_smul]

lemma representation_combine {K : Finset ι} (x : T.Dual) (c : T.Coefficients K)
    (hc : T.totalMap K c = fun v : K => x (T.unitVector v.val)) :
    (∑ F, T.combine (fun S : T.LocalIndex F => S.val) (c F)) = T.headDual K x := by
  apply T.dual_ext
  intro v
  simp only [sum_apply, headDual_unit]
  by_cases hv : v ∈ K
  · rw [ite_eq_left hv]
    have he := congrFun hc ⟨v,hv⟩
    change (∑ F, T.localMap F (c F)) ⟨v,hv⟩ = _ at he
    simp only [Finset.sum_apply, localMap_combine] at he
    exact he
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro F _
    rw [combine_unit]
    apply Finset.sum_eq_zero
    intro S _
    rw [ite_eq_right (fun h => hv (T.localFamily_subset F S h))]

/-- Every block decomposition is a finite probability law, with its unused mass
    placed on the zero atom. -/
def lawOfCoefficients {K : Finset ι} (x : T.Dual) {R : ℝ} (hR : 0 < R)
    (c : T.Coefficients K) (hc : c ∈ T.coefficientBall K R)
    (hce : T.totalMap K c = fun v : K => x (T.unitVector v.val)) :
    T.AtomLaw (Option (T.LocalFamily K)) R (T.headDual K x) where
  atom ω := match ω with
    | none => T.zeroAtom R
    | some F => T.blockAtom F (c F) hR.le
  weight ω := match ω with
    | none => 1 - ∑ F, ‖c F‖ / R
    | some F => ‖c F‖ / R
  nonneg := by
    intro ω
    cases ω with
    | none =>
      dsimp
      rw [← Finset.sum_div]
      exact sub_nonneg.mpr ((div_le_one hR).mpr hc)
    | some F => exact div_nonneg (norm_nonneg _) hR.le
  sum_one := by
    rw [Fintype.sum_option]
    dsimp
    ring
  mean := by
    rw [Fintype.sum_option]
    simp only [zeroAtom_value, smul_zero, zero_add]
    simp_rw [T.weighted_blockAtom _ _ hR]
    exact T.representation_combine x c hce

lemma lawOfCoefficients_subset {K : Finset ι} (x : T.Dual) {R : ℝ} (hR : 0 < R)
    (c : T.Coefficients K) (hc : c ∈ T.coefficientBall K R)
    (hce : T.totalMap K c = fun v : K => x (T.unitVector v.val))
    (ω : Option (T.LocalFamily K))
    (i : Fin ((T.lawOfCoefficients x hR c hc hce).atom ω).family.n) :
    ((T.lawOfCoefficients x hR c hc hce).atom ω).family.seg i ⊆ K := by
  cases ω with
  | none => exact Fin.elim0 i
  | some F => exact F.asFamily_subset i

structure BipolarLaw (Ω : Type*) [Fintype Ω] (R : ℝ) (x y : T.Dual)
    extends T.AtomLaw Ω R x where
  sign : Ω → ℝ
  abs_sign : ∀ ω, |sign ω| = 1
  signed_mean : (∑ ω, weight ω • (sign ω • (atom ω).value)) = y

def pairLaws {Ω : Type*} [Fintype Ω] {R : ℝ} {x y : T.Dual}
    (Lp : T.AtomLaw Ω R (x+y)) (Lm : T.AtomLaw Ω R (x-y)) :
    T.BipolarLaw (Bool × Ω) R x y where
  atom ω := if ω.1 then Lp.atom ω.2 else Lm.atom ω.2
  weight ω := (1/2 : ℝ) * (if ω.1 then Lp.weight ω.2 else Lm.weight ω.2)
  nonneg := by
    rintro ⟨b,ω⟩
    cases b <;> exact mul_nonneg (by norm_num) (by first | exact Lm.nonneg ω | exact Lp.nonneg ω)
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Lp.sum_one, Lm.sum_one]
    norm_num
  mean := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      mul_smul, ← Finset.smul_sum]
    rw [Lp.mean, Lm.mean]
    module
  sign ω := if ω.1 then 1 else -1
  abs_sign := by rintro ⟨b,ω⟩; cases b <;> norm_num
  signed_mean := by
    apply ContinuousLinearMap.ext
    intro u
    have hp := congrArg (fun f : T.Dual => f u) Lp.mean
    have hm := congrArg (fun f : T.Dual => f u) Lm.mean
    simp only [sum_apply, smul_apply, smul_eq_mul, add_apply] at hp
    simp only [sum_apply, smul_apply, smul_eq_mul, sub_apply] at hm
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    have hcoeff (ω : Ω) : (1/2:ℝ) * Lm.weight ω * (-1 * (Lm.atom ω).value u) =
        -(1/2:ℝ) * (Lm.weight ω * (Lm.atom ω).value u) := by ring
    simp_rw [hcoeff, one_mul, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hp, hm]
    ring

lemma pairLaws_subset {Ω : Type*} [Fintype Ω] {R : ℝ} {x y : T.Dual}
    (Lp : T.AtomLaw Ω R (x+y)) (Lm : T.AtomLaw Ω R (x-y)) (K : Finset ι)
    (hp : ∀ ω i, (Lp.atom ω).family.seg i ⊆ K)
    (hm : ∀ ω i, (Lm.atom ω).family.seg i ⊆ K) :
    ∀ ω i, ((T.pairLaws Lp Lm).atom ω).family.seg i ⊆ K := by
  rintro ⟨b,ω⟩ i
  cases b
  · exact hm ω i
  · exact hp ω i

/-- The norm-closed coordinate span, not the full infinite-tree dual. -/
def CoordinatePredual : Submodule ℝ T.Dual :=
  (Submodule.span ℝ (Set.range T.coordinate)).topologicalClosure

lemma span_coordinates_finite_support {x : T.Dual}
    (hx : x ∈ Submodule.span ℝ (Set.range T.coordinate)) :
    ∃ S : Finset ι, ∀ v, v ∉ S → x (T.unitVector v)=0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    refine ⟨{v}, ?_⟩
    intro w hw
    simp only [Finset.mem_singleton] at hw
    simp [coordinate_unitVector,hw]
  | zero => exact ⟨∅, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨S,hS⟩ := hx
    obtain ⟨U,hU⟩ := hy
    refine ⟨S ∪ U, ?_⟩
    intro v hv
    have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
    have hvU : v ∉ U := fun h => hv (Finset.mem_union_right _ h)
    simp only [add_apply,hS v hvS,hU v hvU,add_zero]
  | smul a x _ hx =>
    obtain ⟨S,hS⟩ := hx
    exact ⟨S, fun v hv => by simp only [smul_apply,hS v hv,smul_zero]⟩

end SegmentSystem

end DiamondDistortion

end

end OAI
