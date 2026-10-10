import OAI.Analysis.SegmentLenses.EndpointLaws

namespace OAI

/-!
# Arbitrarily indexed finite-height forests
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


namespace IndexedForest
variable {I : Type*}

def Vertex (height : I → ℕ) := {p : I × List ℕ // p.2.length ≤ height p.1}

def Ancestor {height : I → ℕ} (a b : Vertex height) : Prop :=
  a.val.1 = b.val.1 ∧ a.val.2.IsPrefix b.val.2

variable {height : I → ℕ}

theorem ancestor_refl (v : Vertex height) : Ancestor v v := ⟨rfl, List.prefix_rfl⟩
theorem ancestor_antisymm {a b : Vertex height} (ha : Ancestor a b) (hb : Ancestor b a) : a=b :=
  Subtype.ext (Prod.ext ha.1 (prefix_antisymm ha.2 hb.2))

instance : SegmentSystem (Vertex height) where
  isSegment := IsInterval Ancestor
  singleton v := by
    refine ⟨v, v, ancestor_refl _, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨ancestor_refl _, ancestor_refl _⟩
    · rintro ⟨hvw, hwv⟩
      exact ancestor_antisymm hwv hvw

instance : PartialOrder (Vertex height) where
  le := Ancestor
  lt := fun a b => Ancestor a b ∧ ¬ Ancestor b a
  le_refl := ancestor_refl
  le_trans := fun _ _ _ hab hbc => ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm := fun _ _ => ancestor_antisymm

instance : TreeOrder (Vertex height) where
  lower_chain := by
    intro a b c hac hbc
    rcases List.prefix_or_prefix_of_prefix hac.2 hbc.2 with hab | hba
    · exact Or.inl ⟨hac.1.trans hbc.1.symm, hab⟩
    · exact Or.inr ⟨hbc.1.trans hac.1.symm, hba⟩

instance : IntervalSegments (Vertex height) where
  iff_interval _ := Iff.rfl

instance : LocallyFiniteOrder (Vertex height) :=
  LocallyFiniteOrder.ofFiniteIcc (by
    intro a b
    apply Set.Finite.of_injOn (f := fun v : Vertex height => v.val.2)
      (t := {w : List ℕ | w.IsPrefix b.val.2})
    · intro v hv; exact hv.2.2
    · intro v hv w hw he
      exact Subtype.ext (Prod.ext (hv.2.1.trans hw.2.1.symm) he)
    · exact b.val.2.inits.finite_toSet.subset (by
        intro w hw; exact (List.mem_inits w b.val.2).mpr hw))

instance : LocallyFiniteOrderBot (Vertex height) := by
  classical
  have hf : ∀ b : Vertex height, {v : Vertex height | v ≤ b}.Finite := by
    intro b
    apply Set.Finite.of_injOn (f := fun v : Vertex height => v.val.2)
      (t := {w : List ℕ | w.IsPrefix b.val.2})
    · intro v hv; exact hv.2
    · intro v hv w hw he
      exact Subtype.ext (Prod.ext (hv.1.trans hw.1.symm) he)
    · exact b.val.2.inits.finite_toSet.subset (by
        intro w hw; exact (List.mem_inits w b.val.2).mpr hw)
  exact LocallyFiniteOrderBot.ofIic (Vertex height) (fun b => (hf b).toFinset)
    (fun a x => by simp)

instance [Countable I] : Countable (Vertex height) := by unfold Vertex; infer_instance

abbrev J (height : I → ℕ) := Primal (Vertex height)
abbrev X (height : I → ℕ) := FullDual (Vertex height)

variable [decidableEqI : DecidableEq I]
local instance : DecidableEq (Vertex height) := Classical.decEq _
section HeightBlocks


def heightTest (h : I) : Test (Vertex height) →ₗ[ℝ] Test (Vertex height) where
  toFun u := Test.ofFinsupp (u.coeff.filter (fun v => v.val.1 = h))
  map_add' _u _v := Finsupp.filter_add
  map_smul' _c _u := Finsupp.filter_smul

@[simp] theorem heightTest_apply (h : I) (u : Test (Vertex height)) (v : (Vertex height)) :
    ((heightTest (height := height)) h u).coeff v = if v.val.1 = h then u.coeff v else 0 := Finsupp.filter_apply _ _ _

theorem norm_heightTest_le (h : I) (u : Test (Vertex height)) : ‖(heightTest (height := height)) h u‖ ≤ ‖u‖ := by
  classical
  apply norm_filter_le
  intro a b v ha hb hav hvb
  exact hav.1.symm.trans ha


theorem segment_same_height {S : Finset (Vertex height)} (hS : SegmentSystem.isSegment S)
    {v w : (Vertex height)} (hv : v ∈ S) (hw : w ∈ S) : v.val.1 = w.val.1 := by
  have _ := decidableEqI
  obtain ⟨a, b, hab, hs⟩ := hS
  exact ((hs v).mp hv).1.1.symm.trans ((hs w).mp hw).1.1


theorem segment_level_injective {S : Finset (Vertex height)} (hS : SegmentSystem.isSegment S) :
    Set.InjOn (fun v : (Vertex height) => v.val.2.length) S := by
  have _ := decidableEqI
  obtain ⟨a, b, hab, hs⟩ := hS
  intro v hv w hw he
  have hvb := ((hs v).mp hv).2
  have hwb := ((hs w).mp hw).2
  apply Subtype.ext
  refine Prod.ext (hvb.1.trans hwb.1.symm) ?_
  rcases List.prefix_or_prefix_of_prefix hvb.2 hwb.2 with h | h
  · exact h.eq_of_length he
  · exact (h.eq_of_length he.symm).symm

theorem segment_card_bound {S : Finset (Vertex height)} (hS : SegmentSystem.isSegment S)
    {h : I} (hc : ∀ v ∈ S, v.val.1 = h) : S.card ≤ height h + 1 := by
  classical
  calc
    S.card = (S.image (fun v => v.val.2.length)).card :=
      (Finset.card_image_of_injOn ((segment_level_injective (height := height)) hS)).symm
    _ ≤ (Finset.range (height h + 1)).card := Finset.card_le_card (by
      intro n hn
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
      apply Finset.mem_range.mpr
      have hh := v.property
      rw [hc v hv] at hh
      omega)
    _ = height h + 1 := Finset.card_range _


def familyAtHeight (F : SegmentFamily (Vertex height)) (h : I) :
    SegmentFamily (Vertex height) where
  sets := F.sets.filter (fun S => ∀ v ∈ S, v.val.1 = h)
  segment S hS := F.segment S (Finset.mem_filter.mp hS).1
  disjoint := by
    intro S hS T hT hne
    exact F.disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem atHeight_seminorm (F : SegmentFamily (Vertex height)) (h : I) (u : Test (Vertex height)) :
    ((familyAtHeight (height := height)) F h).seminorm u.coeff = F.seminorm ((heightTest (height := height)) h u).coeff := by
  have he : ((familyAtHeight (height := height)) F h).seminorm u.coeff ^ 2 = F.seminorm ((heightTest (height := height)) h u).coeff ^ 2 := by
    rw [SegmentFamily.seminorm_sq, SegmentFamily.seminorm_sq]
    rw [Finset.sum_coe_sort ((familyAtHeight (height := height)) F h).sets (fun S => (∑ v ∈ S, u.coeff v) ^ 2),
      Finset.sum_coe_sort F.sets (fun S => (∑ v ∈ S, ((heightTest (height := height)) h u).coeff v) ^ 2)]
    change (∑ S ∈ F.sets.filter _, _) = ∑ S ∈ F.sets, _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs with hc
    · congr 1
      apply Finset.sum_congr rfl
      intro v hv
      simp only [(heightTest_apply (height := height)), hc v hv, ite_true]
    · have hz : ∀ v ∈ S, v.val.1 ≠ h := by
        intro v hv heq
        apply hc
        intro w hw
        exact ((segment_same_height (height := height)) (F.segment S hS) hw hv).trans heq
      simp only [(heightTest_apply (height := height))]
      simp only [Finset.sum_eq_zero (fun v hv => ite_eq_right (hz v hv)), zero_pow (by decide : 2 ≠ 0)]
  nlinarith [apply_nonneg ((familyAtHeight (height := height)) F h).seminorm u.coeff,
    apply_nonneg F.seminorm ((heightTest (height := height)) h u).coeff]



theorem height_hilbert_upper (h : I) (u : Test (Vertex height))
    (hu : (heightTest (height := height)) h u = u) :
    ‖u‖ ^ 2 ≤ (height h + 1 : ℝ) * ∑ v ∈ u.coeff.support, u.coeff v ^ 2 := by
  classical
  obtain ⟨F, hF⟩ := exists_norming_family u
  let G := (familyAtHeight (height := height)) F h
  have hG : G.seminorm u.coeff = ‖u‖ := by rw [(atHeight_seminorm (height := height)), hu, hF]
  rw [← hG, G.seminorm_sq]
  have hlocal : ∀ S : G.sets, (∑ v ∈ S.val, u.coeff v) ^ 2 ≤
      (height h + 1 : ℝ) * ∑ v ∈ S.val, u.coeff v ^ 2 := by
    intro S
    have hcs : (∑ v ∈ S.val, u.coeff v) ^ 2 ≤
        (S.val.card : ℝ) * ∑ v ∈ S.val, u.coeff v ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S.val (fun _ => (1 : ℝ)) (fun v => u.coeff v)
    have hc := (segment_card_bound (height := height)) (G.segment _ S.property)
      (Finset.mem_filter.mp S.property).2
    have hcr : (S.val.card : ℝ) ≤ height h + 1 := by exact_mod_cast hc
    exact hcs.trans (mul_le_mul_of_nonneg_right hcr (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    (∑ S : G.sets, (∑ v ∈ S.val, u.coeff v) ^ 2) ≤
        ∑ S : G.sets, (height h + 1 : ℝ) * ∑ v ∈ S.val, u.coeff v ^ 2 := Finset.sum_le_sum (fun S _ => hlocal S)
    _ = (height h + 1 : ℝ) * ∑ S : G.sets, ∑ v ∈ S.val, u.coeff v ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ (height h + 1 : ℝ) * ∑ v ∈ u.coeff.support, u.coeff v ^ 2 := by
      gcongr
      rw [Finset.sum_coe_sort G.sets (fun S => ∑ v ∈ S, u.coeff v ^ 2)]
      have hs : (∑ v ∈ G.sets.biUnion id, u.coeff v ^ 2) =
          ∑ S ∈ G.sets, ∑ v ∈ S, u.coeff v ^ 2 := by
        simpa only [id_eq] using Finset.sum_biUnion (f := fun v => u.coeff v ^ 2) G.disjoint
      rw [← hs]
      have he : (∑ v ∈ G.sets.biUnion id, u.coeff v ^ 2) =
          ∑ v ∈ G.sets.biUnion id ∩ u.coeff.support, u.coeff v ^ 2 := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro v hv hnv
        have hn : v ∉ u.coeff.support := fun hs => hnv (Finset.mem_inter.mpr ⟨hv, hs⟩)
        simp only [Finsupp.notMem_support_iff.mp hn, zero_pow (by decide : 2 ≠ 0)]
      rw [he]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => sq_nonneg _)

end HeightBlocks

section ForestNormDecomposition

def testHeights (u : Test (Vertex height)) : Finset I := u.coeff.support.image (fun v => v.val.1)

theorem heightTest_eq_zero {u : Test (Vertex height)} {h : I} (hh : h ∉ (testHeights (height := height)) u) :
    (heightTest (height := height)) h u = 0 := by
  apply Finsupp.ext
  intro v
  change ((heightTest (height := height)) h u).coeff v = 0
  rw [(heightTest_apply (height := height))]
  split_ifs with hv
  · apply Finsupp.notMem_support_iff.mp
    intro hs
    exact hh (Finset.mem_image.mpr ⟨v, hs, hv⟩)
  · rfl

theorem heightTest_idem (h : I) (u : Test (Vertex height)) :
    (heightTest (height := height)) h ((heightTest (height := height)) h u) = (heightTest (height := height)) h u := by
  apply Finsupp.ext
  intro v
  change ((heightTest (height := height)) h ((heightTest (height := height)) h u)).coeff v = ((heightTest (height := height)) h u).coeff v
  by_cases hv : v.val.1 = h <;> simp [(heightTest_apply (height := height)), hv]

theorem heightTest_ne {h k : I} (hk : h ≠ k) (u : Test (Vertex height)) :
    (heightTest (height := height)) h ((heightTest (height := height)) k u) = 0 := by
  apply Finsupp.ext
  intro v
  change ((heightTest (height := height)) h ((heightTest (height := height)) k u)).coeff v = 0
  simp only [(heightTest_apply (height := height))]
  split_ifs with hv hv'
  · exact (hk (hv.symm.trans hv')).elim
  · rfl
  · rfl


theorem forest_norm_sq_decomposition (u : Test (Vertex height)) :
    ‖u‖ ^ 2 = ∑ h ∈ (testHeights (height := height)) u, ‖(heightTest (height := height)) h u‖ ^ 2 := by
  classical
  apply le_antisymm
  · obtain ⟨F, hF⟩ := exists_norming_family u
    have he : F.seminorm u.coeff ^ 2 =
        ∑ h ∈ (testHeights (height := height)) u, F.seminorm ((heightTest (height := height)) h u).coeff ^ 2 := by
      simp_rw [F.seminorm_sq]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      obtain ⟨a, b, hab, hs⟩ := F.segment S.val S.property
      have hc : ∀ v ∈ S.val, v.val.1 = a.val.1 := fun v hv => ((hs v).mp hv).1.1.symm
      have hv : ∀ h, (∑ v ∈ S.val, ((heightTest (height := height)) h u).coeff v) ^ 2 =
          if h = a.val.1 then (∑ v ∈ S.val, u.coeff v) ^ 2 else 0 := by
        intro h
        by_cases hh : h = a.val.1
        · subst h
          simp only [(heightTest_apply (height := height)), Finset.sum_congr rfl (fun v hv => ite_eq_left (hc v hv)), ite_true]
        · have hn : ∀ v ∈ S.val, v.val.1 ≠ h := fun v hv he => hh (he.symm.trans (hc v hv))
          simp only [(heightTest_apply (height := height)), Finset.sum_congr rfl (fun v hv => ite_eq_right (hn v hv)), Finset.sum_const_zero,
            zero_pow (by decide : 2 ≠ 0), ite_eq_right hh]
      simp_rw [hv]
      by_cases ha : a.val.1 ∈ (testHeights (height := height)) u
      · simp only [Finset.sum_ite_eq', ite_eq_left ha]
      · have hz : ∑ v ∈ S.val, u.coeff v = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          apply Finsupp.notMem_support_iff.mp
          intro hvs
          exact ha (Finset.mem_image.mpr ⟨v, hvs, hc v hv⟩)
        simp [hz]
    rw [← hF, he]
    exact Finset.sum_le_sum (fun h _ => sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg _) |>.mpr
      (le_segmentSeminorm _ _))
  · have hex : ∀ h : (testHeights (height := height)) u, ∃ F : SegmentFamily (Vertex height),
        F.seminorm ((heightTest (height := height)) h.val u).coeff = ‖(heightTest (height := height)) h.val u‖ :=
      fun h => exists_norming_family _
    choose F hF using hex
    let G : (testHeights (height := height)) u → SegmentFamily (Vertex height) := fun h => (familyAtHeight (height := height)) (F h) h.val
    have hn : ∀ h, (G h).seminorm u.coeff = ‖(heightTest (height := height)) h.val u‖ := by
      intro h
      exact ((atHeight_seminorm (height := height)) (F h) h.val u).trans (hF h)
    let pieces : (h : (testHeights (height := height)) u) × (G h).sets → Finset (Vertex height) := fun j => j.2.val
    have hseg : ∀ j, pieces j = ∅ ∨ SegmentSystem.isSegment (pieces j) := fun j =>
      Or.inr ((G j.1).segment _ j.2.property)
    have hd : Pairwise fun i j => Disjoint (pieces i) (pieces j) := by
      intro i j hij
      by_cases hh : i.1 = j.1
      · rcases i with ⟨i, S⟩
        rcases j with ⟨j, T⟩
        dsimp at hh
        subst j
        exact (G i).disjoint S.property T.property (fun he => hij (by cases Subtype.ext he; rfl))
      · apply Finset.disjoint_left.mpr
        intro v hv hw
        have hvh := (Finset.mem_filter.mp i.2.property).2 v hv
        have hwh := (Finset.mem_filter.mp j.2.property).2 v hw
        exact hh (Subtype.ext (hvh.symm.trans hwh))
    have hb := indexed_test_bound u.coeff pieces hseg hd
    change (∑ j, (∑ v ∈ pieces j, u.coeff v) ^ 2) ≤ ‖u‖ ^ 2 at hb
    rw [Fintype.sum_sigma] at hb
    have he : (∑ h : (testHeights (height := height)) u, ∑ S : (G h).sets, (∑ v ∈ S.val, u.coeff v) ^ 2) =
        ∑ h ∈ (testHeights (height := height)) u, ‖(heightTest (height := height)) h u‖ ^ 2 := by
      rw [← Finset.sum_coe_sort ((testHeights (height := height)) u) (fun h => ‖(heightTest (height := height)) h u‖ ^ 2)]
      apply Finset.sum_congr rfl
      intro h hh
      rw [← (G h).seminorm_sq, hn]
    exact he ▸ hb

end ForestNormDecomposition

section HeightHilbertEquivalence



def heightTests (h : I) : Submodule ℝ (Test (Vertex height)) := LinearMap.range ((heightTest (height := height)) h)

theorem mem_heightTests {h : I} {u : Test (Vertex height)} :
    u ∈ (heightTests (height := height)) h ↔ (heightTest (height := height)) h u = u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (heightTest_idem (height := height)) h v
  · intro hu
    exact ⟨u, hu⟩

abbrev HeightPrimal (h : I) := UniformSpace.Completion ((heightTests (height := height)) h)

def heightHilbert (h : I) : Submodule ℝ (lp (fun _ : (Vertex height) => ℝ) 2) where
  carrier := {x | ∀ v : (Vertex height), v.val.1 ≠ h → x v = 0}
  zero_mem' := by intro v hv; rfl
  add_mem' := by intro x y hx hy v hv; simp only [lp.coeFn_add, Pi.add_apply, hx v hv, hy v hv, add_zero]
  smul_mem' := by intro c x hx v hv; simp only [lp.coeFn_smul, Pi.smul_apply, hx v hv, smul_zero]

theorem heightHilbert_closed (h : I) : IsClosed ((heightHilbert (height := height)) h : Set (lp (fun _ : (Vertex height) => ℝ) 2)) := by
  have _ := decidableEqI
  change IsClosed {x : lp (fun _ : (Vertex height) => ℝ) 2 | ∀ v, v.val.1 ≠ h → x v = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  exact isClosed_eq (lp.evalCLM ℝ (fun _ : (Vertex height) => ℝ) 2 v).continuous continuous_const

instance (h : I) : CompleteSpace ((heightHilbert (height := height)) h) := ((heightHilbert_closed (height := height)) h).completeSpace_coe


def heightToHilbert (h : I) : (heightTests (height := height)) h →ₗ[ℝ] (heightHilbert (height := height)) h where
  toFun u := ⟨testL2 u.val, by
    intro v hv
    rw [testL2_apply, ← (mem_heightTests (height := height)).mp u.property]
    exact ite_eq_right hv⟩
  map_add' u v := Subtype.ext (testL2.map_add u.val v.val)
  map_smul' c u := Subtype.ext (testL2.map_smul c u.val)

@[simp] theorem heightToHilbert_apply (h : I) (u : (heightTests (height := height)) h) (v : (Vertex height)) :
    ((heightToHilbert (height := height)) h u).val v = u.val.coeff v := testL2_apply _ _


theorem heightToHilbert_dense (h : I) : DenseRange ((heightToHilbert (height := height)) h) := by
  classical
  intro x
  let u : Finset (Vertex height) → (heightTests (height := height)) h := fun s =>
    ⟨(heightTest (height := height)) h (Test.ofFinite s (fun v => x.val v)), ⟨_, rfl⟩⟩
  have he : ∀ s, ((heightToHilbert (height := height)) h (u s)).val = ∑ v ∈ s, lp.single 2 v (x.val v) := by
    intro s
    apply Subtype.ext
    funext v
    simp only [(heightToHilbert_apply (height := height)), u, (heightTest_apply (height := height))]
    rw [Test.coeff_ofFinite]
    have hs : (∑ w ∈ s, lp.single 2 w (x.val w)) v = if v ∈ s then x.val v else 0 := by
      simp only [lp.coeFn_sum, Finset.sum_apply]
      by_cases hv : v ∈ s
      · rw [Finset.sum_eq_single v]
        · simp only [lp.single_apply_self, ite_eq_left hv]
        · intro w hw hwv; exact lp.single_apply_ne _ _ _ hwv.symm
        · exact fun hn => (hn hv).elim
      · rw [ite_eq_right hv]
        apply Finset.sum_eq_zero
        intro w hw
        exact lp.single_apply_ne _ _ _ (fun he => hv (he ▸ hw))
    rw [hs]
    by_cases hv : v.val.1 = h
    · simp [hv]
    · simp [hv, x.property v hv]
  have ht : Filter.Tendsto (fun s => (heightToHilbert (height := height)) h (u s)) Filter.atTop (nhds x) := by
    apply tendsto_subtype_rng.mpr
    simpa only [HasSum, SummationFilter.unconditional_filter, he] using (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x.val)
  exact isClosed_closure.mem_of_tendsto ht (Filter.Eventually.of_forall (fun s =>
    subset_closure ⟨u s, rfl⟩))


def heightHilbertEquiv (h : I) : (HeightPrimal (height := height)) h ≃L[ℝ] (heightHilbert (height := height)) h :=
  (LinearEquiv.refl ℝ ((heightTests (height := height)) h)).extend
    (UniformSpace.Completion.toComplL : (heightTests (height := height)) h →L[ℝ] (HeightPrimal (height := height)) h).toLinearMap
    ((heightToHilbert (height := height)) h)
    UniformSpace.Completion.denseRange_coe
    ⟨1, fun u => by
      change ‖testL2 u.val‖ ≤ 1 * ‖(u : (HeightPrimal (height := height)) h)‖
      rw [one_mul, UniformSpace.Completion.norm_coe]
      exact norm_testL2_le u.val⟩
    ((heightToHilbert_dense (height := height)) h)
    ⟨Real.sqrt (height h + 1), fun u => by
      change ‖(u : (HeightPrimal (height := height)) h)‖ ≤ Real.sqrt (height h + 1) * ‖testL2 u.val‖
      rw [UniformSpace.Completion.norm_coe]
      have hb := (height_hilbert_upper (height := height)) h u.val ((mem_heightTests (height := height)).mp u.property)
      change ‖u.val‖ ≤ _
      rw [← norm_testL2_sq] at hb
      have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ height h + 1)
      nlinarith [norm_nonneg u, norm_nonneg (testL2 u.val), Real.sqrt_nonneg (height h + 1),
        mul_nonneg (Real.sqrt_nonneg (height h + 1)) (norm_nonneg (testL2 u.val))]⟩

theorem heightPrimal_reflexive (h : I) : Reflexive ((HeightPrimal (height := height)) h) :=
  (hilbert_reflexive ((heightHilbert (height := height)) h)).of_equiv ((heightHilbertEquiv (height := height)) h).symm

end HeightHilbertEquivalence

section ForestCompletionIdentification

local instance heightPrimalFamilyNormed : ∀ h, NormedAddCommGroup ((HeightPrimal (height := height)) h) := fun _h => inferInstance
local instance heightPrimalFamilySpace : ∀ h, NormedSpace ℝ ((HeightPrimal (height := height)) h) := fun _h => inferInstance
local instance : Module ℝ (J height) := (inferInstance : NormedSpace ℝ (J height)).toModule
local instance : Module ℝ (L2Sum (HeightPrimal (height := height))) := (inferInstance : NormedSpace ℝ (L2Sum (HeightPrimal (height := height)))).toModule
local instance : AddCommMonoid (L2Sum (HeightPrimal (height := height))) :=
  (inferInstance : NormedAddCommGroup (L2Sum (HeightPrimal (height := height)))).toAddCommMonoid


def heightBlockTest (h : I) : Test (Vertex height) →ₗ[ℝ] (HeightPrimal (height := height)) h :=
  (UniformSpace.Completion.toComplL : (heightTests (height := height)) h →L[ℝ] (HeightPrimal (height := height)) h).toLinearMap.comp
    ((heightTest (height := height)) h).rangeRestrict

@[simp] theorem norm_heightBlockTest (h : I) (u : Test (Vertex height)) :
    ‖(heightBlockTest (height := height)) h u‖ = ‖(heightTest (height := height)) h u‖ := UniformSpace.Completion.norm_coe _

theorem heightBlockTest_zero {h : I} {u : Test (Vertex height)} (hz : (heightTest (height := height)) h u = 0) :
    (heightBlockTest (height := height)) h u = 0 := by
  apply norm_eq_zero.mp
  exact ((norm_heightBlockTest (height := height)) h u).trans (by rw [hz, norm_zero])

def forestBlockVector (u : Test (Vertex height)) : L2Sum (HeightPrimal (height := height)) :=
  ∑ h ∈ (testHeights (height := height)) u, lp.single 2 h ((heightBlockTest (height := height)) h u)

@[simp] theorem forestBlockVector_apply (u : Test (Vertex height)) (h : I) :
    (forestBlockVector (height := height)) u h = (heightBlockTest (height := height)) h u := by
  classical
  simp only [forestBlockVector, lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single h]
  · exact lp.single_apply_self _ _ _
  · intro k hk hkh
    exact lp.single_apply_ne _ _ _ hkh.symm
  · intro hh
    simp only [(heightBlockTest_zero (height := height)) ((heightTest_eq_zero (height := height)) hh), lp.single_zero, lp.coeFn_zero, Pi.zero_apply]

def forestTestBlocks : Test (Vertex height) →ₗ[ℝ] L2Sum (HeightPrimal (height := height)) where
  toFun := (forestBlockVector (height := height))
  map_add' u v := by
    apply Subtype.ext
    funext h
    simp only [(forestBlockVector_apply (height := height)), lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c u := by
    apply Subtype.ext
    funext h
    simp only [(forestBlockVector_apply (height := height)), lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem forestTestBlocks_apply (u : Test (Vertex height)) (h : I) :
    (forestTestBlocks (height := height)) u h = (heightBlockTest (height := height)) h u := (forestBlockVector_apply (height := height)) u h

theorem norm_forestTestBlocks (u : Test (Vertex height)) : ‖(forestTestBlocks (height := height)) u‖ = ‖u‖ := by
  have he : ‖(forestTestBlocks (height := height)) u‖ ^ 2 = ‖u‖ ^ 2 := by
    change ‖∑ h ∈ (testHeights (height := height)) u, lp.single 2 h ((heightBlockTest (height := height)) h u)‖ ^ 2 = _
    rw [l2_norm_sum_single_sq, (forest_norm_sq_decomposition (height := height))]
    simp only [(norm_heightBlockTest (height := height))]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he



theorem forestTestBlocks_of_height (h : I) (u : (heightTests (height := height)) h) :
    (forestTestBlocks (height := height)) u.val = lp.single 2 h (u : (HeightPrimal (height := height)) h) := by
  classical
  apply Subtype.ext
  funext k
  rw [(forestTestBlocks_apply (height := height))]
  by_cases hk : k = h
  · subst k
    rw [lp.single_apply_self]
    change ((⟨(heightTest (height := height)) h u.val, _⟩ : (heightTests (height := height)) h) : (HeightPrimal (height := height)) h) = _
    congr 1
    exact Subtype.ext ((mem_heightTests (height := height)).mp u.property)
  · rw [lp.single_apply_ne _ _ _ hk]
    apply (heightBlockTest_zero (height := height))
    rw [← (mem_heightTests (height := height)).mp u.property]
    exact (heightTest_ne (height := height)) hk u.val



theorem forestTestBlocks_dense : DenseRange (forestTestBlocks (height := height)) := by
  classical
  let M := (LinearMap.range (forestTestBlocks (height := height))).topologicalClosure
  have hclosed : IsClosed (M : Set (L2Sum (HeightPrimal (height := height)))) := Submodule.isClosed_topologicalClosure _
  have hs : ∀ h (x : (HeightPrimal (height := height)) h), lp.single 2 h x ∈ M := by
    intro h x
    refine UniformSpace.Completion.induction_on x
      (p := fun x => lp.single 2 h x ∈ M)
      (by exact hclosed.preimage (lp.singleContinuousLinearMap ℝ (HeightPrimal (height := height)) 2 h).continuous) ?_
    intro u
    apply Submodule.le_topologicalClosure
    exact ⟨u.val, (forestTestBlocks_of_height (height := height)) h u⟩
  intro x
  change x ∈ M
  apply hclosed.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun s => M.sum_mem (fun h hh => hs h (x h)))


def forestL2Equiv : (J height) ≃ₗᵢ[ℝ] L2Sum (HeightPrimal (height := height)) :=
  (LinearEquiv.refl ℝ (Test (Vertex height))).extendOfIsometry
    (UniformSpace.Completion.toComplL : Test (Vertex height) →L[ℝ] (J height)).toLinearMap
    (forestTestBlocks (height := height)) UniformSpace.Completion.denseRange_coe (forestTestBlocks_dense (height := height))
    (fun u => by
      change ‖(forestTestBlocks (height := height)) u‖ = ‖(u : (J height))‖
      rw [UniformSpace.Completion.norm_coe]
      exact (norm_forestTestBlocks (height := height)) u)

@[simp] theorem forestL2Equiv_test (u : Test (Vertex height)) :
    (forestL2Equiv (height := height)) (u : (J height)) = (forestTestBlocks (height := height)) u :=
  by
    change (forestL2Equiv (height := height)) ((UniformSpace.Completion.toComplL : Test (Vertex height) →L[ℝ] (J height)) u) = _
    unfold forestL2Equiv
    exact
      (LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℝ (Test (Vertex height)))
        (UniformSpace.Completion.toComplL : Test (Vertex height) →L[ℝ] (J height)).toLinearMap
        (forestTestBlocks (height := height)) UniformSpace.Completion.denseRange_coe (forestTestBlocks_dense (height := height))
        (fun u => by change ‖(forestTestBlocks (height := height)) u‖ = ‖(u : (J height))‖; rw [UniformSpace.Completion.norm_coe]; exact (norm_forestTestBlocks (height := height)) u) u)


theorem forest_primal_reflexive : Reflexive (J height) :=
  (l2Sum_reflexive (HeightPrimal (height := height)) (heightPrimal_reflexive (height := height))).of_equiv
    (forestL2Equiv (height := height)).symm.toContinuousLinearEquiv


theorem forest_dual_reflexive : Reflexive (X height) := (forest_primal_reflexive (height := height)).dual

end ForestCompletionIdentification

end IndexedForest



end SegmentLenses

end

end OAI
