import OAI.Analysis.SeparableQuotients.RamseyThinning

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def ordinalHull (s : Finset Γ) (hs : s.Nonempty) : Set Γ :=
  Set.Icc (s.min' hs) (s.max' hs)

lemma ordinalHull_connected (s : Finset Γ) (hs : s.Nonempty) :
    Set.OrdConnected (ordinalHull s hs) := Set.ordConnected_Icc

lemma mem_ordinalHull {s : Finset Γ} (hs : s.Nonempty) {a : Γ} (ha : a ∈ s) :
    a ∈ ordinalHull s hs := ⟨s.min'_le _ ha, s.le_max' _ ha⟩

lemma ordinalHull_successive {s t : Finset Γ} (hs : s.Nonempty) (ht : t.Nonempty)
    (h : ∀ a ∈ s, ∀ b ∈ t, a < b) :
    ∀ a ∈ ordinalHull s hs, ∀ b ∈ ordinalHull t ht, a < b := by
  intro a ha b hb
  exact ha.2.trans_lt ((h _ (s.max'_mem hs) _ (t.min'_mem ht)).trans_le hb.1)

noncomputable def intervalProjection (I : Set Γ) (hI : Set.OrdConnected I) : E →L[ℝ] E :=
  projection (Crop.ordinalSet I hI)

lemma abs_eval_supported_interval (g : Array) (hg : g ∈ Full)
    (I : Set Γ) (hI : Set.OrdConnected I) (hs : (g.support : Set Γ) ⊆ I) (x : E) :
    |norming.evaluateArray x g| ≤ ‖intervalProjection I hI x‖ := by
  have hr : restrict I g = g := by
    ext a
    by_cases ha : a ∈ I
    · simp [ha]
    · have hz : g a = 0 := by
        by_contra hne
        exact ha (hs (Finsupp.mem_support_iff.mpr hne))
      simp [ha, hz]
  have he : norming.evaluateArray (intervalProjection I hI x) g = norming.evaluateArray x g := by
    rw [intervalProjection, evaluateArray_projection, Crop.ordinalSet_set, hr]
  rw [← he, norming.evaluateArray_eq_functional _ ⟨g, hg⟩]
  exact norming.functional_bound _ _

/-- An interval-partition inequality and its constant-16 difference-vector version. Intervals may be unbounded or singletons. -/
def PartitionBound (x : E) (N : ℕ) (A r : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → d ≤ N → ∀ (I : Fin d → Set Γ) (hI : ∀ i, Set.OrdConnected (I i)),
    (∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) →
    ∑ i : Fin d, ‖intervalProjection (I i) (hI i) x‖ ≤ A * (d : ℝ)^(1/r)

lemma typeI_eval_le_of_partition {f : Family} (x : E) (N : ℕ) (A : ℝ)
    (hA : 0 ≤ A) (hx : PartitionBound x N A f.r) (e : TypeI f)
    (he : ∀ i, e.child i ∈ f.norming) (hL : f.L e.weight ≤ N) :
    |norming.evaluateArray x e.value| ≤ A * f.theta e.weight := by
  have hs (i : Fin e.length) : (e.child i).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (e.child_nonzero i)
  let I : Fin e.length → Set Γ := fun i => ordinalHull (e.child i).support (hs i)
  have hI (i : Fin e.length) : Set.OrdConnected (I i) := ordinalHull_connected _ _
  have hIs : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b := by
    intro i j hij
    exact ordinalHull_successive (hs i) (hs j) (fun a ha b hb => (e.successive i j hij a ha b hb).1)
  have hp := hx e.length e.length_pos (e.length_le.trans hL) I hI hIs
  have hb : |∑ i : Fin e.length, norming.evaluateArray x (e.child i)| ≤ A * (e.length : ℝ)^(1/f.r) := by
    apply le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum (fun i _ => ?_)) hp)
    exact abs_eval_supported_interval _ (f.norming_subset_full (he i)) (I i) (hI i)
      (fun a ha => mem_ordinalHull (hs i) ha) x
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos e.weight
  have heq : norming.evaluateArray x e.value = (1 / (f.m e.weight : ℝ)) *
      ∑ i : Fin e.length, norming.evaluateArray x (e.child i) := by
    simp only [TypeI.value, map_smul, map_sum, Rat.smul_def, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast]
  rw [heq, abs_mul, abs_of_pos (one_div_pos.mpr hm), Family.theta_formula]
  calc
    _ ≤ (1 / (f.m e.weight : ℝ)) * (A * (e.length : ℝ)^(1/f.r)) :=
      mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr hm.le)
    _ ≤ (1 / (f.m e.weight : ℝ)) * (A * (f.L e.weight : ℝ)^(1/f.r)) := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hm.le)
      apply mul_le_mul_of_nonneg_left _ hA
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le)
        (one_div_nonneg.mpr f.r_pos.le)
    _ = _ := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

/-- Algebraic finite blocks in the specified tail, with no completion added. -/
noncomputable def BlockSequence.tailSpan {f : Family} (z : BlockSequence f) (a : ℕ) :
    Submodule ℝ (Γ →₀ ℝ) := Submodule.span ℝ (Set.range (fun n => z.vector (n+a)))

structure UnitBlocks (f : Family) (S : Submodule ℝ (Γ →₀ ℝ)) (k : ℕ) where
  vector : Fin k → Γ →₀ ℝ
  mem : ∀ i, vector i ∈ S
  unit : ∀ i, ‖norming.includeFinite (vector i)‖ = 1
  successive : ∀ i j, i < j → ∀ a ∈ (vector i).support, ∀ b ∈ (vector j).support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)
  pure_color : ∀ c, f = .pure c → ∀ i a, a ∈ (vector i).support → Colors.color a = c

lemma UnitBlocks.nonzero {f S k} (v : UnitBlocks f S k) (i : Fin k) : v.vector i ≠ 0 := by
  intro h
  have := v.unit i
  simp [h] at this

noncomputable def UnitBlocks.select {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k)) :
    UnitBlocks f S t.card where
  vector i := v.vector (t.orderEmbOfFin rfl i)
  mem i := v.mem (t.orderEmbOfFin rfl i)
  unit i := v.unit (t.orderEmbOfFin rfl i)
  successive i j hij := v.successive (t.orderEmbOfFin rfl i) (t.orderEmbOfFin rfl j) ((t.orderEmbOfFin rfl).strictMono hij)
  pure_color c hc i := v.pure_color c hc (t.orderEmbOfFin rfl i)

lemma UnitBlocks.select_sum {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k)) :
    ∑ i, (v.select t).vector i = ∑ i ∈ t, v.vector i := by
  change ∑ i, v.vector (t.orderEmbOfFin rfl i) = _
  conv_rhs => rw [← t.map_orderEmbOfFin_univ rfl]
  rw [Finset.sum_map]
  rfl

noncomputable def BlockSequence.unitBlocks {f : Family} (z : BlockSequence f) (a k : ℕ) :
    UnitBlocks f (z.tailSpan a) k where
  vector i := (‖norming.includeFinite (z.vector (i+a))‖⁻¹) • z.vector (i+a)
  mem i := Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  unit i := by
    rw [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (fun h => z.nonzero (i+a) (norming.includeFinite_injective (by simpa using h)))
  successive i j hij α hα β hβ := by
    apply z.successive (i+a) (j+a) (by omega) α _ β _
    · exact Finsupp.support_smul hα
    · exact Finsupp.support_smul hβ
  pure_color c hc i α hα := z.pure_color c hc (i+a) α (Finsupp.support_smul hα)

noncomputable def blockSumSup (f : Family) (S : Submodule ℝ (Γ →₀ ℝ)) (k : ℕ) : ℝ :=
  sSup (Set.range (fun v : UnitBlocks f S k => ‖norming.includeFinite (∑ i, v.vector i)‖))

lemma UnitBlocks.norm_sum_le_length {f S k} (v : UnitBlocks f S k) :
    ‖norming.includeFinite (∑ i, v.vector i)‖ ≤ k := by
  rw [map_sum]
  exact (norm_sum_le _ _).trans (by simp [v.unit])

lemma blockSumSup_bdd (f S k) : BddAbove
    (Set.range (fun v : UnitBlocks f S k => ‖norming.includeFinite (∑ i, v.vector i)‖)) :=
  ⟨k, by rintro _ ⟨v, rfl⟩; exact v.norm_sum_le_length⟩

lemma UnitBlocks.norm_sum_le_sup {f S k} (v : UnitBlocks f S k) :
    ‖norming.includeFinite (∑ i, v.vector i)‖ ≤ blockSumSup f S k :=
  le_csSup (blockSumSup_bdd f S k) ⟨v, rfl⟩

lemma UnitBlocks.norm_subsum_le_sup {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k)) :
    ‖norming.includeFinite (∑ i ∈ t, v.vector i)‖ ≤ blockSumSup f S t.card := by
  rw [← v.select_sum t]
  exact (v.select t).norm_sum_le_sup

lemma blockSumSup_le_length {f S k} (hne : Nonempty (UnitBlocks f S k)) :
    blockSumSup f S k ≤ k := by
  apply csSup_le (Set.range_nonempty_iff_nonempty.mpr hne)
  rintro _ ⟨v, rfl⟩
  exact v.norm_sum_le_length

lemma blockSumSup_nonneg {f S k} (hne : Nonempty (UnitBlocks f S k)) :
    0 ≤ blockSumSup f S k := by
  obtain ⟨v⟩ := hne
  exact (norm_nonneg _).trans v.norm_sum_le_sup

lemma unitBlocks_near_sup {f S k} (hne : Nonempty (UnitBlocks f S k)) (ha : 0 < blockSumSup f S k) :
    ∃ v : UnitBlocks f S k, blockSumSup f S k / 2 < ‖norming.includeFinite (∑ i, v.vector i)‖ := by
  obtain ⟨b, ⟨v, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (s := Set.range
    (fun v : UnitBlocks f S k => ‖norming.includeFinite (∑ i, v.vector i)‖))
    (Set.range_nonempty_iff_nonempty.mpr hne)
    (by linarith : blockSumSup f S k / 2 < blockSumSup f S k)
  exact ⟨v, hv⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

noncomputable def vectorCrop (x : Γ →₀ ℝ) (hx : x ≠ 0) : Crop where
  ordinal := ordinalHull x.support (Finsupp.support_nonempty_iff.mpr hx)
  ordinal_convex := ordinalHull_connected _ _
  colors := Set.Icc ((x.support.image Colors.color).min' ((Finsupp.support_nonempty_iff.mpr hx).image _))
    ((x.support.image Colors.color).max' ((Finsupp.support_nonempty_iff.mpr hx).image _))
  colors_convex := Set.ordConnected_Icc

lemma support_mem_vectorCrop (f : Family) (x : Γ →₀ ℝ) (hx : x ≠ 0) (a : Γ)
    (ha : a ∈ x.support) : a ∈ (vectorCrop x hx).set f := by
  have ho := mem_ordinalHull (Finsupp.support_nonempty_iff.mpr hx) ha
  have hc : Colors.color a ∈ (vectorCrop x hx).colors := by
    exact ⟨Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩),
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)⟩
  cases f with
  | pure _ => exact ho
  | mixed => exact ⟨ho, hc⟩

lemma vectorCrop_successive {f : Family} {x y : Γ →₀ ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ a ∈ x.support, ∀ b ∈ y.support,
      a < b ∧ (f = .mixed → Colors.color a < Colors.color b)) :
    ∀ a ∈ (vectorCrop x hx).set f, ∀ b ∈ (vectorCrop y hy).set f,
      a < b ∧ (f = .mixed → Colors.color a < Colors.color b) := by
  intro a ha b hb
  have haO : a ∈ (vectorCrop x hx).ordinal := by cases f <;> simp_all [Crop.set]
  have hbO : b ∈ (vectorCrop y hy).ordinal := by cases f <;> simp_all [Crop.set]
  refine ⟨ordinalHull_successive _ _ (fun c hc d hd => (h c hc d hd).1) a haO b hbO, ?_⟩
  intro hf
  subst f
  obtain ⟨c, hc, hcx⟩ := Finset.mem_image.mp ((x.support.image Colors.color).max'_mem
    ((Finsupp.support_nonempty_iff.mpr hx).image _))
  obtain ⟨d, hd, hdy⟩ := Finset.mem_image.mp ((y.support.image Colors.color).min'_mem
    ((Finsupp.support_nonempty_iff.mpr hy).image _))
  have hcd := (h c hc d hd).2 rfl
  rw [hcx, hdy] at hcd
  exact ha.2.2.trans_lt (hcd.trans_le hb.2.1)

lemma family_norming_crop (f : Family) (A : Crop) (g : Array) (hg : g ∈ f.norming) :
    restrict (A.set f) g ∈ f.norming := by
  cases f with
  | pure k => exact pure_crop k A g hg
  | mixed => exact full_crop A g hg

lemma exists_unit_vector_normer {f : Family} (x : Γ →₀ ℝ) (hx : ‖norming.includeFinite x‖ = 1)
    (hcolor : ∀ k, f = .pure k → ∀ a ∈ x.support, Colors.color a = k) :
    ∃ (g : Array), g ∈ f.norming ∧ g ≠ 0 ∧
      (∀ a ∈ g.support, a ∈ (vectorCrop x (by intro h; simp [h] at hx)).set f) ∧
      1/2 < norming.evaluateArray (norming.includeFinite x) g := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hn : ∃ g ∈ f.norming, 1/2 < norming.evaluateArray (norming.includeFinite x) g := by
    cases f with
    | pure k =>
      apply exists_pure_normer k _ _ _ (by norm_num) (by rw [hx]; norm_num)
      intro a ha
      rw [norming.coordinate_includeFinite]
      exact Finsupp.notMem_support_iff.mp (fun h => ha (hcolor k rfl a h))
    | mixed => exact exists_full_normer _ _ (by norm_num) (by rw [hx]; norm_num)
  obtain ⟨g, hg, hgv⟩ := hn
  let A := vectorCrop x hx0
  have heq : norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) =
      norming.evaluateArray (norming.includeFinite x) g := by
    apply evaluateArray_crop_of_zero
    intro a ha
    rw [norming.coordinate_includeFinite]
    exact Finsupp.notMem_support_iff.mp (fun h => ha (support_mem_vectorCrop f x hx0 a h))
  refine ⟨restrict (A.set f) g, family_norming_crop f A g hg, ?_, ?_, by rwa [heq]⟩
  · intro hz
    rw [hz, map_zero] at heq
    linarith
  · intro a ha
    by_contra hn
    change a ∉ A.set f at hn
    exact Finsupp.mem_support_iff.mp ha (by simp [restrict, hn])

lemma evaluateArray_finite_disjoint (x : Γ →₀ ℝ) (g : Array)
    (h : Disjoint x.support g.support) : norming.evaluateArray (norming.includeFinite x) g = 0 := by
  rw [evaluateArray_finite]
  apply Finset.sum_eq_zero
  intro a ha
  have hg : g a = 0 := Finsupp.notMem_support_iff.mp (fun hg => Finset.disjoint_left.mp h ha hg)
  simp [hg]

lemma UnitBlocks.norm_sum_lower {f S} (j : ℕ) (hj : 1 ≤ j) (v : UnitBlocks f S (f.L j)) :
    (f.L j : ℝ) / (2 * (f.m j : ℝ)) ≤ ‖norming.includeFinite (∑ i, v.vector i)‖ := by
  have hn := fun i => exists_unit_vector_normer (v.vector i) (v.unit i)
    (fun k hk => v.pure_color k hk i)
  choose g hg hgn hgs hgv using hn
  let e : TypeI f := {
    weight := j
    weight_pos := hj
    length := f.L j
    length_pos := f.L_pos j
    length_le := le_rfl
    child := g
    child_nonzero := hgn
    successive := by
      intro i l hil a ha b hb
      exact vectorCrop_successive (v.nonzero i) (v.nonzero l) (v.successive i l hil)
        a (hgs i a ha) b (hgs l b hb) }
  have hall : e.value ∈ Full := f.norming_subset_full (e.mem_family hg)
  have heval (i : Fin (f.L j)) : norming.evaluateArray (norming.includeFinite (∑ l, v.vector l)) (g i) =
      norming.evaluateArray (norming.includeFinite (v.vector i)) (g i) := by
    have hgi : g i ∈ Full := f.norming_subset_full (hg i)
    simp only [norming.evaluateArray_eq_functional _ ⟨g i, hgi⟩, map_sum]
    apply Finset.sum_eq_single i
    · intro l _ hli
      rw [← norming.evaluateArray_eq_functional]
      apply evaluateArray_finite_disjoint
      apply Finset.disjoint_left.mpr
      intro a ha hag
      rcases lt_or_gt_of_ne hli with hli | hil
      · exact (lt_irrefl a) (vectorCrop_successive (v.nonzero l) (v.nonzero i)
          (v.successive l i hli) a (support_mem_vectorCrop f _ _ a ha) a (hgs i a hag)).1
      · exact (lt_irrefl a) (vectorCrop_successive (v.nonzero i) (v.nonzero l)
          (v.successive i l hil) a (hgs i a hag) a (support_mem_vectorCrop f _ _ a ha)).1
    · simp
  have hm : (0 : ℝ) < f.m j := by exact_mod_cast f.m_pos j
  calc
    (f.L j : ℝ)/(2*(f.m j : ℝ)) = (1/(f.m j : ℝ)) * ∑ _ : Fin (f.L j), (1/2 : ℝ) := by simp; ring
    _ ≤ (1/(f.m j : ℝ)) * ∑ i, norming.evaluateArray (norming.includeFinite (v.vector i)) (g i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hgv i).le)) (one_div_nonneg.mpr hm.le)
    _ = norming.evaluateArray (norming.includeFinite (∑ i, v.vector i)) e.value := by
      rw [TypeI.value, map_smul, map_sum]
      simp only [e, Rat.smul_def, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, heval]
    _ ≤ |norming.evaluateArray (norming.includeFinite (∑ i, v.vector i)) e.value| := le_abs_self _
    _ ≤ ‖norming.includeFinite (∑ i, v.vector i)‖ := by
      rw [norming.evaluateArray_eq_functional _ ⟨_, hall⟩]
      exact norming.functional_bound _ _

end SeparableQuotient.ActualSpace

end

end OAI
