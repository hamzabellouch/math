import OAI.Analysis.SeparableQuotients.CoordinateDual

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

/-- The full norming set obtained from finite-stage pure and mixed operations. -/
def norming : NormingSet Γ where
  carrier := Full
  coordinate_mem := Norming.coordinate_mem
  coefficient_bound := full_coefficient_bound

/-- The actual real Banach space E of the CH construction. -/
abbrev E := norming.Space

@[reducible] instance EGroup : NormedAddCommGroup E := inferInstanceAs (NormedAddCommGroup norming.Space)
@[reducible] instance ESpace : NormedSpace ℝ E := inferInstanceAs (NormedSpace ℝ norming.Space)
instance ETopologicalAdd : IsTopologicalAddGroup E :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup
instance EContinuousAdd : ContinuousAdd E := ETopologicalAdd.toContinuousAdd

instance : CompleteSpace E := inferInstanceAs (CompleteSpace norming.Space)

instance : Infinite Γ := Cardinal.infinite_iff.mpr (by
  simp [Γ, CoherentClosures.OmegaOne])

lemma infiniteDimensional : ¬ Module.Finite ℝ E := norming.infiniteDimensional

abbrev e (a : Γ) : E := norming.generator a
abbrev coordinate (a : Γ) : StrongDual ℝ E := norming.coordinate a

lemma norm_e (a : Γ) : ‖e a‖ = 1 := norming.norm_generator a

lemma support_countable (x : E) : Set.Countable {a | coordinate a x ≠ 0} :=
  norming.support_countable x

lemma coordinate_ext (x y : E) (h : ∀ a, coordinate a x = coordinate a y) : x = y :=
  norming.coordinate_ext h

lemma cropStable (A : Crop) : norming.CropStable (A.set .mixed) :=
  full_crop A

/-- Every ordinal/color rectangle projection is defined on the full completion. -/
def projection (A : Crop) : E →L[ℝ] E := norming.projection (A.set .mixed) (cropStable A)

lemma norm_projection_le (A : Crop) (x : E) : ‖projection A x‖ ≤ ‖x‖ :=
  ((norming.projection (A.set .mixed) (cropStable A)).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norming.norm_projection_le (A.set .mixed) (cropStable A)) (norm_nonneg x))

lemma coordinate_projection (A : Crop) (x : E) (a : Γ) :
    coordinate a (projection A x) = if a ∈ A.set .mixed then coordinate a x else 0 :=
  norming.coordinate_projection (A.set .mixed) (cropStable A) a x

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction LpFinite
open scoped Classical ENNReal

/-- The ℓs-coordinate estimate on finite vectors. -/
lemma norm_includeFinite_on_color (k : ℕ) (x : Γ →₀ ℝ)
    (hx : ∀ a ∈ x.support, Colors.color a = k) :
    ‖norming.includeFinite x‖ ≤ ‖realArray (Family.pure k).primalExponent x‖ := by
  change ‖norming.finiteMap x‖ ≤ ‖realArray (Family.pure k).primalExponent x‖
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro f
  rw [norming.finiteMap_apply]
  have heq : x.sum (fun a t => t * (f.val a : ℝ)) =
      x.sum (fun a t => t * (restrict (colorSet k) f.val a : ℝ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [restrict_apply, colorSet, Set.mem_ofPred_eq, hx a ha, ↓reduceIte]
  rw [heq]
  calc
    _ ≤ ‖realArray (Family.pure k).primalExponent x‖ *
        ‖array (Family.pure k).exponent (restrict (colorSet k) f.val)‖ :=
      pairing_le (Family.conjugate (.pure k)) _ _
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (full_color_lp_bound k f.val f.property)
        (norm_nonneg (realArray (Family.pure k).primalExponent x))

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

lemma Family.L_pos (f : Family) (j : ℕ) : 0 < f.L j := Parameters.L_pos _ _

/-- Every finite successive family of existing normers has its prescribed
Type I average in the same actual family. -/
lemma pure_typeI_mem (k : ℕ) (e : TypeI (.pure k))
    (h : ∀ i, e.child i ∈ Pure k) : e.value ∈ Pure k := by
  classical
  choose n hn using (fun i => Set.mem_iUnion.mp (h i))
  let N := Finset.univ.sup n
  have hn' : ∀ i, e.child i ∈ stage (pureBase k) (.pure k) N := by
    intro i
    exact stage_mono _ _ (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  exact Set.mem_iUnion.mpr ⟨N+1, Or.inl (Or.inr ⟨e, rfl, hn'⟩)⟩

lemma mixed_typeI_mem (e : TypeI .mixed)
    (h : ∀ i, e.child i ∈ Full) : e.value ∈ Full := by
  classical
  choose n hn using (fun i => Set.mem_iUnion.mp (h i))
  let N := Finset.univ.sup n
  have hn' : ∀ i, e.child i ∈ stage (⋃ k, Pure k) .mixed N := by
    intro i
    exact stage_mono _ _ (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  exact Set.mem_iUnion.mpr ⟨N+1, Or.inl (Or.inr ⟨e, rfl, hn'⟩)⟩

/-- A concrete signed coordinate Type I expression. -/
def coordinateAverage (k j n : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n)
    (hnj : n ≤ (Family.pure k).L j) (a : Fin n ↪o Γ)
    (c : Fin n → ℚ) (hc : ∀ i, c i ≠ 0) : TypeI (.pure k) where
  weight := j
  weight_pos := hj
  length := n
  length_pos := hn
  length_le := hnj
  child := fun i => Finsupp.single (a i) (c i)
  child_nonzero := fun i => by simpa using hc i
  successive := by
    intro i l hil α hα β hβ
    have hα' : α = a i := by simpa [Finsupp.support_single _ (hc i)] using hα
    have hβ' : β = a l := by simpa [Finsupp.support_single _ (hc l)] using hβ
    subst α; subst β
    exact ⟨a.strictMono hil, by simp⟩

lemma coordinateAverage_mem (k j n : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n)
    (hnj : n ≤ (Family.pure k).L j) (a : Fin n ↪o Γ)
    (ha : ∀ i, Colors.color (a i) = k) (c : Fin n → ℚ)
    (hc : ∀ i, c i ≠ 0) (hsign : ∀ i, c i = 1 ∨ c i = -1) :
    (coordinateAverage k j n hj hn hnj a c hc).value ∈ Full := by
  apply pure_subset_full k
  apply pure_typeI_mem
  intro i
  apply Set.mem_iUnion.mpr
  refine ⟨0, Or.inr ⟨a i, ha i, ?_⟩⟩
  rcases hsign i with hi | hi <;> simp [coordinateAverage, hi]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

abbrev X₀ := norming.predual
abbrev coordinate₀ (a : Γ) : X₀ := norming.predualCoordinate a

@[reducible] local instance dualEGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma signed_coordinate_bound (g : StrongDual ℝ X₀)
    (k j n : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n) (hnj : n ≤ (Family.pure k).L j)
    (a : Fin n ↪o Γ) (ha : ∀ i, Colors.color (a i) = k) :
    (1 / ((Family.pure k).m j : ℝ)) * ∑ i, |g (coordinate₀ (a i))| ≤ ‖g‖ := by
  let c : Fin n → ℚ := fun i => if 0 ≤ g (coordinate₀ (a i)) then 1 else -1
  have hc : ∀ i, c i ≠ 0 := by intro i; dsimp [c]; split_ifs <;> norm_num
  have hsign : ∀ i, c i = 1 ∨ c i = -1 := by intro i; dsimp [c]; split_ifs <;> simp
  let e := coordinateAverage k j n hj hn hnj a c hc
  have he : e.value ∈ Full := coordinateAverage_mem k j n hj hn hnj a ha c hc hsign
  have hb := g.le_opNorm (norming.rationalPredual e.value)
  have hbound : |g (norming.rationalPredual e.value)| ≤ ‖g‖ := by
    exact hb.trans (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left
      (norming.norm_rationalPredual_le e.value he) (norm_nonneg g)))
  have heval : g (norming.rationalPredual e.value) =
      (1 / ((Family.pure k).m j : ℝ)) * ∑ i, |g (coordinate₀ (a i))| := by
    simp only [e, TypeI.value, coordinateAverage, map_sum,
      norming.rationalPredual_single, map_rat_smul, Rat.smul_def,
      Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [c]
    split_ifs with hi
    · simp [abs_of_nonneg hi, coordinate₀]
    · simp [abs_of_neg (lt_of_not_ge hi), coordinate₀]
  exact (le_abs_self _).trans (by rwa [heval] at hbound)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical

@[reducible] local instance dualEGroup2 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace2 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup2 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace2 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup2 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace2 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma predual_large_coordinates_finite (g : StrongDual ℝ X₀) (k : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    Set.Finite {a : Γ | Colors.color a = k ∧ δ ≤ |g (coordinate₀ a)|} := by
  by_contra hfin
  have hInf : Set.Infinite {a : Γ | Colors.color a = k ∧ δ ≤ |g (coordinate₀ a)|} := hfin
  have ht := Parameters.ratio_tendsto_atTop (Family.s_ge_two (.pure k))
  obtain ⟨l, hl⟩ := (ht.eventually (eventually_gt_atTop (‖g‖ / δ))).exists
  let j := l+1
  let n := (Family.pure k).L j
  have hn : 1 ≤ n := (Family.L_pos (.pure k) j)
  obtain ⟨s, hs, hcard⟩ := hInf.exists_subset_card_eq n
  let a : Fin n ↪o Γ := s.orderEmbOfFin hcard
  have ha : ∀ i, Colors.color (a i) = k := fun i =>
    (hs (s.orderEmbOfFin_mem hcard i)).1
  have hlarge : ∀ i, δ ≤ |g (coordinate₀ (a i))| := fun i =>
    (hs (s.orderEmbOfFin_mem hcard i)).2
  have hbound := signed_coordinate_bound g k j n (by omega) hn le_rfl a ha
  have hsum : (n : ℝ) * δ ≤ ∑ i, |g (coordinate₀ (a i))| := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlarge i)
  have hm : (0 : ℝ) < (Family.pure k).m j := by exact_mod_cast Family.m_pos _ _
  have hl' : ‖g‖ / δ < (n : ℝ) / ((Family.pure k).m j : ℝ) := by
    simpa [n, j, Family.L, Family.m] using hl
  have hr : ‖g‖ < ((n : ℝ) / ((Family.pure k).m j : ℝ)) * δ :=
    (div_lt_iff₀ hδ).mp hl'
  have hsmall : (1 / ((Family.pure k).m j : ℝ)) * ((n : ℝ) * δ) ≤ ‖g‖ :=
    (mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hm.le)).trans hbound
  have heq : (1 / ((Family.pure k).m j : ℝ)) * ((n : ℝ) * δ) =
      ((n : ℝ) / ((Family.pure k).m j : ℝ)) * δ := by ring
  rw [heq] at hsmall
  exact (not_lt_of_ge hsmall) hr

/-- Direct countable support of every candidate dual-predual vector, from the
actual Type I operations and L_j/m_j→∞. No bounded completeness is assumed. -/
lemma predual_coordinate_support_countable (g : StrongDual ℝ X₀) :
    Set.Countable {a : Γ | g (coordinate₀ a) ≠ 0} := by
  have h : Set.Countable (⋃ k : ℕ, ⋃ n : ℕ,
      {a : Γ | Colors.color a = k ∧ 1 / ((n : ℝ)+1) ≤ |g (coordinate₀ a)|}) :=
    Set.countable_iUnion fun k => Set.countable_iUnion fun n =>
      (predual_large_coordinates_finite g k _ (by positivity)).countable
  apply h.mono
  intro a ha
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr ha)
  exact Set.mem_iUnion.mpr ⟨Colors.color a,
    Set.mem_iUnion.mpr ⟨n, rfl, hn.le⟩⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.ordinalSet (I : Set Γ) (hI : Set.OrdConnected I) : Crop :=
  ⟨I, hI, Set.univ, Set.ordConnected_univ⟩

def Crop.colorSet (D : Set ℕ) (hD : Set.OrdConnected D) : Crop :=
  ⟨Set.univ, Set.ordConnected_univ, D, hD⟩

def Crop.oneColor (k : ℕ) : Crop := Crop.colorSet {k} Set.ordConnected_singleton

def Crop.colorsBelow (n : ℕ) : Crop := Crop.colorSet (Set.Iio n) Set.ordConnected_Iio

def Crop.colorsFrom (n : ℕ) : Crop := Crop.colorSet (Set.Ici n) Set.ordConnected_Ici

@[simp] lemma Crop.oneColor_set (k : ℕ) : (Crop.oneColor k).set .mixed = Norming.colorSet k := by
  ext a
  simp [Crop.oneColor, Crop.colorSet, Crop.set, Norming.colorSet]

@[simp] lemma Crop.colorsBelow_set (n : ℕ) :
    (Crop.colorsBelow n).set .mixed = {a | Colors.color a < n} := by
  ext a
  simp [Crop.colorsBelow, Crop.colorSet, Crop.set]

@[simp] lemma Crop.ordinalSet_set (I : Set Γ) (hI : Set.OrdConnected I) :
    (Crop.ordinalSet I hI).set .mixed = I := by
  ext a
  simp [Crop.ordinalSet, Crop.set]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma evaluateArray_projection (A : Crop) (x : E) (f : Array) :
    norming.evaluateArray (projection A x) f =
      norming.evaluateArray x (restrict (A.set .mixed) f) :=
  norming.evaluateArray_projection x (A.set .mixed) (cropStable A) f

lemma evaluateArray_crop_of_zero (A : Set Γ) (x : E)
    (hx : ∀ a ∉ A, coordinate a x = 0) (f : Array) :
    norming.evaluateArray x (restrict A f) = norming.evaluateArray x f :=
  norming.evaluateArray_filter_of_zero x A hx f

/-- The full and pure norms coincide on a single color. -/
lemma norm_le_of_pure (k : ℕ) (x : E) (hx : ∀ a, Colors.color a ≠ k → coordinate a x = 0)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ f ∈ Pure k, |norming.evaluateArray x f| ≤ r) : ‖x‖ ≤ r := by
  apply norming.norm_le_of_evaluateArray x r hr
  intro f hf
  have hb := absConvexHull_min h (absConvex_abs_le (norming.evaluateArray x) r hr)
    (full_color_hull k f hf)
  change |norming.evaluateArray x (restrict (colorSet k) f)| ≤ r at hb
  rwa [evaluateArray_crop_of_zero (colorSet k) x (fun a ha => hx a ha) f] at hb

lemma exists_full_normer (x : E) (r : ℝ) (hr : 0 ≤ r) (hx : r < ‖x‖) :
    ∃ f ∈ Full, r < norming.evaluateArray x f := by
  by_contra h
  push Not at h
  have hb : ‖x‖ ≤ r := norming.norm_le_of_evaluateArray x r hr (by
    intro f hf
    apply abs_le.mpr
    constructor
    · have hn := h (-f) (full_neg f hf)
      simpa only [map_neg, neg_le] using hn
    · exact h f hf)
  exact (not_lt_of_ge hb) hx

lemma exists_pure_normer (k : ℕ) (x : E)
    (hc : ∀ a, Colors.color a ≠ k → coordinate a x = 0)
    (r : ℝ) (hr : 0 ≤ r) (hx : r < ‖x‖) :
    ∃ f ∈ Pure k, r < norming.evaluateArray x f := by
  by_contra h
  push Not at h
  have hb : ‖x‖ ≤ r := norm_le_of_pure k x hc r hr (by
    intro f hf
    apply abs_le.mpr
    constructor
    · have hn := h (-f) (pure_neg k f hf)
      simpa only [map_neg, neg_le] using hn
    · exact h f hf)
  exact (not_lt_of_ge hb) hx

lemma tendsto_colorsBelow (x : E) :
    Tendsto (fun n => projection (Crop.colorsBelow n) x) atTop (𝓝 x) := by
  apply norming.tendsto_projection
  intro a
  filter_upwards [eventually_gt_atTop (Colors.color a)] with n hn
  simpa using hn

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

def Family.normers : Family → Set Array
  | .pure k => Pure k
  | .mixed => Full

lemma Family.normers_subset_full (t : Family) : t.normers ⊆ Full := by
  cases t with
  | pure k => exact pure_subset_full k
  | mixed => exact Set.Subset.rfl

lemma Family.typeI_mem (t : Family) (e : TypeI t)
    (h : ∀ i, e.child i ∈ t.normers) : e.value ∈ t.normers := by
  cases t with
  | pure k => exact pure_typeI_mem k e h
  | mixed => exact mixed_typeI_mem e h

lemma Family.exists_large_ratio (t : Family) (R : ℝ) :
    ∃ j, 1 ≤ j ∧ R < (t.L j : ℝ) / (t.m j : ℝ) := by
  obtain ⟨l, hl⟩ := ((Parameters.ratio_tendsto_atTop t.s_ge_two).eventually
    (Filter.eventually_gt_atTop R)).exists
  exact ⟨l+1, by omega, by simpa [Family.L, Family.m] using hl⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

@[reducible] local instance dualEGroup3 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace3 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup3 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace3 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup3 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace3 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma predual_array_apply (g : StrongDual ℝ X₀) (f : Array) :
    g (norming.rationalPredual f) = ∑ a ∈ f.support, (f a : ℝ) * g (coordinate₀ a) := by
  simp only [NormingSet.rationalPredual, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_rat_smul, Rat.smul_def, coordinate₀]

lemma predual_array_eq_evaluate (g : StrongDual ℝ X₀) (f : Array) (x : E)
    (hx : ∀ a ∈ f.support, coordinate a x = g (coordinate₀ a)) :
    g (norming.rationalPredual f) = norming.evaluateArray x f := by
  rw [predual_array_apply, norming.evaluateArray_eq]
  exact Finset.sum_congr rfl (fun a ha => by rw [← hx a ha])

/-- A Type I obstruction to successive uniformly positive normers. -/
lemma no_successive_positive_normers (g : StrongDual ℝ X₀) (t : Family)
    (f : ℕ → Array) (hf : ∀ i, f i ∈ t.normers)
    (hs : ∀ i j, i < j → Successive t (f i) (f j))
    (δ : ℝ) (hδ : 0 < δ) (hlarge : ∀ i, δ ≤ g (norming.rationalPredual (f i))) : False := by
  obtain ⟨j, hj, hratio⟩ := t.exists_large_ratio (‖g‖ / δ)
  let n := t.L j
  let e : TypeI t := {
    weight := j
    weight_pos := hj
    length := n
    length_pos := t.L_pos j
    length_le := le_rfl
    child := fun i => f i.val
    child_nonzero := fun i => by
      intro hz
      have h := hlarge i.val
      rw [hz, map_zero, map_zero] at h
      exact (not_le_of_gt hδ) h
    successive := fun i l hil => hs i.val l.val hil }
  have he : e.value ∈ Full := t.normers_subset_full (t.typeI_mem e (fun i => hf i.val))
  have hbound : g (norming.rationalPredual e.value) ≤ ‖g‖ := by
    calc
      _ ≤ |g (norming.rationalPredual e.value)| := le_abs_self _
      _ ≤ ‖g‖ * ‖norming.rationalPredual e.value‖ := g.le_opNorm _
      _ ≤ ‖g‖ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (norming.norm_rationalPredual_le e.value he) (norm_nonneg g)
  have heval : g (norming.rationalPredual e.value) =
      (1 / (t.m j : ℝ)) * ∑ i : Fin n, g (norming.rationalPredual (f i.val)) := by
    simp only [e, TypeI.value, map_rat_smul, Rat.smul_def, map_sum,
      Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  have hsum : (n : ℝ) * δ ≤ ∑ i : Fin n, g (norming.rationalPredual (f i.val)) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hlarge i.val)
  have hm : (0 : ℝ) < t.m j := by exact_mod_cast t.m_pos j
  have hb : (1 / (t.m j : ℝ)) * ((n : ℝ) * δ) ≤ ‖g‖ :=
    (mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hm.le)).trans (by rwa [← heval])
  have hr : ‖g‖ < ((n : ℝ) / (t.m j : ℝ)) * δ := (div_lt_iff₀ hδ).mp hratio
  have heq : (1 / (t.m j : ℝ)) * ((n : ℝ) * δ) = ((n : ℝ) / (t.m j : ℝ)) * δ := by ring
  rw [heq] at hb
  exact (not_lt_of_ge hb) hr

end SeparableQuotient.ActualSpace

end

end OAI
