import OAI.Analysis.SeparableQuotients.WindowThinning

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- A crop meets but does not contain an actual finite block support. -/
def PartialBlock {f : Family} (z : BlockSequence f) (A : Crop) (i : ℕ) : Prop :=
  (∃ a ∈ (z.vector i).support, a ∈ A.set f) ∧ ¬ (↑(z.vector i).support : Set Γ) ⊆ A.set f

lemma BlockSequence.partial_crop_le_four {f : Family} (z : BlockSequence f) (A : Crop) (s : Finset ℕ) :
    (s.filter (PartialBlock z A)).card ≤ 4 := by
  cases f with
  | pure k =>
    have ho := IntervalIncidence.partial_intersections_le_two s (fun i => (z.vector i).support)
      (fun i j hij a ha b hb => (z.successive i j hij a ha b hb).1) A.ordinal A.ordinal_convex
    have he : s.filter (PartialBlock z A) =
        s.filter (fun i => (∃ a ∈ (z.vector i).support, a ∈ A.ordinal) ∧ ¬ (↑(z.vector i).support : Set Γ) ⊆ A.ordinal) := by
      ext i
      simp [PartialBlock, Crop.set]
    rw [he]
    omega
  | mixed =>
    have ho := IntervalIncidence.partial_intersections_le_two s (fun i => (z.vector i).support)
      (fun i j hij a ha b hb => (z.successive i j hij a ha b hb).1) A.ordinal A.ordinal_convex
    let F (i : ℕ) : Finset ℕ := (z.vector i).support.image Colors.color
    have hF : ∀ i j, i < j → ∀ a ∈ F i, ∀ b ∈ F j, a < b := by
      intro i j hij a ha b hb
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hb
      exact (z.successive i j hij α hα β hβ).2 rfl
    have hc := IntervalIncidence.partial_intersections_le_two s F hF A.colors A.colors_convex
    let O := s.filter (fun i => (∃ a ∈ (z.vector i).support, a ∈ A.ordinal) ∧
      ¬ (↑(z.vector i).support : Set Γ) ⊆ A.ordinal)
    let C := s.filter (fun i => (∃ a ∈ F i, a ∈ A.colors) ∧ ¬ (↑(F i) : Set ℕ) ⊆ A.colors)
    have hsub : s.filter (PartialBlock z A) ⊆ O ∪ C := by
      intro i hi
      obtain ⟨hi, ⟨a, ha, hao, hac⟩, hnot⟩ := Finset.mem_filter.mp hi
      by_cases hO : (↑(z.vector i).support : Set Γ) ⊆ A.ordinal
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hi, ⟨Colors.color a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hac⟩, ?_⟩
        intro hC
        apply hnot
        intro b hb
        exact ⟨hO hb, hC (Finset.mem_image.mpr ⟨b, hb, rfl⟩)⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, ⟨a, ha, hao⟩, hO⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by dsimp [O,C]; omega))

lemma evaluateArray_crop_finite_fixed {f : Family} (x : Γ →₀ ℝ) (A : Crop)
    (hx : (↑x.support : Set Γ) ⊆ A.set f) (g : Array) :
    norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) =
      norming.evaluateArray (norming.includeFinite x) g := by
  apply evaluateArray_crop_of_zero
  intro a ha
  rw [norming.coordinate_includeFinite]
  exact Finsupp.notMem_support_iff.mp (fun hh => ha (hx hh))

lemma evaluateArray_crop_nonzero_support {f : Family} (x : Γ →₀ ℝ) (A : Crop) (g : Array)
    (h : norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) ≠ 0) :
    ∃ a ∈ x.support, a ∈ A.set f := by
  by_contra hn
  push Not at hn
  apply h
  rw [evaluateArray_finite]
  apply Finset.sum_eq_zero
  intro a ha
  simp [restrict_apply, hn a ha]

lemma crop_or_fixed_of_nonzero {f : Family} (z : BlockSequence f) (A : Crop) (i : ℕ) (g : Array)
    (h : norming.evaluateArray (z.embed i) (restrict (A.set f) g) ≠ 0) :
    PartialBlock z A i ∨ norming.evaluateArray (z.embed i) (restrict (A.set f) g) =
      norming.evaluateArray (z.embed i) g := by
  by_cases hh : (↑(z.vector i).support : Set Γ) ⊆ A.set f
  · exact Or.inr (evaluateArray_crop_finite_fixed _ _ hh _)
  · exact Or.inl ⟨evaluateArray_crop_nonzero_support _ _ _ h, hh⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- The weighted absolute column estimate, obtained using the actual rational
Type II normers and density of rational coefficients, not an assumed dual ball. -/
lemma cropped_weighted_abs_sum_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j))))
    (c : Fin h → ℝ) (x : E) :
    (∑ i, |c i| * |croppedPathFunctional (P i) (A i) x|) ≤
      (∑ i, |c i|^f.q)^(1/f.q) * ‖x‖ := by
  let d : Fin h → ℝ := fun i => |c i| * RealCoefficients.signChoice (croppedPathFunctional (P i) (A i) x)
  have hd (i : Fin h) : |d i| = |c i| := by simp only [d, abs_mul, abs_abs, RealCoefficients.abs_signChoice, mul_one]
  have he : (∑ i, d i • croppedPathFunctional (P i) (A i)) x =
      ∑ i, |c i| * |croppedPathFunctional (P i) (A i) x| := by
    simp only [sum_apply, smul_apply, smul_eq_mul, d, mul_assoc, RealCoefficients.signChoice_mul]
  calc
    _ = |(∑ i, d i • croppedPathFunctional (P i) (A i)) x| := by
      rw [he, abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
    _ ≤ ‖∑ i, d i • croppedPathFunctional (P i) (A i)‖ * ‖x‖ :=
      by simpa only [Real.norm_eq_abs] using (∑ i, d i • croppedPathFunctional (P i) (A i)).le_opNorm x
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [hd] using real_cropped_path_bound P A hm hdis d) (norm_nonneg _)

lemma TypeII.window_column_bound {f : Family} (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming)
    (J T : ℕ) (c : Fin e.length → ℝ) (x : E) :
    (∑ b, |c b| * |norming.evaluateArray x (restrict ((e.crop b).set f) ((e.path b).window J T))|) ≤
      (∑ b, |c b|^f.q)^(1/f.q) * ‖x‖ := by
  let A (b : Fin e.length) := ((e.path b).weightCrop J T).inter (e.crop b)
  have hd : Pairwise (fun i j => Disjoint ((e.path i).active (A i)) ((e.path j).active (A j))) := by
    intro b c hbc
    exact (e.disjoint_active hbc).mono (TypeII.active_crop_subset _ _ _) (TypeII.active_crop_subset _ _ _)
  have he (b : Fin e.length) : croppedPathFunctional (e.path b) (A b) x =
      norming.evaluateArray x (restrict ((e.crop b).set f) ((e.path b).window J T)) := by
    change norming.evaluateArray x (restrict ((A b).set f) (e.path b).value) = _
    dsimp only [A]
    rw [Crop.inter_set, Set.inter_comm, ← restrict_restrict, FinitePath.weightCrop_value]
  simpa only [he] using cropped_weighted_abs_sum_bound e.path A hm hd c x

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma cropped_window_anchor {f : Family} (P : FinitePath f) (A : Crop) (x : E) (J T : ℕ)
    (h : norming.evaluateArray x (restrict (A.set f) (P.window J T)) ≠ 0) :
    ∃ j ∈ P.active A, J ≤ j ∧ j ≤ T := by
  simp only [FinitePath.window, restrict_sum, map_sum] at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hw : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T := by
    by_contra hn
    simp only [ite_eq_right hn, restrict_zero, map_zero, ne_eq, not_true_eq_false] at hi
  rw [ite_eq_left hw] at hi
  refine ⟨P.raw.weight i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩, hw⟩
  intro hh
  exact hi (by rw [hh, map_zero])

/-- Distinct original active weights bound the number of paths contributing
in a window. The +1 version is convenient for zero-based natural indices;
the positive-weight sharper T bound is not needed for the geometric charge. -/
lemma TypeII.cropped_window_count {f : Family} (e : TypeII f) (x : E) (J T : ℕ) :
    (Finset.univ.filter (fun b => norming.evaluateArray x
      (restrict ((e.crop b).set f) ((e.path b).window J T)) ≠ 0)).card ≤ T+1 := by
  let S := Finset.univ.filter (fun b => norming.evaluateArray x
    (restrict ((e.crop b).set f) ((e.path b).window J T)) ≠ 0)
  have h (b : S) : ∃ j ∈ (e.path b).active (e.crop b), J ≤ j ∧ j ≤ T :=
    cropped_window_anchor _ _ _ _ _ (Finset.mem_filter.mp b.property).2
  choose w hw hwJ hwT using h
  let v (b : S) : Fin (T+1) := ⟨w b, by have := hwT b; omega⟩
  have hinj : Function.Injective v := by
    intro b c hbc
    apply Subtype.ext
    by_contra hne
    have hd := e.disjoint_active hne
    have he : w b = w c := congrArg Fin.val hbc
    exact Finset.disjoint_left.mp hd (hw b) (he.symm ▸ hw c)
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective v hinj

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def firstNonzero (s : Finset ℕ) (t : ℕ → ℝ) : ℕ :=
  if h : (s.filter (fun i => t i ≠ 0)).Nonempty then (s.filter (fun i => t i ≠ 0)).min' h else 0

lemma firstNonzero_mem {s : Finset ℕ} {t : ℕ → ℝ} {i : ℕ} (hi : i ∈ s) (ht : t i ≠ 0) :
    firstNonzero s t ∈ s ∧ t (firstNonzero s t) ≠ 0 := by
  have h : (s.filter (fun i => t i ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, ht⟩⟩
  rw [firstNonzero, dite_eq_left h]
  exact Finset.mem_filter.mp (Finset.min'_mem _ h)

lemma firstNonzero_le {s : Finset ℕ} {t : ℕ → ℝ} {i : ℕ} (hi : i ∈ s) (ht : t i ≠ 0) :
    firstNonzero s t ≤ i := by
  have h : (s.filter (fun i => t i ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, ht⟩⟩
  rw [firstNonzero, dite_eq_left h]
  exact Finset.min'_le _ i (Finset.mem_filter.mpr ⟨hi, ht⟩)

noncomputable def ThinnedWindows.middleEval {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (b : Fin e.length) (i : ℕ) : ℝ :=
  norming.evaluateArray (w.blocks.embed i)
    (restrict ((e.crop b).set f) ((e.path b).window (w.lower i) (w.upper i)))

noncomputable def ThinnedWindows.marks {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (b : Fin e.length) : Finset ℕ :=
  let n := firstNonzero s (w.middleEval e b)
  ({n} ∩ s) ∪ (s.filter (PartialBlock w.blocks (e.crop b))) ∪
    (s.filter (fun i => n < i ∧ WindowHit ⟨e.path b, hm b⟩ (w.blocks.vector i)
      (w.lower i) (w.upper i) (w.threshold n)))

lemma ThinnedWindows.marks_card {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (b : Fin e.length) :
    (w.marks e hm s b).card ≤ 8 := by
  have h1 : ({firstNonzero s (w.middleEval e b)} ∩ s).card ≤ 1 := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have h2 := w.blocks.partial_crop_le_four (e.crop b) s
  have h3 := w.hits_after_le_three (firstNonzero s (w.middleEval e b)) s ⟨e.path b, hm b⟩
  unfold marks
  apply (Finset.card_union_le _ _).trans
  have hh := Finset.card_union_le ({firstNonzero s (w.middleEval e b)} ∩ s)
    (s.filter (PartialBlock w.blocks (e.crop b)))
  omega

lemma ThinnedWindows.unmarked_small {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (b : Fin e.length)
    (i : ℕ) (hi : i ∈ s) (ht : w.middleEval e b i ≠ 0) (hmark : i ∉ w.marks e hm s b) :
    firstNonzero s (w.middleEval e b) < i ∧
      |w.middleEval e b i| ≤ w.threshold (firstNonzero s (w.middleEval e b)) := by
  have hle := firstNonzero_le hi ht
  have hne : i ≠ firstNonzero s (w.middleEval e b) := by
    intro hh
    apply hmark
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_singleton.mpr hh, hi⟩))
  have hlt : firstNonzero s (w.middleEval e b) < i := lt_of_le_of_ne hle (Ne.symm hne)
  have hp : ¬ PartialBlock w.blocks (e.crop b) i := by
    intro hh
    exact hmark (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hh⟩)))
  have hn : ¬ WindowHit ⟨e.path b, hm b⟩ (w.blocks.vector i) (w.lower i) (w.upper i)
      (w.threshold (firstNonzero s (w.middleEval e b))) := by
    intro hh
    exact hmark (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hlt,hh⟩))
  have he := (crop_or_fixed_of_nonzero w.blocks (e.crop b) i
    ((e.path b).window (w.lower i) (w.upper i)) ht).resolve_left hp
  refine ⟨hlt, ?_⟩
  change |norming.evaluateArray (w.blocks.embed i) _| ≤ _
  rw [he]
  exact le_of_not_gt hn

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma geometric_charge_le (ε : ℝ) (hε : 0 ≤ ε) (i : ℕ) :
    (∑ n ∈ Finset.range i, ε*(1/2 : ℝ)^(n+1)) ≤ ε := by
  have he : ∀ i, (∑ n ∈ Finset.range i, ε*(1/2 : ℝ)^(n+1)) = ε*(1-(1/2 : ℝ)^i) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [he]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) i]

lemma ThinnedWindows.unmarked_column {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (hε : 0 ≤ ε) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ)
    (i : ℕ) (hi : i ∈ s) :
    (∑ b, if i ∉ w.marks e hm s b then |(e.coefficient b : ℝ)| * |w.middleEval e b i| else 0) ≤ ε := by
  let U : Finset (Fin e.length) := Finset.univ.filter
    (fun b => w.middleEval e b i ≠ 0 ∧ i ∉ w.marks e hm s b)
  let first (b : Fin e.length) := firstNonzero s (w.middleEval e b)
  have hU (b : Fin e.length) (hb : b ∈ U) : first b < i ∧ |w.middleEval e b i| ≤ w.threshold (first b) :=
    w.unmarked_small e hm s b i hi (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2
  have hcount (n : ℕ) : (U.filter (fun b => first b = n)).card ≤ w.upper n+1 := by
    apply le_trans (Finset.card_le_card ?_) (TypeII.cropped_window_count e (w.blocks.embed n) (w.lower n) (w.upper n))
    intro b hb
    have hbU := Finset.mem_filter.mp hb
    have hn := (firstNonzero_mem hi (Finset.mem_filter.mp hbU.1).2.1).2
    change w.middleEval e b (first b) ≠ 0 at hn
    rw [hbU.2] at hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
  calc
    _ = ∑ b ∈ U, |(e.coefficient b : ℝ)| * |w.middleEval e b i| := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases ht : w.middleEval e b i = 0 <;> by_cases hm' : i ∈ w.marks e hm s b <;> simp [ht,hm']
    _ ≤ ∑ b ∈ U, w.threshold (first b) := Finset.sum_le_sum (fun b hb =>
      (mul_le_mul_of_nonneg_right (e.coefficient_le_one b) (abs_nonneg _)).trans (by simpa using (hU b hb).2))
    _ = ∑ n ∈ Finset.range i, ∑ b ∈ U.filter (fun b => first b = n), w.threshold (first b) :=
      (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_range.mpr (hU b hb).1) _).symm
    _ = ∑ n ∈ Finset.range i, ((U.filter (fun b => first b = n)).card : ℝ)*w.threshold n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [show (∑ b ∈ U.filter (fun b => first b = n), w.threshold (first b)) =
          ∑ b ∈ U.filter (fun b => first b = n), w.threshold n from
        Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2])]
      simp
    _ ≤ ∑ n ∈ Finset.range i, ε*(1/2 : ℝ)^(n+1) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← w.threshold_charge_succ n]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount n) (w.threshold_pos n).le
    _ ≤ ε := geometric_charge_le ε hε i

end SeparableQuotient.ActualSpace

end

end OAI
