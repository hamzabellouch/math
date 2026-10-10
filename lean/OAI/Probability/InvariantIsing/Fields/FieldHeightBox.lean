import OAI.Probability.InvariantIsing.Fields.FieldHeightLocal

namespace OAI

/-! A convex increment box carrying one joint derivative family for two
strict field-height vectors and the segment joining them. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def fieldHeightBox (n : ℕ) (m V : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {r | ∀ j, fieldHeightIncrement r j ∈ Ioo m V}

lemma isOpen_fieldHeightBox (n : ℕ) (m V : ℝ) : IsOpen (fieldHeightBox n m V) := by
  simpa only [fieldHeightBox, ofPred_forall, Set.preimage] using
    isOpen_iInter_of_finite (fun j : Fin (n + 1) =>
      isOpen_Ioo.preimage (continuous_fieldHeightIncrement j))

lemma convex_fieldHeightBox (n : ℕ) (m V : ℝ) : Convex ℝ (fieldHeightBox n m V) := by
  intro r hr s hs a b ha hb hab j
  have he : fieldHeightIncrement (a • r + b • s) j =
      a * fieldHeightIncrement r j + b * fieldHeightIncrement s j := by
    unfold fieldHeightIncrement
    split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he]
  exact (convex_Ioo m V) (hr j) (hs j) ha hb hab

lemma fieldHeightBox_subset_strict {n : ℕ} {m V : ℝ} (hm : 0 ≤ m) :
    fieldHeightBox n m V ⊆ fieldStrictHeightCone n := by
  intro r hr j
  exact hm.trans_lt (hr j).1

lemma fieldHeightBox_pair {n : ℕ} (r s : Fin (n + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone n) (hs : s ∈ fieldStrictHeightCone n) :
    ∃ m V : ℝ, 0 < m ∧ r ∈ fieldHeightBox n m V ∧ s ∈ fieldHeightBox n m V := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ
  have hS : S.Nonempty := ⟨0, Finset.mem_univ _⟩
  let lo := S.inf' hS (fun j => min (fieldHeightIncrement r j) (fieldHeightIncrement s j))
  let hi := S.sup' hS (fun j => max (fieldHeightIncrement r j) (fieldHeightIncrement s j))
  have hlo : 0 < lo := (Finset.lt_inf'_iff hS).mpr (fun j _ => lt_min (hr j) (hs j))
  have hl (j : Fin (n + 1)) : lo ≤ min (fieldHeightIncrement r j) (fieldHeightIncrement s j) :=
    Finset.inf'_le (s := S)
      (fun j => min (fieldHeightIncrement r j) (fieldHeightIncrement s j)) (Finset.mem_univ j)
  have hu (j : Fin (n + 1)) : max (fieldHeightIncrement r j) (fieldHeightIncrement s j) ≤ hi :=
    Finset.le_sup' (s := S)
      (fun j => max (fieldHeightIncrement r j) (fieldHeightIncrement s j)) (Finset.mem_univ j)
  refine ⟨lo / 2, hi + 1, by positivity, ?_, ?_⟩
  · intro j
    have hlj := (hl j).trans (min_le_left _ _)
    have huj := (le_max_left _ _).trans (hu j)
    constructor <;> linarith
  · intro j
    have hlj := (hl j).trans (min_le_right _ _)
    have huj := (le_max_right _ _).trans (hu j)
    constructor <;> linarith

theorem fieldHeightBox_family (h : FieldStep) (m V : ℝ) (hm : 0 < m) :
    ∃ F : FieldFiniteFamily (h.depth + 1) (fieldHeightBox h.depth m V),
      F.U = fieldFiniteValue (fieldHeightFiniteList h) := by
  let I := fieldHeightBox h.depth m V
  let L := fieldHeightFiniteList h
  have hI : IsOpen I := isOpen_fieldHeightBox _ _ _
  obtain ⟨B, hB, hb⟩ := fieldFinite_coefficient_bound L
  let R := B / (2 * Real.sqrt m)
  let D := (B / 2) * m⁻¹ * R
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hbracket (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) :
      m < fieldFiniteVariance av.base av.slope r ∧ fieldFiniteVariance av.base av.slope r < V := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hav
    change m < fieldFiniteVariance 0 (fieldHeightSlope j) r ∧
      fieldFiniteVariance 0 (fieldHeightSlope j) r < V
    rw [fieldHeightSlope_variance]
    exact hr j
  have hv (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) :
      0 < fieldFiniteVariance av.base av.slope r ∧ fieldFiniteVariance av.base av.slope r ≤ V :=
    ⟨hm.trans (hbracket av hav r hr).1, (hbracket av hav r hr).2.le⟩
  have hc (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i : Fin (h.depth + 1)) :
      |fieldFiniteSlope av.base av.slope r i| ≤ R :=
    fieldFinite_slope_bound av.base av.slope r hm (hbracket av hav r hr).1.le (hb av hav) i
  have hd (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i j : Fin (h.depth + 1)) :
      |fieldFiniteCurvature av.base av.slope r i j| ≤ D :=
    fieldFinite_curvature_bound av.base av.slope r hm hB (hbracket av hav r hr).1.le (hb av hav) i j
  exact ⟨fieldFiniteFamily I hI V R D hR hD L hv hc hd,
    fieldFiniteFamily_value I hI V R D hR hD L hv hc hd⟩

end InvariantIsing

end

end OAI
