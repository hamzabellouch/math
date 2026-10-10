import OAI.Probability.InvariantIsing.Fields.FieldFiniteRecursion

namespace OAI

/-! Every strictly positive finite covariance list admits the joint
height derivative construction on a neighborhood of its parameter vector. -/

noncomputable section
open Set IsingPerceptron
open scoped Topology BigOperators

namespace InvariantIsing

lemma fieldFinite_variance_neighborhood {n : ℕ} (L : List (FieldFiniteStep n))
    (h : Fin n → ℝ) (hpos : ∀ av ∈ L, 0 < fieldFiniteVariance av.base av.slope h) :
    ∃ (I : Set (Fin n → ℝ)) (_ : IsOpen I), h ∈ I ∧ ∃ m V : ℝ, 0 < m ∧
      ∀ av ∈ L, ∀ t ∈ I, m ≤ fieldFiniteVariance av.base av.slope t ∧
        fieldFiniteVariance av.base av.slope t ≤ V := by
  induction L with
  | nil => exact ⟨univ, isOpen_univ, mem_univ _, 1, 1, by norm_num, by simp⟩
  | cons av L ih =>
    obtain ⟨J, hJ, hhJ, m, V, hm, hL⟩ := ih (fun bv hb => hpos bv (List.mem_cons_of_mem av hb))
    let b := fieldFiniteVariance av.base av.slope h
    have hb : 0 < b := hpos av List.mem_cons_self
    let K := (fun t => fieldFiniteVariance av.base av.slope t) ⁻¹' Ioo (b / 2) (b + 1)
    have hK : IsOpen K := isOpen_Ioo.preimage (by dsimp only [fieldFiniteVariance]; fun_prop)
    have hhK : h ∈ K := by change b / 2 < b ∧ b < b + 1; constructor <;> linarith
    refine ⟨J ∩ K, hJ.inter hK, ⟨hhJ, hhK⟩, min m (b / 2), max V (b + 1),
      lt_min hm (by positivity), ?_⟩
    intro bv hmem t ht
    rcases List.mem_cons.mp hmem with heq | htail
    · subst bv
      exact ⟨(min_le_right _ _).trans ht.2.1.le, ht.2.2.le.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_left _ _).trans (hL bv htail t ht.1).1,
        (hL bv htail t ht.1).2.trans (le_max_left _ _)⟩

lemma fieldFinite_coefficient_bound {n : ℕ} (L : List (FieldFiniteStep n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ av ∈ L, ∀ i, |av.slope i| ≤ B := by
  classical
  induction L with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons av L ih =>
    obtain ⟨B, hB, hb⟩ := ih
    refine ⟨max B (∑ i, |av.slope i|), hB.trans (le_max_left _ _), ?_⟩
    intro bv hv i
    rcases List.mem_cons.mp hv with heq | hv
    · subst bv
      exact (Finset.single_le_sum (fun j _ => abs_nonneg (av.slope j)) (Finset.mem_univ i)).trans
        (le_max_right _ _)
    · exact (hb bv hv i).trans (le_max_left _ _)

lemma fieldFinite_slope_bound {n : ℕ} (a : ℝ) (v h : Fin n → ℝ)
    {m B : ℝ} (hm : 0 < m) (hs : m ≤ fieldFiniteVariance a v h)
    (hb : ∀ i, |v i| ≤ B) (i : Fin n) :
    |fieldFiniteSlope a v h i| ≤ B / (2 * Real.sqrt m) :=
  (abs_div_two_sqrt_le hm hs (v i)).trans (div_le_div_of_nonneg_right (hb i) (by positivity))

lemma fieldFinite_curvature_bound {n : ℕ} (a : ℝ) (v h : Fin n → ℝ)
    {m B : ℝ} (hm : 0 < m) (hB : 0 ≤ B) (hs : m ≤ fieldFiniteVariance a v h)
    (hb : ∀ i, |v i| ≤ B) (i j : Fin n) :
    |fieldFiniteCurvature a v h i j| ≤ (B / 2) * m⁻¹ * (B / (2 * Real.sqrt m)) := by
  have hS := hm.trans_le hs
  have hj := fieldFinite_slope_bound a v h hm hs hb j
  unfold fieldFiniteCurvature
  rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_inv, abs_of_pos hS]
  gcongr
  exact hb i

/-- Joint gradient and symmetric Hessian data for the actual finite Gaussian
recursion, constructed on a neighborhood of every strict covariance vector. -/
theorem fieldFiniteValue_local_family {n : ℕ} (L : List (FieldFiniteStep n))
    (h : Fin n → ℝ) (hpos : ∀ av ∈ L, 0 < fieldFiniteVariance av.base av.slope h) :
    ∃ (I : Set (Fin n → ℝ)) (_ : IsOpen I), h ∈ I ∧
      ∃ F : FieldFiniteFamily n I, F.U = fieldFiniteValue L := by
  obtain ⟨I, hI, hh, m, V, hm, hL⟩ := fieldFinite_variance_neighborhood L h hpos
  obtain ⟨B, hB, hb⟩ := fieldFinite_coefficient_bound L
  let R := B / (2 * Real.sqrt m)
  let D := (B / 2) * m⁻¹ * R
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hval (av : FieldFiniteStep n) (hav : av ∈ L) (t : Fin n → ℝ) (ht : t ∈ I) :
      0 < fieldFiniteVariance av.base av.slope t ∧ fieldFiniteVariance av.base av.slope t ≤ V :=
    ⟨hm.trans_le (hL av hav t ht).1, (hL av hav t ht).2⟩
  have hc (av : FieldFiniteStep n) (hav : av ∈ L) (t : Fin n → ℝ) (ht : t ∈ I) (i : Fin n) :
      |fieldFiniteSlope av.base av.slope t i| ≤ R :=
    fieldFinite_slope_bound av.base av.slope t hm (hL av hav t ht).1 (hb av hav) i
  have hd (av : FieldFiniteStep n) (hav : av ∈ L) (t : Fin n → ℝ) (ht : t ∈ I) (i j : Fin n) :
      |fieldFiniteCurvature av.base av.slope t i j| ≤ D :=
    fieldFinite_curvature_bound av.base av.slope t hm hB (hL av hav t ht).1 (hb av hav) i j
  exact ⟨I, hI, hh, fieldFiniteFamily I hI V R D hR hD L hval hc hd,
    fieldFiniteFamily_value I hI V R D hR hD L hval hc hd⟩

end InvariantIsing

end

end OAI
