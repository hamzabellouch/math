import OAI.MeasureTheory.SelfSimilar.Main

namespace OAI

universe uι uα

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

/-- Absence of equality between complete affine maps of distinct finite words. -/
def NoExactOverlaps (S : System ι) : Prop := Function.Injective S.wordAffine

noncomputable def symbolEntropy (S : System ι) : ℝ :=
  ∑ i, Real.negMulLog (S.weight i)

/-- The equivalent fixed-length convention for exact overlaps. -/
def SameLengthNoExactOverlaps (S : System ι) : Prop :=
  ∀ n : ℕ, Function.Injective (S.completeMap (n := n))

noncomputable def naturalLyapunov (S : System ι) : ℝ :=
  -(∑ i, S.weight i * Real.log |S.ratio i|)

theorem wordAffine_slope_pos (S : System ι) (u : List ι) :
    0 < |(S.wordAffine u).1| := by
  induction u with
  | nil => simp [System.wordAffine]
  | cons i u ih =>
    simpa only [System.wordAffine, abs_mul] using mul_pos (S.ratio_pos i) ih

theorem wordAffine_slope_le_one (S : System ι) (u : List ι) :
    |(S.wordAffine u).1| ≤ 1 := by
  induction u with
  | nil => simp [System.wordAffine]
  | cons i u ih =>
    simpa only [System.wordAffine, abs_mul, mul_one] using
      mul_le_mul (S.ratio_lt_one i).le ih (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

theorem wordAffine_slope_lt_one (S : System ι) {u : List ι} (hu : u ≠ []) :
    |(S.wordAffine u).1| < 1 := by
  cases u with
  | nil => exact (hu rfl).elim
  | cons i u =>
    change |S.ratio i * (S.wordAffine u).1| < 1
    rw [abs_mul]
    calc
      _ ≤ |S.ratio i| * 1 :=
        mul_le_mul_of_nonneg_left (wordAffine_slope_le_one S u) (abs_nonneg _)
      _ < 1 := by simpa using S.ratio_lt_one i

/-- An equal prefix map cannot have a nonempty residual contraction. -/
theorem equal_map_prefix (S : System ι) (u w : List ι)
    (he : S.wordAffine u = S.wordAffine (u ++ w)) : w = [] := by
  have hs := congrArg Prod.fst he
  rw [S.wordAffine_append] at hs
  have hn : (S.wordAffine u).1 ≠ 0 := abs_pos.mp (wordAffine_slope_pos S u)
  have hw : (S.wordAffine w).1 = 1 := by
    apply mul_left_cancel₀ hn
    simpa using hs.symm
  by_contra hne
  have hc := wordAffine_slope_lt_one S hne
  rw [hw, abs_one] at hc
  exact (lt_irrefl 1) hc

/-- Prefix comparison extracted directly from equality of concatenations. -/
theorem prefix_comparison {α : Type uα} (u v x y : List α)
    (h : u ++ x = v ++ y) :
    (∃ w, v = u ++ w) ∨ (∃ w, u = v ++ w) := by
  induction u generalizing v with
  | nil => exact Or.inl ⟨v, rfl⟩
  | cons a u ih =>
    cases v with
    | nil => exact Or.inr ⟨a :: u, rfl⟩
    | cons b v =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, ht⟩ := h
      rcases ih v ht with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inl ⟨w, by simp [hw]⟩
      · exact Or.inr ⟨w, by simp [hw]⟩

/-- Source lemma `lem:overlap-lengths`, with complete signed affine maps. -/
theorem overlap_lengths (S : System ι) {u v : List ι}
    (_hu : u ≠ []) (_hv : v ≠ []) (hne : u ≠ v)
    (he : S.wordAffine u = S.wordAffine v) :
    ∃ a b : List ι, a ≠ [] ∧ b ≠ [] ∧ a.length = b.length ∧
      a ≠ b ∧ S.wordAffine a = S.wordAffine b := by
  refine ⟨u ++ v, v ++ u, ?_, ?_, ?_, ?_, ?_⟩
  · intro hempty
    exact _hu (List.append_eq_nil_iff.mp hempty).1
  · intro hempty
    exact _hv (List.append_eq_nil_iff.mp hempty).1
  · simp [Nat.add_comm]
  · intro hc
    rcases prefix_comparison u v v u hc with ⟨w, hw⟩ | ⟨w, hw⟩
    · have hw0 := equal_map_prefix S u w (hw ▸ he)
      apply hne
      simpa [hw0] using hw.symm
    · have hw0 := equal_map_prefix S v w (hw ▸ he.symm)
      apply hne
      simpa [hw0] using hw
  · simp only [S.wordAffine_append, he]

theorem noExactOverlaps_sameLength (S : System ι) (h : NoExactOverlaps S) :
    SameLengthNoExactOverlaps S := by
  intro n u v huv
  have he : List.ofFn u = List.ofFn v := h huv
  exact List.ofFn_injective he

theorem sameLength_list_injective (S : System ι) (h : SameLengthNoExactOverlaps S)
    (u v : List ι) (hl : u.length = v.length)
    (he : S.wordAffine u = S.wordAffine v) : u = v := by
  induction u using List.ofFnRec with
  | h n f =>
    induction v using List.ofFnRec with
    | h m g =>
      simp only [List.length_ofFn] at hl
      subst m
      exact congrArg List.ofFn (h n he)

/-- Adding the empty word does not strengthen the usual overlap assumption. -/
theorem noExactOverlaps_iff_nonempty (S : System ι) :
    NoExactOverlaps S ↔ ∀ u v : List ι, u ≠ [] → v ≠ [] →
      S.wordAffine u = S.wordAffine v → u = v := by
  constructor
  · intro h u v _ _ he
    exact h he
  · intro h u v he
    by_cases hu : u = []
    · subst u
      have hv := equal_map_prefix S [] v (by simpa using he)
      exact hv.symm
    by_cases hv : v = []
    · subst v
      exact equal_map_prefix S [] u (by simpa using he.symm)
    exact h u v hu hv he

theorem noExactOverlaps_iff_sameLength (S : System ι) :
    NoExactOverlaps S ↔ SameLengthNoExactOverlaps S := by
  refine ⟨noExactOverlaps_sameLength S, ?_⟩
  intro h
  apply (noExactOverlaps_iff_nonempty S).mpr
  intro u v hu hv he
  by_contra hne
  obtain ⟨a,b,_,_,hl,hab,heab⟩ := overlap_lengths S hu hv hne he
  exact hab (sameLength_list_injective S h a b hl heab)

/-- Native product entropy of the symbol word; no random-walk entropy hypothesis. -/
theorem word_entropy (S : System ι) (n : ℕ) :
    FiniteEntropy.entropy Finset.univ (S.wordWeight (n := n)) =
      (n : ℝ) * symbolEntropy S := by
  classical
  have hlog (w : Fin n → ι) :
      Real.log (S.wordWeight w) = ∑ j, Real.log (S.weight (w j)) := by
    unfold System.wordWeight
    exact Real.log_prod (fun j _ => (S.weight_pos (w j)).ne')
  calc
    FiniteEntropy.entropy Finset.univ (S.wordWeight (n := n)) =
        -(∑ w : Fin n → ι, S.wordWeight w * ∑ j, Real.log (S.weight (w j))) := by
      simp only [FiniteEntropy.entropy, Real.negMulLog, hlog,
        neg_mul, Finset.sum_neg_distrib]
    _ = -((n : ℝ) * ∑ i, S.weight i * Real.log (S.weight i)) := by
      exact congrArg (fun x : ℝ => -x)
        (S.wordWeight_expect_sum (fun i => Real.log (S.weight i)) n)
    _ = (n : ℝ) * symbolEntropy S := by
      simp only [symbolEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, mul_neg]

theorem walkEntropy_eq_symbolEntropy [Nonempty ι] (S : System ι)
    (h : SameLengthNoExactOverlaps S) (n : ℕ) :
    S.walkEntropy n = (n : ℝ) * (symbolEntropy S / Real.log 2) := by
  classical
  have he := FiniteEntropy.observableEntropy_of_injective Finset.univ
    (S.wordWeight (n := n)) S.completeMap
    (fun w _ => (S.wordWeight_pos w).le) (h n)
  rw [S.map_entropy_as_observation, word_entropy] at he
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [← mul_div_assoc]
  apply (eq_div_iff h2).mpr
  exact he

theorem entropyRate_eq_symbolEntropy [Nonempty ι] (S : System ι)
    (h : SameLengthNoExactOverlaps S) :
    S.entropyRate = symbolEntropy S / Real.log 2 := by
  have hw (n : ℕ) : S.walkEntropy (n+1) / (n+1 : ℕ) =
      symbolEntropy S / Real.log 2 := by
    rw [walkEntropy_eq_symbolEntropy S h]
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn]
  unfold System.entropyRate
  simp only [hw, Set.range_const, csInf_singleton]

theorem lyapunov_eq_naturalLyapunov (S : System ι) :
    S.lyapunov = naturalLyapunov S / Real.log 2 := by
  simp only [System.lyapunov, naturalLyapunov, ← mul_div_assoc,
    ← Finset.sum_div, neg_div]

theorem no_exact_overlaps_dimension [Nonempty ι] (S : System ι)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (h : NoExactOverlaps S) :
    lowerHausdorffDimension μ =
      ENNReal.ofReal (min 1 (symbolEntropy S / naturalLyapunov S)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : 0 < naturalLyapunov S := by
    have hp := S.lyapunov_pos
    rw [lyapunov_eq_naturalLyapunov] at hp
    exact (div_pos_iff_of_pos_right hlog).mp hp
  have hu : Coding.exponent S ≤ symbolEntropy S / naturalLyapunov S := by
    apply (le_div_iff₀ hn).mpr
    have hb := Coding.exponent_symbol_entropy_bound S
    change Coding.exponent S * S.lyapunov * Real.log 2 ≤ symbolEntropy S at hb
    rw [lyapunov_eq_naturalLyapunov] at hb
    have hc : Coding.exponent S * (naturalLyapunov S / Real.log 2) * Real.log 2 =
        Coding.exponent S * naturalLyapunov S := by
      field_simp [hlog.ne']
    rwa [hc] at hb
  have hl := S.exponent_lower_bound μ hμ
  rw [entropyRate_eq_symbolEntropy S (noExactOverlaps_sameLength S h),
    lyapunov_eq_naturalLyapunov, div_div_div_cancel_right₀ hlog.ne'] at hl
  rw [S.selfSimilar_dimension μ hμ]
  exact congrArg ENNReal.ofReal (le_antisymm (le_min (S.exponent_le_one μ hμ) hu) hl)


theorem homogeneous_naturalLyapunov (S : System ι) {lam : ℝ} (hlam : 0 < lam)
    (hr : ∀ i, S.ratio i = lam) : naturalLyapunov S = Real.log (1/lam) := by
  simp only [naturalLyapunov, hr, abs_of_pos hlam, ← Finset.sum_mul,
    S.weight_sum, one_mul, one_div, Real.log_inv]

theorem homogeneous_dimension [Nonempty ι] (S : System ι)
    {lam : ℝ} (hlam : 0 < lam) (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (h : NoExactOverlaps S) :
    lowerHausdorffDimension μ =
      ENNReal.ofReal (min 1 (symbolEntropy S / Real.log (1/lam))) := by
  rw [no_exact_overlaps_dimension S μ hμ h, homogeneous_naturalLyapunov S hlam hr]

/-- The three named translations, with all positivity and normalization supplied explicitly. -/
noncomputable def threeMapSystem (lam t : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1)
    (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) : System (Fin 3) where
  ratio := fun _ => lam
  offset := ![0, 1, t]
  weight := p
  ratio_pos := fun _ => by simpa [abs_of_pos hlam] using hlam
  ratio_lt_one := fun _ => by simpa [abs_of_pos hlam] using hlam1
  weight_pos := hp
  weight_sum := hp1

theorem three_maps_dimension (lam t : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1)
    (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : (threeMapSystem lam t hlam hlam1 p hp hp1).SelfSimilar μ)
    (h : NoExactOverlaps (threeMapSystem lam t hlam hlam1 p hp hp1)) :
    lowerHausdorffDimension μ = ENNReal.ofReal
      (min 1 ((-(∑ i, p i * Real.log (p i))) / Real.log (1/lam))) := by
  simpa [symbolEntropy, threeMapSystem, Real.negMulLog, neg_mul,
    Finset.sum_neg_distrib] using
    homogeneous_dimension (threeMapSystem lam t hlam hlam1 p hp hp1) hlam
      (fun _ => rfl) μ hμ h

end EntropyRateDimension.Extensions

end OAI
