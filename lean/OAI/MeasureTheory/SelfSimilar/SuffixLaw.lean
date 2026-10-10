import OAI.MeasureTheory.SelfSimilar.FiniteVariance

namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def listLaw (S : System α) (tag : α → β) (W : List α) : Law :=
  law S tag W.get
noncomputable def listTail (S : System α) (tag : α → β) (μ : Measure ℝ) (W : List α) : Measure ℝ :=
  tail S tag μ W.get

omit [Fintype α] [DecidableEq β] in
theorem apply_word_congr {γ : Type uγ} (F : (n : ℕ) → (Fin n → α) → γ)
    {m n : ℕ} (h : m=n) (v : Fin m → α) (w : Fin n → α)
    (he : ∀ i, v i=w (Fin.cast h i)) : F m v=F n w := by
  subst n
  exact congrArg (F m) (funext he)

theorem listLaw_ofFn (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) :
    listLaw S tag (List.ofFn w)=law S tag w := by
  apply apply_word_congr (fun _ v => law S tag v) (List.length_ofFn ..)
  intro i
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

theorem listTail_ofFn (S : System α) (tag : α → β) (μ : Measure ℝ) {n : ℕ} (w : Fin n → α) :
    listTail S tag μ (List.ofFn w)=tail S tag μ w := by
  apply apply_word_congr (fun _ v => tail S tag μ v) (List.length_ofFn ..)
  intro i
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

noncomputable def listScaledTail (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) (W : List α) : Measure ℝ := (listTail S tag μ W).map (fun x => a*x)

theorem listScaledTail_ofFn (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) {n : ℕ} (w : Fin n → α) :
    listScaledTail S tag μ a (List.ofFn w)=scaledTail S tag μ a w := by
  simp only [listScaledTail,listTail_ofFn,scaledTail]

instance listScaledTail_probability (S : System α) (tag : α → β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) (W : List α) : IsProbabilityMeasure (listScaledTail S tag μ a W) :=
  scaledTail_probability S tag μ a W.get

theorem listScaledTail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (a : ℝ) (W : List α) :
    CompactlyCarried (listScaledTail S tag μ a W) := scaledTail_compact S tag μ hμ a W.get

theorem listScaledTail_append (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) (U V : List α) :
    listScaledTail S tag μ a (U++V)=
      finiteConv (listLaw S tag U) a (listScaledTail S tag μ (a*(S.wordAffine U).1) V) := by
  have h := scaledTail_append S tag hr μ a U.get V.get
  rw [← listScaledTail_ofFn,← listScaledTail_ofFn,← listLaw_ofFn] at h
  simpa only [List.ofFn_fin_append,List.ofFn_get,System.completeMap] using h

noncomputable def suffixLaw (S : System α) (tag : α → β) (μ : Measure ℝ) (W : List α) (j : ℕ) : Measure ℝ :=
  listScaledTail S tag μ (S.wordAffine (W.take j)).1 (W.drop j)

instance suffixLaw_probability (S : System α) (tag : α → β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (W : List α) (j : ℕ) : IsProbabilityMeasure (suffixLaw S tag μ W j) :=
  listScaledTail_probability S tag μ _ _

theorem suffixLaw_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (W : List α) (j : ℕ) : CompactlyCarried (suffixLaw S tag μ W j) :=
  listScaledTail_compact S tag μ hμ _ _

theorem suffixLaw_convolution (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (W : List α) (j n : ℕ) :
    suffixLaw S tag μ W j=finiteConv (listLaw S tag ((W.drop j).take n))
      (S.wordAffine (W.take j)).1 (suffixLaw S tag μ W (j+n)) := by
  have h := listScaledTail_append S tag hr μ (S.wordAffine (W.take j)).1
    ((W.drop j).take n) ((W.drop j).drop n)
  rw [List.take_append_drop,List.drop_drop] at h
  simpa only [suffixLaw,List.take_add,System.wordAffine_append] using h

noncomputable def suffixWindow (S : System α) (tag : α → β) (μ : Measure ℝ)
    (s : ℝ) (N : ℕ) (W : List α) (j : ℕ) : ℝ :=
  window (suffixLaw S tag μ W j) s (N*s)

theorem suffixWindow_antitone (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (W : List α) :
    Antitone (suffixWindow S tag μ s N W) := by
  intro j k hjk
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjk
  change window (suffixLaw S tag μ W (j+n)) s (N*s) ≤ window (suffixLaw S tag μ W j) s (N*s)
  rw [suffixLaw_convolution S tag hr μ W j n]
  exact finiteConv_window_mono _ _ _ (suffixLaw_compact S tag μ hμ W (j+n)) hs hN

theorem suffixWindow_bounds (S : System α) (tag : α → β)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (W : List α) (j : ℕ) :
    0 ≤ suffixWindow S tag μ s N W j ∧ suffixWindow S tag μ s N W j ≤ Real.log N :=
  averaged_nested_bounds _ (suffixLaw_compact S tag μ hμ W j) hs hN

end EntropyRateDimension.Typed

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

noncomputable def listDepth (S : System α) (W : List α) : ℝ := (W.map S.letterDepth).sum

theorem listDepth_nonneg (S : System α) (W : List α) : 0 ≤ S.listDepth W :=
  List.sum_nonneg (by intro x hx; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx; exact (S.letterDepth_pos a).le)

theorem listDepth_ofFn (S : System α) {n : ℕ} (w : Fin n → α) :
    S.listDepth (List.ofFn w)=S.wordDepth w := by
  simp only [listDepth,List.map_ofFn,List.sum_ofFn,wordDepth_sum,Function.comp_apply]

theorem listDepth_append (S : System α) (U V : List α) : S.listDepth (U++V)=S.listDepth U+S.listDepth V := by
  simp only [listDepth,List.map_append,List.sum_append]

theorem listDepth_take_add (S : System α) (W : List α) (j n : ℕ) :
    S.listDepth (W.take (j+n))=S.listDepth (W.take j)+S.listDepth ((W.drop j).take n) := by
  rw [List.take_add,listDepth_append]

theorem listDepth_monotone (S : System α) (W : List α) : Monotone (fun j => S.listDepth (W.take j)) := by
  intro j k hjk
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjk
  dsimp only
  rw [listDepth_take_add]
  exact le_add_of_nonneg_right (S.listDepth_nonneg _)

theorem exists_depth_bound (S : System α) : ∃ D : ℝ, 0 < D ∧ ∀ a, S.letterDepth a ≤ D := by
  let D := 1+∑ a, S.letterDepth a
  have hn : 0 ≤ ∑ a, S.letterDepth a := Finset.sum_nonneg (fun a _ => (S.letterDepth_pos a).le)
  refine ⟨D,by dsimp [D]; linarith,fun a => ?_⟩
  have hh := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => (S.letterDepth_pos a).le) (Finset.mem_univ a)
  dsimp [D]
  linarith

theorem listDepth_le (S : System α) {D : ℝ} (hD : ∀ a, S.letterDepth a ≤ D) (W : List α) :
    S.listDepth W ≤ D*W.length := by
  induction W with
  | nil => simp [listDepth]
  | cons a W ih =>
    simp only [listDepth,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
    nlinarith [hD a]

theorem listDepth_take_le (S : System α) {D : ℝ} (hD : 0 ≤ D) (hd : ∀ a, S.letterDepth a ≤ D)
    (W : List α) (j : ℕ) : S.listDepth (W.take j) ≤ D*j := by
  have hh := S.listDepth_le hd (W.take j)
  rw [List.length_take] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left j W.length) hD)

end EntropyRateDimension.System

end OAI
