import OAI.MeasureTheory.SelfSimilar.Windows

namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace System
variable {ι : Type uι} [Fintype ι]

theorem wordAffine_slope (S : System ι) (w : List ι) :
    (S.wordAffine w).1 = (w.map S.ratio).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [wordAffine,List.map_cons,List.prod_cons] using congrArg (S.ratio i * ·) ih

theorem completeMap_slope (S : System ι) {n : ℕ} (w : Fin n → ι) :
    (S.completeMap w).1 = ∏ j, S.ratio (w j) := by
  rw [completeMap,wordAffine_slope,List.map_ofFn,List.prod_ofFn]
  rfl

theorem completeMap_slope_ne_zero (S : System ι) {n : ℕ} (w : Fin n → ι) :
    (S.completeMap w).1 ≠ 0 := by
  rw [completeMap_slope]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => abs_pos.mp (S.ratio_pos (w j)))

theorem wordAffine_append (S : System ι) (v w : List ι) :
    S.wordAffine (v++w) = ((S.wordAffine v).1*(S.wordAffine w).1,
      (S.wordAffine v).1*(S.wordAffine w).2+(S.wordAffine v).2) := by
  induction v with
  | nil => simp [wordAffine]
  | cons i v ih => simp only [List.cons_append,wordAffine,ih]; ext <;> dsimp <;> ring

noncomputable def blockType {b n : ℕ} (w : Fin (n*b) → ι) : Fin n → ι → Fin (b+1) := by
  classical
  exact fun j i => ⟨(Finset.univ.filter (fun k : Fin b => w (finProdFinEquiv (j,k))=i)).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin b))⟩

theorem block_product_eq (S : System ι) {b n : ℕ} (w : Fin (n*b) → ι) (j : Fin n) :
    ∏ k : Fin b, S.ratio (w (finProdFinEquiv (j,k))) =
      ∏ i, S.ratio i ^ (blockType w j i).val := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (fun k : Fin b => w (finProdFinEquiv (j,k)))]
  apply Finset.prod_congr rfl
  intro i _
  calc
    ∏ k ∈ Finset.univ.filter (fun k : Fin b => w (finProdFinEquiv (j,k))=i),
        S.ratio (w (finProdFinEquiv (j,k))) =
        ∏ _k ∈ Finset.univ.filter (fun k : Fin b => w (finProdFinEquiv (j,k))=i), S.ratio i := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := by simp only [Finset.prod_const,blockType]

theorem completeMap_slope_blockType (S : System ι) {b n : ℕ} (w : Fin (n*b) → ι) :
    (S.completeMap w).1 = ∏ j, ∏ i, S.ratio i ^ (blockType w j i).val := by
  rw [completeMap_slope,← finProdFinEquiv.prod_comp (fun k => S.ratio (w k)),Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  exact S.block_product_eq w j

theorem map_entropy_as_observation (S : System ι) (n : ℕ) :
    FiniteEntropy.observableEntropy Finset.univ (S.wordWeight (n := n)) S.completeMap =
      S.walkEntropy n*Real.log 2 := by
  classical
  unfold walkEntropy FiniteEntropy.observableEntropy FiniteEntropy.entropy mapSupport
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2)))]
  rfl

theorem blockType_entropy_le (S : System ι) (b n : ℕ) :
    FiniteEntropy.observableEntropy Finset.univ (S.wordWeight (n := n*b)) blockType ≤
      (n : ℝ)*Fintype.card ι*Real.log (b+1) := by
  classical
  let p : (Fin (n*b) → ι) → ℝ := S.wordWeight
  let f : (Fin (n*b) → ι) → (Fin n → ι → Fin (b+1)) := blockType
  let q := FiniteEntropy.mass Finset.univ p f
  have hq : ∀ a, 0 ≤ q a :=
    FiniteEntropy.mass_nonneg Finset.univ p f (fun w _ => (S.wordWeight_pos w).le)
  have hq1 : ∑ a, q a = 1 := by
    calc
      ∑ a, q a = ∑ a ∈ Finset.univ.image f, q a := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a _ ha
        exact FiniteEntropy.mass_eq_zero_of_not_mem _ _ _ ha
      _ = 1 := by rw [FiniteEntropy.mass_sum]; exact S.wordWeight_sum (n*b)
  have hh := FiniteEntropy.entropy_le_log_card Finset.univ q (fun a _ => hq a) hq1
  have hs := FiniteEntropy.observableEntropy_on_superset Finset.univ Finset.univ p f
    (fun _ _ => Finset.mem_univ _)
  change FiniteEntropy.observableEntropy Finset.univ p f ≤ _
  rw [hs]
  convert hh using 1
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [Real.log_pow,Real.log_pow]
  ring

theorem conditional_translation_entropy_lower (S : System ι) (b n : ℕ) :
    S.walkEntropy (n*b)*Real.log 2-(n : ℝ)*Fintype.card ι*Real.log (b+1) ≤
      FiniteEntropy.conditionalEntropy Finset.univ (S.wordWeight (n := n*b))
        (fun w => (S.completeMap w).2) blockType := by
  classical
  have hh := FiniteEntropy.observableEntropy_le_of_fibers Finset.univ
    (S.wordWeight (n := n*b)) S.completeMap (fun w => ((S.completeMap w).2,blockType w))
    (fun w _ => (S.wordWeight_pos w).le) (by
      intro w _ v _ hv
      apply Prod.ext
      · rw [completeMap_slope_blockType,completeMap_slope_blockType,(Prod.mk.inj hv).2]
      · exact (Prod.mk.inj hv).1)
  rw [S.map_entropy_as_observation] at hh
  have ht := S.blockType_entropy_le b n
  unfold FiniteEntropy.conditionalEntropy
  linarith

theorem conditional_translation_entropy_rate_lower (S : System ι) {b n : ℕ}
    (hb : 0 < b) (hn : 0 < n) :
    (n : ℝ)*((b : ℝ)*S.entropyRate*Real.log 2-Fintype.card ι*Real.log (b+1)) ≤
      FiniteEntropy.conditionalEntropy Finset.univ (S.wordWeight (n := n*b))
        (fun w => (S.completeMap w).2) blockType := by
  have hnb : 0 < n*b := Nat.mul_pos hn hb
  have hh := S.entropyRate_le (n*b-1)
  rw [Nat.sub_add_cancel hnb] at hh
  have hrate := (le_div_iff₀ (by exact_mod_cast hnb : (0 : ℝ)<(n*b : ℕ))).mp hh
  have hm := mul_le_mul_of_nonneg_right hrate (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  push_cast at hm
  have ht := S.conditional_translation_entropy_lower b n
  nlinarith

end System
end EntropyRateDimension

end OAI
