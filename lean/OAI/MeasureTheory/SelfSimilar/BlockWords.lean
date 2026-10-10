import OAI.MeasureTheory.SelfSimilar.TypedEntropy

namespace OAI

universe uι uα uβ uγ

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators

theorem observableEntropy_reindex {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype β] [DecidableEq γ]
    (e : α ≃ β) (p : β → ℝ) (f : β → γ) :
    observableEntropy Finset.univ (fun a => p (e a)) (fun a => f (e a))=
      observableEntropy Finset.univ p f := by
  classical
  have hi : Finset.univ.image (fun a => f (e a))=Finset.univ.image f := by
    ext c
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun ⟨a,ha⟩ => ⟨e a,ha⟩,fun ⟨b,hb⟩ => ⟨e.symm b,by simpa using hb⟩⟩
  have hm (c : γ) : mass Finset.univ (fun a => p (e a)) (fun a => f (e a)) c=
      mass Finset.univ p f c := by
    simp only [mass,Finset.sum_filter]
    exact e.sum_comp (fun b => if f b=c then p b else 0)
  simp only [observableEntropy,entropy,hi,hm]

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

noncomputable def blocks (S : System ι) {b : ℕ} (hb : 0 < b) : System (Fin b → ι) where
  ratio w := (S.completeMap w).1
  offset w := (S.completeMap w).2
  weight w := S.wordWeight w
  ratio_pos w := abs_pos.mpr (S.completeMap_slope_ne_zero w)
  ratio_lt_one w := S.completeMap_abs_lt_one hb w
  weight_pos w := S.wordWeight_pos w
  weight_sum := S.wordWeight_sum b

theorem selfSimilar_blocks (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {b : ℕ} (hb : 0 < b) : (S.blocks hb).SelfSimilar μ := S.selfSimilar_words μ hμ b

theorem blocks_lyapunov (S : System ι) {b : ℕ} (hb : 0 < b) :
    (S.blocks hb).lyapunov=(b : ℝ)*S.lyapunov := by
  simp only [lyapunov,blocks,S.completeMap_log_slope,Finset.sum_div]
  rw [S.wordWeight_expect_sum (fun i => Real.log |S.ratio i|/Real.log 2)]
  ring

def flattenWordEquiv (n b : ℕ) : (Fin n → Fin b → ι) ≃ (Fin (n*b) → ι) :=
  (Equiv.curry (Fin n) (Fin b) ι).symm.trans (Equiv.piCongrLeft (fun _ => ι) finProdFinEquiv)

omit [Fintype ι] in
@[simp] theorem flattenWordEquiv_apply (n b : ℕ) (w : Fin n → Fin b → ι)
    (i : Fin n) (j : Fin b) : flattenWordEquiv n b w (finProdFinEquiv (i,j))=w i j := by
  simp [flattenWordEquiv]

theorem wordAffine_blocks (S : System ι) {b : ℕ} (hb : 0 < b) (W : List (Fin b → ι)) :
    (S.blocks hb).wordAffine W=S.wordAffine (W.flatMap List.ofFn) := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    rw [wordAffine,ih,List.flatMap_cons,S.wordAffine_append]
    rfl

theorem completeMap_flatten (S : System ι) {b : ℕ} (hb : 0 < b) {n : ℕ}
    (w : Fin n → Fin b → ι) :
    (S.blocks hb).completeMap w=S.completeMap (flattenWordEquiv n b w) := by
  rw [completeMap,S.wordAffine_blocks,completeMap,List.ofFn_mul]
  congr 1
  rw [List.flatMap,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  apply congrArg List.ofFn
  funext j
  convert (flattenWordEquiv_apply n b w i j).symm using 1
  apply congrArg (flattenWordEquiv n b w)
  apply Fin.ext
  simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem wordWeight_flatten (S : System ι) {b : ℕ} (hb : 0 < b) {n : ℕ}
    (w : Fin n → Fin b → ι) :
    (S.blocks hb).wordWeight w=S.wordWeight (flattenWordEquiv n b w) := by
  simp only [wordWeight,blocks]
  rw [← finProdFinEquiv.prod_comp (fun j => S.weight (flattenWordEquiv n b w j)),
    Fintype.prod_prod_type]
  simp only [flattenWordEquiv_apply]

theorem blocks_walkEntropy (S : System ι) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    (S.blocks hb).walkEntropy n=S.walkEntropy (n*b) := by
  have he := FiniteEntropy.observableEntropy_reindex (flattenWordEquiv n b)
    S.wordWeight S.completeMap
  simp only [← S.wordWeight_flatten hb,← S.completeMap_flatten hb] at he
  rw [(S.blocks hb).map_entropy_as_observation,S.map_entropy_as_observation] at he
  exact mul_right_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne' he

theorem blocks_entropyRate_lower (S : System ι) {b : ℕ} (hb : 0 < b) :
    (b : ℝ)*S.entropyRate ≤ (S.blocks hb).entropyRate := by
  apply le_csInf ⟨_,Set.mem_range_self 0⟩
  intro x hx
  obtain ⟨n,rfl⟩ := hx
  dsimp only
  rw [S.blocks_walkEntropy]
  have hpos : 0 < (n+1)*b := Nat.mul_pos (Nat.succ_pos n) hb
  have hh := S.entropyRate_le ((n+1)*b-1)
  rw [Nat.sub_add_cancel hpos] at hh
  have hh' := (le_div_iff₀ (by exact_mod_cast hpos : (0 : ℝ)<((n+1)*b : ℕ))).mp hh
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(n+1 : ℕ))).mpr
  push_cast at hh' ⊢
  nlinarith

noncomputable def wordType {b : ℕ} (w : Fin b → ι) : ι → Fin (b+1) := by
  classical
  exact fun i => ⟨(Finset.univ.filter (fun j => w j=i)).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin b))⟩

theorem ratio_wordType (S : System ι) {b : ℕ} (hb : 0 < b) (w v : Fin b → ι)
    (h : wordType w=wordType v) : (S.blocks hb).ratio w=(S.blocks hb).ratio v := by
  classical
  have ht (u : Fin b → ι) : (S.completeMap u).1=∏ i, S.ratio i^(wordType u i).val := by
    rw [S.completeMap_slope,← Finset.prod_fiberwise Finset.univ u]
    apply Finset.prod_congr rfl
    intro i _
    calc
      ∏ j ∈ Finset.univ.filter (fun j => u j=i), S.ratio (u j) =
          ∏ _j ∈ Finset.univ.filter (fun j => u j=i), S.ratio i := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [(Finset.mem_filter.mp hj).2]
      _ = _ := by simp only [Finset.prod_const,wordType]
  change (S.completeMap w).1=(S.completeMap v).1
  rw [ht,ht,h]

end EntropyRateDimension.System

end OAI
