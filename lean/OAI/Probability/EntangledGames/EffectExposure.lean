import OAI.Probability.EntangledGames.Resampling

namespace OAI

universe u_R u_n u_X u_Y u_I u_A u_B u_m u_J u_K

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability

namespace FiniteProbability.Law
variable {R : Type u_R} {n : Type u_n} [Fintype R] [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n] in
lemma avg_posSemidef (p : Law R) (A : R → Matrix n n ℂ) (hA : ∀ r, (A r).PosSemidef) :
    (p.avg A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro r _
  exact (hA r).smul (p.nonneg r)
lemma avg_matrix_mono (p : Law R) {A B : R → Matrix n n ℂ} (h : ∀ r, A r ≤ B r) :
    p.avg A ≤ p.avg B := by
  unfold avg
  exact Finset.sum_le_sum (fun r _ => smul_le_smul_of_nonneg_left (h r) (p.nonneg r))
lemma avg_matrix_le (p : Law R) {A : R → Matrix n n ℂ} {B : Matrix n n ℂ}
    (h : ∀ r, A r ≤ B) : p.avg A ≤ B := by
  simpa only [avg_const] using p.avg_matrix_mono h

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq I]
omit [DecidableEq Y] [Fintype n] [DecidableEq n] in
lemma lefts_posSemidef (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) (hf : ∀ z, (f z).PosSemidef) :
    ∀ z, (μ.lefts x₀ l f z).PosSemidef := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_posSemidef _ _ (fun _ => ih _)
omit [DecidableEq X] [Fintype n] [DecidableEq n] in
lemma rights_posSemidef (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) (hf : ∀ z, (f z).PosSemidef) :
    ∀ z, (μ.rights y₀ l f z).PosSemidef := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_posSemidef _ _ (fun _ => ih _)
omit [DecidableEq Y] in
lemma lefts_le (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) {B : Matrix n n ℂ} (hf : ∀ z, f z ≤ B) :
    ∀ z, μ.lefts x₀ l f z ≤ B := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_matrix_le _ (fun _ => ih _)
omit [DecidableEq X] in
lemma rights_le (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) {B : Matrix n n ℂ} (hf : ∀ z, f z ≤ B) :
    ∀ z, μ.rights y₀ l f z ≤ B := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_matrix_le _ (fun _ => ih _)
end FiniteProbability.Law

namespace QuantumSampling.POVM
variable {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} [Fintype n] [DecidableEq n] [Fintype A] [Fintype B] [Fintype R]
lemma le_one (P : POVM n A) (a : A) : P.effect a ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun b _ => (P.pos b).nonneg) (Finset.mem_univ a)

def coarsen (P : POVM n A) (f : A → B) : POVM n B := by
  classical
  exact {
    effect b := ∑ a with f a=b, P.effect a
    pos b := Matrix.posSemidef_sum _ (fun a _ => P.pos a)
    total := by simp only [Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (f a)), P.total] }

lemma coarsen_sum (P : POVM n A) (f : A → B) (g : B → Matrix n n ℂ →ₗ[ℝ] ℝ) :
    (∑ b, g b ((P.coarsen f).effect b)) = ∑ a, g (f a) (P.effect a) := by
  classical
  simp only [coarsen, map_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def average (p : Law R) (P : R → POVM n A) : POVM n A where
  effect a := p.avg (fun r => (P r).effect a)
  pos a := p.avg_posSemidef _ (fun r => (P r).pos a)
  total := by
    simp only [Law.avg]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, (P _).total]
    exact p.avg_const 1
end QuantumSampling.POVM

namespace OperatorEntropy
variable {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
lemma potential_left_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hH : ∀ r, (H r).PosSemidef) (hH1 : ∀ r, H r ≤ 1)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ r, w r ≤ d) (hp : 0 < p)
    (hm : ∑ r, w r*prob C (F r) (H r) = p) :
    -p*Real.log (d/p) ≤ ∑ r, w r * prob C (effectEntropy (F r)) (H r) := by
  have h := ScalarEntropy.weighted_negMulLog_le w (fun r => prob C (F r) (H r)) hw
    (fun r => prob_nonneg (hF r) (hH r)) hd hs hp hm
  have h' : -(∑ r, w r*prob C (effectEntropy (F r)) (H r)) ≤
      ∑ r, w r*Real.negMulLog (prob C (F r) (H r)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun r _ => by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left
        (prob_entropy_left_lower C hC (hF r) (hH r) (hH1 r)) (hw r))
  linarith
lemma potential_right_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hF1 : ∀ r, F r ≤ 1) (hH : ∀ r, (H r).PosSemidef)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ r, w r ≤ d) (hp : 0 < p)
    (hm : ∑ r, w r*prob C (F r) (H r) = p) :
    -p*Real.log (d/p) ≤ ∑ r, w r * prob C (F r) (effectEntropy (H r)) := by
  have h := ScalarEntropy.weighted_negMulLog_le w (fun r => prob C (F r) (H r)) hw
    (fun r => prob_nonneg (hF r) (hH r)) hd hs hp hm
  have h' : -(∑ r, w r*prob C (F r) (effectEntropy (H r))) ≤
      ∑ r, w r*Real.negMulLog (prob C (F r) (H r)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun r _ => by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left
        (prob_entropy_right_lower C hC (hF r) (hF1 r) (hH r)) (hw r))
  linarith
omit [DecidableEq n] in
lemma potential_left_nonpos (C : Matrix m n ℂ)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hF1 : ∀ r, F r ≤ 1) (hH : ∀ r, (H r).PosSemidef) :
    (∑ r, w r * prob C (effectEntropy (F r)) (H r)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro r _
  apply mul_nonpos_of_nonneg_of_nonpos (hw r)
  simpa only [prob, eval_eq_trace, Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero,
    Complex.zero_re] using prob_mono_left C (hH r) (effectEntropy_nonpos (hF r) (hF1 r))
omit [DecidableEq m] in
lemma potential_right_nonpos (C : Matrix m n ℂ)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hH : ∀ r, (H r).PosSemidef) (hH1 : ∀ r, H r ≤ 1) :
    (∑ r, w r * prob C (F r) (effectEntropy (H r))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro r _
  apply mul_nonpos_of_nonneg_of_nonpos (hw r)
  simpa only [prob, eval_eq_trace, Matrix.transpose_zero, Matrix.mul_zero, Matrix.trace_zero,
    Complex.zero_re] using prob_mono_right C (hF r) (effectEntropy_nonpos (hH r) (hH1 r))
end OperatorEntropy

namespace Resolvent
variable {J : Type u_J} {n : Type u_n} [Fintype J] [Nonempty J] [DecidableEq J] [Fintype n] [DecidableEq n]

def effectIndex (A : J → Matrix n n ℂ) (T : Matrix n n ℂ) : J :=
  if h : T ∈ Set.range A then Classical.choose h else Classical.choice inferInstance

def commonMap (A : J → Matrix n n ℂ) (T : Matrix n n ℂ) : Matrix (J×n) n ℂ :=
  finitePurification A (effectIndex A T)

omit [DecidableEq J] [DecidableEq n] in
lemma effectIndex_eq (A : J → Matrix n n ℂ) {T : Matrix n n ℂ} (hT : T ∈ Set.range A) :
    A (effectIndex A T) = T := by
  simp only [effectIndex, dite_eq_left hT]
  exact Classical.choose_spec hT
lemma commonMap_gram (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef)
    {T : Matrix n n ℂ} (hT : T ∈ Set.range A) :
    (commonMap A T)ᴴ*commonMap A T = T := by
  rw [commonMap, finitePurification_self A hA, effectIndex_eq A hT]

lemma commonMap_jensen {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) :
    p.avg (fun r => (commonMap A (F r)-commonMap A (p.avg F))ᴴ *
      (commonMap A (F r)-commonMap A (p.avg F))) ≤
      p.avg (fun r => effectEntropy (F r)) - effectEntropy (p.avg F) := by
  have h := finitePurification_jensen A hA hA1 (fun r => effectIndex A (F r)) p.weight
    (effectIndex A (p.avg F)) p.nonneg p.total (by
      simp only [effectIndex_eq A (hF _), effectIndex_eq A hmean]; rfl)
  simp only [effectIndex_eq A (hF _), effectIndex_eq A hmean] at h
  exact h

variable {m : Type u_m} {K : Type u_K} [Fintype m] [DecidableEq m] [Fintype K] [DecidableEq K]
omit [DecidableEq m] in
lemma commonMap_error_left {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) (C : Matrix n m ℂ) (L : Matrix K m ℂ) :
    p.avg (fun r => hsSq ((commonMap A (F r)-commonMap A (p.avg F))*C*Lᵀ)) ≤
      p.avg (fun r => prob C (effectEntropy (F r)) (Lᴴ*L)) -
        prob C (effectEntropy (p.avg F)) (Lᴴ*L) := by
  have h := prob_mono_left C (Matrix.posSemidef_conjTranspose_mul_self L)
    (commonMap_jensen A hA hA1 p F hF hmean)
  rw [prob_sub_left] at h
  have he (T : R → Matrix n n ℂ) : prob C (p.avg T) (Lᴴ*L) =
      p.avg (fun r => prob C (T r) (Lᴴ*L)) := p.avg_linear T (probLeft C (Lᴴ*L))
  rw [he, he] at h
  convert h using 1
  apply congrArg p.avg
  funext r
  exact (prob_gram C _ L).symm
omit [DecidableEq m] in
lemma commonMap_error_right {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) (C : Matrix m n ℂ) (L : Matrix K m ℂ) :
    p.avg (fun r => hsSq (L*C*(commonMap A (F r)-commonMap A (p.avg F))ᵀ)) ≤
      p.avg (fun r => prob C (Lᴴ*L) (effectEntropy (F r))) -
        prob C (Lᴴ*L) (effectEntropy (p.avg F)) := by
  have h := prob_mono_right C (Matrix.posSemidef_conjTranspose_mul_self L)
    (commonMap_jensen A hA hA1 p F hF hmean)
  rw [prob_sub_right] at h
  have he (T : R → Matrix n n ℂ) : prob C (Lᴴ*L) (p.avg T) =
      p.avg (fun r => prob C (Lᴴ*L) (T r)) := p.avg_linear T (probRight C (Lᴴ*L))
  rw [he, he] at h
  convert h using 1
  apply congrArg p.avg
  funext r
  exact (prob_gram C L _).symm
end Resolvent

end ThresholdParallelRepetition

end

end OAI
