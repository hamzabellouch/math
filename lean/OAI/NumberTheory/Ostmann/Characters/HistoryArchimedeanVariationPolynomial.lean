import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationPiece
import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearCells

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Polynomial Set
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable

def polynomialHistoryWeight {σ τ : Type*} [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) (profile : τ → HistoryProfile) (X : τ → ℝ)
    (supports : σ → ℝ[X]) (strict : σ → Bool)
    (arguments : τ → ℝ[X]) (denom : τ → ℝ) (t : ℝ) : ℂ :=
  if polynomialSupport supports strict t then
    historyArchimedeanProduct ρ profile
      (fun i => Real.log (X i / ((arguments i).eval t / denom i))) else 0

theorem polynomialHistoryWeight_piece_variation_le {σ τ : Type*} [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) (profile : τ → HistoryProfile) (X : τ → ℝ)
    (supports : σ → ℝ[X]) (strict : σ → Bool)
    (arguments : τ → ℝ[X]) (denom A B : τ → ℝ)
    (Q a N : ℕ) {M : ℝ} (hM : 0 ≤ M) (hAB : ∀ i, A i ≤ B i)
    (hX : ∀ i, 0 < X i)
    (hpos : ∀ t, polynomialSupport supports strict t →
      ∀ i, 0 < (arguments i).eval t / denom i)
    (hrange : ∀ t, polynomialSupport supports strict t → ∀ i,
      Real.log (X i / ((arguments i).eval t / denom i)) ∈ Icc (A i) (B i))
    (hbound : ∀ i, (profile i).bound ρ (B i) ≤ M)
    (c : CutPieceIndex (polynomialSupportCuts supports arguments)) :
    progressionVariation (pieceProgressionWeight (polynomialSupportCuts supports arguments) Q a
      (fun n => polynomialHistoryWeight ρ profile X supports strict arguments denom ((Q*n+a : ℕ) : ℝ)) c) N ≤
      M ^ (Fintype.card τ) * (3 + (∑ i : τ, (B i - A i))) := by
  classical
  obtain ⟨b,hb⟩ := polynomialSupport_boolean_on_piece supports arguments strict c
  cases b with
  | false =>
    have heq : pieceProgressionWeight (polynomialSupportCuts supports arguments) Q a
        (fun n => polynomialHistoryWeight ρ profile X supports strict arguments denom ((Q*n+a : ℕ) : ℝ)) c =
        fun _ => 0 := by
      funext n
      unfold pieceProgressionWeight
      split_ifs with hn
      · have hs : ¬ polynomialSupport supports strict ((Q*n+a : ℕ) : ℝ) := by
          simpa only [Bool.false_eq_true,iff_false] using hb _ hn
        simp only [polynomialHistoryWeight,ite_eq_right hs]
      · rfl
    rw [heq]
    simp only [progressionVariation,sub_self,norm_zero,Finset.sum_const_zero,add_zero]
    exact mul_nonneg (pow_nonneg hM _) (add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hAB i))))
  | true =>
    have hs (t : ℝ) (ht : t ∈ cutPiece (polynomialSupportCuts supports arguments) c) :
        polynomialSupport supports strict t := (hb t ht).mpr rfl
    have heq : pieceProgressionWeight (polynomialSupportCuts supports arguments) Q a
        (fun n => polynomialHistoryWeight ρ profile X supports strict arguments denom ((Q*n+a : ℕ) : ℝ)) c =
        sampledSetWeight (cutPiece (polynomialSupportCuts supports arguments) c) Q a
          (fun n => historyArchimedeanProduct ρ profile
            (fun i => Real.log (X i / ((arguments i).eval ((Q*n+a : ℕ) : ℝ) / denom i)))) := by
      funext n
      unfold pieceProgressionWeight sampledSetWeight
      split_ifs with hn
      · simp only [polynomialHistoryWeight,ite_eq_left (hs _ hn)]
      · rfl
    rw [heq]
    apply historyArchimedeanProduct_piece_variation_le ρ profile
      (fun i t => Real.log (X i / ((arguments i).eval t / denom i))) A B _
      (cutPiece_convex _ c) Q a N hM hAB
    · intro i t ht
      exact hrange t (hs t ht) i
    · intro i
      exact log_ratio_monotone_on _ (hX i) (fun t ht => hpos t (hs t ht) i)
        (polynomialArgument_monotone_on_piece supports arguments denom c i)
    · exact hbound

theorem polynomialHistoryWeight_total_variation_le {σ τ : Type*} [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) (profile : τ → HistoryProfile) (X : τ → ℝ)
    (supports : σ → ℝ[X]) (strict : σ → Bool)
    (arguments : τ → ℝ[X]) (denom A B : τ → ℝ)
    (Q a N : ℕ) {M : ℝ} (hM : 0 ≤ M) (hAB : ∀ i, A i ≤ B i)
    (hX : ∀ i, 0 < X i)
    (hpos : ∀ t, polynomialSupport supports strict t →
      ∀ i, 0 < (arguments i).eval t / denom i)
    (hrange : ∀ t, polynomialSupport supports strict t → ∀ i,
      Real.log (X i / ((arguments i).eval t / denom i)) ∈ Icc (A i) (B i))
    (hbound : ∀ i, (profile i).bound ρ (B i) ≤ M) :
    (∑ c : CutPieceIndex (polynomialSupportCuts supports arguments),
      progressionVariation (pieceProgressionWeight (polynomialSupportCuts supports arguments) Q a
        (fun n => polynomialHistoryWeight ρ profile X supports strict arguments denom ((Q*n+a : ℕ) : ℝ)) c) N) ≤
      ((2 * ((∑ i, (supports i).natDegree) + ∑ i, ((arguments i).natDegree - 1)) + 1 : ℕ) : ℝ) *
        (M ^ (Fintype.card τ) * (3 + (∑ i : τ, (B i - A i)))) := by
  have hcost : 0 ≤ M ^ (Fintype.card τ) * (3 + (∑ i : τ, (B i - A i))) := mul_nonneg (pow_nonneg hM _) (add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hAB i))))
  calc
    _ ≤ ∑ c : CutPieceIndex (polynomialSupportCuts supports arguments),
        M ^ (Fintype.card τ) * (3 + (∑ i : τ, (B i - A i))) :=
      Finset.sum_le_sum (fun c _ => polynomialHistoryWeight_piece_variation_le
        ρ profile X supports strict arguments denom A B Q a N hM hAB hX hpos hrange hbound c)
    _ = (Fintype.card (CutPieceIndex (polynomialSupportCuts supports arguments)) : ℝ) *
        (M ^ (Fintype.card τ) * (3 + (∑ i : τ, (B i - A i)))) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (polynomial_support_total_partition supports arguments strict denom).1) hcost

end Ostmann.Characters

end

end OAI
