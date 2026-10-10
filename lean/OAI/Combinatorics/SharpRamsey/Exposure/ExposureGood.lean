import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.GoodRound

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

def exposureBad (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → β) → (B × Fin (n+k) ↪ ι) →
    (ι → Option B) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundBad p e own (fun _ _ => 0) J D a)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureBad n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (B → Fin (n+k+1))) j

def exposureSelectedBad (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → β) → (B × Fin (n+k) ↪ ι) →
    (ι → Option B) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundSelectedBad p e own (fun _ _ => 0) J D a)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureSelectedBad n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (B → Fin (n+k+1))) j

lemma roundSelectedBad_nonneg {ι : Type u} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (p : Law (ι→β)) (e : B×Fin m ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) : 0≤roundSelectedBad p e own c J D a := by
  unfold roundSelectedBad
  positivity

theorem exposureSelectedBad_le (n k : ℕ) (J D a : ℝ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : B×Fin (n+k) ↪ ι) (own : ι→Option B)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k) :
    (n:ℝ)*exposureSelectedBad n J D a k p e own t≤exposureBad n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change (n:ℝ)*roundSelectedBad p e own (fun _ _ => 0) J D a≤
        roundBad p e own (fun _ _ => 0) J D a
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (show n≤n+(k+1) by omega))
        (roundSelectedBad_nonneg p e own _ J D a)).trans (roundSelectedBad_le p e own hown _ J D a)
    · change (n:ℝ)*((∑ f : B→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            exposureSelectedBad n J D a k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ)
              (remainingEmbedding e f) (fun i => own i) j)/_)≤_
      rw [←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [mul_sum]
      apply sum_le_sum
      intro f _
      rw [mul_sum]
      apply sum_le_sum
      intro z _
      rw [mul_left_comm]
      apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
      exact ih _ (remainingEmbedding e f) (fun i => own i)
        (fun b x => remaining_own e f own hown b x) j

theorem exposureBad_budget (n k : ℕ) (J D a : ℝ) (hD : 0<D) (ha : 0<a)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : B×Fin (n+k) ↪ ι) (own : ι→Option B) (S : ι→Finset β)
    (hS : tupleSupported p S) (hJ : ∀ i,Real.log (S i).card≤J) (t : Fin k) :
    exposureBad n J D a k p e own t≤
      exposureDeficits n J k p e t/D+exposureScores n k p e own t/a := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change roundBad p e own (fun _ _ => 0) J D a≤tupleDeficit J p/D+roundInformation p e own/a
      simpa only [NNReal.coe_zero,sum_const_zero,zero_div,add_zero] using
        roundBad_le (by omega : 0<n+(k+1)) p e own (fun _ _ => 0) J D a hD ha
          (tupleSupported_marginal_cap p S hS J hJ)
    · change (∑ f : B→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            exposureBad n J D a k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ)
              (remainingEmbedding e f) (fun i => own i) j)/_≤_
      calc
        _ ≤ (∑ f : B→Fin (n+k+1),∑ z,
            (p.restrict (freshRepresentatives e f)).mass z *
            (exposureDeficits n J k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) j/D+
             exposureScores n k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i => own i) j/a)) /
                Fintype.card (B→Fin (n+k+1)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply sum_le_sum
          intro f _
          apply sum_le_sum
          intro z _
          by_cases hz : (p.restrict (freshRepresentatives e f)).mass z=0
          · rw [hz,zero_mul,zero_mul]
          · apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
            exact ih _ (remainingEmbedding e f) (fun i => own i) (fun i => S i)
              (tupleSupported_cond_restrict p S hS _ z hz) (fun i => hJ i) j
        _ = _ := by
          rw [exposureDeficits_succ,exposureScores_succ]
          simp only [mul_add,←mul_div_assoc,sum_add_distrib,←sum_div,add_div]
          ring

theorem exists_good_exposure (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a : ℝ)
    (hD : 0<D) (ha : 0<a) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : B×Fin (n+k) ↪ ι) (own : ι→Option B)
    (hown : ∀ b x,own (e (b,x))=some b) (S : ι→Finset β)
    (hS : tupleSupported p S) (hJ : ∀ i,Real.log (S i).card≤J) :
    ∃ t : Fin k,
      exposureBad n J D a k p e own t≤tupleDeficit J p/D+2*totalCorrelation p/((k:ℝ)*a) ∧
      (n:ℝ)*exposureSelectedBad n J D a k p e own t≤
        tupleDeficit J p/D+2*totalCorrelation p/((k:ℝ)*a) := by
  obtain ⟨t,ht⟩ := exists_exposure_round n k hn hk p e own hown
  have hb := exposureBad_budget n k J D a hD ha p e own S hS hJ t
  have hb' : exposureBad n J D a k p e own t≤
      tupleDeficit J p/D+2*totalCorrelation p/((k:ℝ)*a) := by
    have hd := exposureDeficits_le n k J p e S hS hJ t
    calc
      _ ≤ exposureDeficits n J k p e t/D+exposureScores n k p e own t/a := hb
      _ ≤ tupleDeficit J p/D+(2*totalCorrelation p/(k:ℝ))/a := by gcongr
      _ = _ := by rw [div_div]
  exact ⟨t,hb',(exposureSelectedBad_le n k J D a p e own hown t).trans hb'⟩

end
end SharpLogRamsey.Selection

end

end OAI
