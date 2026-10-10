import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalChargeHistories

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w
variable {C : Type v} {A B : Type w} [Fintype C] [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def chargedBad (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → A×B) → (C × Fin (n+k) ↪ ι) →
    (ι → Option C) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundBad p e own (reciprocalCharges p v w ρ r s) J D a)
      (fun t => (∑ f : C → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          chargedBad v w ρ r s n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (C → Fin (n+k+1))) j

def chargedSelectedBad (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → A×B) → (C × Fin (n+k) ↪ ι) →
    (ι → Option C) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundSelectedBad p e own (reciprocalCharges p v w ρ r s) J D a)
      (fun t => (∑ f : C → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          chargedSelectedBad v w ρ r s n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (C → Fin (n+k+1))) j

omit [FiniteDimensional K V] in

theorem chargedSelectedBad_le (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (n k : ℕ) (J D a : ℝ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→A×B))
    (e : C×Fin (n+k) ↪ ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k) :
    (n:ℝ)*chargedSelectedBad v w ρ r s n J D a k p e own t≤chargedBad v w ρ r s n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change (n:ℝ)*roundSelectedBad p e own (reciprocalCharges p v w ρ r s) J D a≤
        roundBad p e own (reciprocalCharges p v w ρ r s) J D a
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (show n≤n+(k+1) by omega))
        (roundSelectedBad_nonneg p e own _ J D a)).trans (roundSelectedBad_le p e own hown _ J D a)
    · change (n:ℝ)*((∑ f : C→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            chargedSelectedBad v w ρ r s n J D a k
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

omit [FiniteDimensional K V] in
lemma history_average_const {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    {m : ℕ} (hm : 0 < m) (p : Law (ι→β)) (e : C×Fin m ↪ ι) (a : ℝ) :
    (∑ f : C→Fin m,∑ z,(p.restrict (freshRepresentatives e f)).mass z*a)/
      Fintype.card (C→Fin m)=a := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hc : (Fintype.card (C→Fin m):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hi (f : C→Fin m) : ∑ z, (p.restrict (freshRepresentatives e f)).mass z*a=a := by
    rw [←sum_mul,Law.total,one_mul]
  simp_rw [hi]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ a hc

theorem chargedBad_budget (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 0<n) (J D a N M : ℝ) (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→A×B))
    (e : C×Fin (n+k) ↪ ι) (own : ι→Option C) (S : ι→Finset (A×B))
    (hS : tupleSupported p S) (hJ : ∀ i,Real.log (S i).card≤J)
    (hN : (Fintype.card ι:ℝ)≤N) (hf : tupleFlags p v w) (ho : rectangleBound p v w M)
    (t : Fin k) :
    chargedBad v w ρ r s n J D a k p e own t≤
      exposureDeficits n J k p e t/D+exposureScores n k p e own t/a+2*N*M/((n:ℝ)*a) := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change roundBad p e own (reciprocalCharges p v w ρ r s) J D a≤
        tupleDeficit J p/D+roundInformation p e own/a+2*N*M/((n:ℝ)*a)
      refine (roundBad_le (by omega : 0<n+(k+1)) p e own _ J D a hD ha
        (tupleSupported_marginal_cap p S hS J hJ)).trans ?_
      apply add_le_add_right
      have hc : (∑ i,∑ j,(reciprocalCharges p v w ρ r s i j:ℝ))≤2*N*M := by
        exact (reciprocalCharges_sum p v w hρ hsum hf ho).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hN (by norm_num)) hM)
      have hm : (0:ℝ)<n := by exact_mod_cast hn
      have hN0 : 0≤N := (Nat.cast_nonneg _).trans hN
      apply div_le_div₀ (by positivity) hc (by positivity)
      gcongr
      exact_mod_cast (show n≤n+(k+1) by omega)
    · change (∑ f : C→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            chargedBad v w ρ r s n J D a k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ)
              (remainingEmbedding e f) (fun i => own i) j)/_≤_
      calc
        _ ≤ (∑ f : C→Fin (n+k+1),∑ z,
            (p.restrict (freshRepresentatives e f)).mass z *
            (exposureDeficits n J k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) j/D+
             exposureScores n k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i => own i) j/a+
              2*N*M/((n:ℝ)*a))) /Fintype.card (C→Fin (n+k+1)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply sum_le_sum
          intro f _
          apply sum_le_sum
          intro z _
          by_cases hz : (p.restrict (freshRepresentatives e f)).mass z=0
          · rw [hz,zero_mul,zero_mul]
          · apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
            exact ih _ (remainingEmbedding e f) (fun i => own i) (fun i => S i)
              (tupleSupported_cond_restrict p S hS _ z hz) (fun i => hJ i)
              ((Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hN)
              (tupleFlags_cond_restrict p v w hf _ z hz)
              (rectangleBound_cond_restrict p v w ho _ z hz) j
        _ = _ := by
          rw [exposureDeficits_succ,exposureScores_succ]
          simp only [mul_add,sum_add_distrib,add_div]
          rw [history_average_const (by omega : 0<n+k+1)]
          simp only [←mul_div_assoc,←sum_div]
          ring

theorem exists_good_reciprocal_exposure (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a M : ℝ) (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→A×B))
    (e : C×Fin (n+k) ↪ ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (S : ι→Finset (A×B))
    (hS : tupleSupported p S) (hJ : ∀ i,Real.log (S i).card≤J)
    (hf : tupleFlags p v w) (ho : rectangleBound p v w M) :
    ∃ t : Fin k,
      chargedBad v w ρ r s n J D a k p e own t≤
        tupleDeficit J p/D+2*totalCorrelation p/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (n:ℝ)*chargedSelectedBad v w ρ r s n J D a k p e own t≤
        tupleDeficit J p/D+2*totalCorrelation p/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) := by
  obtain ⟨t,ht⟩ := exists_exposure_round n k hn hk p e own hown
  have hb := chargedBad_budget v w hρ hsum n k (by omega) J D a (Fintype.card ι) M
    hD ha hM p e own S hS hJ le_rfl hf ho t
  have hb' : chargedBad v w ρ r s n J D a k p e own t≤
      tupleDeficit J p/D+2*totalCorrelation p/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) := by
    have hd := exposureDeficits_le n k J p e S hS hJ t
    calc
      _ ≤ exposureDeficits n J k p e t/D+exposureScores n k p e own t/a+_ := hb
      _ ≤ tupleDeficit J p/D+(2*totalCorrelation p/(k:ℝ))/a+_ := by gcongr
      _ = _ := by rw [div_div]
  exact ⟨t,hb',(chargedSelectedBad_le v w ρ r s n k J D a p e own hown t).trans hb'⟩

end
end SharpLogRamsey.Selection

end

end OAI
