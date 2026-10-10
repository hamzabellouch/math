import Mathlib
import OAI.Combinatorics.KMedian.Preparation.CoupledReindex
import OAI.Combinatorics.KMedian.Preparation.CoupledWeights
import OAI.Combinatorics.KMedian.Preparation.PreparationStars
import OAI.Combinatorics.KMedian.Sparse.SparseCoupledPreparation

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

abbrev size (f n : ℕ) := f+(n*n+n)

def index : Fin (size f n) ≃ Star (Fin f) (Fin n) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) <|
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

def flagQ : Star (Fin f) (Fin n) → ℚ
  | .inl _ => 1
  | .inr _ => 0

def weightQ (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ : ℚ) : Star (Fin f) (Fin n) → ℚ
  | .inl i => if i ∈ outside P then y i else 0
  | .inr (.inl st) => ∑ i ∈ A st.1 ∩ P st.2, y i
  | .inr (.inr t) => γ*c t

theorem flag_cast (e : Star (Fin f) (Fin n)) : (flagQ e : ℝ)=flag e := by
  cases e <;> simp [flagQ, flag]

theorem weight_cast (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ : ℚ) (e : Star (Fin f) (Fin n)) :
    (weightQ y P A c γ e : ℝ) = weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e := by
  rcases e with i | (st | t)
  · dsimp only [weightQ, weight]
    split_ifs <;> simp
  · simp [weightQ, weight, Rat.cast_sum]
  · simp [weightQ, weight]

def D (A : Fin n → Finset (Fin f)) : Fin (size f n) → Finset (Fin n) := targets A ∘ index

def a : Fin (size f n) → ℚ := flagQ ∘ index

def q (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ g : ℚ) (e : Fin (size f n)) : ℚ := weightQ y P A c γ (index e) / g

theorem a_bounds (e : Fin (size f n)) : 0 ≤ a e ∧ a e ≤ 1 := by
  dsimp only [a, Function.comp_apply]
  generalize index e = z
  cases z <;> norm_num [flagQ]

theorem q_nonneg (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ g : ℚ) (hy : ∀ i, 0 ≤ y i) (hc : ∀ t, 0 ≤ c t)
    (hγ : 0 ≤ γ) (hg : 0 ≤ g) (e : Fin (size f n)) : 0 ≤ q y P A c γ g e := by
  apply div_nonneg _ hg
  have hw := weight_nonneg (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) (γ : ℝ)
    (fun i => by exact_mod_cast hy i) (fun t => by exact_mod_cast hc t)
    (by exact_mod_cast hγ) (index e)
  rw [← weight_cast] at hw
  exact_mod_cast hw

theorem scaled_q (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ g : ℚ) (hg : g ≠ 0) (e : Fin (size f n)) :
    (g : ℝ) * (q y P A c γ g e : ℝ) =
      weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) := by
  have hh : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  simp [q, Rat.cast_div, mul_div_cancel₀ _ hh, weight_cast]

noncomputable def coupled (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (p c : Fin n → ℚ) (γ g : ℚ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hm : ∀ t, ∑ i ∈ P t, y i=p t) (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8) (hunit : ∀ t, p t+c t=1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hg : 0 < g) (heven : Even Δ) (hgrid : g*(Δ:ℚ)=1) :
    CoupledLaw (targets A) flag
      (weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ)
      P (fun i => (y i : ℝ)) (fun t => (p t : ℝ)) (fun t => (c t : ℝ))
      g γ (∑ i, (y i : ℝ)) Δ := by
  have hcR : ∀ t, ∑ i ∈ A t, (y i : ℝ)=(c t : ℝ) := by
    intro t
    exact_mod_cast hc t
  have huR : ∀ t, (p t : ℝ)+(c t : ℝ)=1 := by
    intro t
    exact_mod_cast hunit t
  have hmR : ∀ t, ∑ i ∈ P t, (y i : ℝ)=(p t : ℝ) := by
    intro t
    exact_mod_cast hm t
  have mean : ∀ t, (g : ℝ)*(SparseOuterLaw.targetMean (D A) (q y P A c γ g) t : ℝ) =
      (1+(γ:ℝ))*(c t : ℝ) := by
    intro t
    simp only [SparseOuterLaw.targetMean, Rat.cast_sum, mul_sum]
    calc
      _ = ∑ e, if t ∈ targets A (index e) then
          weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) else 0 := by
        apply sum_congr rfl
        intro e _
        change (g:ℝ) * ((if t ∈ targets A (index e) then q y P A c γ g e else 0 : ℚ):ℝ) = _
        split_ifs <;> simp only [scaled_q y P A c γ g hg.ne', Rat.cast_zero, mul_zero]
      _ = _ := by
        rw [(index (f:=f) (n:=n)).sum_comp (fun e => if t ∈ targets A e then
          weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e else 0)]
        exact targeted_weight _ _ _ _ _ hP hcR t
  have planned : (g : ℝ) * (((n:ℚ)*(Δ:ℚ) +
      (∑ e, SparseSignedPreparation.signed (D A) a e * q y P A c γ g e) : ℚ) : ℝ) =
      (∑ i, (y i : ℝ)) - (γ:ℝ)*∑ t, (c t : ℝ) := by
    have hgR : (g:ℝ)*(Δ:ℝ)=1 := by exact_mod_cast hgrid
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum, mul_add, mul_sum]
    have hf : (g:ℝ)*((n:ℝ)*(Δ:ℝ))=(n:ℝ) := by nlinarith only [hgR]
    rw [hf]
    have he : (∑ e, (g:ℝ) * ((SparseSignedPreparation.signed (D A) a e : ℝ) *
        (q y P A c γ g e : ℝ))) = ∑ e,
        (flag (index e) - ((targets A (index e)).card : ℝ)) *
        weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) := by
      apply sum_congr rfl
      intro e _
      rw [mul_left_comm, scaled_q y P A c γ g hg.ne']
      simp only [SparseSignedPreparation.signed, Rat.cast_sub, Rat.cast_natCast, D, a,
        Function.comp_apply, flag_cast]
    rw [he, (index (f:=f) (n:=n)).sum_comp (fun e =>
      (flag e - ((targets A e).card : ℝ)) *
        weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e)]
    simpa only [Fintype.card_fin, mul_sum] using raw_identity (fun i => (y i : ℝ)) P A
      (fun t => (c t : ℝ)) (γ:ℝ) hP hcR (fun t => by rw [hmR]; exact huR t)
  let L := SparsePrepared.coupled (D A) a (q y P A c γ g) Δ P y p a_bounds
    (q_nonneg y P A c γ g hy hc0 hγ.le hg.le) g (fun t => (c t : ℝ)) γ
    (∑ i, (y i : ℝ)) hg (by exact_mod_cast hγ) (by exact_mod_cast hγ1) heven hgrid
    hy hp hm (fun t => by exact_mod_cast hc0 t) (fun t => by
      have hh : (c t : ℝ) ≤ ((1/8:ℚ):ℝ) := Rat.cast_le.mpr (hc1 t)
      norm_num at hh ⊢
      exact hh)
    huR mean planned
  have L' : CoupledLaw (targets A ∘ index) (flag ∘ index)
      (weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ ∘ index)
      P (fun i => (y i : ℝ)) (fun t => (p t : ℝ)) (fun t => (c t : ℝ))
      g γ (∑ i, (y i : ℝ)) Δ := by
    exact L.castWeights (funext (fun e => flag_cast (index e)))
      (funext (fun e => scaled_q y P A c γ g hg.ne' e))
  exact L'.reindexStars index

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
