import Mathlib
import OAI.NumberTheory.Jacobsthal.Partitions.SourceLabelCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells

theorem discard_coefficient_bound (S Z eps : ℝ) (n labels : ℕ) (hS : 0 < S) (hZ : 0 < Z)
    (hn : S/Z^eps ≤ (n : ℝ)) (hl : (labels : ℝ) ≤ Z^eps) :
    (labels : ℝ)*(S/Z)*Z^eps/(n : ℝ) ≤ Z^(3*eps-1) := by
  have hZpow : 0 < Z^eps := Real.rpow_pos_of_pos hZ eps
  have hn0 : (0 : ℝ) < n := (div_pos hS hZpow).trans_le hn
  calc
    _ ≤ Z^eps*(S/Z)*Z^eps/(n : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hl (div_pos hS hZ).le) hZpow.le) hn0.le
    _ ≤ Z^eps*(S/Z)*Z^eps/(S/Z^eps) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hS hZpow) hn
    _ = (S*S⁻¹)*(Z^eps*Z^eps*Z^eps/Z) := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    _ = Z^eps*Z^eps*Z^eps/Z := by rw [mul_inv_cancel₀ hS.ne',one_mul]
    _ = Z^(eps+eps+eps-1) := by
      rw [← Real.rpow_add hZ,← Real.rpow_add hZ]
      simpa only [Real.rpow_one] using (Real.rpow_sub hZ (eps+eps+eps) 1).symm
    _ = Z^(3*eps-1) := by congr 1;ring

end ErdosInverseCells

end

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

theorem subset_weight_spread {α : Type*} (Q D : Finset α) (hD : D ⊆ Q) (hQ : 0 < Q.card)
    (w : α → ℝ) (G : ℝ) (hspread : ∀ q ∈ Q,∀ r ∈ Q,w q ≤ G*w r) :
    (∑ q ∈ D,w q) ≤ ((D.card : ℝ)*G/(Q.card : ℝ))*(∑ r ∈ Q,w r) := by
  have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast hQ
  have hdouble : (Q.card : ℝ)*(∑ q ∈ D,w q) ≤ (D.card : ℝ)*G*(∑ r ∈ Q,w r) := by
    calc
      _ = ∑ q ∈ D,∑ _r ∈ Q,w q := by
        simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
      _ ≤ ∑ q ∈ D,∑ r ∈ Q,G*w r :=
        Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hspread q (hD hq) r hr))
      _ = _ := by
        simp only [← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
        ring
  calc
    _ ≤ ((D.card : ℝ)*G*(∑ r ∈ Q,w r))/(Q.card : ℝ) :=
      (le_div_iff₀ hQpos).mpr (by nlinarith [hdouble])
    _ = _ := by ring

theorem discarded_weight_bound {ι : Type*} [Fintype ι]
    (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) (htau : 0 ≤ tau) (hQ : 0 < Q.card)
    (w : ℕ → ℝ) (hw : ∀ q ∈ Q,0 ≤ w q) (G : ℝ) (hG : 0 ≤ G)
    (hspread : ∀ q ∈ Q,∀ r ∈ Q,w q ≤ G*w r) :
    (∑ q ∈ discardedPoints Q label tau,w q) ≤
      ((Fintype.card ι : ℝ)*tau*G/(Q.card : ℝ))*(∑ q ∈ Q,w q) := by
  have hsum : 0 ≤ ∑ q ∈ Q,w q := Finset.sum_nonneg hw
  have hcard := discardedPoints_card_bound Q label tau htau
  calc
    _ ≤ (((discardedPoints Q label tau).card : ℝ)*G/(Q.card : ℝ))*(∑ q ∈ Q,w q) :=
      subset_weight_spread Q _ (discardedPoints_subset Q label tau) hQ w G hspread
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hG) (Nat.cast_nonneg _)) hsum

end ErdosInverseCells

end

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseCells
open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler
open NumberTheoryLean.LogarithmicBinScale

noncomputable def initialDiscarded (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k : ℕ) (w Z : ℝ) : Finset ℕ := by
  letI : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  exact discardedPoints Q (initialLabel a B xi k (smallModulus w)) (B/Z)

theorem source_initial_discard_power (C xi eps : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ (m : Fin (binCount (sourceW z) z xi) → ℕ) (a : ℕ → ℕ),
      ((∑ i,m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      let Q := cofactorChoices (actualBins z xi) m
      let S := cofactorScale z xi m
      let k := ∑ i,m i
      (∑ q ∈ initialDiscarded Q a S xi k (sourceW z) (sourceZ z),(q : ℝ)⁻¹) ≤
        (sourceZ z)^(3*eps-1)*(∑ q ∈ Q,(q : ℝ)⁻¹) := by
  filter_upwards [source_cofactor_cell_data C xi eps hC hxi hxi1 heps,
    source_initial_label_count C eps hC heps,source_cofactor_weight_variation C xi eps hC hxi hxi1 heps]
    with z hc hl hw
  intro m a hm
  let Q := cofactorChoices (actualBins z xi) m
  let S := cofactorScale z xi m
  let k := ∑ i,m i
  let : NeZero (smallModulus (sourceW z)) := ⟨(smallModulus_pos _).ne'⟩
  have hdata := hc m hm
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hlabel : (Fintype.card (InitialLabel k (smallModulus (sourceW z))) : ℝ) ≤ (sourceZ z)^eps := by
    rw [initialLabel_card]
    exact hl k hm
  have hspread : ∀ q ∈ Q,∀ r ∈ Q,(q : ℝ)⁻¹ ≤ (sourceZ z)^eps*(r : ℝ)⁻¹ :=
    fun q hq r hr => (hw m hm q r hq hr).2
  have hmass : 0 ≤ ∑ q ∈ Q,(q : ℝ)⁻¹ := by positivity
  have hdiscard := discarded_weight_bound Q (initialLabel a S xi k (smallModulus (sourceW z)))
    (S/sourceZ z) (div_pos hdata.1 hZ).le hdata.2.1 (fun q => (q : ℝ)⁻¹)
    (fun _ _ => by positivity) ((sourceZ z)^eps) (Real.rpow_nonneg hZ.le _) hspread
  have hcoef := discard_coefficient_bound S (sourceZ z) eps Q.card
    (Fintype.card (InitialLabel k (smallModulus (sourceW z)))) hdata.1 hZ hdata.2.2.1 hlabel
  exact hdiscard.trans (mul_le_mul_of_nonneg_right hcoef hmass)

theorem source_initial_discard_small (C xi tolerance : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (ht : 0 < tolerance) :
    ∀ᶠ z : ℝ in atTop,∀ (m : Fin (binCount (sourceW z) z xi) → ℕ) (a : ℕ → ℕ),
      ((∑ i,m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      let Q := cofactorChoices (actualBins z xi) m
      let S := cofactorScale z xi m
      let k := ∑ i,m i
      (∑ q ∈ initialDiscarded Q a S xi k (sourceW z) (sourceZ z),(q : ℝ)⁻¹) ≤
        tolerance*(∑ q ∈ Q,(q : ℝ)⁻¹) := by
  have hT := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5/8)).comp sourceZ_tendsto_atTop
  have hs := (tendsto_order.mp hT).2 tolerance ht
  filter_upwards [source_initial_discard_power C xi (1/8) hC hxi hxi1 (by norm_num),hs] with z hc hz
  intro m a hm
  have hh := hc m a hm
  norm_num only at hh
  have hz' : (sourceZ z)^(-((5 : ℝ)/8)) < tolerance := hz
  have hp : (sourceZ z)^(-((5 : ℝ)/8)) ≤ tolerance := by linarith
  exact hh.trans (mul_le_mul_of_nonneg_right hp (by positivity))

end ErdosInverseCells

end

end Erdos970

end OAI
