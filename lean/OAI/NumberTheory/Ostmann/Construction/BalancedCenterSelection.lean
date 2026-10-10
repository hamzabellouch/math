import OAI.NumberTheory.Ostmann.Construction.BalancedCellScale
import OAI.NumberTheory.Ostmann.Construction.IntegerCenterSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter

lemma eventually_good_center_in_window (d : Decomposition) (n a b ρ : ℝ)
    (hn : 0<n) (ha : 0<a/n-ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ T : ℤ,
      a*favorableBlockWidth L≤(T:ℝ) → (T:ℝ)≤b*favorableBlockWidth L →
      ∀ c : ℤ, c∈integerCenterWindow ((T:ℝ)/n) (ρ*favorableBlockWidth L) →
      c∉badLogCellCenters d (cellPrimeCutoff L)
        (integerCenterWindow ((T:ℝ)/n) (ρ*favorableBlockWidth L)) (1/8) →
      BalancedCellAfterTwo d c := by
  classical
  filter_upwards [balancedCellAfterTwo_eventually d ha (b/n+ρ)] with L hL
  intro T hTlo hThi c hc hbad
  obtain ⟨hclo,hchi⟩ := abs_le.mp ((mem_integerCenterWindow _ _ _).mp hc)
  have htlo := div_le_div_of_nonneg_right hTlo hn.le
  have hthi := div_le_div_of_nonneg_right hThi hn.le
  have e₁ : a*favorableBlockWidth L/n=(a/n)*favorableBlockWidth L := by ring
  have e₂ : b*favorableBlockWidth L/n=(b/n)*favorableBlockWidth L := by ring
  rw [e₁] at htlo
  rw [e₂] at hthi
  apply hL c (by nlinarith) (by nlinarith)
  have hn : ¬(1/8:ℝ)≤badLogCellMass d (cellPrimeCutoff L) c := by
    intro h
    exact hbad (Finset.mem_filter.mpr ⟨hc,h⟩)
  exact (lt_of_not_ge hn).le

lemma eventually_center_window_budget (d : Decomposition) {ρ : ℝ} (hρ : 0<ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ K : Finset ℤ,
      4*((badLogCellCenters d (cellPrimeCutoff L) K (1/8)).card:ℝ)+4≤
        ρ*favorableBlockWidth L := by
  obtain ⟨C,hC,hbudget⟩ := badLogCellCenters_linear_bound d
  have hratio : ∀ᶠ L : ℝ in atTop, (4*C+4)/ρ≤favorableBlockWidth L/L := by
    have h := (tendsto_exp_mul_div_rpow_atTop 1 (1/100) (by norm_num)).eventually_ge_atTop ((4*C+4)/ρ)
    simpa only [Real.rpow_one,favorableBlockWidth] using h
  filter_upwards [hbudget,hratio,eventually_ge_atTop (1:ℝ)] with L hb hratio hL
  intro K
  have hL0 : 0<L := by linarith
  have hmul := mul_le_mul_of_nonneg_left ((le_div_iff₀ hL0).mp hratio) hρ.le
  have he : ρ*((4*C+4)/ρ*L)=(4*C+4)*L := by field_simp
  rw [he] at hmul
  have hk := hb K
  nlinarith

theorem exists_balanced_pair_centers (d : Decomposition) (a b ρ : ℝ)
    (hρ : 0<ρ) (ha : 0<a/2-ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ T : ℤ,
      a*favorableBlockWidth L≤(T:ℝ) → (T:ℝ)≤b*favorableBlockWidth L →
      ∃u v : ℤ,u+v=T ∧ |(u:ℝ)-(T:ℝ)/2|≤ρ*favorableBlockWidth L ∧
        |(v:ℝ)-(T:ℝ)/2|≤ρ*favorableBlockWidth L ∧
        BalancedCellAfterTwo d u ∧ BalancedCellAfterTwo d v := by
  filter_upwards [eventually_center_window_budget d hρ,
    eventually_good_center_in_window d 2 a b ρ (by norm_num) ha] with L hbudget hgood
  intro T hTlo hThi
  let K := integerCenterWindow ((T:ℝ)/2) (ρ*favorableBlockWidth L)
  let B := badLogCellCenters d (cellPrimeCutoff L) K (1/8)
  have hb := hbudget K
  have hc0 : 0≤(B.card:ℝ) := Nat.cast_nonneg _
  have hb' : 2*(B.card:ℝ)+2≤ρ*favorableBlockWidth L := by change 4*(B.card:ℝ)+4≤_ at hb; linarith
  obtain ⟨u,v,hu,hv,hsum,hub,hvb⟩ := exists_pair_integer_centers B T (ρ*favorableBlockWidth L) hb'
  refine ⟨u,v,hsum,hub,hvb,?_,?_⟩
  · exact hgood T hTlo hThi u ((mem_integerCenterWindow _ _ _).mpr hub) hu
  · exact hgood T hTlo hThi v ((mem_integerCenterWindow _ _ _).mpr hvb) hv

theorem exists_balanced_triple_centers (d : Decomposition) (a b ρ : ℝ)
    (hρ : 0<ρ) (ha : 0<a/3-ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ T : ℤ,
      a*favorableBlockWidth L≤(T:ℝ) → (T:ℝ)≤b*favorableBlockWidth L →
      ∃u v w : ℤ,u+v+w=T ∧ |(u:ℝ)-(T:ℝ)/3|≤ρ*favorableBlockWidth L ∧
        |(v:ℝ)-(T:ℝ)/3|≤ρ*favorableBlockWidth L ∧
        |(w:ℝ)-(T:ℝ)/3|≤ρ*favorableBlockWidth L ∧
        BalancedCellAfterTwo d u ∧ BalancedCellAfterTwo d v ∧ BalancedCellAfterTwo d w := by
  filter_upwards [eventually_center_window_budget d hρ,
    eventually_good_center_in_window d 3 a b ρ (by norm_num) ha] with L hbudget hgood
  intro T hTlo hThi
  let K := integerCenterWindow ((T:ℝ)/3) (ρ*favorableBlockWidth L)
  let B := badLogCellCenters d (cellPrimeCutoff L) K (1/8)
  obtain ⟨u,v,w,hu,hv,hw,hsum,hub,hvb,hwb⟩ :=
    exists_triple_integer_centers B T (ρ*favorableBlockWidth L) (hbudget K)
  refine ⟨u,v,w,hsum,hub,hvb,hwb,?_,?_,?_⟩
  · exact hgood T hTlo hThi u ((mem_integerCenterWindow _ _ _).mpr hub) hu
  · exact hgood T hTlo hThi v ((mem_integerCenterWindow _ _ _).mpr hvb) hv
  · exact hgood T hTlo hThi w ((mem_integerCenterWindow _ _ _).mpr hwb) hw

end Ostmann.Construction

end

end OAI
