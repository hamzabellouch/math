import OAI.NumberTheory.Jacobsthal.Primes.FullPrimeEventFibres

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceLargeMap
open ErdosVarianceSmallModel ErdosVarianceLargeCount
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def patternEventWeight (w : ℝ) (H : ℕ) (E : ErdosLargePatternLaw.FullPattern w H → Prop) : ℝ :=
  ∑ _v ∈ Finset.univ.filter E,ErdosLargePatternLaw.weight w H

theorem full_pattern_card_numeric (w : ℝ) (H : ℕ) :
    Fintype.card (ErdosLargePatternLaw.FullPattern w H) = patternCard (divisorModulus w H) (coprimeModulus w H) := by
  rw [ErdosLargePatternLaw.pattern_card,patternCard]
  ring

theorem full_pattern_weight_numeric (w : ℝ) (H : ℕ) :
    ErdosLargePatternLaw.weight w H = 1/(patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ) := by
  unfold ErdosLargePatternLaw.weight patternCard
  push_cast
  congr 1
  ring

theorem patternEventWeight_card (w : ℝ) (H : ℕ) (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    patternEventWeight w H E = ((Finset.univ.filter E).card : ℝ)/
      (patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ) := by
  rw [patternEventWeight,Finset.sum_const,nsmul_eq_mul,full_pattern_weight_numeric]
  ring

theorem patternEventWeight_nonneg (w : ℝ) (H : ℕ) (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    0 ≤ patternEventWeight w H E := Finset.sum_nonneg (fun _ _ => (ErdosLargePatternLaw.weight_positive w H).le)

end ErdosVarianceLargeMap



namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosLargeHeightBlocks ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem full_event_count_bound (R theta w C err : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (herr : 0 ≤ err) (hw : 0 ≤ w)
    (hP : ∀ p ∈ primeBin R theta,p.Prime) (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (hbound : ∀ (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern w H),
      ((blockPatternPrimes R theta w H C0 hw hP hlarge i v).card : ℝ) ≤
        C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/
          ((patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ)*Real.log R)+err)
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) :
    ((fullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E).card : ℝ) ≤
      C*theta*R/Real.log R*patternEventWeight w H E+
        (blockCount C0 R theta H : ℝ)*(patternCard (divisorModulus w H) (coprimeModulus w H) : ℝ)*err := by
  let B := Finset.univ.filter E
  let M : ℝ := patternCard (divisorModulus w H) (coprimeModulus w H)
  let n : ℝ := blockCount C0 R theta H
  have hinner : (∑ i : Fin (blockCount C0 R theta H),
      (C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/(M*Real.log R)+err)) =
        C*(theta*R)/(M*Real.log R)+n*err := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    congr 1
    calc
      _ = (C/(M*Real.log R))*∑ i : Fin (blockCount C0 R theta H),
          (blockRight C0 R theta H i-blockLeft C0 R theta H i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [block_width_sum];ring
  have hsum : ((fullPrimeEvent (primeBin R theta) w H C0 hw hP hlarge E).card : ℝ) ≤
      (B.card : ℝ)*(C*(theta*R)/(M*Real.log R)+n*err) := by
    rw [fullPrimeEvent_card_fibres R theta w H C0 hR htheta hw hP hlarge E,Nat.cast_sum]
    simp_rw [Nat.cast_sum]
    calc
      _ ≤ ∑ i : Fin (blockCount C0 R theta H),∑ _v ∈ B,
          (C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/(M*Real.log R)+err) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Finset.sum_le_sum (fun v _hv => hbound i v)
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [hinner,Finset.sum_const,nsmul_eq_mul]
  have hB : (B.card : ℝ) ≤ M := by
    have hh := Finset.card_le_univ B
    rw [full_pattern_card_numeric] at hh
    dsimp [M]
    exact_mod_cast hh
  have hevent : patternEventWeight w H E = (B.card : ℝ)/M := patternEventWeight_card w H E
  have herror : (B.card : ℝ)*(n*err) ≤ M*(n*err) := mul_le_mul_of_nonneg_right hB (by dsimp [n];positivity)
  have he : (B.card : ℝ)*(C*(theta*R)/(M*Real.log R)+n*err) =
      C*theta*R/Real.log R*patternEventWeight w H E+(B.card : ℝ)*(n*err) := by
    rw [hevent]
    ring
  have hright : C*theta*R/Real.log R*patternEventWeight w H E+(B.card : ℝ)*(n*err) ≤
      C*theta*R/Real.log R*patternEventWeight w H E+n*M*err := by nlinarith
  exact hsum.trans (he.trans_le hright)

end ErdosVarianceLargeMap



open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosLargeHeightBlocks
  ErdosInversePrimeBin ErdosInverseBoxHeight
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_full_event_count (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R theta : ℝ),z^alpha ≤ R → 0 < theta → theta ≤ 1 →
      ∀ (H : ℕ) (C0 : ℤ),2 ≤ H → Int.gcd C0 (H : ℤ) = 1 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 →
      ∀ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
        (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ))
        (E : ErdosLargePatternLaw.FullPattern (sourceW z) H → Prop),
        ((fullPrimeEvent (primeBin R theta) (sourceW z) H C0 hw hP hlarge E).card : ℝ) ≤
          C*theta*R/Real.log R*patternEventWeight (sourceW z) H E+
          (blockCount C0 R theta H : ℝ)*
            (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ)*R^((9 : ℝ)/10) := by
  obtain ⟨C,hC,hbound⟩ := source_block_fibre_bound alpha halpha
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with z hz
  refine ⟨hz.1,?_⟩
  intro R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge E
  have hR : 0 < R := (Real.rpow_pos_of_pos (by linarith [hz.1]) alpha).trans_le hRlo
  exact full_event_count_bound R theta (sourceW z) C (R^((9 : ℝ)/10)) H C0 hR htheta
    (Real.rpow_nonneg hR.le _) hw hP hlarge
    (hz.2 R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge) E

end ErdosVarianceLargeMap


end Erdos970

end OAI
