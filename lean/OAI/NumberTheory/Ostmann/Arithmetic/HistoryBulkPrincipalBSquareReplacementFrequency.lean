import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum Filter
open HistoryGiantFrequencyCount ScaleBudget
attribute [local instance] Classical.propDecidable
local instance squareFrequencyInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem frequency_error_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀l,l≤k →
      ∀z : FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → ℂ,
      (∀f g,‖z f g‖≤Real.exp (-Real.exp ((1/500:ℝ)*L))) →
      (∑f,∑g,‖z f g‖)≤Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  obtain ⟨A,hA,hcard⟩ := eventually_actual_pair_card_le Bs BD Bz hk
  filter_upwards [hcard,eventually_double_exp_error A 1
    (a:=0) (b:=1/500) (d:=3/2000) (c:=1)
    (by norm_num) (by norm_num) (by norm_num)] with L hc herr
  intro l hl z hz
  calc
    _ ≤ ∑f : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
        ∑g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
          Real.exp (-Real.exp ((1/500:ℝ)*L)) :=
      Finset.sum_le_sum (fun f _=>Finset.sum_le_sum (fun g _=>hz f g))
    _ = (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l ×
        FrequencyChoices (frequencyBound Bs BD Bz k L) l):ℝ)*
          Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul,mul_assoc]
    _ ≤ Real.exp (A*L)*Real.exp (-Real.exp ((1/500:ℝ)*L)) :=
      mul_le_mul_of_nonneg_right (hc l hl) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [←Real.exp_add]
      simpa only [zero_mul,Real.exp_zero,mul_one,pow_one,one_mul,neg_mul,add_comm] using herr

theorem selected_principal_B_cmean_frequencies_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hBs : 0≤Bs) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop, ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀l (corrected mixed : Bool),(if corrected then l<k else l≤k) →
      ∀outside : List ℕ,(∀p∈outside,0<p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀(α : Type) [Fintype α](μ : FinitePrior α),
      ∀R : FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α → ReferenceFamily C outside l,
      ∀mask : FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        (Block p → CommonSample C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop,
      (∑f,∑g,‖μ.cmean (fun a=>principalBErrorSum (R f g a) corrected mixed (mask f g a))‖) ≤
        Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [selected_principal_B_error_eventually d Bs BD Bz hBs hk,
    frequency_error_eventually Bs BD Bz (by omega : 0<k)] with L he hf
  intro E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl outside hpos hlen hlog
    α _ μ R mask
  have hl' : l≤k := by
    cases corrected with
    | false => exact hl
    | true => exact Nat.le_of_lt hl
  apply hf l hl'
  intro f g
  apply GiantCollisionError.norm_cmean_le_of_mass_ne_zero
  intro a _
  exact he E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl
    outside hpos hlen hlog (R f g a) (mask f g a)

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
