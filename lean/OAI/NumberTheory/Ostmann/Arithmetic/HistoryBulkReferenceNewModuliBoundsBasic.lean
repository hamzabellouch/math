import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModulusBoundCost
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantIndependentModulusBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceNewModuli
open Construction Conclusion Filter HistoryCRTIntegration HistorySignedResidues HistoryPairBulkTransport

theorem newComparisonModulus_le {N l : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (newh oldh oldk : History l) (hr : (rootModulus newh:ℝ) ≤ B^N)
    (hh : factorBound N B oldh) (hg : factorBound N B oldk)
    (outside : List ℕ) (hlen : outside.length ≤ N) (hout : ∀ q∈outside,(q:ℝ) ≤ B)
    (K : ℕ) :
    (newComparisonModulus newh oldh oldk outside K:ℝ) ≤
      B^(crtCostCoefficient l (K+2)*(N+1)) := by
  have ho := outsideModulus_le hB outside hlen hout
  have hf := frequencyModulus_le hB oldh oldk hh hg (K+2)
  have hp := representativeModulus_le hB oldh oldk hh hg
  have hc : N+N+2*2^(l+1)*(K+2)+2*(divisorCost oldh+divisorCost oldk) ≤
      crtCostCoefficient l (K+2)*(N+1) := by
    have hd := Nat.add_le_add (divisorCost_le oldh hh) (divisorCost_le oldk hg)
    have hextra : 0 ≤ (2*2^(l+1)*(K+2))*N := Nat.zero_le _
    unfold crtCostCoefficient
    nlinarith
  calc
    _ ≤ B^N*B^N*B^(2*2^(l+1)*(K+2))*B^(2*(divisorCost oldh+divisorCost oldk)) := by
      change ((rootModulus newh * outsideModulus outside * frequencyModulus oldh oldk (K+2) *
        representativeModulus oldh oldk:ℕ):ℝ) ≤ _
      push_cast
      gcongr
    _ = B^(N+N+2*2^(l+1)*(K+2)+2*(divisorCost oldh+divisorCost oldk)) := by
      simp only [pow_add]
    _ ≤ _ := pow_le_pow_right₀ hB hc

theorem actual_newComparisonModulus_log_le_eventually (Bs BD Bz : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ (newh oldh oldk : History l) (outside : List ℕ),
      (rootModulus newh:ℝ) ≤ (actualFactorCap Bs BD Bz k L)^(actualFactorCount k L) →
      factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L) oldh →
      factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L) oldk →
      outside.length ≤ actualFactorCount k L →
      (∀ q∈outside,(q:ℝ) ≤ actualFactorCap Bs BD Bz k L) →
      0 < newComparisonModulus newh oldh oldk outside k →
      Real.log (newComparisonModulus newh oldh oldk outside k:ℝ) ≤ Real.exp ((3/250:ℝ)*L) := by
  filter_upwards [actual_log_budget_eventually Bs BD Bz k (crtCostCoefficient k (k+2))
    (Nat.cast_nonneg _)] with L hbudget
  intro l hl newh oldh oldk outside hr hh hg hlen hout hpos
  have hB := actualFactorCap_one_le Bs BD Bz k L
  have hle := newComparisonModulus_le hB newh oldh oldk hr hh hg outside hlen hout k
  have hp : (0:ℝ) < newComparisonModulus newh oldh oldk outside k := by exact_mod_cast hpos
  have hlog := Real.log_le_log hp hle
  rw [Real.log_pow] at hlog
  have hcost : (crtCostCoefficient l (k+2):ℝ) ≤ crtCostCoefficient k (k+2) := by
    exact_mod_cast crtCostCoefficient_mono hl (le_refl (k+2))
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] at hlog
  exact hlog.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (by positivity)) (Real.log_nonneg hB)).trans hbudget)

theorem selected_assigned_rootModulus_le_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase → C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀ (x : SourceAssignment C.sources (Template.current seed l))
        (s : ℤ) (gp gm : ℕ) (c : HistoryChoices C.sources seed V l),
      (assignmentPrior C.sources _).mass x ≠ 0 →
      (rootModulus (assignedHistory C.sources seed V l s gp gm x c):ℝ) ≤
        (actualFactorCap Bs BD Bz k L)^(actualFactorCount k L) := by
  filter_upwards [selected_sources_factorCap_eventually d Bs BD Bz hk] with L hcap
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x s gp gm c hx
  rw [rootModulus_assignedHistory]
  have hB := actualFactorCap_one_le Bs BD Bz k L
  have hs := assignedSlots_source_mass_ne_zero C.sources _ x hx
  have hv : ∀ q∈assignedSlots C.sources _ x,(q.value:ℝ) ≤ actualFactorCap Bs BD Bz k L :=
    fun q hq => sourceMass_value_le (hcap E C hG hcl hcu hb hd) (hs q hq)
  have hp := smallProduct_intSize_le (by linarith : 0 ≤ actualFactorCap Bs BD Bz k L) _ hv
  have hp' := (abs_le.mp hp).2
  have hlen : (assignedSlots C.sources _ x).length ≤ actualFactorCount k L := by
    rw [assignedSlots_length]
    exact actual_current_length_le k L hl
  exact hp'.trans (pow_le_pow_right₀ hB hlen)

end Ostmann.Arithmetic.HistoryBulkReferenceNewModuli

end

end OAI
