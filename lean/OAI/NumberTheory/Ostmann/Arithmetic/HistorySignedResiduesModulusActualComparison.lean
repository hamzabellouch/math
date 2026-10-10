import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModulusBoundCost
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundComparison

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion Filter HistoryCRTIntegration

theorem actual_comparisonModulus_log_le_eventually (Bs BD Bz : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ (h g : History l) (outside : List ℕ),
      factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L) h →
      factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L) g →
      outside.length ≤ actualFactorCount k L →
      (∀ q ∈ outside, (q:ℝ) ≤ actualFactorCap Bs BD Bz k L) →
      0 < pairModulus h g outside → 0 < crtModulus h g outside (k+2) →
      Real.log (comparisonModulus h g outside (k+2)) ≤ Real.exp ((3/250:ℝ)*L) := by
  filter_upwards [actual_log_budget_eventually Bs BD Bz k
    (pairedCostCoefficient k + crtCostCoefficient k (k+2)) (by positivity)] with L hL
  intro l hl h g outside hh hg hlen hout hp hc
  have hB := actualFactorCap_one_le Bs BD Bz k L
  have hcrt : (crtModulus h g outside (k+2):ℝ) ≤
      (actualFactorCap Bs BD Bz k L)^(crtCostCoefficient l (k+2)*(actualFactorCount k L+1)) :=
    minimalCRT_le hB h g hh hg outside hlen hout (k+2)
  have hlog := comparisonModulus_log_le hB h g hh hg outside hlen hout (k+2) hp hc hcrt
  have hcost : pairedCostCoefficient l + crtCostCoefficient l (k+2) ≤
      pairedCostCoefficient k + crtCostCoefficient k (k+2) :=
    Nat.add_le_add (pairedCostCoefficient_mono hl) (crtCostCoefficient_mono hl le_rfl)
  have hcostReal : ((pairedCostCoefficient l + crtCostCoefficient l (k+2):ℕ):ℝ) ≤
      (pairedCostCoefficient k:ℝ) + (crtCostCoefficient k (k+2):ℝ) := by exact_mod_cast hcost
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcostReal (by positivity : 0 ≤ (actualFactorCount k L:ℝ)+1))
    (Real.log_nonneg hB)
  exact hlog.trans (hmul.trans hL)

lemma comparisonModulus_le_double_exp {l : ℕ} (h g : History l) (outside : List ℕ)
    (n : ℕ) (L : ℝ) (hpos : 0 < comparisonModulus h g outside n)
    (hlog : Real.log (comparisonModulus h g outside n) ≤ Real.exp ((3/250:ℝ)*L)) :
    (comparisonModulus h g outside n:ℝ) ≤ Real.exp (Real.exp ((3/250:ℝ)*L)) := by
  have hp : (0:ℝ) < comparisonModulus h g outside n := by exact_mod_cast hpos
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hlog

theorem selected_comparisonModulus_cap_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ outside : List ℕ, (∀ p ∈ outside, p ∈ spectator.candidates) →
      outside.length ≤ actualFactorCount k L →
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀ (x y : OuterSample C.sources (Template.current seed l) C.giant) (s t : ℤ)
        (c e : HistoryChoices C.sources seed V l),
        (outerPrior C.sources (Template.current seed l) C.giant).mass x ≠ 0 →
        (outerPrior C.sources (Template.current seed l) C.giant).mass y ≠ 0 →
        choicesMass C.sources seed V l c ≠ 0 → choicesMass C.sources seed V l e ≠ 0 →
        (decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant x s) c).Supported V outside →
        (decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant y t) e).Supported V outside →
        let h := decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant x s) c
        let g := decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant y t) e
        0 < comparisonModulus h g outside (k+2) ∧
          Real.log (comparisonModulus h g outside (k+2)) ≤ Real.exp ((3/250:ℝ)*L) ∧
          (comparisonModulus h g outside (k+2):ℝ) ≤ Real.exp (Real.exp ((3/250:ℝ)*L)) := by
  filter_upwards [selected_decoded_pair_factorBound_eventually d Bs BD Bz hk,
    actual_comparisonModulus_log_le_eventually Bs BD Bz k,
    eventually_ge_atTop (0:ℝ)] with L hbound hlog hL
  intro E C hG hcl hcu hb hd spectator hspec outside hout hlen l hl
  dsimp only
  intro x y s t c e hx hy hc he hs gs
  have hh := hbound E C hG hcl hcu hb hd l hl x y s t c e outside hx hy hc he hs gs
  have hprime : ∀ q ∈ outside, Nat.Prime q := fun q hq => spectator.prime q (hout q hq)
  have hp := pairModulus_pos _ _ hs gs (fun q hq => (hprime q hq).pos)
  have hcrt := crtModulus_pos _ _ hs gs hprime (k+2)
  have hcmp := comparisonModulus_pos _ _ hs gs hprime (k+2)
  have hcap := hlog l hl _ _ outside hh.1 hh.2 hlen
    (fun q hq => spectator_le_actualFactorCap Bs BD Bz k hL (hprime q hq).pos
      (hspec ⟨q,hout q hq⟩)) hp hcrt
  exact ⟨hcmp, hcap, comparisonModulus_le_double_exp _ _ outside (k+2) L hcmp hcap⟩

theorem selected_spectator_comparisonModulus_cap_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      let outside := spectatorList spectator ds
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀ (x y : OuterSample C.sources (Template.current seed l) C.giant) (s t : ℤ)
        (c e : HistoryChoices C.sources seed V l),
        (outerPrior C.sources (Template.current seed l) C.giant).mass x ≠ 0 →
        (outerPrior C.sources (Template.current seed l) C.giant).mass y ≠ 0 →
        choicesMass C.sources seed V l c ≠ 0 → choicesMass C.sources seed V l e ≠ 0 →
        (decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant x s) c).Supported V outside →
        (decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant y t) e).Supported V outside →
        let h := decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant x s) c
        let g := decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant y t) e
        0 < comparisonModulus h g outside (k+2) ∧
          Real.log (comparisonModulus h g outside (k+2)) ≤ Real.exp ((3/250:ℝ)*L) ∧
          (comparisonModulus h g outside (k+2):ℝ) ≤ Real.exp (Real.exp ((3/250:ℝ)*L)) := by
  filter_upwards [selected_comparisonModulus_cap_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd spectator hspec ds
  dsimp only
  apply hL E C hG hcl hcu hb hd spectator hspec (spectatorList spectator ds)
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact (ds i).property
  · exact initial_spectator_count_le k L spectator ds

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
