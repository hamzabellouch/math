import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundSize
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusCost

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion Filter

theorem pairedCostCoefficient_mono {l k : ℕ} (hl : l ≤ k) :
    pairedCostCoefficient l ≤ pairedCostCoefficient k := by
  have h₄ : 4^(l+1) ≤ (4^(k+1):ℕ) := Nat.pow_le_pow_right (by omega) (by omega)
  have h₈ : 8^(l+1) ≤ (8^(k+1):ℕ) := Nat.pow_le_pow_right (by omega) (by omega)
  have hleft := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hl) h₄
  have hright := Nat.mul_le_mul_left 2 h₈
  unfold pairedCostCoefficient
  omega

theorem actual_pairModulus_log_le_eventually (Bs BD Bz : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ (h g : History l) (outside : List ℕ),
      factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L) h →
      factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L) g →
      outside.length ≤ actualFactorCount k L →
      (∀ q ∈ outside, (q:ℝ) ≤ actualFactorCap Bs BD Bz k L) →
      0 < pairModulus h g outside →
      Real.log (pairModulus h g outside) ≤ Real.exp ((3/250:ℝ)*L) := by
  filter_upwards [actual_log_budget_eventually Bs BD Bz k (pairedCostCoefficient k)
    (Nat.cast_nonneg _)] with L hL
  intro l hl h g outside hh hg hlen hout hpos
  have hcost := (pairedCost_le h g hh hg outside hlen).trans
    (Nat.mul_le_mul_right (actualFactorCount k L+1) (pairedCostCoefficient_mono hl))
  have hcostReal : ((l*(divisorCost h+divisorCost g)+testCost h+testCost g+outside.length:ℕ):ℝ) ≤
      (pairedCostCoefficient k:ℝ)*((actualFactorCount k L:ℝ)+1) := by exact_mod_cast hcost
  have hmul := mul_le_mul_of_nonneg_right hcostReal
    (Real.log_nonneg (actualFactorCap_one_le Bs BD Bz k L))
  exact (log_pairModulus_le (actualFactorCap_one_le Bs BD Bz k L) h g hh hg outside hout hpos).trans
    (by simpa only [Nat.cast_add, Nat.cast_mul] using hmul.trans hL)

theorem selected_pairModulus_log_le_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
        0 < pairModulus h g outside ∧
          Real.log (pairModulus h g outside) ≤ Real.exp ((3/250:ℝ)*L) := by
  filter_upwards [selected_decoded_pair_factorBound_eventually d Bs BD Bz hk,
    actual_pairModulus_log_le_eventually Bs BD Bz k, eventually_ge_atTop (0:ℝ)] with L hbound hlog hL
  intro E C hG hcl hcu hb hd spectator hspec outside hout hlen l hl
  dsimp only
  intro x y s t c e hx hy hc he hs gs
  have hh := hbound E C hG hcl hcu hb hd l hl x y s t c e outside hx hy hc he hs gs
  have hp := pairModulus_pos _ _ hs gs (fun q hq => (spectator.prime q (hout q hq)).pos)
  refine ⟨hp, hlog l hl _ _ outside hh.1 hh.2 hlen ?_ hp⟩
  intro q hq
  exact spectator_le_actualFactorCap Bs BD Bz k hL (spectator.prime q (hout q hq)).pos
    (hspec ⟨q,hout q hq⟩)

theorem selected_spectator_pairModulus_log_le_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
        0 < pairModulus h g outside ∧
          Real.log (pairModulus h g outside) ≤ Real.exp ((3/250:ℝ)*L) := by
  filter_upwards [selected_pairModulus_log_le_eventually d Bs BD Bz hk] with L hL
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
