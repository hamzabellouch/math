import OAI.NumberTheory.Ostmann.QuadraticCenter.RootSplitPrimeMassParameters
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootSplitPrimeMassSquare

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem exists_eventually_rootSplitPrimeMass_lower :
    ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax≤1/1000 ∧
      ∀ᶠ X : ℝ in atTop, ∀ eta : ℝ, 0≤eta → eta≤etaMax →
        ∀ n : ℤ, n≠0 → ∀ m : ℕ, 0 < m → (m:ℝ)≤X^eta →
          |(n:ℝ)|≤X^(2*eta) →
          (3/100:ℝ)*Real.log X≤rootSplitPrimeMass n m (X^(1/2-5*eta:ℝ)) := by
  obtain ⟨etaMax,hetaPos,hetaSmall,hmain⟩ :=
    Dirichlet.exists_eventually_splitPrimeMass_manuscript_lower
  refine ⟨etaMax,hetaPos,hetaSmall,?_⟩
  filter_upwards [hmain 4,eventually_square_rootSplitPrimeMass_lower,
    eventually_ge_atTop (4:ℝ)] with X hnonsquare hsquare hX
  intro eta heta0 heta n hn m hm hmX hnX
  have hsmall := heta.trans hetaSmall
  obtain ⟨hq,hM,hqM,hqlog,hMlog⟩ :=
    rootSplitPrimeMass_modulus_bounds hX hsmall hn hm hmX hnX
  by_cases hs : IsSquare n
  · exact hsquare eta heta0 hsmall n hs m hM hMlog
  · let : NeZero (4*n.natAbs) := ⟨by omega⟩
    rw [rootSplitPrimeMass_eq_character n hn]
    exact hnonsquare eta heta0 heta (4*n.natAbs)
      (Arithmetic.signedRightJacobiCharacter n hn)
      (Arithmetic.signedRightJacobiCharacter_ne_one n hn hs)
      (Arithmetic.signedRightJacobiCharacter_isQuadratic n hn)
      hqlog (4*m*n.natAbs) hM hqM hMlog

theorem exists_eventually_root_split_prime_sum_lower :
    ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax≤1/1000 ∧
      ∀ᶠ X : ℝ in atTop, ∀ eta : ℝ, 0≤eta → eta≤etaMax →
        ∀ n : ℤ, n≠0 → ∀ m : ℕ, 0 < m → (m:ℝ)≤X^eta →
          |(n:ℝ)|≤X^(2*eta) →
          (3/100:ℝ)*Real.log X≤
            ∑ p ∈ (⌊X^(1/2-5*eta:ℝ)⌋₊).primesLE.filter
              (fun p=>¬p∣4*m*n.natAbs ∧ jacobiSym n p=1),Real.log p/(p:ℝ) :=
  exists_eventually_rootSplitPrimeMass_lower

end Ostmann.QuadraticCenter

end

end OAI
