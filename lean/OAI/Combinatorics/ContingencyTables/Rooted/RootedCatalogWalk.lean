import OAI.Combinatorics.ContingencyTables.Rooted.RootedCatalogStep

namespace OAI

/-! # Mixing of the executed catalog-order oracle walk -/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion ResidualMixture FirstSuccess
open CompanionOracleDensity (rationalHeight oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

theorem walkLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a≤rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) (N : ℕ) :
    FirstSuccess.walkLaw (bitStepLaw A C a z) v N=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK (gridEquiv A K v) N) := by
  induction N with
  | zero =>
    apply RationalLaw.ext
    funext w
    simp only [RootedOracleDensity.oracleWalkLaw,FirstSuccess.walkLaw,equivLaw,pointLaw,
      Equiv.symm_symm,Equiv.apply_eq_iff_eq]
  | succ N ih =>
    have hm (b : Grid (I := Fin (freeCount A)) K) :
        (FirstSuccess.walkLaw (bitStepLaw A C a z) v N).mass b=
          (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK
            (gridEquiv A K v) N).mass (gridEquiv A K b) :=
      congrArg (fun p => p.mass b) ih
    have hk (b w : Grid (I := Fin (freeCount A)) K) :
        (bitStepLaw A C a z b).mass w=
          (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK
            (gridEquiv A K b)).mass (gridEquiv A K w) :=
      congrArg (fun p => p.mass w) (bitStepLaw_eq A C a hC haH z hz hK hKB b)
    apply RationalLaw.ext
    funext w
    change (∑ b,(FirstSuccess.walkLaw (bitStepLaw A C a z) v N).mass b*
        (bitStepLaw A C a z b).mass w)=
      ∑ b,(RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK
        (gridEquiv A K v) N).mass b*
        (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK b).mass
          (gridEquiv A K w)
    simp_rw [hm,hk]
    exact Fintype.sum_equiv (gridEquiv A K) _ _ (fun _ => rfl)

theorem wordWalkLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a≤rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) (N : ℕ) :
    FirstSuccess.wordWalkLaw (bitStep A C a z) v N=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK (gridEquiv A K v) N) := by
  rw [FirstSuccess.wordWalkLaw_eq]
  exact walkLaw_eq A C a hC haH z hz hK hKB v N

/-- The original quantitative mixing estimate holds for the actual
catalog-order word walk, with the identical number of steps. -/
theorem wordWalkLaw_variation (A : Instance (Fin m) (Fin n)) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a≤rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1≤K) (hQ : 0 < Q) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (CompanionOracleDensity.dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger
      (Grid (I := Fin (CompanionOracleDensity.dimension A)) K))
    (v : Grid (I := Fin (freeCount A)) K) :
    (variation (FirstSuccess.wordWalkLaw (bitStep A C a z) v (oracleTime A C K Q theta))
      (equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleStationaryLaw A (rowColumn A.T) C a z hK)):ℝ)≤theta/(8*Q) := by
  rw [wordWalkLaw_eq A C a hC haH z hz hK hKB,variation_equiv]
  apply RootedOracleDensity.oracleWalkLaw_variation A (rowColumn A.T) C a theta
    hC _ htheta z hz K Q hK hQ hKB hPL hCheeger (gridEquiv A K v)
  rw [←CompanionOracleDensity.rationalHeight_cast]
  exact_mod_cast haH

end
end ContingencyTables.RootedCatalogGrid

end OAI
