import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBoundsFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryPairSmoothXi HistoryProductWindows HistoryCRTIntegration
open HistorySymbolicEncoding HistorySelectedPairDerivativeBounds HistorySelectedPairDerivativeCounts
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition
open HistoryGiantGridCellBounds HistoryGiantReplacementError HistorySignedResidues
open HistoryGiantPrincipalMassBounds HistoryGiantPriorExceptionalError SourcePriorGridDeletion
open PrimeCellReplacement Filter
open scoped BigOperators

theorem eventually_actual_error_bounds (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) {k₀ : ℕ} (hk₀ : 0 < k₀) {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      ∀ l ≤ k₀, ∀ (h k : History l),
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k →
      ∀ (outside : List ℕ), (∀ q ∈ outside, q.Prime) → ∀ (deleted : Finset ℕ), deleted.card ≤ 2 →
      ∀ (n : ℕ) [NeZero (comparisonModulus h k outside n)],
      Real.log (comparisonModulus h k outside n : ℝ) ≤ Real.exp (giant.μ*L) →
      Real.exp (giant.a₀*L) ≤ (C.giantCenter : ℝ)-1 → ∀ L₀ : ℝ,
      PrimeBounds k₀ δ K L₀ C.giantCenter L (comparisonModulus h k outside n) deleted →
      primeErrorUpper C h k outside deleted (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n) K δ ≤
          29*Real.exp (-Real.exp (giant.target*L)) ∧
      mixedErrorUpper C h k outside deleted (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n) K δ ≤
          8*Real.exp (-Real.exp (giant.target*L)) := by
  let c₀ := selectedExponent Bs BD Bz k₀
  have ht : Tendsto (fun L : ℝ => Real.exp (giant.a₁*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num [giant]))
  filter_upwards [eventually_giant_grid_errors k₀ (C:=c₀) hK hδ,
    eventually_variation_with_mass k₀ c₀ (by norm_num : (0:ℝ) ≤ 10),
    eventually_exceptional_errors k₀ c₀,
    (bulkSize_tendsto_atTop hk₀).eventually_ge_atTop (1:ℝ),
    ht.eventually_ge_atTop 2, eventually_ge_atTop (0:ℝ)]
    with L hgrid hvar hexc hbulk hlen hL
  intro E C l hl h k hh hk outside hout deleted hdeleted n _ hmod hlo L₀ hb
  let M := comparisonModulus h k outside n
  let G : ℝ := C.giantCenter
  let A := referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l
  let Dp := referenceDerivative C h k [false,true]
  let Dm := referenceDerivative C h k [true]
  let F := smoothGrowthFactor k₀ c₀ giant.μ L
  let J : ℝ := (meshIntervals giant L : ℝ)^2
  let a := 2+2^(l+1)
  let Q : ℝ := (M:ℝ)^a
  let r := Real.exp (-Real.exp (giant.target*L))
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne _)
  have ha : a ≤ residueCostExponent k₀ := by
    have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) (Nat.add_le_add_right hl 1)
    dsimp [a, residueCostExponent]
    omega
  have ha' : 2^(l+1) ≤ residueCostExponent k₀ := by dsimp [a] at ha; omega
  have hm : 1 ≤ bulkSize k₀ L := by exact_mod_cast hbulk
  have hEp := reference_envelopes C hBs hk₀ hm hl h k hh hk [false,true] (by simp)
  have hEm := reference_envelopes C hBs hk₀ hm hl h k hh hk [true] (by simp)
  have hDp : 0 ≤ Dp := referenceDerivative_nonneg C h k _
  have hDm : 0 ≤ Dm := referenceDerivative_nonneg C h k _
  have hA : 0 ≤ A := referenceAmplitude_nonneg Bs L k₀ l
  have hF : 0 ≤ F := Real.exp_nonneg _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hG : 2 ≤ G := by
    have hh₀ : 1 ≤ Real.exp (giant.a₀*L) := Real.one_le_exp
      (mul_nonneg (by norm_num [giant]) hL)
    dsimp [G]
    linarith
  have hmass := original_giant_principal_masses M hM (bulkSize k₀ L) G deleted
    hG hb.mass_pos hb.inverse_cost
  have hgrid' := hgrid G L₀ M deleted hM hmod hb a ha
  have hvarp := hvar a M
    (principalMass M (fun _ : Bool => G-1) (fun _ => G+1) (fun _ => logCellMass G deleted))
    ha hM hmod hmass.1.2
  have hvarm := hvar a M
    (mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G deleted))
    ha hM hmod hmass.2.2
  have ho : (outside.prod : ℝ) ≤ M := by
    exact_mod_cast outside_prod_le_comparisonModulus h k outside n hM
  have hHA : (outside.prod : ℝ)^(2^(l+1))*A ≤ (M:ℝ)^(2^(l+1))*F := by
    apply mul_le_mul (pow_le_pow_left₀ (by positivity) ho _) hEp.2 hA
    positivity
  have hex := (hexc G M hM hmod hlo deleted hdeleted).errors
    (2^(l+1)) ((outside.prod : ℝ)^(2^(l+1))*A) ha' (by positivity) hHA
  have hSp := sum_norm_actual_prime_comparison_le d (frequencyBound Bs BD Bz k₀ L) outside h k n hout
  have hSm := sum_norm_actual_mixed_comparison_le d (frequencyBound Bs BD Bz k₀ L) outside h k n hout
  constructor
  · exact primeErrorUpper_algebra C h k outside deleted M
      (pairModulus_dvd_comparisonModulus h k outside n) K δ F J Q r hF hJ hQ
      hmass.1.1 hb.error_nonneg hb.mesh_le_one hEp.1 hEp.2
      (prime_grid_card_le G L hlen) hSp hex.1 hvarp hgrid'.1
  · exact mixedErrorUpper_algebra C h k outside deleted M
      (pairModulus_dvd_comparisonModulus h k outside n) K δ F J Q r hF hJ hQ
      hmass.2.1 (giantMixedError_nonneg hb.error_nonneg) hb.mesh_le_one hEm.1 hEm.2
      (mixed_grid_card_le G L hlen) hSm hex.2.2.1 hvarm hgrid'.2

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
