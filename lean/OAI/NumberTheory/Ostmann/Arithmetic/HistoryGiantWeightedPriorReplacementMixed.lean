import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementGrid
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
open Construction Construction.SourcePriorGridDeletion HistoryGiantPriorGrid
open PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open HistoryPairSmoothXi HistorySymbolicEncoding
open scoped BigOperators

theorem exists_periodicSourceMixedMean_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
    ∀ (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
      (M : ℕ) [NeZero M] (R : ZMod M × ZMod M → ℂ)
      (_hsize : (M : ℝ) < Real.exp (G-1)) (ηI : ℝ) (η : Unit → ℝ),
      0 ≤ G → L₀ ≤ G-1 → 0 < ηI → (∀ i, 0 < η i ∧ η i ≤ 1) →
      (M : ℝ) ≤ Real.exp (d*(G-1)^(1/3:ℝ)) →
    ∀ ε B error : ℝ, 0 ≤ ε → 1 ≤ B → 0 ≤ error →
      (∀ (j : MixedGridIndex (G-1) (G+1) ηI (fun _ : Unit => G-1) (fun _ => G+1) η) i,
        (K/logCellMass G E)*Real.exp (-d*(boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i)^(1/3:ℝ))+
          (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i))⁻¹ ≤ ε) →
      (∀ (j : MixedGridIndex (G-1) (G+1) ηI (fun _ : Unit => G-1) (fun _ => G+1) η) i,
        |harmonicIntegral M (boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i)
            (boxUpper (fun _ => G-1) (fun _ => G+1) η j.2 i)/logCellMass G E|+
          ((K/logCellMass G E)*Real.exp (-d*(boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i)^(1/3:ℝ))+
            (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i))⁻¹) ≤ B) →
      (∀ j : MixedGridIndex (G-1) (G+1) ηI (fun _ : Unit => G-1) (fun _ => G+1) η,
        mixedGridError (ι:=Unit) M (G-1) (G+1) ηI G 1 partitionDerivativeConstant
          smoothPartition ε B j.1 ≤ error) →
    ∀ (f : (Option Unit → ℝ) → ℂ) (D mesh A H : ℝ), 0 ≤ D → 0 ≤ mesh → 0 ≤ H →
      ηI ≤ mesh → (∀ i, η i ≤ mesh) →
      (∀ z∈logRectangle (Option.elim' (G-1) (fun _ : Unit => G-1))
          (Option.elim' (G+1) (fun _ => G+1)),
        DifferentiableAt ℝ (fun y => mixedGiantPrimeTest G f (fun i => Real.exp (y i))) z) →
      (∀ z∈logRectangle (Option.elim' (G-1) (fun _ : Unit => G-1))
          (Option.elim' (G+1) (fun _ => G+1)), ∀ i,
        ‖deriv (fun t => mixedGiantPrimeTest G f
          (Characters.RationalHistory.Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤ D) →
      (∀ z∈logRectangle (Option.elim' (G-1) (fun _ : Unit => G-1))
          (Option.elim' (G+1) (fun _ => G+1)),
        ‖mixedGiantPrimeTest G f (fun i => Real.exp (z i))‖ ≤ A) →
      (∀ n∈integerPivotCell G, externalPivotWeight G n ≠ 0 →
        ∀ p∈logCellPrimes G, logCellWeight G p ≠ 0 →
        ‖R (n,p) *
          f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ)))‖ ≤ H) →
      ‖periodicSourceMixedMean G E hZ M R f -
        mixedPrincipalIntegral M (G-1) (G+1) G smoothPartition
          (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G E) (mixedGiantPrimeTest G f) *
          ∑ r : ZMod M, ∑ u : Unit → (ZMod M)ˣ, mixedTest R r u‖ ≤
      (Real.exp 1+1)*deletionCap G E*H +
        (2*(2*D*mesh)*mixedPrincipalMass M (G-1) (G+1) G smoothPartition
          (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G E) +
          (2*D*mesh+A)*(Fintype.card (MixedGridIndex (G-1) (G+1) ηI
            (fun _ : Unit => G-1) (fun _ => G+1) η)*error)) *
          ∑ r : ZMod M, ∑ u : Unit → (ZMod M)ˣ, ‖mixedTest R r u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hgrid⟩ := exists_mixed_grid_smooth_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro G E hZ M _ R hsize ηI η hG hlo hηI hη hM ε B error
    hε hB herror hE hmass herr f D mesh A H hD hmesh hH hwidthI hwidth hf hderiv hA hbound
  have hcell (i : Unit) : L₀ ≤ G-1 ∧ G-1 ≤ G+1 ∧ 0<η i ∧ η i≤1 ∧
      ⌊Real.exp (G+1)⌋₊ ≤ giantPrimeCutoff G ∧ 0<logCellMass G E ∧
      (M:ℝ) ≤ Real.exp (d*(G-1)^(1/3:ℝ)) :=
    ⟨hlo,by linarith,(hη i).1,(hη i).2,Nat.floor_le_ceil _,hZ,hM⟩
  have hφ : ∀t,HasDerivAt smoothPartition (deriv smoothPartition t) t :=
    fun t => (smoothPartition_contDiff.differentiable (by simp) t).hasDerivAt
  have hp := hgrid Unit (giantPrimeCutoff G) (fun _ => giantPrimeCutoff G) M
    (G-1) (G+1) ηI G 1 partitionDerivativeConstant smoothPartition (deriv smoothPartition)
    (fun _ => G-1) (fun _ => G+1) η (fun _ => logCellMass G E) (by linarith) hηI
    (Nat.floor_le_ceil _) hφ (smoothPartition_contDiff.continuous_deriv (by simp))
    (fun t _ => smoothPartition_nonneg _) (fun t _ => by
      rw [abs_of_nonneg (smoothPartition_nonneg _)]; exact smoothPartition_le_one _)
    (fun t _ => partition_deriv_le_constant _) hcell ε B error hε hB herror hE hmass herr
    (mixedTest R) (mixedGiantPrimeTest G f) D mesh A
    hD hmesh hwidthI hwidth hf hderiv hA
  have hdelete := integer_prime_grid_deletion_le_uniform G hG E hZ
    (fun n p => R (n,p) *
      f (Option.elim' (n:ℝ) (fun _ : Unit => (p:ℝ)))) hH hbound
  rw [integer_prime_gridMean_periodicTest_eq_mixedSmoothTestSum G E M R hsize f] at hdelete
  rw [norm_sub_rev] at hdelete
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hdelete hp).trans_eq (by simp only [Fintype.card_unique,Nat.cast_one,one_add_one_eq_two]))

end Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement

end

end OAI
