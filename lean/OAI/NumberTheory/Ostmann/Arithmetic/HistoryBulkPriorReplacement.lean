import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellGridReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open scoped BigOperators

theorem exists_sourceBulkMean_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
      (L : ℝ) (E : Finset ℕ) (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E))
      (M : ℕ) [NeZero M] (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) (η : ι → ℝ),
      0 ≤ L → L₀ ≤ bulkLogLower L → (∀ i, 0 < η i ∧ η i ≤ 1) →
      (M : ℝ) ≤ Real.exp (d*(bulkLogLower L)^(1/3 : ℝ)) →
    ∀ ε B : ℝ, 0 ≤ ε → 1 ≤ B →
      (∀ (j : GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L) η) i,
        (K/bulkNormalizer L E)*Real.exp
            (-d*(boxLower (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η j i)^(1/3 : ℝ))+
          (bulkNormalizer L E*Real.exp
            (boxLower (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η j i))⁻¹ ≤ ε) →
      (∀ (j : GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L) η) i,
        |harmonicIntegral M
            (boxLower (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η j i)
            (boxUpper (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η j i)/bulkNormalizer L E|+
          ((K/bulkNormalizer L E)*Real.exp
            (-d*(boxLower (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η j i)^(1/3 : ℝ))+
            (bulkNormalizer L E*Real.exp
              (boxLower (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η j i))⁻¹) ≤ B) →
    ∀ (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) (D mesh A H : ℝ),
      0 ≤ D → 0 ≤ mesh → 0 ≤ H → (∀ i, η i ≤ mesh) →
      (∀ z∈logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
        DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i))) z) →
      (∀ z∈logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L), ∀ i,
        ‖deriv (fun t => f
          (Characters.RationalHistory.Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤ D) →
      (∀ z∈logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
        ‖f (fun i => Real.exp (z i))‖ ≤ A) →
      (∀ p : BulkPrimeTuple ι L,
        ‖F (bulkTupleUnits L M hsize p)*f (fun i => ((p i).val : ℝ))‖ ≤ H) →
      ‖sourceBulkMean L E hZ M hsize F f-
        principalIntegral M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
          (fun _ => bulkNormalizer L E) f * ∑ u : ι → (ZMod M)ˣ, F u‖ ≤
      (bulkFullMassRatio L E^Fintype.card ι-1)*H+
        (2*((Fintype.card ι : ℝ)*D*mesh)*principalMass M
            (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L) (fun _ => bulkNormalizer L E)+
          ((Fintype.card ι : ℝ)*D*mesh+A)*
            (Fintype.card (GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L) η)*
              (Fintype.card ι*ε*B^Fintype.card ι))) * ∑ u : ι → (ZMod M)ˣ, ‖F u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hgrid⟩ := exists_grid_smooth_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro ι _ _ L E hZ M _ hsize η hL hlo hη hM ε B hε hB hεcell hmass
    F f D mesh A H hD hmesh hH hwidth hf hderiv hA hbound
  have horder : bulkLogLower L ≤ bulkLogUpper L := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcell (i : ι) : L₀ ≤ bulkLogLower L ∧ bulkLogLower L ≤ bulkLogUpper L ∧
      0 < η i ∧ η i ≤ 1 ∧ ⌊Real.exp (bulkLogUpper L)⌋₊ ≤ bulkPrimeCutoff L ∧
      0 < bulkNormalizer L E ∧ (M : ℝ) ≤ Real.exp (d*(bulkLogLower L)^(1/3 : ℝ)) :=
    ⟨hlo,horder,(hη i).1,(hη i).2,Nat.floor_le_ceil _,hZ,hM⟩
  have hap := hgrid ι (fun _ => bulkPrimeCutoff L) M
    (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η (fun _ => bulkNormalizer L E)
    hcell ε B hε hB hεcell hmass F f D mesh A hD hmesh hwidth hf hderiv hA
  have hdelete := bulkGridMean_sub_source_cmean_le L E hZ
    (fun p : ι → ℕ => jointUnitTest F (fun i => (p i : ZMod M))*f (fun i => (p i : ℝ))) hH
    (fun p => by rw [jointUnitTest_bulkTuple L M hsize F p]; exact hbound p)
  rw [bulkGridMean_joint_eq_smoothJointTestSum, ← sourceBulkMean_eq_jointUnitTest L E hZ M hsize F f,
    norm_sub_rev] at hdelete
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hdelete hap)

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
