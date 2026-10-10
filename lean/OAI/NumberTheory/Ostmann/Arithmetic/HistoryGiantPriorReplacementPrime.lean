import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridResiduesPrime
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellGridReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction Construction.SourcePriorGridDeletion HistorySignedResidues
open PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open scoped BigOperators

def sourcePrimeMean {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (G : ℝ) (E : Finset ℕ)
    (hZ : 0 < logCellMass G E) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (f : (Bool → ℝ) → ℂ) : ℂ :=
  (logCellPrimeSource G E hZ).law.cmean (fun p =>
    (logCellPrimeSource G E hZ).law.cmean (fun q =>
      liftedResidueTest g V outside h k M hd ((p : ℕ), (q : ℕ)) *
        f (fun t => if t then ((q : ℕ) : ℝ) else ((p : ℕ) : ℝ))))

theorem exists_sourcePrimeMean_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
    ∀ (l : ℕ) (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
      (h k : History l) (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
      (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
      (_hsize : (M : ℝ) < Real.exp (G-1)) (η : Bool → ℝ),
      L₀ ≤ G-1 → (∀ i, 0 < η i ∧ η i ≤ 1) →
      (M : ℝ) ≤ Real.exp (d*(G-1)^(1/3:ℝ)) →
    ∀ ε B : ℝ, 0 ≤ ε → 1 ≤ B →
      (∀ (j : GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1) η) i,
        (K/logCellMass G E)*Real.exp (-d*(boxLower (fun _ => G-1) (fun _ => G+1) η j i)^(1/3:ℝ))+
          (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j i))⁻¹ ≤ ε) →
      (∀ (j : GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1) η) i,
        |harmonicIntegral M (boxLower (fun _ => G-1) (fun _ => G+1) η j i)
            (boxUpper (fun _ => G-1) (fun _ => G+1) η j i)/logCellMass G E|+
          ((K/logCellMass G E)*Real.exp (-d*(boxLower (fun _ => G-1) (fun _ => G+1) η j i)^(1/3:ℝ))+
            (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j i))⁻¹) ≤ B) →
    ∀ (f : (Bool → ℝ) → ℂ) (D mesh A H : ℝ), 0 ≤ D → 0 ≤ mesh → 0 ≤ H →
      (∀ i, η i ≤ mesh) →
      (∀ z∈logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
        DifferentiableAt ℝ (fun y => primeCutoff G f (fun i => Real.exp (y i))) z) →
      (∀ z∈logRectangle (fun _ : Bool => G-1) (fun _ => G+1), ∀ i,
        ‖deriv (fun t => primeCutoff G f
          (Characters.RationalHistory.Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤ D) →
      (∀ z∈logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
        ‖primeCutoff G f (fun i => Real.exp (z i))‖ ≤ A) →
      (∀ p∈logCellPrimes G, logCellWeight G p ≠ 0 →
        ∀ q∈logCellPrimes G, logCellWeight G q ≠ 0 →
        ‖liftedResidueTest g V outside h k M hd (p,q) *
          f (fun t => if t then (q : ℝ) else (p : ℝ))‖ ≤ H) →
      ‖sourcePrimeMean g V outside h k G E hZ M hd f -
        principalIntegral M (fun _ : Bool => G-1) (fun _ => G+1)
          (fun _ => logCellMass G E) (primeCutoff G f) *
          ∑ u : Bool → (ZMod M)ˣ, primeResidueTest g V outside h k M hd u‖ ≤
      deletionCap G E*(1+fullMassRatio G E)*H +
        (2*(2*D*mesh)*principalMass M (fun _ : Bool => G-1) (fun _ => G+1)
          (fun _ => logCellMass G E) +
          (2*D*mesh+A)*(Fintype.card (GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1) η)*
            (2*ε*B^2))) * ∑ u : Bool → (ZMod M)ˣ, ‖primeResidueTest g V outside h k M hd u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hgrid⟩ := exists_grid_smooth_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro l g V outside h k G E hZ M _ hmod hsize η hlo hη hM ε B hε hB hE hmass
    f D mesh A H hD hmesh hH hwidth hf hderiv hA hbound
  have hcell (i : Bool) : L₀ ≤ G-1 ∧ G-1 ≤ G+1 ∧ 0<η i ∧ η i≤1 ∧
      ⌊Real.exp (G+1)⌋₊ ≤ giantPrimeCutoff G ∧ 0<logCellMass G E ∧
      (M:ℝ) ≤ Real.exp (d*(G-1)^(1/3:ℝ)) :=
    ⟨hlo,by linarith,(hη i).1,(hη i).2,Nat.floor_le_ceil _,hZ,hM⟩
  have hp := hgrid Bool (fun _ => giantPrimeCutoff G) M
    (fun _ => G-1) (fun _ => G+1) η (fun _ => logCellMass G E) hcell
    ε B hε hB hE hmass (primeResidueTest g V outside h k M hmod)
    (primeCutoff G f) D mesh A hD hmesh hwidth hf hderiv hA
  have hdelete := pair_grid_sub_source_cmean_le G E hZ
    (fun p q => liftedResidueTest g V outside h k M hmod (p,q) *
      f (fun t => if t then (q:ℝ) else (p:ℝ))) hH hbound
  rw [gridMean_pair_liftedResidueTest_eq_smoothJointTestSum g V outside h k G E M hmod hsize f] at hdelete
  rw [norm_sub_rev] at hdelete
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hdelete hp).trans_eq (by
    simp only [Fintype.card_bool,Nat.cast_ofNat]))

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
