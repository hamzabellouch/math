import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExprDeriv
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellFreezing

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellFreezing
open Characters.RationalHistory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coordinate_deriv_eq (F : (ι → ℝ) → ℂ) (y : ι → ℝ) (i : ι)
    (hF : DifferentiableAt ℝ F y) :
    deriv (fun t : ℝ => F (y+t • (Pi.single i (1:ℝ) : ι → ℝ))) 0 =
      fderiv ℝ F y ((Pi.single i (1:ℝ) : ι → ℝ)) := by
  have hcurve := ((hasDerivAt_id (0:ℝ)).smul_const
    (Pi.single i (1:ℝ) : ι → ℝ)).const_add y
  simp only [one_smul] at hcurve
  have hh : HasFDerivAt F (fderiv ℝ F y) (y+(0:ℝ) • (Pi.single i (1:ℝ) : ι → ℝ)) := by
    simpa using hF.hasFDerivAt
  simpa only [Function.comp_def, id_eq] using (hh.comp_hasDerivAt 0 hcurve).deriv

omit [Fintype ι] in
theorem logCurve_eq_exp_coordinate (y : ι → ℝ) (i : ι) (t : ℝ) :
    Expr.logCurve (fun j => Real.exp (y j)) i t =
      (fun j => Real.exp ((y+t • (Pi.single i (1:ℝ) : ι → ℝ)) j)) := by
  funext j
  simp only [Expr.logCurve,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  by_cases hj : j=i
  · subst j
    simp [Real.exp_add]
  · simp [hj]

theorem logCurve_deriv_eq_fderiv (f : (ι → ℝ) → ℂ) (y : ι → ℝ) (i : ι)
    (hf : DifferentiableAt ℝ (fun z => f (fun j => Real.exp (z j))) y) :
    deriv (fun t : ℝ => f (Expr.logCurve (fun j => Real.exp (y j)) i t)) 0 =
      fderiv ℝ (fun z => f (fun j => Real.exp (z j))) y ((Pi.single i (1:ℝ) : ι → ℝ)) := by
  simp_rw [logCurve_eq_exp_coordinate]
  exact coordinate_deriv_eq _ y i hf

theorem positive_norm_sub_le (f : (ι → ℝ) → ℂ) (lo hi : ι → ℝ)
    {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hf : ∀ z ∈ logRectangle lo hi,
      DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z ∈ logRectangle lo hi, ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    {x y : ι → ℝ} (hx : x ∈ logRectangle lo hi) (hy : y ∈ logRectangle lo hi)
    (hxy : ∀ i,|x i-y i| ≤ mesh) :
    ‖f (fun j => Real.exp (x j))-f (fun j => Real.exp (y j))‖ ≤
      (Fintype.card ι:ℝ)*D*mesh := by
  apply norm_sub_le_of_partials _ lo hi hD hm hf _ hx hy hxy
  intro z hz i
  rw [← logCurve_deriv_eq_fderiv f z i (hf z hz)]
  exact hd z hz i

theorem positive_weighted_freezing_bound {A : Type*} (s : Finset A) (c : A → ℂ)
    (f : (ι → ℝ) → ℂ) (lo hi : ι → ℝ) (x y : A → ι → ℝ)
    {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hf : ∀ z ∈ logRectangle lo hi,
      DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z ∈ logRectangle lo hi, ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    (hx : ∀ a ∈ s,x a ∈ logRectangle lo hi) (hy : ∀ a ∈ s,y a ∈ logRectangle lo hi)
    (hxy : ∀ a ∈ s,∀ i,|x a i-y a i| ≤ mesh) :
    ‖(∑ a ∈ s,c a*f (fun j => Real.exp (x a j)))-
      (∑ a ∈ s,c a*f (fun j => Real.exp (y a j)))‖ ≤
      (Fintype.card ι:ℝ)*D*mesh*∑ a ∈ s,‖c a‖ := by
  apply weighted_freezing_bound s c _ lo hi x y hD hm hf _ hx hy hxy
  intro z hz i
  rw [← logCurve_deriv_eq_fderiv f z i (hf z hz)]
  exact hd z hz i

end Ostmann.Arithmetic.PrimeCellFreezing

end

end OAI
