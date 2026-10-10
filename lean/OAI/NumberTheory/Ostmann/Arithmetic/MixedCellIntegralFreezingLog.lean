import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellIntegralFreezing

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.MixedCellIntegralFreezing
open MeasureTheory PrimeCellFreezing Characters.RationalHistory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def optionCoordinates (t : ℝ × (ι → ℝ)) : Option ι → ℝ := Option.elim' t.1 t.2

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_optionCoordinates : Continuous (optionCoordinates (ι := ι)) := by
  apply continuous_pi
  intro i
  cases i with
  | none => exact continuous_fst
  | some i => exact (continuous_apply i).comp continuous_snd

omit [Fintype ι] [DecidableEq ι] in
theorem optionCoordinates_mem_logRectangle (loI hiI : ℝ) (lo hi : ι → ℝ)
    {t : ℝ × (ι → ℝ)} :
    optionCoordinates t ∈ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi) ↔
      t ∈ mixedLogRectangle loI hiI lo hi := by
  constructor
  · intro h
    exact ⟨h none (Set.mem_univ _), fun i _ => h (some i) (Set.mem_univ _)⟩
  · intro h i _
    cases i with
    | none => exact h.1
    | some i => exact h.2 i (Set.mem_univ i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem optionCoordinates_mixedExp (t : ℝ × (ι → ℝ)) :
    optionCoordinates (mixedExp t) = fun j => Real.exp (optionCoordinates t j) := by
  funext j
  cases j <;> rfl

theorem mixed_integral_freezing_of_log_partials
    (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ) (w lo hi : ι → ℝ)
    (hφ : Continuous φ) (hφ0 : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 0 < lo i)
    (f : (Option ι → ℝ) → ℂ) {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidthI : hiI-loI ≤ mesh) (hwidth : ∀ i, hi i-lo i ≤ mesh)
    (hf : ∀ z ∈ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),
      DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z ∈ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi), ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    {base : ℝ × (ι → ℝ)} (hbase : base ∈ mixedLogRectangle loI hiI lo hi) :
    ‖mixedLogIntegral M loI hiI G φ w lo hi (fun x => f (optionCoordinates x)) -
      mixedLogMass M loI hiI G φ w lo hi • f (optionCoordinates (mixedExp base))‖ ≤
      ((Fintype.card ι : ℝ)+1)*D*mesh * mixedLogMass M loI hiI G φ w lo hi := by
  have hF : ContinuousOn (fun z => f (optionCoordinates (mixedExp z)))
      (mixedLogRectangle loI hiI lo hi) := by
    intro z hz
    have hh := (hf (optionCoordinates z)
      ((optionCoordinates_mem_logRectangle loI hiI lo hi).mpr hz)).continuousAt.comp
        continuous_optionCoordinates.continuousAt
    simpa only [Function.comp_def, optionCoordinates_mixedExp] using hh.continuousWithinAt
      (s := mixedLogRectangle loI hiI lo hi)
  apply mixed_freezing_of_variation M loI hiI G φ w lo hi hφ hφ0 hw hlo
    (fun z => f (optionCoordinates (mixedExp z))) hF base
  intro z hz
  have hwidth' : ∀ i : Option ι,
      Option.elim' hiI hi i - Option.elim' loI lo i ≤ mesh := by
    intro i
    cases i with
    | none => exact hwidthI
    | some i => exact hwidth i
  have hz' := (optionCoordinates_mem_logRectangle loI hiI lo hi).mpr hz
  have hb' := (optionCoordinates_mem_logRectangle loI hiI lo hi).mpr hbase
  have h := positive_norm_sub_le f (Option.elim' loI lo) (Option.elim' hiI hi)
    hD hm hf hd hz' hb'
    (logRectangle_coordinate_dist_le _ _ hwidth' hz' hb')
  simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one, optionCoordinates_mixedExp] using h

theorem residue_mixed_integral_freezing_of_log_partials
    (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ) (Z lo hi : ι → ℝ)
    (hφ : Continuous φ) (hφ0 : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hZ : ∀ i, 0 < Z i) (hlo : ∀ i, 0 < lo i)
    (hI : loI ≤ hiI) (horder : ∀ i, lo i ≤ hi i)
    (f : (Option ι → ℝ) → ℂ) {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidthI : hiI-loI ≤ mesh) (hwidth : ∀ i, hi i-lo i ≤ mesh)
    (hf : ∀ z ∈ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),
      DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z ∈ logRectangle (Option.elim' loI lo) (Option.elim' hiI hi), ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    {base : ℝ × (ι → ℝ)} (hbase : base ∈ mixedLogRectangle loI hiI lo hi) :
    ‖mixedLogIntegral M loI hiI G φ (fun i => ((Nat.totient M : ℝ)*Z i)⁻¹) lo hi
        (fun x => f (optionCoordinates x)) -
      (IntegerCell.integerDensityMass M loI hiI G φ *
        ∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i)/Z i) •
          f (optionCoordinates (mixedExp base))‖ ≤
      ((Fintype.card ι : ℝ)+1)*D*mesh * (IntegerCell.integerDensityMass M loI hiI G φ *
        ∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i)/Z i) := by
  rw [← residue_mixedLogMass_eq M loI hiI G φ Z lo hi hI horder]
  exact mixed_integral_freezing_of_log_partials M loI hiI G φ _ lo hi hφ hφ0
    (fun i => inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hZ i).le))
    hlo f hD hm hwidthI hwidth hf hd hbase

end Ostmann.Arithmetic.MixedCellIntegralFreezing

end

end OAI
