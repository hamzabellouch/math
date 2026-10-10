import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonOccupationBound

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma physical_exit_subset_path_norm {d : ℕ} (e f : Direction d)
    (x : Lattice d) (θ r n T A : ℝ) (hr : 0 < r) (hn : 0 < n) (hT : 0 < T) :
    PhysicalGapExit e f (A*r) (⌊T*n⌋₊+1) (x,x) ⊆
      {P | A/2 ≤ ‖recordLinearPath (realPosition (step e)) f θ r n T (fun j => P.1 j-x)‖} ∪
      {P | A/2 ≤ ‖recordLinearPath (realPosition (step e)) f θ r n T (fun j => P.2 j-x)‖} := by
  rintro P ⟨h,hh,hex⟩
  by_contra hno
  simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hno
  have hTn : 0 < T*n := mul_pos hT hn
  have hhh : (h:ℝ) ≤ T*n := (show (h:ℝ) ≤ (⌊T*n⌋₊:ℝ) by exact_mod_cast (Nat.le_of_lt_succ hh)).trans (Nat.floor_le hTn.le)
  let s : unitInterval := ⟨(h:ℝ)/(T*n),div_nonneg (Nat.cast_nonneg _) hTn.le,(div_le_one hTn).mpr hhh⟩
  have hs : T*n*(s:ℝ)=h := by dsimp [s]; field_simp
  let ℓ := realPosition (step e)
  let F := recordLinearPath ℓ f θ r n T (fun j => P.1 j-x)
  let G := recordLinearPath ℓ f θ r n T (fun j => P.2 j-x)
  have hF : |F s| < A/2 := (F.norm_coe_le_norm s).trans_lt hno.1
  have hG : |G s| < A/2 := (G.norm_coe_le_norm s).trans_lt hno.2
  have hFe : F s=(signedCoordinate f (recordIndexPosition ℓ h (fun j => P.1 j-x))-(h:ℝ)*θ)/r :=
    heightPolygon_grid _ r n T hTn.le h s hs
  have hGe : G s=(signedCoordinate f (recordIndexPosition ℓ h (fun j => P.2 j-x))-(h:ℝ)*θ)/r :=
    heightPolygon_grid _ r n T hTn.le h s hs
  have he : physicalFirstHitGap ℓ f x x h P=r*(F s-G s) := by
    rw [hFe,hGe]
    have hz : signedCoordinate f (x-x) = 0 := by simp [signedCoordinate]
    dsimp only [physicalFirstHitGap,firstHitPairGap]
    rw [hz]
    field_simp
    ring
  have hab : |F s-G s| < A := (abs_sub _ _).trans_lt (by linarith)
  rw [he,abs_mul,abs_of_pos hr] at hex
  nlinarith

theorem shared_physical_exit_gaussian {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x : ℕ → Lattice d) {T A : ℝ} (hT : 0 < T) (hA : 0 < A) :
    let ℓ := realPosition (step e)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    ∀ᶠ i in atTop, (sharedConditionedPairLaw ν ℓ (x i) (x i)).real
      (PhysicalGapExit e f (A*r i) (⌊T*n i⌋₊+1) (x i,x i)) ≤
        8*Real.exp (-commonMeanWidth ν ℓ*A^2/(4*T)) := by
  let ℓ := realPosition (step e)
  let m := commonMeanWidth ν ℓ
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (x i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ (x i) (x i)
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (x i)))
  let F := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) T (fun j => P.1 j-x i)
  let G := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) T (fun j => P.2 j-x i)
  have hFm (i : ℕ) : Measurable (F i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  have hGm (i : ℕ) : Measurable (G i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  have hm : 0 < m := zero_lt_one.trans_le (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e)
    (signedHeight_projection e) (signedHeight_step_le e))
  obtain ⟨W,hW,hlim⟩ := shared_path_marginal_limits ν hue e f hef htrans r hr hT.le
  have hV : 0 < T/(2*m) := by positivity
  have hF := distribution_path_norm_limsup μ F hFm W (hlim x x (fun _ => rfl)).1
    (T/(2*m)) hV hW (A/2) (by positivity)
  have hG := distribution_path_norm_limsup μ G hGm W (hlim x x (fun _ => rfl)).2
    (T/(2*m)) hV hW (A/2) (by positivity)
  have he : -(A/2)^2/(2*(T/(2*m))) = -m*A^2/(4*T) := by field_simp; ring
  rw [he] at hF hG
  let c := Real.exp (-m*A^2/(4*T))
  have hc : 0 < c := Real.exp_pos _
  have hFb : IsBoundedUnder (· ≤ ·) atTop (fun i => (μ i).real {P | A/2 ≤ ‖F i P‖}) :=
    ⟨1,show ∀ᶠ i in atTop, (μ i).real {P | A/2 ≤ ‖F i P‖} ≤ 1 from
      Eventually.of_forall fun _ => measureReal_le_one⟩
  have hGb : IsBoundedUnder (· ≤ ·) atTop (fun i => (μ i).real {P | A/2 ≤ ‖G i P‖}) :=
    ⟨1,show ∀ᶠ i in atTop, (μ i).real {P | A/2 ≤ ‖G i P‖} ≤ 1 from
      Eventually.of_forall fun _ => measureReal_le_one⟩
  have hFe := eventually_lt_of_limsup_lt (hF.trans_lt (show 2*c < 3*c by linarith)) hFb
  have hGe := eventually_lt_of_limsup_lt (hG.trans_lt (show 2*c < 3*c by linarith)) hGb
  filter_upwards [hFe,hGe,hr.1.eventually_gt_atTop 0] with i hi hj hri
  have hni : 0 < n i := recordFluctuationScale_pos ν hue e f hef htrans hri
  have hs := physical_exit_subset_path_norm e f (x i) (θ i) (r i) (n i) T A hri hni hT
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by
    change (μ i).real {P | A/2 ≤ ‖F i P‖} + (μ i).real {P | A/2 ≤ ‖G i P‖} ≤ 8*c
    linarith))

end DirectionalTransience

end

end

end OAI
