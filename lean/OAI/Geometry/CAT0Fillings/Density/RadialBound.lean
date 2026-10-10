import Mathlib
import OAI.Geometry.CAT0Fillings.Density.InverseCutoff
import OAI.Geometry.CAT0Fillings.Density.Normalized

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma exists_positive_shell_null_sequence {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (o : X) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝[>] 0) ∧
      ∀ j, 0 < r j ∧ μ {x | dist o x = r j} = 0 := by
  have hc := Measure.countable_meas_level_set_pos (μ := μ)
    (continuous_const.dist continuous_id : Continuous (fun x : X => dist o x)).measurable
  have ha : ∀ᵐ t : ℝ, μ {x | dist o x = t} = 0 := by
    filter_upwards [hc.ae_notMem volume] with t ht
    exact le_antisymm (le_of_not_gt ht) bot_le
  have hchoose (j : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1/((j:ℝ)+1) ∧ μ {x | dist o x = r} = 0 := by
    have hpos : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
    obtain ⟨r,hr,hnull⟩ := (Measure.dense_of_ae ha).inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.mpr hpos)
    exact ⟨r,hr.1,hr.2,hnull⟩
  choose r hr hrb hrnull using hchoose
  refine ⟨r,?_,fun j => ⟨hr j,hrnull j⟩⟩
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨squeeze_zero (fun j => (hr j).le) (fun j => (hrb j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hr⟩

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma radial_density_coefficient (hX : IsCAT0 X) (hM : 0 < mass T)
    {ell : ℝ} (hell : 0 < ell)
    (hrad : ∀ o : X, ∀ r : ℝ, 0 < r →
      ell*q.radialVariation o (fun x => inverseSquareCutoff r (dist o x)) ≤
        q.sweptMass o (fun x => inverseSquareCutoff r (dist o x)))
    {ε v d : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hv : 1+ε < v) (hd : d < Real.pi) :
    2*ell*d/v^2 ≤ (1-ε)⁻¹^2*mass T/(8*ell) := by
  obtain ⟨o,ho⟩ := q.exists_almost_euclidean_density hX hM hε hε1
  obtain ⟨r,hr,hrnull⟩ := exists_positive_shell_null_sequence (MassMeasure.currentMassMeasure hT) o
  have hlim : Tendsto r atTop (𝓝 0) := hr.mono_right nhdsWithin_le_nhds
  have hevent := hr.eventually (ho v hv d hd)
  have hsmall := hlim.eventually (eventually_lt_nhds (by linarith : (0:ℝ) < 2*ell))
  have hineq : ∀ᶠ j in atTop,
      (2*ell-r j)*d/v^2 ≤ (1-ε)⁻¹^2*mass T/(8*ell) := by
    filter_upwards [hevent,hsmall] with j hj hjs
    have hu := q.cutoff_mass_upper o (hrnull j).1 hell (hrnull j).2 (hrad o (r j) (hrnull j).1)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos (hrnull j).1)).mp
    calc
      _ = (2*ell-r j)*(d*(r j/v)^2) := by ring
      _ ≤ (2*ell-r j)*((1-ε)⁻¹^2*(MassMeasure.currentMassMeasure hT).real (ball o (r j))) :=
        mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr hjs.le)
      _ = (1-ε)⁻¹^2*((2*ell-r j)*(MassMeasure.currentMassMeasure hT).real (ball o (r j))) := by ring
      _ ≤ (1-ε)⁻¹^2*((r j)^2/(8*ell)*mass T) := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = _ := by ring
  apply le_of_tendsto _ hineq
  simpa only [sub_zero] using ((tendsto_const_nhds.sub hlim).mul_const d).div_const (v^2)

include q in
lemma radial_coefficient_bound_two (hX : IsCAT0 X) (hM : 0 < mass T)
    {ell : ℝ} (hell : 0 < ell)
    (hrad : ∀ o : X, ∀ r : ℝ, 0 < r →
      ell*q.radialVariation o (fun x => inverseSquareCutoff r (dist o x)) ≤
        q.sweptMass o (fun x => inverseSquareCutoff r (dist o x))) :
    16*Real.pi*ell^2 ≤ mass T := by
  let ε (j : ℕ) : ℝ := 1/((j:ℝ)+2)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j < 1 := by
    dsimp [ε]
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 1))
  have hi (j : ℕ) := q.radial_density_coefficient hX hM hell hrad (hε j) (hε1 j)
    (show 1+ε j < 1+2*ε j by linarith [hε j]) (show Real.pi-ε j < Real.pi by linarith [hε j])
  have hleft : Tendsto (fun j => 2*ell*(Real.pi-ε j)/(1+2*ε j)^2) atTop (𝓝 (2*ell*Real.pi)) := by
    simpa only [Pi.div_def,Pi.pow_def,mul_zero,add_zero,sub_zero,one_pow,div_one] using ((hlim.const_sub Real.pi).const_mul (2*ell)).div
      (((hlim.const_mul 2).const_add 1).pow 2) (by norm_num : ((1:ℝ)+2*0)^2 ≠ 0)
  have hright : Tendsto (fun j => (1-ε j)⁻¹^2*mass T/(8*ell)) atTop (𝓝 (mass T/(8*ell))) := by
    simpa using ((((hlim.const_sub 1).inv₀ (by norm_num : (1:ℝ)-0 ≠ 0)).pow 2).mul_const (mass T)).div_const (8*ell)
  have hh := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hi)
  have hh' := (le_div_iff₀ (by positivity : (0:ℝ) < 8*ell)).mp hh
  nlinarith
end ChartGeometry
end CAT0Fillings
end

end OAI
