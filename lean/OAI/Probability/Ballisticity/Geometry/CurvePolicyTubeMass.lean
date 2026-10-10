import Mathlib
import OAI.Probability.Ballisticity.Estimates.PolicyGoodMass
import OAI.Probability.Ballisticity.Estimates.FinitePolicyFailure
import OAI.Probability.Ballisticity.Geometry.CurveWordTube
import OAI.Probability.Ballisticity.Estimates.ListPrefixSum

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
local instance CurvePolicyTubeMassMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤
local instance CurvePolicyTubeMassSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_tube_density {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) {H : ℕ} (hH : 0 < H)
    (θ r : ℝ) (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (n : ℕ) :
    (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure {w | w.length=n ∧
        policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w ∧
        listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w ≤ r} ≤
      ((α*δ)⁻¹)^n * quenchedKernel (ω,x)
        (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)) := by
  let S : Set (List (Lattice d)) := {w | w.length=n ∧
        policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w ∧
        listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w ≤ r}
  have hd := curvePolicy_event_density (realPosition (step e)) f b B H E hδ hα hα1 dummy ω i x n S
    (fun _ h => h.1) (fun _ h => h.2.1)
  apply hd.trans
  apply mul_le_mul_right
  apply measure_mono_ae
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro hX
  obtain ⟨w,hX⟩ := Set.mem_iUnion.mp hX
  obtain ⟨hw,hX⟩ := Set.mem_iUnion.mp hX
  have hmax := hw.2.2
  have hp : ∀ k ≤ w.length, |(0:ℝ)+signedCoordinate f (w.take k).sum-(k:ℝ)*(H:ℝ)*θ| ≤ r := by
    intro k hk
    simpa only [zero_add,mul_assoc] using (listCenteredMax_prefix f ((H:ℝ)*θ) w hk).trans hmax
  obtain ⟨m,hm⟩ := curveWordEvent_shifted_tube e f x b hB hD hH θ 0 r hb w hp X h0 hnn hX
  apply Set.mem_iUnion.mpr
  refine ⟨m,?_⟩
  simpa only [hw.1,sub_zero,CurvePrefixAt,TubePrefixAt] using hm

lemma curvePolicy_tube_mass {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) {H : ℕ} (hH : 0 < H)
    (θ r : ℝ) (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (n : ℕ) :
    (α*δ)^n *
      (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure {w | w.length=n ∧
        policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w ∧
        listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w ≤ r} ≤
      quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)) := by
  have hd := mul_le_mul_right (curvePolicy_tube_density e f b hB hD hH θ r hb E hδ hα hα1 dummy ω i x n) ((α*δ)^n)
  have hne : α*δ ≠ 0 := mul_ne_zero hα.ne' hδ.ne'
  have ht : α*δ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (by simpa using mul_le_mul' hα1 hδ1) ENNReal.one_lt_top)
  simpa only [← mul_assoc,← mul_pow,ENNReal.mul_inv_cancel hne ht,one_pow,one_mul] using hd

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
local instance CurvePolicyTubeProbabilityMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤
local instance CurvePolicyTubeProbabilitySingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_tube_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    {H : ℕ} (hH : 0 < H) (θ : ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (dummy : Lattice d) (hd : signedHeight e dummy=H) (hdb : signedCoordinate f dummy=b H)
    (i n : ℕ) (x : Lattice d) (hx : signedHeight e x=(i:ℤ)*H)
    (hc : (H:ℝ)*θ = ∫ u, signedCoordinate f u
      ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure) :
    environmentLaw ν {ω | quenchedKernel (ω,x)
      (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)) < (α*δ)^n/2} ≤
      2*((n:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} +
        ENNReal.ofReal ((4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2
          ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure))/r^2)) := by
  let Q := fun (_ : ℕ) ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω
  let F := fun ω => (finitePolicyPMF Q ω i x n).toMeasure
    {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w}
  let M := fun ω => (finitePolicyPMF Q ω i x n).toMeasure
    {w | r ≤ listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w}
  have hF : Measurable F := curvePolicy_failure_measurable e f b B hH E hδ hα dummy i x n
  have hM : Measurable M := curvePolicy_fixed_event_measurable e f b B hH E hδ hα dummy i x n _
  have hlow := low_mass_probability (environmentLaw ν) (fun ω => F ω+M ω)
    (fun ω => quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)))
    (hF.add hM).aemeasurable ((α*δ)^n/2) (by
      intro ω hcost
      have hp := policy_good_mass Q ω i x n
        (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ)
        (listCenteredMax (signedCoordinate f) ((H:ℝ)*θ)) r hcost
      have ht := curvePolicy_tube_mass e f b hB hD hH θ r hb E hδ hα hδ1 hα1 dummy ω i x n
      have hs := (mul_le_mul_right hp ((α*δ)^n)).trans ht
      simpa only [div_eq_mul_inv,one_mul] using hs)
  apply hlow.trans
  apply mul_le_mul_right
  rw [lintegral_add_left hF]
  apply add_le_add (curvePolicy_actual_failure ν e f b B hH E hδ hα dummy hd i n x hx)
  have hMt : (∫⁻ ω, M ω ∂environmentLaw ν) ≠ ⊤ := by
    have hbnd : (∫⁻ ω, M ω ∂environmentLaw ν) ≤ 1 := by
      calc
        _ ≤ ∫⁻ ω, (1:ℝ≥0∞) ∂environmentLaw ν := lintegral_mono (fun ω => prob_le_one)
        _ = 1 := by simp
    exact ne_of_lt (hbnd.trans_lt ENNReal.one_lt_top)
  rw [← ENNReal.ofReal_toReal hMt]
  apply ENNReal.ofReal_le_ofReal
  simpa only [M,Q,hc] using curvePolicy_maximal_tail ν e f b hB hH E hδ hα dummy hd hdb i x hx n hr

end DirectionalTransience

end

end

end OAI
