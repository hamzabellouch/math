import Mathlib
import OAI.NumberTheory.PrimePackets.PacketMoments

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology Matrix
open scoped ENNReal BigOperators Classical

 

lemma cusp_indicator_le_siegel {n : ℕ} {θ : ℝ} (x : X n) :
    (thickLattices n θ)ᶜ.indicator (fun _ => (1:ℝ≥0∞)) x ≤
      siegelTransform (boxIndicator (fun _ : Fin n => 0) θ) x := by
  by_cases hx : x ∈ (thickLattices n θ)ᶜ
  · rw [Set.indicator_of_mem hx]
    obtain ⟨g,hg,z,hz,hzθ⟩ : ∃ g : G n,
        Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x ∧
          ∃ z : Fin n → ℤ, z ≠ 0 ∧ ‖(fun i => (z i:ℝ)) ᵥ* g.1‖ < θ := by
      simpa only [thickLattices,Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall,
        Classical.not_imp,not_le,exists_prop] using hx
    rw [← hg,siegelTransform_mk]
    have hv : integerRowMap g.1 z ∈ coordinateBox (fun _ => 0) θ := by
      intro j
      rw [integerRowMap_apply,sub_zero]
      exact (show |((fun i => (z i:ℝ)) ᵥ* g.1) j| ≤
        ‖(fun i => (z i:ℝ)) ᵥ* g.1‖ by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm ((fun i => (z i:ℝ)) ᵥ* g.1) j).trans hzθ.le
    have H := ENNReal.le_tsum (f := fun v : {z : Fin n → ℤ // z ≠ 0} =>
      boxIndicator (fun _ => 0) θ (integerRowMap g.1 v.1)) ⟨z,hz⟩
    simpa only [boxIndicator,Set.indicator_of_mem hv] using H
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

lemma cusp_mass_le_cube_moment {n : ℕ} (μ : Measure (X n)) (θ : ℝ) :
    μ (thickLattices n θ)ᶜ ≤
      ∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin n => 0) θ) x ∂μ := by
  calc
    _ = ∫⁻ x, (thickLattices n θ)ᶜ.indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator (thickLattices_isClosed n θ).isOpen_compl.measurableSet]
      simp
    _ ≤ _ := lintegral_mono cusp_indicator_le_siegel

 

lemma right_ball_indicator_le_siegel {n : ℕ} (g : G n) (z : Fin n → ℤ)
    (hz : z ≠ 0) {r ε : ℝ} (_hr : 0 ≤ r)
    (hε : r*(∑ i, |integerRowMap g.1 z i|) ≤ ε) (y : X n) :
    ((fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r).indicator
      (fun _ => (1:ℝ≥0∞)) y ≤ siegelTransform (boxIndicator (integerRowMap g.1 z) ε) y := by
  let S := (fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r
  by_cases hy : y ∈ S
  · obtain ⟨h,hh,rfl⟩ := hy
    change S.indicator (fun _ => (1:ℝ≥0∞)) (Quotient.mk _ (g*h)) ≤
      siegelTransform (boxIndicator (integerRowMap g.1 z) ε) (Quotient.mk _ (g*h))
    rw [siegelTransform_mk]
    have hv : integerRowMap (g*h).1 z ∈ coordinateBox (integerRowMap g.1 z) ε := by
      intro j
      have H := vecMul_sub_coordinate_le (integerRowMap g.1 z) h hh j
      rw [integerRowMap_apply,integerRowMap_apply,
        Matrix.SpecialLinearGroup.coe_mul,← Matrix.vecMul_vecMul]
      simpa only [integerRowMap_apply] using H.trans hε
    have H := ENNReal.le_tsum (f := fun v : {z : Fin n → ℤ // z ≠ 0} =>
      boxIndicator (integerRowMap g.1 z) ε (integerRowMap (g*h).1 v.1)) ⟨z,hz⟩
    have hyS : Quotient.mk _ (g*h) ∈ S := ⟨h,hh,rfl⟩
    simpa only [boxIndicator,Set.indicator_of_mem hv,Set.indicator_of_mem hyS] using H
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

lemma right_ball_mass_le_box_moment {n : ℕ} (μ : Measure (X n)) (g : G n)
    (z : Fin n → ℤ) (hz : z ≠ 0) {r ε : ℝ} (hr : 0 ≤ r)
    (hε : r*(∑ i, |integerRowMap g.1 z i|) ≤ ε) :
    μ ((fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r) ≤
      ∫⁻ x, siegelTransform (boxIndicator (integerRowMap g.1 z) ε) x ∂μ := by
  calc
    _ = ∫⁻ x, ((fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r).indicator
        (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator (right_ball_isOpen (Quotient.mk _ g) r).measurableSet]
      simp
    _ ≤ _ := lintegral_mono (right_ball_indicator_le_siegel g z hz hr hε)

 

lemma open_mass_le_of_probability_limit {n : ℕ}
    (μ : ℕ → ProbabilityMeasure (X n)) (ν : ProbabilityMeasure (X n))
    (hlim : Tendsto μ atTop (𝓝 ν)) {S : Set (X n)} (hS : IsOpen S)
    {B : ℝ≥0∞} (hB : ∀ᶠ i in atTop, (μ i : Measure (X n)) S ≤ B) :
    (ν : Measure (X n)) S ≤ B := by
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hS).trans
    (liminf_le_of_frequently_le (Filter.Eventually.frequently hB))

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology Matrix
open scoped ENNReal BigOperators Classical

 

theorem packet_ball_bound_bounded_discr (d : ℕ) (hodd : Odd (d+1))
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ N : ℕ,
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → |NumberField.discr K| ≤ N → packetScale M = Q →
        ∀ x ∈ Ω, packetMeasure M σ ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
          ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨b,c,hb,hc,Hvec⟩ := compact_uniform_vector_envelope hΩ
  obtain ⟨A,ε₀,hA,hε₀,Hbox⟩ := packet_box_moment_bounded_discr d hodd hb.le hc
  let E : ℝ := (d+1:ℕ)*b
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨A*E^(d+1),ε₀/E,by positivity,div_pos hε₀ hE,?_⟩
  intro r hr hrr N
  have hrε : E*r < ε₀ := by nlinarith [(lt_div_iff₀ hE).mp hrr]
  filter_upwards [Hbox (E*r) (mul_pos hE hr) hrε N] with Q hQ
  intro K _ _ _ M σ hn hD hMQ x hx
  obtain ⟨g,hg,z,hz⟩ := Hvec x hx
  have hzne : z ≠ 0 := by
    intro he
    have H : c < (0:ℝ) := by simpa [he,Matrix.vecMul,dotProduct] using (hz 0).1
    exact hc.not_gt H
  have hlo (i) : c ≤ |integerRowMap g.1 z i| := by
    simpa only [integerRowMap_apply] using (hz i).1.le
  have hhi (i) : |integerRowMap g.1 z i| ≤ b := by
    simpa only [integerRowMap_apply] using (hz i).2.le
  have hsum : (∑ i, |integerRowMap g.1 z i|) ≤ E := by
    calc
      _ ≤ ∑ _ : Fin (d+1), b := Finset.sum_le_sum fun i _ => hhi i
      _ = E := by simp [E]
  have H := right_ball_mass_le_box_moment (packetMeasure M σ) g z hzne hr.le
    (show r*(∑ i, |integerRowMap g.1 z i|) ≤ E*r by nlinarith)
  rw [hg] at H
  refine H.trans ((hQ K M σ hn hD hMQ (integerRowMap g.1 z) hlo hhi).trans_eq ?_)
  congr 1
  rw [mul_pow]
  ring

 
def packetProbability {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    (hodd : Odd (d+1)) : ProbabilityMeasure (X (d+1)) :=
  ⟨packetMeasure M σ,packetMeasure_isProbabilityMeasure M σ hn hodd⟩

 

theorem packet_limit_ball_bound_bounded_discr (d : ℕ) (hodd : Odd (d+1))
    (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (N : ℕ) (hN : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν))
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → r < r₀ →
      (ν : Measure (X (d+1))) ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
        ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨C,r₀,hC,hr₀,H⟩ := packet_ball_bound_bounded_discr d hodd hΩ
  refine ⟨C,r₀,hC,hr₀,?_⟩
  intro x hx r hr hrr
  apply open_mass_le_of_probability_limit _ ν hlim (right_ball_isOpen x r)
  filter_upwards [hQ.eventually (H r hr hrr N)] with i hi
  exact hi (K i) (M i) (σ i) (hn i) (hN i) rfl x hx

end PrimeDegreePackets


namespace PrimeDegreePackets

 

def logMomentConstant (d : ℕ) : ℝ :=
  ∑' j : ℕ, ((j : ℝ)+1)^d * Real.exp (-(j : ℝ))

lemma logMoment_summable (d : ℕ) :
    Summable (fun j : ℕ => ((j : ℝ)+1)^d * Real.exp (-(j : ℝ))) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
    (r := Real.exp (-1)) (by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by norm_num))
  have H := (summable_nat_add_iff 1).mpr h
  have H' := H.mul_right (Real.exp 1)
  apply H'.congr
  intro j
  simp only [Nat.cast_add,Nat.cast_one]
  rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
  congr 2
  push_cast
  ring

lemma logMomentConstant_nonneg (d : ℕ) : 0 ≤ logMomentConstant d :=
  tsum_nonneg (fun _ => by positivity)

lemma logarithmic_shell {X r : ℝ} (hX : 0 < X) (hr : 0 < r) (hrX : r ≤ X) :
    let j := ⌊Real.log (X/r)⌋₊
    Real.log (X/r) < (j : ℝ)+1 ∧ r ≤ X*Real.exp (-(j : ℝ)) := by
  have hlog : 0 ≤ Real.log (X/r) := Real.log_nonneg ((le_div_iff₀ hr).mpr (by simpa))
  let j := ⌊Real.log (X/r)⌋₊
  refine ⟨Nat.lt_floor_add_one _,?_⟩
  have H := Real.exp_le_exp.mpr (Nat.floor_le hlog)
  rw [Real.exp_log (div_pos hX hr)] at H
  have H' : r * Real.exp (j : ℝ) ≤ X := by
    simpa [mul_comm] using (le_div_iff₀ hr).mp H
  rw [Real.exp_neg,← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr H'

 

theorem log_weighted_sum_le {α : Type*} (S : Finset α) (N w : α → ℝ)
    (d : ℕ) (X A : ℝ) (hX : 0 < X) (hA : 0 ≤ A)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hN : ∀ a ∈ S, 0 < N a ∧ N a ≤ X)
    (hcount : ∀ t : ℝ, 0 ≤ t → t ≤ X →
      (∑ a ∈ S.filter (fun a => N a ≤ t), w a) ≤ A*t) :
    (∑ a ∈ S, w a * (Real.log (X/N a))^d) ≤ A*X*logMomentConstant d := by
  classical
  let k : α → ℕ := fun a => ⌊Real.log (X/N a)⌋₊
  have hk (a : α) (ha : a ∈ S) := logarithmic_shell hX (hN a ha).1 (hN a ha).2
  have hlogs (a : α) (ha : a ∈ S) : 0 ≤ Real.log (X/N a) :=
    Real.log_nonneg ((le_div_iff₀ (hN a ha).1).mpr (by simpa using (hN a ha).2))
  calc
    _ ≤ ∑ a ∈ S, w a * ((k a : ℝ)+1)^d := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hlogs a ha) (hk a ha).1.le d) (hw a ha)
    _ = ∑ j ∈ S.image k, ∑ a ∈ S.filter (fun a => k a = j), w a * ((k a : ℝ)+1)^d := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image k) (g := k)
        (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) _
    _ ≤ ∑ j ∈ S.image k, A*X*(((j : ℝ)+1)^d * Real.exp (-(j : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hfilter : S.filter (fun a => k a = j) ⊆
          S.filter (fun a => N a ≤ X*Real.exp (-(j : ℝ))) := by
        intro a ha
        obtain ⟨ha,hka⟩ := Finset.mem_filter.mp ha
        refine Finset.mem_filter.mpr ⟨ha,?_⟩
        simpa only [← hka] using (hk a ha).2
      have hc := hcount (X*Real.exp (-(j : ℝ))) (by positivity) (by
        apply mul_le_of_le_one_right hX.le
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr (Nat.cast_nonneg j))
      have hwf : (∑ a ∈ S.filter (fun a => k a = j), w a) ≤
          A*(X*Real.exp (-(j : ℝ))) := by
        apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hfilter ?_) hc
        intro a ha _
        exact hw a (Finset.mem_filter.mp ha).1
      have he : (∑ a ∈ S.filter (fun a => k a = j), w a * ((k a : ℝ)+1)^d) =
          ((j : ℝ)+1)^d * (∑ a ∈ S.filter (fun a => k a = j), w a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
        ring
      rw [he]
      have H := mul_le_mul_of_nonneg_left hwf (show 0 ≤ ((j : ℝ)+1)^d by positivity)
      convert H using 1
      ring
    _ = A*X*(∑ j ∈ S.image k, ((j : ℝ)+1)^d * Real.exp (-(j : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ A*X*logMomentConstant d := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hX.le)
      exact (logMoment_summable d).sum_le_tsum _ (fun _ _ => by positivity)

 

theorem log_weighted_sum_cutoff {α : Type*} (S : Finset α) (N w : α → ℝ)
    (d : ℕ) (X U Q A : ℝ) (hX : 0 < X) (hA : 0 ≤ A)
    (hQ : 1 ≤ Q) (hXQ : X ≤ Q)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hN : ∀ a ∈ S, 1 ≤ N a ∧ N a ≤ X)
    (hcount : ∀ t : ℝ, U ≤ t →
      (∑ a ∈ S.filter (fun a => N a ≤ t), w a) ≤ A*t) :
    (∑ a ∈ S, w a * (Real.log (X/N a))^d) ≤
      A*U*(Real.log Q)^d + A*X*logMomentConstant d := by
  classical
  have hQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlog (a : α) (ha : a ∈ S) :
      0 ≤ Real.log (X/N a) ∧ Real.log (X/N a) ≤ Real.log Q := by
    have ha0 : 0 < N a := lt_of_lt_of_le zero_lt_one (hN a ha).1
    refine ⟨Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using (hN a ha).2)),?_⟩
    apply Real.log_le_log (div_pos hX ha0)
    apply (div_le_iff₀ ha0).mpr
    exact le_trans hXQ (le_mul_of_one_le_right (by linarith) (hN a ha).1)
  have hsmall : (∑ a ∈ S.filter (fun a => N a ≤ U),
      w a * (Real.log (X/N a))^d) ≤ A*U*(Real.log Q)^d := by
    calc
      _ ≤ ∑ a ∈ S.filter (fun a => N a ≤ U), w a * (Real.log Q)^d := by
        apply Finset.sum_le_sum
        intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hlog a haS).1 (hlog a haS).2 d) (hw a haS)
      _ = (∑ a ∈ S.filter (fun a => N a ≤ U), w a) * (Real.log Q)^d := by
        rw [Finset.sum_mul]
      _ ≤ A*U*(Real.log Q)^d := mul_le_mul_of_nonneg_right (hcount U le_rfl) (by positivity)
  have hlarge : (∑ a ∈ S.filter (fun a => ¬ N a ≤ U),
      w a * (Real.log (X/N a))^d) ≤ A*X*logMomentConstant d := by
    apply log_weighted_sum_le _ N w d X A hX hA
    · intro a ha
      exact hw a (Finset.mem_filter.mp ha).1
    · intro a ha
      have haS := (Finset.mem_filter.mp ha).1
      exact ⟨lt_of_lt_of_le zero_lt_one (hN a haS).1,(hN a haS).2⟩
    · intro t ht _
      by_cases hUt : U ≤ t
      · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hcount t hUt)
        · intro a ha
          obtain ⟨ha,hat⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,hat⟩
        · intro a ha _
          exact hw a (Finset.mem_filter.mp ha).1
      · have he : (S.filter (fun a => ¬ N a ≤ U)).filter (fun a => N a ≤ t) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro a ha hat
          exact (Finset.mem_filter.mp ha).2 (le_trans hat (le_of_not_ge hUt))
        rw [he,Finset.sum_empty]
        exact mul_nonneg hA ht
  rw [← Finset.sum_filter_add_sum_filter_not S (fun a => N a ≤ U)]
  exact add_le_add hsmall hlarge

lemma cusp_log_error_vanishes (d : ℕ) :
    Tendsto (fun Q : ℝ => (Real.log Q)^d / Q^((1:ℝ)/4)) atTop (𝓝 0) := by
  have H := (isLittleO_log_rpow_rpow_atTop (d : ℝ)
    (by norm_num : (0:ℝ) < 1/4)).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast] using H

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set
open scoped ENNReal BigOperators Classical

lemma cube_fiber_log_rectangle {d : ℕ} {θ z : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (s : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d)
    (hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
      (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈
      coordinateBox (fun _ => 0) θ) :
    u ∈ Set.Icc (fun _ => Real.log θ-Real.log (θ^(d+1)/z)) (fun _ => Real.log θ) := by
  have hup (i : Fin d) : u i ≤ Real.log θ := by
    have H := hu i.castSucc
    simp only [Fin.snoc_castSucc,sub_zero,abs_mul,signValue_abs,one_mul,
      abs_of_pos (Real.exp_pos _)] at H
    exact (Real.le_log_iff_exp_le hθ).mpr H
  have hlast : Real.log z - ∑ i, u i ≤ Real.log θ := by
    have H := hu (Fin.last d)
    simp only [Fin.snoc_last,sub_zero,abs_mul,signValue_abs,one_mul,
      abs_of_pos hz,abs_of_pos (Real.exp_pos _)] at H
    have Hlog := Real.log_le_log (mul_pos hz (Real.exp_pos _)) H
    simpa only [Real.log_mul hz.ne' (Real.exp_ne_zero _),Real.log_exp,sub_eq_add_neg]
      using Hlog
  have hsum : ∑ i, (Real.log θ-u i) ≤ Real.log (θ^(d+1)/z) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Real.log_div (pow_ne_zero _ hθ.ne') hz.ne',Real.log_pow,Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨?_,hup⟩
  intro i
  have H := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hup j))
    (Finset.mem_univ i)
  have := H.trans hsum
  linarith

lemma cube_fiber_product_le {d : ℕ} {θ z : ℝ} (hz : 0 ≤ z) (s : Fin (d+1) → SignTypeˣ)
    (u : LogCoordinates d)
    (hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
      (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈
      coordinateBox (fun _ => 0) θ) : z ≤ θ^(d+1) := by
  let v : Fin (d+1) → ℝ := Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
    (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i))
  have H : (∏ i, |v i|) ≤ ∏ _i : Fin (d+1), θ :=
    Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => abs_nonneg (v i))
      (fun i (_ : i ∈ Finset.univ) => by simpa only [sub_zero] using hu i)
  dsimp only [v] at H
  simpa only [fiberPoint_abs_prod,abs_of_nonneg hz,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin] using H

 

theorem productFiberIntegral_cube_eq_zero {d : ℕ} {θ z : ℝ} (hz : 0 ≤ z)
    (hzt : θ^(d+1) < z) :
    productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ) z = 0 := by
  unfold productFiberIntegral
  apply Finset.sum_eq_zero
  intro s _
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro u
  have hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
      (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∉ coordinateBox (fun _ => 0) θ :=
    fun H => (cube_fiber_product_le hz s u H).not_gt hzt
  simp only [boxIndicator,Set.indicator_of_notMem hu,Pi.zero_apply]

 

theorem productFiberIntegral_cube_le {d : ℕ} {θ z : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (hzt : z ≤ θ^(d+1)) :
    productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ) z ≤
      (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) *
        ENNReal.ofReal ((Real.log (θ^(d+1)/z))^d) := by
  let L := Real.log (θ^(d+1)/z)
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hz).mpr hzt)
  let a : LogCoordinates d := fun _ => Real.log θ-L
  let b : LogCoordinates d := fun _ => Real.log θ
  have H (s : Fin (d+1) → SignTypeˣ) :
      (∫⁻ u : LogCoordinates d, boxIndicator (fun _ => 0) θ
        (Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
          (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)))) ≤ ENNReal.ofReal (L^d) := by
    calc
      _ ≤ ∫⁻ u : LogCoordinates d, (Set.Icc a b).indicator (fun _ => (1:ℝ≥0∞)) u := by
        apply lintegral_mono
        intro u
        by_cases hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
            (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈ coordinateBox (fun _ => 0) θ
        · have hab : u ∈ Set.Icc a b := cube_fiber_log_rectangle hθ hz s u hu
          simp only [boxIndicator,Set.indicator_of_mem hu,Set.indicator_of_mem hab,le_refl]
        · simp only [boxIndicator,Set.indicator_of_notMem hu]
          exact bot_le
      _ = volume (Set.Icc a b) := by rw [lintegral_indicator measurableSet_Icc]; simp
      _ = ∏ i : Fin d, ENNReal.ofReal (b i-a i) := Real.volume_Icc_pi
      _ = ENNReal.ofReal (L^d) := by simp [a,b,← ENNReal.ofReal_pow hL]
  unfold productFiberIntegral
  exact (Finset.sum_le_sum (fun s _ => H s)).trans_eq (by simp [nsmul_eq_mul,L])

end PrimeDegreePackets
end
end

end OAI
