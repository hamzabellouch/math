import Mathlib
import OAI.Geometry.CAT0Fillings.Minimizers.CriticalEnergy
import OAI.Geometry.CAT0Fillings.Chord.Bubble

namespace OAI

section
open Set Filter MeasureTheory

namespace CAT0Fillings.Conformal
lemma chord_rational_bounds {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t|/(1+a*t^2) ≤ 1+a⁻¹ ∧ t^2/(1+a*t^2)^2 ≤ a⁻¹ := by
  have hb : 0 < 1+a*t^2 := by positivity
  have h1 : 1 ≤ 1+a*t^2 := by nlinarith [mul_nonneg ha.le (sq_nonneg t)]
  have ht : |t| ≤ 1+t^2 := by nlinarith [sq_nonneg (|t|-1),sq_abs t]
  have hd : t^2/(1+a*t^2) ≤ a⁻¹ := by
    rw [←one_div,div_le_div_iff₀ hb ha]
    nlinarith
  constructor
  · calc
      _ ≤ (1+t^2)/(1+a*t^2) := div_le_div_of_nonneg_right ht hb.le
      _ = 1/(1+a*t^2)+t^2/(1+a*t^2) := add_div _ _ _
      _ ≤ 1+a⁻¹ := add_le_add (div_le_one_of_le₀ h1 hb.le) hd
  · apply le_trans (div_le_div_of_nonneg_left (sq_nonneg t) hb ?_) hd
    nlinarith
lemma chordBubbleD_bound {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (t : ℝ) :
    |chordBubbleD q a t| ≤ 2*q*a*(1+a⁻¹) := by
  have hb : 0 < 1+a*t^2 := by positivity
  have hp := (chordBubble_pos ha.le q t).le
  have hp1 := chordBubble_le_one ha.le hq t
  have hid : |chordBubbleD q a t| = 2*q*a*(|t|/(1+a*t^2))*chordBubble q a t := by
    unfold chordBubbleD chordBubble
    rw [Real.rpow_sub hb,Real.rpow_one]
    simp only [abs_mul,abs_div,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hq,abs_of_pos ha,abs_of_pos hb,abs_of_pos (Real.rpow_pos_of_pos hb (-q))]
    ring
  rw [hid]
  calc
    _ ≤ 2*q*a*(1+a⁻¹)*1 := mul_le_mul (mul_le_mul_of_nonneg_left (chord_rational_bounds ha t).1 (by positivity)) hp1 hp (by positivity)
    _ = _ := mul_one _
lemma chordBubbleDD_bound {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (t : ℝ) :
    |chordBubbleDD q a t| ≤ 2*q*a+4*q*(q+1)*a := by
  have hb : 0 < 1+a*t^2 := by positivity
  have h1 : 1 ≤ 1+a*t^2 := by nlinarith [mul_nonneg ha.le (sq_nonneg t)]
  have hp := (chordBubble_pos ha.le q t).le
  have hp1 := chordBubble_le_one ha.le hq t
  have hfirst : |(-2*q*a)*(1+a*t^2)^(-q-1)| ≤ 2*q*a := by
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hb.le _)]
    have hpow : (1+a*t^2)^(-q-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have habs : |-2*q*a| = 2*q*a := by rw [abs_of_nonpos (by nlinarith)]; ring
    rw [habs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*q*a by positivity)
  have hsecond : |4*q*(q+1)*a^2*t^2*(1+a*t^2)^(-q-2)| ≤ 4*q*(q+1)*a := by
    rw [abs_of_nonneg (by positivity)]
    have hid : 4*q*(q+1)*a^2*t^2*(1+a*t^2)^(-q-2) =
        (4*q*(q+1)*a^2)*(t^2/(1+a*t^2)^2)*chordBubble q a t := by
      rw [Real.rpow_sub hb,Real.rpow_two]
      unfold chordBubble
      ring
    rw [hid]
    calc
      _ ≤ (4*q*(q+1)*a^2)*a⁻¹*1 := mul_le_mul (mul_le_mul_of_nonneg_left (chord_rational_bounds ha t).2 (by positivity)) hp1 hp (by positivity)
      _ = _ := by field_simp
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
lemma chordBubble_bounded_derivatives {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |chordBubble q a t| ≤ B ∧
      |deriv (chordBubble q a) t| ≤ B ∧ |deriv (chordBubbleD q a) t| ≤ B := by
  let B := 1+2*q*a*(1+a⁻¹)+(2*q*a+4*q*(q+1)*a)
  have hA : 0 ≤ 2*q*a*(1+a⁻¹) := by positivity
  have hC : 0 ≤ 2*q*a+4*q*(q+1)*a := by positivity
  refine ⟨B,by dsimp [B]; linarith,fun t => ?_⟩
  rw [(chordBubble_hasDerivAt ha.le q t).deriv,(chordBubbleD_hasDerivAt ha.le q t).deriv]
  have hw := chordBubble_le_one ha.le hq t
  rw [←abs_of_nonneg (chordBubble_pos ha.le q t).le] at hw
  exact ⟨hw.trans (by dsimp [B]; linarith),
    (chordBubbleD_bound ha hq t).trans (by dsimp [B]; linarith),
    (chordBubbleDD_bound ha hq t).trans (by dsimp [B]; linarith)⟩
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chord_combined (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β a : ℝ}
    (hb : 0 < β) (ha : 0 < a) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0) (_hg : LipschitzWith K g),
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g) :
    let w := chordBubble (1/(2*β)) a
    let f := averageProfile (k+1) (chordBubbleD (1/(2*β)) a)
    ∃ P : q.Sobolev,
      (q.inclusion P : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => q.inclusion v x*w (κ*dist o x*(q.inclusion v x)^β)) ∧
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P ≤
        (k+1:ℝ)*(∫ x, (q.inclusion v x)^(2+4*β)*(w (κ*dist o x*(q.inclusion v x)^β))^2 ∂MassMeasure.currentMassMeasure hT)+
        β*(k+1:ℝ)*(∫ x, (κ*dist o x*(q.inclusion v x)^β)^2*
          f (κ*dist o x*(q.inclusion v x)^β)*(q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT) := by
  dsimp only
  let c := 1/(2*β)
  let w := chordBubble c a
  let d := chordBubbleD c a
  let f := averageProfile (k+1) d
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨B,hB,hbounds⟩ := chordBubble_bounded_derivatives ha hc
  have hw : ContDiff ℝ 1 w := chordBubble_contDiff ha.le c 1
  have hd : ContDiff ℝ 1 d := chordBubbleD_contDiff ha.le c 1
  have hdB : ∀ t, |d t| ≤ B ∧ |deriv d t| ≤ B := by
    intro t
    refine ⟨?_,(hbounds t).2.2⟩
    simpa only [(chordBubble_hasDerivAt ha.le c t).deriv] using (hbounds t).2.1
  obtain ⟨P,hP,hInt,hE⟩ := q.chord_ground_state hz o v (κ := κ) hb hB hw
    (fun t => ⟨(hbounds t).1,(hbounds t).2.1⟩) hv hm hpow heuler
  have hf : ContDiff ℝ 1 f := averageProfile_contDiff (Nat.succ_pos _) hd hB hdB
  have hfB : ∀ t, |f t| ≤ B^2+2*B^2 ∧ |deriv f t| ≤ B^2+2*B^2 := by
    intro t
    exact ⟨(averageProfile_bound (fun t => (hdB t).1) t).trans (by nlinarith [sq_nonneg B]),
      (averageProfile_deriv_bound (Nat.succ_pos _) hd hB hdB t).trans (by nlinarith [sq_nonneg B])⟩
  have hf0 : ∀ t, 0 ≤ f t := fun t => averageProfile_nonneg (k+1) d t
  have hce := (q.chord_energy hz o v (κ := κ) hb hn (show 0 ≤ B^2+2*B^2 by positivity)
    hf hf0 hfB hv hm hpow heuler hr).2
  have hident (t : ℝ) : (k+1:ℝ)*f t+t*deriv f t = (deriv w t)^2 := by
    have hi := averageProfile_identity (Nat.succ_pos k) hd hB hdB t
    have hwder : deriv w t = d t := (chordBubble_hasDerivAt ha.le c t).deriv
    rw [hwder]
    simpa only [Nat.cast_succ] using hi
  have hleft : (∫ z, ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) =
    (∫ z, (deriv w (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))^2*
      ‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact congrArg (fun r : ℝ => r*‖q.chordXi o v κ β z‖^2) (hident _)
  change _ ≤ _ at hce
  rw [hleft] at hce
  refine ⟨P,hP,?_⟩
  apply hE.le.trans
  apply add_le_add le_rfl
  calc
    _ ≤ 4*β*((k+1:ℝ)/4*_) := mul_le_mul_of_nonneg_left hce (by positivity)
    _ = _ := by ring
end CAT0Fillings.ChartGeometry
end

end OAI
