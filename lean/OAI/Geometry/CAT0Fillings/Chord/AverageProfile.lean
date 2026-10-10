import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Chord.TestIdentity
import OAI.Geometry.CAT0Fillings.Chord.RadialIntegral
import OAI.Geometry.CAT0Fillings.Chord.GroundProducts
import OAI.Geometry.CAT0Fillings.Radial.Extension

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chord_energy (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f) (hf0 : ∀ t, 0 ≤ f t)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
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
    Integrable (fun z => ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2) q.atlasMeasure ∧
    (∫ z, ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) ≤
      (k+1:ℝ)/4*(∫ x, (κ*dist o x*(q.inclusion v x)^β)^2*
        f (κ*dist o x*(q.inclusion v x)^β)*(q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT) := by
  obtain ⟨G,Q,hG,hQ,hDG,hDQ⟩ := q.closed_added_tests hz o v (κ := κ) hb hB hf hfB hv hm hpow
  have hG0 : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion G x := by
    filter_upwards [hv,hG] with x hv hG
    rw [hG]
    exact mul_nonneg (Real.rpow_nonneg hv _) (hf0 _)
  have hrG := q.completed_radial o G hG0 (q.radialDefect_nonpos hz o hr G hG0)
  obtain ⟨hE,hbound⟩ := q.added_energy_integral o v G Q
    (q.added_tests_identity o v G Q hb hn hv hG hQ hDG hDQ) hrG (heuler Q)
  refine ⟨hE,hbound.trans_eq ?_⟩
  rw [show κ^2*(k+1:ℝ)/4 = (k+1:ℝ)/4*κ^2 by ring, mul_assoc,←integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [hv,hQ] with x hv hQ
  rw [hQ]
  have hp : (q.inclusion v x)^(1+4*β)*(q.inclusion v x)^(1+2*β) =
      ((q.inclusion v x)^β)^2*(q.inclusion v x)^(2+4*β) := by
    rw [←Real.rpow_add' hv (by linarith : 1+4*β+(1+2*β) ≠ 0),←Real.rpow_mul_natCast hv,Nat.cast_ofNat,
      ←Real.rpow_add' hv (by linarith : β*(2:ℝ)+(2+4*β) ≠ 0)]
    congr 1
    ring
  calc
    _ = κ^2*dist o x^2*((q.inclusion v x)^(1+4*β)*(q.inclusion v x)^(1+2*β))*f (κ*dist o x*(q.inclusion v x)^β) := by ring
    _ = _ := by rw [hp]; ring
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
noncomputable def averageProfile (n : ℕ) (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Icc (0:ℝ) 1, τ^(n-1)*(d (τ*t))^2
noncomputable def averageProfileDeriv (n : ℕ) (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Icc (0:ℝ) 1, 2*τ^n*d (τ*t)*deriv d (τ*t)
lemma avg_pow_bound {τ : ℝ} (hτ : τ ∈ Icc (0:ℝ) 1) (n : ℕ) : |τ^n| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg hτ.1 _)]
  exact pow_le_one₀ hτ.1 hτ.2
lemma avg_integrand_bound {d : ℝ → ℝ} {B τ t : ℝ} (hτ : τ ∈ Icc (0:ℝ) 1)
    (hd : ∀ x, |d x| ≤ B) (n : ℕ) : |τ^(n-1)*(d (τ*t))^2| ≤ B^2 := by
  simp only [abs_mul,abs_pow]
  have hp : |τ|^(n-1) ≤ 1 := by simpa only [abs_pow] using avg_pow_bound hτ (n-1)
  calc
    _ ≤ 1*B^2 := mul_le_mul hp (pow_le_pow_left₀ (abs_nonneg _) (hd _) _) (by positivity) zero_le_one
    _ = _ := one_mul _
lemma avg_deriv_bound {d : ℝ → ℝ} {B τ t : ℝ} (hB : 0 ≤ B) (hτ : τ ∈ Icc (0:ℝ) 1)
    (hd : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (n : ℕ) :
    |2*τ^n*d (τ*t)*deriv d (τ*t)| ≤ 2*B^2 := by
  rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*1*B*B := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (avg_pow_bound hτ _) (by norm_num)) (hd _).1 (abs_nonneg _) (by norm_num)) (hd _).2 (abs_nonneg _) (by positivity)
    _ = _ := by ring
lemma averageProfile_hasDerivAt {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (t : ℝ) :
    HasDerivAt (averageProfile n d) (averageProfileDeriv n d t) t := by
  have hdc := hd.continuous_deriv_one
  have hmeas (x : ℝ) : AEStronglyMeasurable (fun τ : ℝ => τ^(n-1)*(d (τ*x))^2) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => τ^(n-1)*(d (τ*x))^2)).aestronglyMeasurable
  have hmeas' (x : ℝ) : AEStronglyMeasurable (fun τ : ℝ => 2*τ^n*d (τ*x)*deriv d (τ*x)) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => 2*τ^n*d (τ*x)*deriv d (τ*x))).aestronglyMeasurable
  have hi : Integrable (fun τ : ℝ => τ^(n-1)*(d (τ*t))^2) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => τ^(n-1)*(d (τ*t))^2)).integrableOn_Icc
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc (0:ℝ) 1))
    (F := fun x τ => τ^(n-1)*(d (τ*x))^2) (F' := fun x τ => 2*τ^n*d (τ*x)*deriv d (τ*x))
    (bound := fun _ => 2*B^2) (s := univ) (by simp) (Eventually.of_forall hmeas) hi (hmeas' t) ?_ (integrable_const _) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ x hx
    exact avg_deriv_bound hB hτ hdB n
  · filter_upwards [] with τ x hx
    have hg := ((hd.differentiable (by norm_num) (τ*x)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul τ)).pow 2
    have hh := hg.const_mul (τ^(n-1))
    convert hh using 1 <;> try rfl
    simp only [Function.comp_apply,Nat.cast_ofNat,mul_one]
    have hp : τ^(n-1)*τ = τ^n := by rw [←pow_succ,Nat.sub_add_cancel hn]
    calc
      _ = 2*(τ^(n-1)*τ)*d (τ*x)*deriv d (τ*x) := by rw [hp]
      _ = _ := by ring
lemma averageProfile_contDiff {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) :
    ContDiff ℝ 1 (averageProfile n d) := by
  have hdc := hd.continuous_deriv_one
  rw [contDiff_one_iff_deriv]
  constructor
  · exact fun t => (averageProfile_hasDerivAt hn hd hB hdB t).differentiableAt
  · have he : deriv (averageProfile n d) = averageProfileDeriv n d :=
      funext fun t => (averageProfile_hasDerivAt hn hd hB hdB t).deriv
    rw [he]
    apply continuous_of_dominated (bound := fun _ => 2*B^2)
    · intro t
      exact (by fun_prop : Continuous (fun τ : ℝ => 2*τ^n*d (τ*t)*deriv d (τ*t))).aestronglyMeasurable
    · intro t
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact avg_deriv_bound hB hτ hdB n
    · exact integrable_const _
    · filter_upwards [] with τ
      fun_prop
lemma averageProfile_nonneg (n : ℕ) (d : ℝ → ℝ) (t : ℝ) : 0 ≤ averageProfile n d t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact mul_nonneg (pow_nonneg hτ.1 _) (sq_nonneg _)
end CAT0Fillings.Conformal
end

end OAI
