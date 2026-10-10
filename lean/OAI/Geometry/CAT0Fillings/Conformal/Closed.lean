import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Conformal.Growth
import OAI.Geometry.CAT0Fillings.Calculus.Polynomial

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
noncomputable def profileRD (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (r z : ℝ) : ℝ :=
  (m:ℝ)*r^(m-1)*z^α*f (κ*r*z^β)+κ*r^m*z^(α+β)*deriv f (κ*r*z^β)
noncomputable def profileZD (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (r z : ℝ) : ℝ :=
  α*r^m*z^(α-1)*f (κ*r*z^β)+β*κ*r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β)
lemma profileRD_eq {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (1,0) = profileRD m α β κ f r z :=
  profile_partial_r hf hz
lemma profileZD_eq {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (0,1) = profileZD m α β κ f r z :=
  profile_partial_z hf hz
end CAT0Fillings.Conformal
namespace CAT0Fillings.ChartGeometry
open _root_.OAI.CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_conformal (hz : IsCycle T)
    {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r) {R : ℝ}
    (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {m : ℕ} {α β κ B : ℝ} {f : ℝ → ℝ}
    (hα : 1 ≤ α) (hβ : 0 < β) (hB : 0 ≤ B)
    (hf : ContDiff ℝ 1 f) (hb : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (P : q.Sobolev)
    (hp : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion P) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w)) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => profile m α β κ f (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if 0 < q.inclusion P (q.atlasParam w) then
          profileRD m α β κ f (r (q.atlasParam w)) (q.inclusion P (q.atlasParam w)) • q.gradient hr w +
          profileZD m α β κ f (r (q.atlasParam w)) (q.inclusion P (q.atlasParam w)) • q.closedGradient P w else 0) := by
  have hR : 0 ≤ R := (hrange (Classical.choice ‹Nonempty X›)).1.trans (hrange _).2
  have hα0 : 0 < α := by linarith
  have ha : 0 ≤ α+β := by linarith
  have hd := hf.differentiable (by norm_num)
  obtain ⟨C,hC,hgrowth⟩ := profile_polynomial_growth (m := m) (κ := κ) hα hβ hR hB hd hb
  obtain ⟨Q,hQ,hG⟩ := q.closed_positive_polynomial hz hr hrange
    (profile_measurable hf.continuous.measurable) (profile_contDiffOn hf)
    (fun z _ => profile_zero hα0 z) (fun _ _ => profile_tendsto_zero hf.continuous hα0 hβ)
    (fun _ _ => profile_partial_r_tendsto_zero hf hα0 hβ) hC ha hgrowth P hp hm
    (q.weighted_gradient_memLp P hpow ha)
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hG] with w hw
  rw [hw]
  split_ifs with ht
  · rw [profileRD_eq hd ht,profileZD_eq hd ht]
  · rfl
end CAT0Fillings.ChartGeometry
end

end OAI
