import OAI.Geometry.RCD.Transport.HopfDirichletSequence
import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds

namespace OAI

/-! # Sharp local-gradient recovery for every interior smooth Euclidean test

The functions belong to the actual source Dirichlet spaces. Their values
converge uniformly almost everywhere, and their rescaled minimal gradients
are bounded by the differential of the target test plus an arbitrary error.
-/

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.sharp_test_recovery_sequence_supported {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    ∃ c : ℝ, 0<c ∧ c<S ∧ ∃ N : ℕ, ∃ w : ∀ k : ℕ, SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
        (ball (p (k+N)) (S*r (k+N))),
      (∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (S*r (k+N))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k).val x-ψ (v (k+N) x)|≤η) ∧
      (∀ ρ : ℝ, 0≤ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (ρ*r (k+N))),
          r (k+N)*SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (w k).val x≤
            ‖fderiv ℝ ψ (v (k+N) x)‖+η) ∧
      ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p (k+N)) (c*r (k+N)) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k).val x=0 := by
  obtain ⟨ρ,hρ,hρS,M,B,hψL,hψB,hψ0⟩ := hψ.metric_bounds hS
  let a := (2*ρ+S)/3
  let b := (ρ+2*S)/3
  have hρa : ρ<a := by dsimp only [a]; linarith
  have hab : a<b := by dsimp only [a,b]; linarith
  have hbS : b<S := by dsimp only [b]; linarith
  have hev := (hεlim.eventually (Iio_mem_nhds zero_lt_one)).and
    (hεlim.eventually (Iio_mem_nhds (show 0<(a-ρ)/3 by linarith)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  have hsmall (k : ℕ) : ε (k+N)<1 ∧ 2*ε (k+N)<a-ρ := by
    have hh := hN (k+N) (Nat.le_add_left N k)
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hrec (k : ℕ) := compact_pointed_test_recovery_support (hr (k+N)) hρ.le hρa hab hbS
    (hε (k+N)) (hsmall k).2 B.coe_nonneg (hv (k+N)).metric hψL hψB hψ0
  choose F L hFL hFC hFs hFb hL hFe using hrec
  let C : ℝ := M+((B:ℝ)+M)/(b-a)
  have hCM : (M:ℝ)≤C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (div_nonneg (add_nonneg B.coe_nonneg M.coe_nonneg)
      (sub_pos.mpr hab).le)
  have hC : 0≤C := M.coe_nonneg.trans hCM
  let D : ℝ≥0 := ⟨C,hC⟩
  have hF' (k : ℕ) : LipschitzWith ⟨(D:ℝ)/r (k+N),div_nonneg D.coe_nonneg (hr (k+N)).le⟩ (F k) := by
    apply (hFL k).weaken
    have hc : r (k+N)*(L k:ℝ)≤C := (hL k).trans (by
      dsimp only [C]
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
      exact add_le_add le_rfl (mul_le_of_le_one_right M.coe_nonneg (hsmall k).1.le))
    have hd : (L k:ℝ)≤C/r (k+N) := (le_div_iff₀ (hr (k+N))).mpr (by simpa only [mul_comm] using hc)
    exact_mod_cast hd
  have hψD : LipschitzWith D ψ := hψL.weaken (by exact_mod_cast hCM)
  have he' (k : ℕ) (x : X) (hx : dist x (p (k+N))≤S*r (k+N)) :
      |F k x-ψ (v (k+N) x)|≤(D:ℝ)*ε (k+N) :=
    (hFe k x hx).trans (mul_le_mul_of_nonneg_right hCM (hε (k+N)))
  let c := (b+S)/2
  have hbc : b<c := by dsimp only [c]; linarith
  have hcS : c<S := by dsimp only [c]; linarith
  obtain ⟨J,w,hw,hgrad,hzero⟩ := hX.hopf_dirichlet_sequence_supported hbc hcS (hψ.1.of_le (by simp)) hψ.2.1 hψD
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N)) (fun k => v (k+N)) F
    (fun k => hr (k+N)) (fun k => hε (k+N)) (hεlim.comp (tendsto_add_atTop_nat N))
    (fun k => (hv (k+N)).metric) hF' hFs he'
  refine ⟨c,by dsimp only [c]; linarith, hcS,J+N,?_⟩
  let w' : ∀ k : ℕ, SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
      (ball (p (k+(J+N))) (S*r (k+(J+N)))) := fun k =>
    ⟨(w k).val,by simpa only [Nat.add_assoc] using (w k).property⟩
  refine ⟨w',?_,?_,?_⟩
  · simpa only [w',Nat.add_assoc] using hw
  · simpa only [w',Nat.add_assoc] using hgrad
  · simpa only [w',Nat.add_assoc] using hzero

end RegularPointCoordinates

end

end OAI
