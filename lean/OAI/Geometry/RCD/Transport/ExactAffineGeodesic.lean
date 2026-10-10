import OAI.Geometry.RCD.Transport.NearbyAffineGeodesic

namespace OAI

/-! # Affine harmonic-coordinate geodesics between prescribed nearby points -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem exists_exact_affine_geodesic {R : ℝ} (hR : 1 ≤ R)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    {b : ℝ} (hb : 50*R < b)
    (hu : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun x => v x i)
    (hH : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) (u i))
    (L : Fin n → ℝ≥0) (hL : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x ≤ (L i:ℝ)^2)
    (c : Fin n → ℝ) (hc : ∀ i, localGamma (hausdorff n X) hX.quadratic (u i) (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c i)
    (hv : ContinuousOn v (ball p b))
    {x y : X} (hx : dist x p ≤ R/2) (hy : dist y p ≤ R/2) :
    ∃ γ : C(Time,X), IsGeodesic γ ∧ γ 0=x ∧ γ 1=y ∧
      (∀ t : Time, dist (γ t) p ≤ 3*R) ∧
      ∀ t : Time, v (γ t)=(1-(t:ℝ)) • v x+(t:ℝ) • v y := by
  have hR0 : 0<R := by linarith
  let ρ : ℕ → ℝ := fun k => (R/2)*heatStep k
  have hρ (k : ℕ) : 0<ρ k := mul_pos (by positivity) (heatStep_pos k)
  have hρR (k : ℕ) : ρ k≤R/2 := by
    apply mul_le_of_le_one_right (by positivity)
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    simpa only [mul_zero] using heatStep_tendsto.const_mul (R/2)
  choose γ hgeo h₀ h₁ hstay haff using fun k =>
    hX.exists_nearby_affine_geodesic hn p hR u v hb hu hH L hL c hc hv
      (hρ k) (hρR k) hx hy
  obtain ⟨η,hη,j,hj,hlim⟩ := (isCompact_bounded_geodesics p (by positivity : 0≤3*R)).tendsto_subseq
    (fun k => show IsGeodesic (γ k) ∧ ∀ t, dist (γ k t) p≤3*R from ⟨hgeo k,hstay k⟩)
  have heval (t : Time) : Tendsto (fun k => γ (j k) t) atTop (𝓝 (η t)) :=
    ((continuous_eval_const t).tendsto η).comp hlim
  have hzero : η 0=x := by
    have hz : Tendsto (fun k => dist (γ (j k) 0) x) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun k => (h₀ (j k)).le)
        (hρlim.comp hj.tendsto_atTop)
    exact dist_eq_zero.mp (tendsto_nhds_unique ((heval 0).dist tendsto_const_nhds) hz)
  have hone : η 1=y := by
    have hz : Tendsto (fun k => dist (γ (j k) 1) y) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun k => (h₁ (j k)).le)
        (hρlim.comp hj.tendsto_atTop)
    exact dist_eq_zero.mp (tendsto_nhds_unique ((heval 1).dist tendsto_const_nhds) hz)
  have hvlim (t : Time) : Tendsto (fun k => v (γ (j k) t)) atTop (𝓝 (v (η t))) := by
    have hm : η t∈ball p b := by
      rw [mem_ball]
      exact (hη.2 t).trans_lt (by linarith)
    exact (hv.continuousAt (isOpen_ball.mem_nhds hm)).tendsto.comp (heval t)
  refine ⟨η,hη.1,hzero,hone,hη.2,?_⟩
  intro t
  have hh := ((hvlim 0).const_smul (1-(t:ℝ))).add ((hvlim 1).const_smul (t:ℝ))
  rw [hzero,hone] at hh
  apply tendsto_nhds_unique (hvlim t)
  exact hh.congr' (Filter.Eventually.of_forall fun k => (haff (j k) t).symm)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
