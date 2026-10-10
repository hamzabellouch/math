import Mathlib

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_C11_hessian_limit_samples {f g : E → ℝ} {S : Set E}
    (hS : IsOpen S) {x0 : E} {Lf Lg : ℝ≥0}
    (hf : LipschitzOnWith Lf (fderiv ℝ f) S)
    (hg : LipschitzOnWith Lg (fderiv ℝ g) S) {P : E → Prop}
    (hselect : ∀ rho eta : ℝ, 0 < rho → 0 < eta → ∃ z∈S,
      dist z x0 < rho ∧ P z ∧ ‖fderiv ℝ f z+fderiv ℝ g z‖≤eta ∧
      ∀ e:E, fderiv ℝ (fderiv ℝ f) z e e+fderiv ℝ (fderiv ℝ g) z e e≤eta*‖e‖^2) :
    ∃ z : ℕ → E, ∃ A B : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ i,z i∈S ∧ P (z i)) ∧ Tendsto z atTop (𝓝 x0) ∧
      Tendsto (fun i => fderiv ℝ (fderiv ℝ f) (z i)) atTop (𝓝 A) ∧
      Tendsto (fun i => fderiv ℝ (fderiv ℝ g) (z i)) atTop (𝓝 B) ∧
      Tendsto (fun i => fderiv ℝ f (z i)+fderiv ℝ g (z i)) atTop (𝓝 0) ∧
      ∀ e:E,A e e+B e e≤0 := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let eps := fun i:ℕ => 1/((i:ℝ)+1)
  have heps : ∀ i,0 < eps i := fun i => by dsimp [eps]; positivity
  have heps0 : Tendsto eps atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose z hzS hdist hzP hgrad hquad using fun i => hselect (eps i) (eps i) (heps i) (heps i)
  let A := fun i => fderiv ℝ (fderiv ℝ f) (z i)
  let B := fun i => fderiv ℝ (fderiv ℝ g) (z i)
  have hA : ∀ i,‖A i‖≤Lf := fun i => norm_fderiv_le_of_lipschitzOn ℝ (hS.mem_nhds (hzS i)) hf
  have hB : ∀ i,‖B i‖≤Lg := fun i => norm_fderiv_le_of_lipschitzOn ℝ (hS.mem_nhds (hzS i)) hg
  have hcompact : IsCompact ((closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lf:ℝ)).prod
      (closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lg:ℝ))) := (isCompact_closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lf:ℝ)).prod
    (isCompact_closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lg:ℝ))
  obtain ⟨AB,hAB,σ,hσ,hlim⟩ := hcompact.tendsto_subseq (x := fun i => (A i,B i))
    (fun i => by
      change dist (A i) 0≤(Lf:ℝ) ∧ dist (B i) 0≤(Lg:ℝ)
      simpa only [dist_zero_right] using And.intro (hA i) (hB i))
  have hzlim : Tendsto z atTop (𝓝 x0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp heps0).2 ε hε] with i hi
    exact (hdist i).trans hi
  have hgradlim : Tendsto (fun i => fderiv ℝ f (z i)+fderiv ℝ g (z i)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hgrad heps0
  have hlimA : Tendsto (fun i => A (σ i)) atTop (𝓝 AB.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto AB).comp hlim
  have hlimB : Tendsto (fun i => B (σ i)) atTop (𝓝 AB.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto AB).comp hlim
  refine ⟨z ∘ σ,AB.1,AB.2,fun i => ⟨hzS (σ i),hzP (σ i)⟩,
    hzlim.comp hσ.tendsto_atTop,hlimA,hlimB,hgradlim.comp hσ.tendsto_atTop,?_⟩
  intro e
  have heval : Continuous (fun J : E →L[ℝ] E →L[ℝ] ℝ => J e e) :=
    (continuous_id.clm_apply (continuous_const (y := e))).clm_apply (continuous_const (y := e))
  have ha : Tendsto (fun i => A (σ i) e e) atTop (𝓝 (AB.1 e e)) := by
    simpa only [Function.comp_def] using (heval.tendsto AB.1).comp hlimA
  have hb : Tendsto (fun i => B (σ i) e e) atTop (𝓝 (AB.2 e e)) := by
    simpa only [Function.comp_def] using (heval.tendsto AB.2).comp hlimB
  have he : Tendsto (fun i => eps (σ i)*‖e‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_mul,Function.comp_def] using (heps0.comp hσ.tendsto_atTop).mul_const (‖e‖^2)
  exact le_of_tendsto_of_tendsto (ha.add hb) he (Filter.Eventually.of_forall (fun i => hquad (σ i) e))

end WeakMTWTransport

end

end OAI
