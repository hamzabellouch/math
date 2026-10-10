import Mathlib
import OAI.Geometry.IntegralFillings.Currents.WeakMass

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]
lemma summable_actions_of_summable_masses [CompactSpace X]
    {k : ℕ} {Ts : ℕ → Functional X k} (hTs : ∀ j, IsMetricCurrent (Ts j))
    (hsum : Summable fun j => mass (Ts j)) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) : Summable fun j => Ts j b π := by
  choose K hK using h.2
  obtain ⟨M, hM⟩ := h.1.2
  apply (hsum.mul_left ((∏ i, (K i : ℝ)) * M)).of_norm_bounded
  intro j
  exact (hTs j).mass_bound_uniform h.1 K hK hM

end Foundations

lemma tendsto_of_lipschitz_dense {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {κ : Type*} {D : κ → A} (hD : DenseRange D)
    (hlim : ∀ i, Tendsto (fun j => f j (D i)) l (𝓝 (g (D i))))
    (x : A) : Tendsto (fun j => f j x) l (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨i, hi⟩ := hD.exists_dist_lt x hδ
  have hdr : (K : ℝ) * dist x (D i) < ε / 4 := by
    have hpos : 0 < (K : ℝ) + 1 := by positivity
    have hm := (mul_lt_mul_of_pos_left hi hpos)
    have heq : ((K : ℝ) + 1) * δ = ε / 4 := by
      dsimp [δ]
      field_simp
    rw [heq] at hm
    calc (K : ℝ) * dist x (D i) ≤ ((K : ℝ) + 1) * dist x (D i) := by
          nlinarith [dist_nonneg (x := x) (y := D i)]
      _ < _ := hm
  filter_upwards [(Metric.tendsto_nhds.mp (hlim i)) (ε / 2) (half_pos hε)] with j hj
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j (D i)) + dist (f j (D i)) (g (D i)) + dist (g (D i)) (g x) :=
        (dist_triangle _ (g (D i)) _).trans (add_le_add (dist_triangle _ (f j (D i)) _) le_rfl)
    _ < ε / 4 + ε / 2 + ε / 4 := by
      apply add_lt_add
      · exact add_lt_add ((hf j).dist_le_mul x (D i) |>.trans_lt hdr) hj
      · rw [dist_comm]
        exact (hg.dist_le_mul x (D i)).trans_lt hdr
    _ = ε := by ring

namespace BorelCoefficients

variable {X : Type u} [MetricSpace X] [CompactSpace X]

def lipAlgebra : Subalgebra ℝ C(X, ℝ) where
  carrier := {f | BoundedLip f}
  algebraMap_mem' r := BoundedLip.const r
  add_mem' hf hg := BoundedLip.add hf hg
  mul_mem' hf hg := BoundedLip.mul hf hg

lemma lipAlgebra_separates : (lipAlgebra (X := X)).SeparatesPoints := by
  intro x y hxy
  let f : C(X, ℝ) := ⟨fun z => dist z x, continuous_id.dist continuous_const⟩
  have hf : BoundedLip f := by
    refine ⟨⟨1, LipschitzWith.dist_left x⟩, ‖f‖, ?_⟩
    intro z
    exact (ContinuousMap.norm_coe_le_norm f z)
  refine ⟨f, ⟨f, hf, rfl⟩, ?_⟩
  change dist x x ≠ dist y x
  simpa only [dist_self, ne_eq, eq_comm, dist_eq_zero] using hxy.symm

lemma lipAlgebra_dense : DenseRange (fun f : lipAlgebra (X := X) => (f : C(X, ℝ))) := by
  rw [denseRange_iff_closure_range]
  rw [Subtype.range_coe_subtype]
  change closure (lipAlgebra (X := X) : Set C(X, ℝ)) = univ
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (lipAlgebra (X := X)) lipAlgebra_separates
  exact congrArg (fun A : Subalgebra ℝ C(X, ℝ) => (A : Set C(X, ℝ))) h

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def lipToL1 : lipAlgebra (X := X) →ₗ[ℝ] Lp ℝ 1 μ :=
  (ContinuousMap.toLp 1 μ ℝ).toLinearMap.comp (lipAlgebra (X := X)).val.toLinearMap

lemma lipToL1_dense : DenseRange (lipToL1 μ) := by
  apply (ContinuousMap.toLp_denseRange ℝ μ ℝ (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp
    lipAlgebra_dense (ContinuousMap.toLp 1 μ ℝ).continuous

lemma norm_lipToL1 (f : lipAlgebra (X := X)) :
    ‖lipToL1 μ f‖ = ∫ x, |f.val x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val] with x hx
  change ‖(ContinuousMap.toLp 1 μ ℝ f.val) x‖ = |f.val x|
  rw [hx, Real.norm_eq_abs]

lemma exists_lipschitz_approximation {b : X → ℝ} (hb : Integrable b μ) :
    ∃ f : ℕ → lipAlgebra (X := X),
      Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂μ) atTop (𝓝 0) := by
  obtain ⟨u,hu,hulim⟩ := mem_closure_iff_seq_limit.mp ((lipToL1_dense μ) hb.toL1)
  choose f hf using hu
  have hfun : (fun j => lipToL1 μ (f j)) = u := funext hf
  have hf := hfun ▸ hulim
  refine ⟨f,?_⟩
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero).mp hf
  convert hnorm using 1
  funext j
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (lipToL1 μ (f j)) hb.toL1,
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (f j).val,
    hb.coeFn_toL1] with x hx hfx hbx
  change |(f j).val x-b x| = ‖(lipToL1 μ (f j)-hb.toL1) x‖
  rw [hx]
  change _ = ‖(ContinuousMap.toLp 1 μ ℝ (f j).val) x - (hb.toL1) x‖
  rw [hfx,hbx,Real.norm_eq_abs]

lemma test_inequality_of_lipschitz
    {ν : Measure X} [IsFiniteMeasure ν] (hν : ν ≤ μ)
    (A : (X → ℝ) → ℝ) {C : ℝ}
    (hA : ∀ f g, Integrable f μ → Integrable g μ →
      |A f-A g| ≤ C * ∫ x, |f x-g x| ∂μ)
    (hbound : ∀ f, BoundedLip f → |A f| ≤ ∫ x, |f x| ∂ν)
    {b : X → ℝ} (hb : Integrable b μ) :
    |A b| ≤ ∫ x, |b x| ∂ν := by
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation μ hb
  have hfi (j : ℕ) : Integrable ((f j).val) μ :=
    (f j).val.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hflim : Tendsto (fun j => A (f j).val) atTop (𝓝 (A b)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) (by simpa using hf.const_mul C)
    simpa only [Real.dist_eq] using hA _ _ (hfi j) hb
  have hib : Integrable b ν := hb.mono_measure hν
  have hfint : Tendsto (fun j => ∫ x, |(f j).val x| ∂ν) atTop (𝓝 (∫ x, |b x| ∂ν)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq,←integral_sub ((hfi j).mono_measure hν).abs hib.abs]
    calc |∫ x, |(f j).val x|-|b x| ∂ν| ≤ ∫ x, abs (|(f j).val x|-|b x|) ∂ν := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun x => |(f j).val x|-|b x|)
      _ ≤ ∫ x, |(f j).val x-b x| ∂ν :=
          integral_mono_ae (((hfi j).mono_measure hν).abs.sub hib.abs).abs
            (((hfi j).mono_measure hν).sub hib).abs
            (Eventually.of_forall fun x => abs_abs_sub_abs_le _ _)
      _ ≤ ∫ x, |(f j).val x-b x| ∂μ :=
          integral_mono_measure hν (Eventually.of_forall fun _ => abs_nonneg _)
            ((hfi j).sub hb).abs
  exact le_of_tendsto_of_tendsto hflim.abs hfint
    (Eventually.of_forall fun j => hbound _ (f j).property)

end BorelCoefficients
end SharpIntegralFillings

end

end OAI
