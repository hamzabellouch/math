import OAI.Analysis.HotSpots.GreenSolution

namespace OAI

section ConformalSmoothEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal

lemma complex_real_inner_mul (a u v : ℂ) :
    inner ℝ (a*u) (a*v) = ‖a‖^2 * inner ℝ u v := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.normSq_apply]
  ring

lemma plane_inner_gradient_comp {f : Plane → Plane} {u v : Plane → ℝ}
    {a : ℂ} {x : Plane} (hf : HasFDerivAt f (planeMul a) x)
    (hu : DifferentiableAt ℝ u (f x)) (hv : DifferentiableAt ℝ v (f x)) :
    inner ℝ (gradient (u ∘ f) x) (gradient (v ∘ f) x) =
      ‖a‖^2 * inner ℝ (gradient u (f x)) (gradient v (f x)) := by
  rw [plane_gradient_comp hf hu,plane_gradient_comp hf hv,coordinate.inner_map_map,
    complex_real_inner_mul,Complex.norm_conj,coordinate.symm.inner_map_map]

lemma plane_dirichlet_pair (e : OpenPartialHomeomorph Plane Plane)
    (d : Plane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {u v : Plane → ℝ} (hu : DifferentiableOn ℝ u e.target) (hv : DifferentiableOn ℝ v e.target) :
    (∫ y in e.target, inner ℝ (gradient u y) (gradient v y)) =
      ∫ x in e.source, inner ℝ (gradient (u ∘ e) x) (gradient (v ∘ e) x) := by
  rw [plane_integral_target e d hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  exact (plane_inner_gradient_comp (hd x hx)
    ((hu _ (e.map_source hx)).differentiableAt (e.open_target.mem_nhds (e.map_source hx)))
    ((hv _ (e.map_source hx)).differentiableAt (e.open_target.mem_nhds (e.map_source hx)))).symm

lemma inner_grad_toH1 {Ω : Set Plane} {u v : Plane → ℝ}
    (hu : HasH1Gradient Ω u (gradient u)) (hv : HasH1Gradient Ω v (gradient v)) :
    inner ℝ (H1.grad hu.toH1) (H1.grad hv.toH1) =
      ∫ x in Ω, inner ℝ (gradient u x) (gradient v x) := by
  rw [H1.grad_toH1,H1.grad_toH1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.2.1.coeFn_toLp,hv.2.1.coeFn_toLp] with x hx hy
  rw [hx,hy]

lemma inner_grad_test {Ω : Set Plane} (ho : IsOpen Ω) {w : Plane → ℝ}
    (hW : HasH1Gradient Ω w (gradient w)) (f : smoothTestSpace Ω) :
    inner ℝ (H1.grad hW.toH1) (H10.grad ho (smoothTestToH10 ho f)) =
      ∫ x in Ω, inner ℝ (gradient w x) (gradient (f : Plane → ℝ) x) := by
  change inner ℝ (H1.grad hW.toH1)
    (H1.grad ((HasH1Gradient.test ho f.property.1 f.property.2.1).toH1)) = _
  exact inner_grad_toH1 hW (HasH1Gradient.test ho f.property.1 f.property.2.1)

variable (e : OpenPartialHomeomorph Plane Plane)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target)

include d hd in
lemma transportTest_dirichlet_pair {w : Plane → ℝ}
    (hw : DifferentiableOn ℝ w e.target) (f : smoothTestSpace e.source) :
    (∫ x in e.target, inner ℝ (gradient w x) (gradient (transportTest e he f : Plane → ℝ) x)) =
      ∫ x in e.source, inner ℝ (gradient (w ∘ e) x) (gradient (f : Plane → ℝ) x) := by
  calc
    _ = ∫ x in e.source, inner ℝ (gradient (w ∘ e) x)
        (gradient ((transportTest e he f : Plane → ℝ) ∘ e) x) :=
      plane_dirichlet_pair e d hd hw
        ((transportTest e he f).property.1.differentiable (by simp)).differentiableOn
    _ = _ := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      have hg : gradient ((CompactChart.transport e f) ∘ e) x = gradient (f : Plane → ℝ) x := by
        unfold gradient
        rw [(CompactChart.transport_comp_eventuallyEq e (f:=f) hx).fderiv_eq]
      exact congrArg (fun a : Plane => inner ℝ (gradient (w ∘ e) x) a) hg

include d hd in
lemma transportTest_mixed_grad {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (f : smoothTestSpace e.source) :
    inner ℝ (H1.grad hW.toH1)
      (H10.grad e.open_target (smoothTestToH10 e.open_target (transportTest e he f))) =
      inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source (smoothTestToH10 e.open_source f)) :=
  (inner_grad_test e.open_target hW (transportTest e he f)).trans
    ((transportTest_dirichlet_pair e he d hd hw f).trans (inner_grad_test e.open_source hV f).symm)

include d hd hb in


lemma transportH10_mixed_grad {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target (transportH10 e he v)) =
      inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source v) := by
  have H : (fun v : H10 e.open_source =>
      inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target (transportH10 e he v))) =
      (fun v : H10 e.open_source => inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source v)) := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      (continuous_const.inner ((H10.grad e.open_target).continuous.comp (transportH10 e he).continuous))
      (continuous_const.inner (H10.grad e.open_source).continuous)
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (fun z : H10 e.open_target =>
      inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target z))
      (transportH10_test e he d hd hb f)).trans (transportTest_mixed_grad e he d hd hw hW hV f)
  exact congrFun H v

end StrictHotSpots.Conformal
end
end ConformalSmoothEnergy

section ConformalAffine

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

include d hd in
lemma smooth_pair_grad {w z : Plane → ℝ}
    (hw : DifferentiableOn ℝ w e.target) (hz : DifferentiableOn ℝ z e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hZ : HasH1Gradient e.target z (gradient z))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (hU : HasH1Gradient e.source (z ∘ e) (gradient (z ∘ e))) :
    inner ℝ (H1.grad hW.toH1) (H1.grad hZ.toH1) =
      inner ℝ (H1.grad hV.toH1) (H1.grad hU.toH1) :=
  (inner_grad_toH1 hW hZ).trans ((plane_dirichlet_pair e d hd hw hz).trans
    (inner_grad_toH1 hV hU).symm)

lemma inner_sum_pair {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a b c d : E) (a' b' c' d' : F)
    (h00 : inner ℝ a c = inner ℝ a' c') (h01 : inner ℝ a d = inner ℝ a' d')
    (h10 : inner ℝ c b = inner ℝ c' b') (h11 : inner ℝ b d = inner ℝ b' d') :
    inner ℝ (a+b) (c+d) = inner ℝ (a'+b') (c'+d') := by
  simp only [inner_add_left,inner_add_right]
  have ht : inner ℝ b c = inner ℝ b' c' :=
    (real_inner_comm _ _).trans (h10.trans (real_inner_comm _ _))
  rw [h00,h01,h11,ht]

lemma inner_H1grad_add {S : Set Plane} (a b c d : H1 S) :
    inner ℝ (H1.grad (a+b)) (H1.grad (c+d)) =
      inner ℝ (H1.grad a+H1.grad b) (H1.grad c+H1.grad d) := by
  rw [map_add,map_add]

include d hd hb in
lemma affine_grad_pair {w z : Plane → ℝ}
    (hw : DifferentiableOn ℝ w e.target) (hz : DifferentiableOn ℝ z e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hZ : HasH1Gradient e.target z (gradient z))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (hU : HasH1Gradient e.source (z ∘ e) (gradient (z ∘ e)))
    (v u : H10 e.open_source) :
    inner ℝ (H1.grad (hW.toH1+(transportH10 e he v).val))
      (H1.grad (hZ.toH1+(transportH10 e he u).val)) =
    inner ℝ (H1.grad (hV.toH1+v.val)) (H1.grad (hU.toH1+u.val)) := by
  have h00 := smooth_pair_grad e d hd hw hz hW hZ hV hU
  have h01 := transportH10_mixed_grad e he d hd hb hw hW hV u
  have h10 := transportH10_mixed_grad e he d hd hb hz hZ hU v
  have h11 := transportH10_inner_grad e he d hd hb v u
  exact (inner_H1grad_add hW.toH1 (transportH10 e he v).val
    hZ.toH1 (transportH10 e he u).val).trans
    ((inner_sum_pair _ _ _ _ _ _ _ _ h00 h01 h10 h11).trans
      (inner_H1grad_add hV.toH1 v.val hU.toH1 u.val).symm)

lemma pull_affine_value {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w)) (v : H10 e.open_source) :
    chartPull e d hd (H1.value (hW.toH1+(transportH10 e he v).val)) =
      chartPull e d hd (H1.value hW.toH1)+weightedValue e he d hd v := by
  exact (chartPull e d hd).map_add (H1.value hW.toH1)
    (H1.value (transportH10 e he v).val)

lemma value_add_H10 {S : Set Plane} (ho : IsOpen S) (a : H1 S) (v : H10 ho) :
    H1.value (a+v.val) = H1.value a+H10.value ho v := H1.value.map_add a v.val

lemma ae_lp_sums {μ ν : Measure Plane} (ha : μ ≪ ν)
    (a b : Lp ℝ 2 μ) (c d : Lp ℝ 2 ν)
    (hac : (a : Plane → ℝ) =ᵐ[μ] c) (hbd : (b : Plane → ℝ) =ᵐ[μ] d) :
    (a+b : Lp ℝ 2 μ) =ᵐ[μ] (c+d : Lp ℝ 2 ν) :=
  (Lp.coeFn_add a b).trans ((hac.add hbd).trans (Filter.EventuallyEq.symm (ha.ae_le (Lp.coeFn_add c d))))

include hb in
lemma affine_value_ae {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    (chartPull e d hd (H1.value (hW.toH1+(transportH10 e he v).val)) : Plane → ℝ)
      =ᵐ[chartMeasure e d] H1.value (hV.toH1+v.val) := by
  have ha := chartPull_test_ae e d hd hW.1
  have hc := (chartMeasure_ac e d).ae_le hV.1.coeFn_toLp
  have hv := weightedValue_ae e he d hd hb v
  have hs := ae_lp_sums (chartMeasure_ac e d)
    (chartPull e d hd (H1.value hW.toH1)) (weightedValue e he d hd v)
    (H1.value hV.toH1) (H10.value e.open_source v) (ha.trans (Filter.EventuallyEq.symm hc)) hv.symm
  exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 (chartMeasure e d) => (f : Plane → ℝ))
    (pull_affine_value e he d hd hW v))).trans
    (hs.trans (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 (volume.restrict e.source) =>
      (f : Plane → ℝ)) (value_add_H10 e.open_source hV.toH1 v))).symm)

lemma isometry_value_pair {μ ν : Measure Plane}
    (L : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) (a b : Lp ℝ 2 μ) {f g : Plane → ℝ}
    (ha : (L a : Plane → ℝ) =ᵐ[ν] f) (hb : (L b : Plane → ℝ) =ᵐ[ν] g) :
    inner ℝ a b = ∫ x, f x*g x ∂ν := by
  apply (L.inner_map_map a b).symm.trans
  apply (L2.inner_def _ _).trans
  apply integral_congr_ae
  filter_upwards [ha,hb] with x hx hy
  rw [hx,hy,Real.inner_apply,mul_comm]

include hd hb in
lemma affine_value_pair {w z : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hZ : HasH1Gradient e.target z (gradient z))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (hU : HasH1Gradient e.source (z ∘ e) (gradient (z ∘ e)))
    (v u : H10 e.open_source) :
    inner ℝ (H1.value (hW.toH1+(transportH10 e he v).val))
      (H1.value (hZ.toH1+(transportH10 e he u).val)) =
      ∫ x, H1.value (hV.toH1+v.val) x*H1.value (hU.toH1+u.val) x ∂chartMeasure e d :=
  isometry_value_pair (chartPull e d hd) _ _
    (affine_value_ae e he d hd hb hW hV v) (affine_value_ae e he d hd hb hZ hU u)

end StrictHotSpots.Conformal
end
end ConformalAffine

section ActualPotential

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.Conformal
open DiskH10

lemma potentialMeasure_bounded {e : OpenPartialHomeomorph Plane Plane} {d : Plane → ℂ}
    {μ B : ℝ} (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hd : ∀ x ∈ e.source, ‖d x‖ ≤ B) :
    potentialMeasure e d μ ≤ ENNReal.ofReal (μ*B^2) • volume.restrict e.source := by
  rw [potentialMeasure_density e d hμ, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hB |>.mpr (hd x hx)) hμ

lemma subcritical_reindex {S T : Set Plane} (ho : IsOpen S) (ho' : IsOpen T)
    (hST : S = T) {ν : Measure Plane} {δ : ℝ}
    (h : ∀ v : H10 ho, (∫ x, (H10.value ho v x)^2 ∂ν) ≤ δ*‖H10.grad ho v‖^2) :
    ∀ v : H10 ho', (∫ x, (H10.value ho' v x)^2 ∂ν) ≤ δ*‖H10.grad ho' v‖^2 := by
  cases hST
  exact h

namespace ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

def potential : Measure Plane := potentialMeasure c.e c.d (firstPositiveNeumannValue Ω)
def densityBound : ℝ≥0∞ := ENNReal.ofReal (firstPositiveNeumannValue Ω*c.bound^2)

lemma density_bound (hμ : 0 ≤ firstPositiveNeumannValue Ω) :
    c.potential ≤ c.densityBound • volume.restrict disk := by
  have h := potentialMeasure_bounded hμ c.bound_pos.le c.bounded_deriv
  simpa only [potential,densityBound,c.source_eq] using h

lemma densityBound_ne_top : c.densityBound ≠ ∞ := ENNReal.ofReal_ne_top

lemma potential_finite (hb : Bornology.IsBounded Ω) : IsFiniteMeasure c.potential :=
  potentialMeasure_finite c.e c.d c.deriv _ (c.target_eq.symm ▸ hb)



theorem subcritical (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hμ : 0 < firstPositiveNeumannValue Ω) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ v : H10 PlaneGreen.diskOpen,
      ‖H10.weightedValue PlaneGreen.diskOpen c.densityBound_ne_top (c.density_bound hμ.le) v‖^2 ≤
        δ*‖H10.grad PlaneGreen.diskOpen v‖^2 := by
  have hh := potentialMeasure_subcritical c.e c.d c.deriv c.inverse_smooth
    (c.target_eq.symm ▸ hb) (c.target_eq.symm ▸ hne) (c.target_eq.symm ▸ hμ)
  obtain ⟨δ,hδ,hδ1,hsub⟩ := hh
  have hs := subcritical_reindex c.e.open_source PlaneGreen.diskOpen c.source_eq hsub
  have hs' : ∀ v : H10 PlaneGreen.diskOpen,
      (∫ x, (H10.value PlaneGreen.diskOpen v x)^2 ∂c.potential) ≤ δ*‖H10.grad PlaneGreen.diskOpen v‖^2 := by
    simpa only [potential,c.target_eq] using hs
  refine ⟨δ,hδ,hδ1,fun v => ?_⟩
  rw [L2Limits.norm_sq_eq_integral_sq]
  have he := H10.weightedValue_ae PlaneGreen.diskOpen c.densityBound_ne_top (c.density_bound hμ.le) v
  exact (integral_congr_ae (he.fun_comp (fun t : ℝ => t^2))).le.trans (hs' v)



theorem operator_norm_lt_one (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hμ : 0 < firstPositiveNeumannValue Ω) :
    ‖PlaneGreen.weightedIntegralOperator c.densityBound_ne_top (c.density_bound hμ.le)‖ < 1 := by
  obtain ⟨δ,hδ,hδ1,hsub⟩ := c.subcritical hb hne hμ
  exact (PlaneGreen.weightedIntegralOperator_norm_le c.densityBound_ne_top
    (c.density_bound hμ.le) hδ.le hsub).trans_lt hδ1

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualPotential

section ActualScalarPull

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal Laplacian
namespace StrictHotSpots.Conformal

lemma observe_inner {S : Set Plane} {ν : Measure Plane} {C : ℝ≥0∞}
    (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict S) (u v : H1 S) :
    inner ℝ (SubcriticalExtension.observe hC hν u) (SubcriticalExtension.observe hC hν v) =
      ∫ x, H1.value u x * H1.value v x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value u),
    Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value v)] with x hx hy
  change inner ℝ (Lp.LpToLpOfMeasureLeSMul hC hν (H1.value u) x)
    (Lp.LpToLpOfMeasureLeSMul hC hν (H1.value v) x) = _
  rw [hx,hy,real_inner_comm]
  rfl

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

include d hd hb in
lemma smooth_H10_value_pair {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    inner ℝ (H1.value hW.toH1) (H10.value e.open_target (transportH10 e he v)) =
      ∫ x, H1.value hV.toH1 x * H10.value e.open_source v x ∂chartMeasure e d := by
  apply isometry_value_pair (chartPull e d hd)
  · have ha : (H1.value hV.toH1 : Plane → ℝ) =ᵐ[chartMeasure e d] w ∘ e :=
      (chartMeasure_ac e d).ae_le hV.1.coeFn_toLp
    exact (chartPull_test_ae e d hd hW.1).trans ha.symm
  · exact (weightedValue_ae e he d hd hb v).symm

namespace ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma potential_diskMap : potentialMeasure c.diskMap c.d (firstPositiveNeumannValue Ω) =
    c.potential := congrArg (fun e => potentialMeasure e c.d (firstPositiveNeumannValue Ω)) c.diskMap_eq

lemma smooth_mixed_mass (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hμ : 0 ≤ firstPositiveNeumannValue Ω) (v : H10 diskOpen) :
    inner ℝ (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (c.pullDatum_H1 hb hs hw).toH1)
      (H10.weightedValue diskOpen c.densityBound_ne_top (c.density_bound hμ) v) =
    firstPositiveNeumannValue Ω * inner ℝ
      (H1.value (smooth_closure_H1 c.diskMap.open_target hb hs hw).toH1)
      (H10.value c.diskMap.open_target (transportH10 c.diskMap c.diskMap_inverse_smooth v)) := by
  have hh := smooth_H10_value_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    (smooth_closure_H1 c.diskMap.open_target hb hs hw) (c.pullDatum_comp_H1 hb hs hw) v
  have hr := congrArg (fun U : H1 disk =>
    ∫ x, H1.value U x * H10.value diskOpen v x ∂chartMeasure c.diskMap c.d)
    (c.pullDatum_comp_toH1 hb hs hw)
  change inner ℝ (SubcriticalExtension.observe _ _ _) (SubcriticalExtension.observe _ _ v.val) = _
  apply (observe_inner c.densityBound_ne_top (c.density_bound hμ)
    (c.pullDatum_H1 hb hs hw).toH1 v.val).trans
  have hq := congrArg (fun ν : Measure Plane => ∫ x,
    H1.value (c.pullDatum_H1 hb hs hw).toH1 x * H10.value diskOpen v x ∂ν)
    c.potential_diskMap
  exact hq.symm.trans ((potentialMeasure_integral c.diskMap c.d hμ _).trans
    (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) (hh.trans hr).symm))

lemma smooth_pull_weak (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hμ : 0 ≤ firstPositiveNeumannValue Ω)
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) :
    SubcriticalExtension.WeakPotential diskOpen c.densityBound_ne_top (c.density_bound hμ)
      (c.pullDatum_H1 hb hs hw).toH1 := by
  intro v
  have hW := smooth_closure_H1 c.diskMap.open_target hb hs hw
  have hh := transportH10_mixed_grad c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    ((hw.mono subset_closure).differentiableOn (by simp)) hW (c.pullDatum_comp_H1 hb hs hw) v
  have hr := congrArg (fun U : H1 disk => inner ℝ (H1.grad U) (H10.grad diskOpen v))
    (c.pullDatum_comp_toH1 hb hs hw)
  have he := H10.helmholtz_pair c.diskMap.open_target (hw.mono subset_closure) hW.1 hW.2.1 hp
    (transportH10 c.diskMap c.diskMap_inverse_smooth v)
  exact (hh.trans hr).symm.trans (he.trans (c.smooth_mixed_mass hb hs hw hμ v).symm)



theorem smooth_K_representation (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    (hne : Ω.Nonempty) (hμ : 0 < firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) (x : disk) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    w (c.F x) = ∫ s, fullBoundaryK c.densityBound_ne_top (c.density_bound hμ.le) x s *
      w (c.F s) ∂boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hb
  obtain ⟨δ,hδ,hδ1,hsub⟩ := c.subcritical hb hne hμ
  obtain ⟨B,hB⟩ := c.datumTrace_lipschitz hb hs hw
  exact value_K_of_trace c.densityBound_ne_top (c.density_bound hμ.le) hδ.le hδ1 hsub
    (c.datumTrace w hw.continuousOn) hB (c.pullDatum_smooth (hw.mono subset_closure))
    (c.pullDatum_continuous hw.continuousOn) (c.pullDatum_H1 hb hs hw) (fun _ => rfl)
    (c.smooth_pull_weak hb hs hw hμ.le hp) x

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualScalarPull

section OriginalGradientKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Laplacian
namespace StrictHotSpots
lemma laplacian_continuousOn {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) : ContinuousOn (Δ f) Ω := by
  have hh : ContinuousOn (fun x => ∑ i : Fin 2,
      directionalDerivative (directionalDerivative f (planeBasis i)) (planeBasis i) x) Ω :=
    continuousOn_finsetSum _ fun i _ =>
      (directionalDerivative_contDiffOn hΩ
        (directionalDerivative_contDiffOn hΩ hf (planeBasis i)) (planeBasis i)).continuousOn
  exact hh.congr fun x hx => (laplacian_eq_sum_directional hΩ hf hx)



lemma eigenfunction_helmholtz {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) {x : Plane} (hx : x ∈ Ω) :
    (Δ u) x + firstPositiveNeumannValue Ω * u x = 0 := by
  have hsu : ContDiffOn ℝ ∞ u Ω := hu.1.mono subset_closure
  have hcont : ContinuousOn (fun y => (Δ u) y + firstPositiveNeumannValue Ω * u y) Ω :=
    (laplacian_continuousOn hΩ hsu).add (hsu.continuousOn.const_mul _)
  have hae := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hΩ.measurableSet (μ := volume)) ?_
  · have hre : (fun y => (Δ u) y + firstPositiveNeumannValue Ω * u y) =ᵐ[volume.restrict Ω]
        (fun _ => 0) := (ae_restrict_iff' hΩ.measurableSet).mpr hae
    exact (Measure.eqOn_open_of_ae_eq hre hΩ hcont continuousOn_const) hx
  intro φ hφ hc hs
  have htest := HasH1Gradient.test hΩ hφ hc
  have heq := hu.2.2.2 φ (gradient φ) htest
  rw [integral_inner_gradient_test hΩ hsu hφ hc hs] at heq
  have h1 : IntegrableOn (fun y => (Δ u) y * φ y) Ω :=
    (integrable_mul_test hΩ (laplacian_continuousOn hΩ hsu) hφ.continuous hc hs).integrableOn
  have h2 : IntegrableOn (fun y => u y * φ y) Ω :=
    (integrable_mul_test hΩ hsu.continuousOn hφ.continuous hc hs).integrableOn
  have heq0 : (∫ y in Ω, ((Δ u) y + firstPositiveNeumannValue Ω * u y) * φ y) = 0 := by
    simp only [add_mul, mul_assoc]
    rw [integral_add h1 (h2.const_mul _), integral_const_mul]
    linarith
  rw [setIntegral_mul_test hs] at heq0
  simpa only [smul_eq_mul, mul_comm] using heq0


lemma directionalDerivative_commute {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω)
    (e d : Plane) : directionalDerivative (directionalDerivative f e) d x =
      directionalDerivative (directionalDerivative f d) e x := by
  have hh := (hf x hx).contDiffAt (hΩ.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hΩ (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)
  change (fderiv ℝ (fun y => (fderiv ℝ f y) e) x) d =
    (fderiv ℝ (fun y => (fderiv ℝ f y) d) x) e
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hh.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; decide) d e

lemma directionalDerivative_congr {Ω : Set Plane} (hΩ : IsOpen Ω)
    {f g : Plane → ℝ} (heq : EqOn f g Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    directionalDerivative f e x = directionalDerivative g e x := by
  have hh : f =ᶠ[nhds x] g := Filter.eventually_of_mem (hΩ.mem_nhds hx) heq
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L e) hh.fderiv_eq

lemma laplacian_directionalDerivative {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    (Δ (directionalDerivative f e)) x = directionalDerivative (Δ f) e x := by
  have D (d : Plane) := directionalDerivative_contDiffOn hΩ hf d
  have DD (d c : Plane) := directionalDerivative_contDiffOn hΩ (D d) c
  rw [laplacian_eq_sum_directional hΩ (D e) hx]
  have hs : EqOn (Δ f) (fun y => ∑ i : Fin 2,
      directionalDerivative (directionalDerivative f (planeBasis i)) (planeBasis i) y) Ω :=
    fun y hy => laplacian_eq_sum_directional hΩ hf hy
  rw [directionalDerivative_congr hΩ hs hx e]
  have heq (i : Fin 2) :
      directionalDerivative (directionalDerivative (directionalDerivative f e) (planeBasis i))
        (planeBasis i) x =
      directionalDerivative (directionalDerivative (directionalDerivative f (planeBasis i))
        (planeBasis i)) e x := by
    rw [directionalDerivative_congr hΩ
      (fun y hy => directionalDerivative_commute hΩ hf hy e (planeBasis i)) hx]
    exact directionalDerivative_commute hΩ (D (planeBasis i)) hx e (planeBasis i)
  simp_rw [heq]
  unfold directionalDerivative
  rw [fderiv_fun_sum]
  · simp
  · intro i _
    exact ((DD (planeBasis i) (planeBasis i) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)



lemma eigenfunction_derivative_helmholtz {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) {x : Plane} (hx : x ∈ Ω)
    (e : Plane) : (Δ (directionalDerivative u e)) x +
      firstPositiveNeumannValue Ω * directionalDerivative u e x = 0 := by
  have hf : ContDiffOn ℝ ∞ u Ω := hu.1.mono subset_closure
  have hs : EqOn (Δ u) (fun y => -(firstPositiveNeumannValue Ω) * u y) Ω := by
    intro y hy
    linear_combination eigenfunction_helmholtz hΩ hu hy
  rw [laplacian_directionalDerivative hΩ hf hx,
    directionalDerivative_congr hΩ hs hx e]
  have hd := ((hf x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  simp only [directionalDerivative, fderiv_const_mul hd,
    smul_apply, smul_eq_mul]
  ring

end StrictHotSpots
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Laplacian Topology
namespace StrictHotSpots
lemma closed_directional_eq {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    fderivWithin ℝ u (closure Ω) x e = directionalDerivative u e x := by
  rw [fderivWithin_of_mem_nhds (mem_of_superset (ho.mem_nhds hx) subset_closure)]
  rfl

namespace Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



theorem gradient_K_representation (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) (x : disk) (e : Plane) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    inner ℝ (gradient u (c.F x)) e =
      ∫ s, fullBoundaryK c.densityBound_ne_top
        (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) x s *
        inner ℝ (closedGradient Ω u (c.F s)) e ∂boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hh := c.smooth_K_representation hΩ.2.2.1 hΩ.2.2.2.2 hΩ.1
    (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne)
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 e) ?_ x
  · have hx : c.F x ∈ Ω := by rw [← c.diskMap_agrees x.property]; exact c.diskMap.map_source x.property
    rw [closed_directional_eq hΩ.2.1 hx e] at hh
    simpa only [gradient,closedGradient,InnerProductSpace.toDual_symm_apply,
      directionalDerivative] using hh
  intro y hy
  have heq : (fun z => fderivWithin ℝ u (closure Ω) z e) =ᶠ[nhds y]
      directionalDerivative u e :=
    Filter.eventually_of_mem (hΩ.2.1.mem_nhds hy)
      (fun _ hz => closed_directional_eq hΩ.2.1 hz e)
  rw [(InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,
    closed_directional_eq hΩ.2.1 hy e]
  linear_combination eigenfunction_derivative_helmholtz hΩ.2.1 hu hy e

end Conformal.ClosedDiskChart
end StrictHotSpots
end
end
end OriginalGradientKernel


end OAI
