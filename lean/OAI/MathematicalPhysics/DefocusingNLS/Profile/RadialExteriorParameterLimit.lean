import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedParameter
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailLimit

namespace OAI

/-! Continuity of the actual weighted tail fixed points at a fixed nonlinearity power. -/

open Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_tail_parameter_limit
    (n : ℕ) (m : ℂ) (δ κ C : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hmixed : ∀ a b h : ℂ, ‖a‖ ≤ ‖m‖+δ → ‖b‖ ≤ ‖m‖+δ → ‖h‖ ≤ ‖m‖+δ →
      ‖(oddPowerNonlinearity n (a+h)-oddPowerNonlinearity n a)-
        (oddPowerNonlinearity n (b+h)-oddPowerNonlinearity n b)‖ ≤ C*‖a-b‖*‖h‖)
    (ν : ℕ → ℂ) (ν₀ : ℂ) (hν : Tendsto ν atTop (nhds ν₀))
    (hκ : radialExteriorMatrixBound ν₀+radialExteriorCutoffRate n m δ < κ)
    (f : ℕ → ℝ →ᵇ ℂ) (f₀ : ℝ →ᵇ ℂ) (hf : Tendsto f atTop (nhds f₀))
    (hbase : ∀ t, ‖f₀ t-m‖ ≤ δ/4)
    (r : ℕ → ℝ →ᵇ ℂ × ℂ) (r₀ : ℝ →ᵇ ℂ × ℂ) (hr : Tendsto r atTop (nhds r₀))
    (v : ℕ → ℝ →ᵇ ℂ × ℂ) (w : ℝ →ᵇ ℂ × ℂ)
    (hv : ∀ᶠ i in atTop, ∀ t, v i t=radialExteriorTailIntegral κ
      (fun s => radialExteriorErrorField κ (ν i) (radialExteriorCutoffPower n m δ)
        (f i) (r i) s (v i s)) t)
    (hw : ∀ t, w t=radialExteriorTailIntegral κ
      (fun s => radialExteriorErrorField κ ν₀ (radialExteriorCutoffPower n m δ)
        f₀ r₀ s (w s)) t) :
    Tendsto v atTop (nhds w) := by
  let L := radialExteriorCutoffRate n m δ
  have hL : 0 ≤ L := radialExteriorCutoffRate_nonneg n m δ
  have hκ0 : 0 < κ := lt_of_lt_of_le (radialExteriorMatrixBound_pos ν₀)
    (by linarith)
  have hdec : Tendsto (fun t : ℝ => Real.exp (-κ*t)*‖w‖) atTop (nhds 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hκ0)).mul_const ‖w‖
    simpa only [Function.comp_def,id_eq,neg_mul,zero_mul] using hh
  obtain ⟨T,hT⟩ := (hdec.eventually (gt_mem_nhds (show 0 < δ/2 by positivity))).exists
  let K := 2*L*Real.exp (κ*T)+C*‖w‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let B := fun i => radialExteriorMatrixBound (ν i)+L
  let E := fun i => radialExteriorMatrixDifference (ν i) ν₀*‖w‖+
    K*‖f i-f₀‖+‖r i-r₀‖
  have hB : Tendsto B atTop (nhds (radialExteriorMatrixBound ν₀+L)) := by
    have hc : Continuous radialExteriorMatrixBound := by unfold radialExteriorMatrixBound; fun_prop
    exact (hc.continuousAt.tendsto.comp hν).add_const L
  have hD : Tendsto (fun i => radialExteriorMatrixDifference (ν i) ν₀) atTop (nhds 0) := by
    have hc : Continuous (fun z => radialExteriorMatrixDifference z ν₀) := by
      unfold radialExteriorMatrixDifference
      fun_prop
    simpa only [Function.comp_def,radialExteriorMatrixDifference,sub_self,norm_zero,add_zero]
      using hc.continuousAt.tendsto.comp hν
  have hE : Tendsto E atTop (nhds 0) := by
    simpa only [E,zero_mul,mul_zero,add_zero] using
      ((hD.mul_const ‖w‖).add ((tendsto_iff_norm_sub_tendsto_zero.mp hf).const_mul K)).add
        (tendsto_iff_norm_sub_tendsto_zero.mp hr)
  have he : ∀ᶠ i in atTop, B i < κ := hB.eventually (gt_mem_nhds hκ)
  have hfnear : ∀ᶠ i in atTop, ∀ t, ‖f i t-m‖ ≤ δ/2 := by
    filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.mp hf).eventually
      (gt_mem_nhds (show 0 < δ/4 by positivity))] with i hi t
    have hn := (f i-f₀).norm_coe_le_norm t
    have ht := hbase t
    have hb : ‖f i t-m‖ ≤ ‖f i t-f₀ t‖+‖f₀ t-m‖ := by
      simpa only [dist_eq_norm] using dist_triangle (f i t) (f₀ t) m
    change ‖f i t-f₀ t‖ ≤ ‖f i-f₀‖ at hn
    linarith
  have hquot : Tendsto (fun i => E i/(κ-B i)) atTop (nhds 0) := by
    have hh := hE.div (tendsto_const_nhds.sub hB) (sub_pos.mpr hκ).ne'
    simpa only [Pi.div_apply,zero_div] using! hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hquot
  filter_upwards [he,hfnear,hv] with i hi hfi hvi
  let N := radialExteriorErrorField κ (ν i) (radialExteriorCutoffPower n m δ) (f i) (r i)
  let M := radialExteriorErrorField κ ν₀ (radialExteriorCutoffPower n m δ) f₀ r₀
  have hLip := radialExteriorCutoffPower_difference n m δ hδ.le
  apply radialExterior_fixedPoint_difference κ (B i)
    (radialExteriorMatrixBound ν₀+L) ‖r i‖ ‖r₀‖ (E i) hκ0
    (add_nonneg (radialExteriorMatrixBound_pos _).le hL)
    (add_nonneg (radialExteriorMatrixBound_pos _).le hL) hi (by
      dsimp [E,radialExteriorMatrixDifference]; positivity) N M
    (radialExteriorErrorField_continuous κ (ν i) _
      (radialExteriorCutoffPower_continuous n m δ) _ (f i).continuous (r i))
    (radialExteriorErrorField_continuous κ ν₀ _
      (radialExteriorCutoffPower_continuous n m δ) _ f₀.continuous r₀)
    (fun t => by simpa only [N,radialExteriorErrorField_zero] using (r i).norm_coe_le_norm t)
    (fun t => by simpa only [M,radialExteriorErrorField_zero] using r₀.norm_coe_le_norm t)
    (radialExteriorErrorField_difference κ L hL (ν i) _ hLip _ _)
    (radialExteriorErrorField_difference κ L hL ν₀ _ hLip _ _)
    (v i) w hvi hw
  intro t
  have hinc := radialWeightedIncrement_base_lipschitz n m δ κ T ‖w‖ C (‖m‖+δ)
    hδ.le hκ0.le (norm_nonneg _) hC le_rfl hT.le hmixed (f i) f₀ t (w t).1
    (hfi t) ((hbase t).trans (by linarith))
    ((norm_fst_le (w t)).trans (w.norm_coe_le_norm t))
  have hinc' : ‖radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ)
      (f i) t (w t).1-radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ)
      f₀ t (w t).1‖ ≤ K*‖f i-f₀‖ :=
    hinc.trans (mul_le_mul_of_nonneg_left ((f i-f₀).norm_coe_le_norm t) hK)
  have heq : N t (w t)-M t (w t) =
      (radialExteriorErrorMatrix (ν i) (w t)-radialExteriorErrorMatrix ν₀ (w t))+
      (0,radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ) (f i) t (w t).1-
        radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ) f₀ t (w t).1)+
      (r i t-r₀ t) := by
    apply Prod.ext <;> dsimp [N,M,radialExteriorErrorField] <;> abel
  rw [heq]
  apply (@norm_add₃_le _ _ _ _ _).trans
  apply add_le_add
  · apply add_le_add
    · exact (radialExteriorErrorMatrix_difference (ν i) ν₀ (w t)).trans
        (mul_le_mul_of_nonneg_left (w.norm_coe_le_norm t) (by
          unfold radialExteriorMatrixDifference; positivity))
    · simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hinc'
  · exact (r i-r₀).norm_coe_le_norm t

end DefocusingNLS

end OAI
