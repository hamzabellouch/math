import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly
import OAI.Analysis.Conductivity.Variational.AxialLocalRegularity
import OAI.Analysis.Conductivity.Flux.CascadeTensorLocality

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def cascadeSymmetricTensor (L K k : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨cascadeTensor L K k x,cascadeTensor_symm L K k x⟩

lemma cascade_connector_regular {L K k A : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0) (hA : A≠0)
    (x : Coord3) (j : ℕ)
    (hj0 : 0<cascadePhase (cascadeLength L K) k j (x 0))
    (hjK : cascadePhase (cascadeLength L K) k j (x 0)<K+2)
    (hsin : sin ((k*2^j)*x (cascadeAxis j))≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  let s := A*cascadeRatio L K^j
  let r := k*2^j
  let c := cascadeCenter (cascadeLength L K) k j
  let F : Coord3 → ℝ := fun y => s*pureModeValue (connectorProfile K) (cascadeAxis j) (r • (y-c)-0)
  let B : Coord3 → Symmetric3 := fun y =>
    ⟨pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k j (y 0))) (cascadeAxis j),
      pureModeTensor_symm _ _⟩
  have hp := pureModeValue_smooth (connectorProfile_smooth K) (cascadeAxis j)
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F := by
    dsimp only [F]
    exact contDiff_const.mul (hp.comp ((contDiff_id.sub contDiff_const).const_smul r |>.sub contDiff_const))
  have hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val) := by
    apply pureModeTensor_smooth
    exact (connectorAngular_smooth K).comp (by unfold cascadePhase; fun_prop)
  apply axialPair_mem_regularRegion_of_model hF hB (i:=cascadeAxis j) ?_ ?_ (cascadeAxis_ne_zero j) ?_ hU hx
  · filter_upwards [cascade_connector_nhds x j hj0 hjK] with y hy
    simpa only [F,s,r,c,sub_zero] using cascadeValue_connector hL hK hk A y j hy.1 hy.2
  · filter_upwards [cascade_connector_nhds x j hj0 hjK] with y hy
    apply Subtype.ext
    exact cascadeTensor_connector_eq hL hK y j hy.1 hy.2
  · change direction (Pi.single (cascadeAxis j) 1)
      (fun y => s*pureModeValue (connectorProfile K) (cascadeAxis j) (r • (y-c)-0)) x≠0
    rw [direction_affineShift (pureModeValue_diff ((connectorProfile_smooth K).differentiable (by simp)) _)]
    rw [pureModeValue_direction ((connectorProfile_smooth K).differentiable (by simp))]
    simp only [cascadeAxis_ne_zero,ite_false,ite_true,zero_add,sub_zero]
    apply mul_ne_zero (mul_ne_zero ?_ ?_)
    · exact mul_ne_zero (neg_ne_zero.mpr (connectorProfile_pos K _).ne') (by
        simpa only [r,c,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero j)] using hsin)
    · exact mul_ne_zero hA (pow_ne_zero j (cascadeRatio_pos L K).ne')
    · exact mul_ne_zero hk (pow_ne_zero j (by norm_num : (2:ℝ)≠0))

lemma cascade_crossing_regular {L K k A : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0) (hA : A≠0)
    (x : Coord3) (j : ℕ)
    (hjK : K+2<cascadePhase (cascadeLength L K) k j (x 0))
    (hjD : cascadePhase (cascadeLength L K) k j (x 0)<cascadeLength L K)
    (hsin : sin ((k*2^j)*x (cascadeAxis j))≠0)
    (hsin2 : sin ((k*2^(j+1))*x (cascadeAxis (j+1)))≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  let s := (A*cascadeRatio L K^j)*(connectorProfile K (K+2)*exp (-3*L))
  let r := k*2^j
  let c := cascadeCenter (cascadeLength L K) k j
  let d : Coord3 := Pi.single 0 (K+2+L)
  let F : Coord3 → ℝ := fun y => s*crossingValue3 L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d)
  let B : Coord3 → Symmetric3 := fun y =>
    ⟨crossingTensor L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d),crossingTensor_symm _ _ _ _⟩
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F := by
    dsimp only [F]
    exact contDiff_const.mul ((crossingValue3_smooth L _ _).comp
      ((contDiff_id.sub contDiff_const).const_smul r |>.sub contDiff_const))
  have hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val) :=
    (crossingTensor_smooth L _ _).comp ((contDiff_id.sub contDiff_const).const_smul r |>.sub contDiff_const)
  have hf : cascadeValue L K k A =ᶠ[𝓝 x] F := by
    filter_upwards [cascade_crossing_nhds x j hjK hjD] with y hy
    exact cascadeValue_crossing hL hK hk A y j hy.1 hy.2
  have htensor : cascadeSymmetricTensor L K k =ᶠ[𝓝 x] B := by
    filter_upwards [cascade_crossing_nhds x j hjK hjD] with y hy
    apply Subtype.ext
    exact cascadeTensor_crossing_eq hL hK y j hy.1 hy.2
  have hs : s≠0 := mul_ne_zero (mul_ne_zero hA (pow_ne_zero j (cascadeRatio_pos L K).ne'))
    (mul_ne_zero (connectorProfile_pos K _).ne' (exp_pos _).ne')
  have hr : r≠0 := mul_ne_zero hk (pow_ne_zero j (by norm_num : (2:ℝ)≠0))
  have ha := cascadeAxis_ne_zero j
  have hb := cascadeAxis_ne_zero (j+1)
  have hab := cascadeAxis_ne_succ j
  by_cases hz : (r • (x-c)-d) 0≤0
  · apply axialPair_mem_regularRegion_of_model hF hB hf htensor ha ?_ hU hx
    change direction (Pi.single (cascadeAxis j) 1)
      (fun y => s*crossingValue3 L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d)) x≠0
    rw [direction_affineShift (crossingValue3_diff L _ _),crossingValue3_direction]
    simp only [ha,hab,ite_false,ite_true,zero_add,add_zero,crossing_first_on_left hL hz]
    apply mul_ne_zero (mul_ne_zero hs hr)
    apply mul_ne_zero (neg_ne_zero.mpr (exp_pos _).ne')
    simpa only [r,c,d,Pi.sub_apply,Pi.single_eq_of_ne ha,sub_zero,
      cascade_dilation_coord _ _ _ _ ha] using hsin
  · apply axialPair_mem_regularRegion_of_model hF hB hf htensor hb ?_ hU hx
    change direction (Pi.single (cascadeAxis (j+1)) 1)
      (fun y => s*crossingValue3 L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d)) x≠0
    rw [direction_affineShift (crossingValue3_diff L _ _),crossingValue3_direction]
    simp only [hb,Ne.symm hab,ite_false,ite_true,zero_add,add_zero,
      crossing_second_on_right hL (le_of_not_ge hz)]
    apply mul_ne_zero (mul_ne_zero hs hr)
    apply mul_ne_zero (mul_ne_zero (by norm_num) (exp_pos _).ne')
    have he : 2*(r • (x-c)-d) (cascadeAxis (j+1))=
        (k*2^(j+1))*x (cascadeAxis (j+1)) := by
      simp only [r,c,d,Pi.sub_apply,Pi.single_eq_of_ne hb,sub_zero,
        cascade_dilation_coord _ _ _ _ hb,pow_succ]
      ring
    rw [he]
    exact hsin2

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma cascade_terminal_regular {L K k A : ℝ} (hL : 0<L) (hK : 0<K)
    (x : Coord3) (ht : 2*cascadeLength L K<k*x 0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  let B : Coord3 → Symmetric3 := fun _ => ⟨1,isSymm_one⟩
  have hn : {y : Coord3 | 2*cascadeLength L K<k*y 0}∈𝓝 x :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).mem_nhds ht
  apply axialPair_mem_regularRegion_of_zero (B:=B) contDiff_const ?_ ?_ hU hx
  · filter_upwards [hn] with y hy
    exact cascadeValue_terminal hL hK A y hy.le
  · filter_upwards [hn] with y hy
    apply Subtype.ext
    exact ite_eq_right (by intro hh; linarith [hh.2])

theorem cascade_regularRegion_ae {L K k A : ℝ} (hL : 0<L) (hK : 0<K)
    (hk : k≠0) (hA : A≠0) {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U → 0≤k*x 0 →
      x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  have h0 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠0 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hD : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠cascadeLength L K :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hK2 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠K+2 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have ht : ∀ᵐ x : Coord3, k*x 0≠2*cascadeLength L K := by
    simpa only [cascadePhase_zero] using ae_cascadePhase_ne hk (cascadeLength L K) (2*cascadeLength L K) 0
  have hsin : ∀ᵐ x : Coord3,∀ n : ℕ,sin ((k*2^n)*x (cascadeAxis n))≠0 :=
    ae_all_iff.mpr (fun n => ae_sin_coord_ne_zero (mul_ne_zero hk (pow_ne_zero n (by norm_num))) _)
  filter_upwards [h0,hD,hK2,ht,hsin] with x hx0 hxD hxK hxt hxs
  intro hxU hx
  by_cases hterm : k*x 0<2*cascadeLength L K
  · have hs := cascadeIndex_spec x hx hterm
    have hs₁ := lt_of_le_of_ne hs.1 (Ne.symm (hx0 _))
    have hs₂ := lt_of_le_of_ne hs.2 (hxD _)
    by_cases hc : cascadePhase (cascadeLength L K) k (cascadeIndex (cascadeLength L K) k x) (x 0)<K+2
    · exact cascade_connector_regular hL hK hk hA x _ hs₁ hc (hxs _) hU hxU
    · exact cascade_crossing_regular hL hK hk hA x _
        (lt_of_le_of_ne (le_of_not_gt hc) (Ne.symm (hxK _))) hs₂ (hxs _) (hxs _) hU hxU
  · exact cascade_terminal_regular hL hK x
      (lt_of_le_of_ne (le_of_not_gt hterm) (Ne.symm hxt)) hU hxU

end ScalarConductivity

end

end OAI
