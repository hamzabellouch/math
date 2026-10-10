import OAI.Analysis.NodalLength.Persistence

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

def rescaleMap (y : Plane) (r : ℝ) (x : Plane) : Plane := y+r • x

lemma smooth_rescaleMap (y : Plane) (r : ℝ) : ContDiff ℝ ∞ (rescaleMap y r) := by
  unfold rescaleMap
  fun_prop

lemma partial_rescale {f : Plane → ℝ} (hf : Smooth f) (y : Plane) (r : ℝ)
    (x : Plane) (i : Fin 2) :
    coordPartial (f ∘ rescaleMap y r) i x=r*coordPartial f i (rescaleMap y r x) := by
  have h := ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
    (((hasFDerivAt_id (𝕜:=ℝ) x).const_smul r).const_add y)
  change fderiv ℝ (f ∘ rescaleMap y r) x _ = _
  have he : fderiv ℝ (f ∘ rescaleMap y r) x=
    (fderiv ℝ f (rescaleMap y r x)).comp (r • ContinuousLinearMap.id ℝ Plane) := by
    simpa only [Function.comp_def,rescaleMap,Pi.smul_apply,id_eq] using h.fderiv
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,coordPartial]

lemma laplacian_rescale {f : Plane → ℝ} (hf : Smooth f) (y : Plane) (r : ℝ) (x : Plane) :
    euclideanLaplacian (f ∘ rescaleMap y r) x=r^2*euclideanLaplacian f (rescaleMap y r x) := by
  unfold euclideanLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (f ∘ rescaleMap y r) i=(fun x =>r*coordPartial f i (rescaleMap y r x)) from
    funext (fun x =>partial_rescale hf y r x i)]
  change coordPartial (fun z =>r*((coordPartial f i) ∘ rescaleMap y r) z) i x = _
  rw [partial_const_mul ((smooth_partial hf i).comp (smooth_rescaleMap y r)),
    partial_rescale (smooth_partial hf i)]
  ring

lemma partial_rescale_local {Ω : Set Plane} {f : Plane → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (y : Plane) (r : ℝ) (x : Plane) (hx : rescaleMap y r x∈Ω)
    (i : Fin 2) :
    coordPartial (f ∘ rescaleMap y r) i x=r*coordPartial f i (rescaleMap y r x) := by
  obtain ⟨g,t,hg,ht,_,he⟩ := smooth_extension_near hΩ hx hf
  have hfg : f=ᶠ[𝓝 (rescaleMap y r x)] g := by
    filter_upwards [Metric.ball_mem_nhds _ ht] with z hz using (he z hz).symm
  have hfg' := hfg.comp_tendsto (smooth_rescaleMap y r).continuous.continuousAt
  rw [(partial_eventuallyEq hfg' i).eq_of_nhds, (partial_eventuallyEq hfg i).eq_of_nhds]
  exact partial_rescale hg y r x i

lemma laplacian_rescale_local {Ω : Set Plane} {f : Plane → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (y : Plane) (r : ℝ) (x : Plane) (hx : rescaleMap y r x∈Ω) :
    euclideanLaplacian (f ∘ rescaleMap y r) x=r^2*euclideanLaplacian f (rescaleMap y r x) := by
  obtain ⟨g,t,hg,ht,_,he⟩ := smooth_extension_near hΩ hx hf
  have hfg : f=ᶠ[𝓝 (rescaleMap y r x)] g := by
    filter_upwards [Metric.ball_mem_nhds _ ht] with z hz using (he z hz).symm
  have hfg' := hfg.comp_tendsto (smooth_rescaleMap y r).continuous.continuousAt
  rw [(laplacian_eventuallyEq hfg').eq_of_nhds, (laplacian_eventuallyEq hfg).eq_of_nhds]
  exact laplacian_rescale hg y r x

lemma rescaleMap_ball_preimage (y : Plane) {s : ℝ} (hs : 0<s) (z : Plane) (r : ℝ) :
    (rescaleMap y s) ⁻¹' Metric.ball (rescaleMap y s z) (s*r)=Metric.ball z r := by
  ext x
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,rescaleMap]
  rw [show y+s • x-(y+s • z)=s • (x-z) by module,
    norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  exact mul_lt_mul_iff_right₀ hs

lemma map_volume_rescaleMap (y : Plane) {s : ℝ} (hs : 0<s) :
    Measure.map (rescaleMap y s) volume=ENNReal.ofReal (s^2)⁻¹ • (volume : Measure Plane) := by
  have he : rescaleMap y s=(fun x : Plane =>y+x) ∘ (fun x : Plane =>s • x) := rfl
  have hm1 : Measurable (fun x : Plane =>y+x) := by fun_prop
  have hm2 : Measurable (fun x : Plane =>s • x) := by fun_prop
  rw [he,← Measure.map_map hm1 hm2,
    Measure.map_addHaar_smul volume hs.ne',Measure.map_smul _ hm1.aemeasurable,map_add_left_eq_self]
  simp only [Plane, finrank_euclideanSpace_fin,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg s)),
    ENNReal.ofReal_inv_of_pos (sq_pos_of_pos hs)]

lemma centeredMass_rescale (T : Plane) (U : Plane → ℝ) (y z : Plane) {s : ℝ} (hs : 0<s) (r : ℝ) :
    centeredMass (s • T) (U ∘ rescaleMap y s) z r=
      ENNReal.ofReal (s^2)⁻¹*centeredMass T U (rescaleMap y s z) (s*r) := by
  let e : Plane ≃ᵐ Plane := ((Homeomorph.smul (Units.mk0 s hs.ne')).trans (Homeomorph.addLeft y)).toMeasurableEquiv
  have he (x : Plane) : e x=rescaleMap y s x := rfl
  have hpre : e ⁻¹' Metric.ball (rescaleMap y s z) (s*r)=Metric.ball z r :=
    rescaleMap_ball_preimage y hs z r
  have hmap := map_volume_rescaleMap y hs
  have hf (x : Plane) :
      ENNReal.ofReal ((Real.exp (-inner ℝ T (e x-rescaleMap y s z))*U (e x))^2)=
        ENNReal.ofReal ((Real.exp (-inner ℝ (s • T) (x-z))*(U ∘ rescaleMap y s) x)^2) := by
    rw [he]
    have hh : rescaleMap y s x-rescaleMap y s z=s • (x-z) := by unfold rescaleMap; module
    rw [hh,inner_smul_right,inner_smul_left]
    rfl
  have hh := lintegral_map_equiv
    ((Metric.ball (rescaleMap y s z) (s*r)).indicator
      (fun x => ENNReal.ofReal ((Real.exp (-inner ℝ T (x-rescaleMap y s z))*U x)^2))) e
    (μ:=(volume : Measure Plane))
  rw [show Measure.map e volume=ENNReal.ofReal (s^2)⁻¹ • (volume : Measure Plane) from hmap,
    lintegral_smul_measure,lintegral_indicator Metric.isOpen_ball.measurableSet] at hh
  have hind : (fun a =>(Metric.ball (rescaleMap y s z) (s*r)).indicator
      (fun x => ENNReal.ofReal ((Real.exp (-inner ℝ T (x-rescaleMap y s z))*U x)^2)) (e a))=
    (Metric.ball z r).indicator
      (fun x => ENNReal.ofReal ((Real.exp (-inner ℝ (s • T) (x-z))*(U ∘ rescaleMap y s) x)^2)) := by
    funext x
    have hm : e x∈Metric.ball (rescaleMap y s z) (s*r) ↔ x∈Metric.ball z r := by
      change x∈e ⁻¹' Metric.ball (rescaleMap y s z) (s*r) ↔ _
      rw [hpre]
    by_cases hx : x∈Metric.ball z r
    · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (hm.mpr hx),hf]
    · simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem (fun h => hx (hm.mp h))]
  rw [hind,lintegral_indicator Metric.isOpen_ball.measurableSet] at hh
  exact hh.symm

lemma centered_excess_rescale (T : Plane) (U : Plane → ℝ) (y z : Plane) {s : ℝ}
    (hs : 0<s) (R r : ℝ) :
    massExcess (centeredMass (s • T) (U ∘ rescaleMap y s) z R)
      (centeredMass (s • T) (U ∘ rescaleMap y s) z r)=
      massExcess (centeredMass T U (rescaleMap y s z) (s*R))
      (centeredMass T U (rescaleMap y s z) (s*r)) := by
  rw [centeredMass_rescale _ _ _ _ hs,centeredMass_rescale _ _ _ _ hs]
  exact massExcess_mul_left _ _ _ (by simp [hs.ne'])
    (by simp)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

structure ScaledWave (Cp a₀ : ℝ) extends UnitWave Cp a₀ where
  side : ℝ
  side_pos : 0 < side
  side_le_one : side ≤ 1
  physical_derivative : ∀i x,x∈Metric.ball (0:Plane) 1000 →
    |coordPartial p i x|≤Cp*side

lemma rescaleMap_mapsTo {y : Plane} {r : ℝ} (hy : ‖y‖≤1) (hr : 0≤r) (hr' : r≤1/2) :
    MapsTo (rescaleMap y r) (Metric.ball 0 1000) (Metric.ball 0 1000) := by
  intro x hx
  rw [Metric.mem_ball,dist_zero_right] at hx ⊢
  calc
    ‖rescaleMap y r x‖ ≤ ‖y‖+r*‖x‖ := by
      simpa only [rescaleMap,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] using norm_add_le y (r • x)
    _ ≤ 1+(1/2)*‖x‖ := add_le_add hy (mul_le_mul_of_nonneg_right hr' (norm_nonneg _))
    _ < 1000 := by linarith

lemma grid_expect {A : ℕ} (hA : 0<A) (f : Plane → ℝ) :
    (𝔼 i : GridIndex A, f (gridCenter A i))=((A:ℝ)⁻¹)^2*∑y∈gridCenters A,f y := by
  classical
  rw [Fintype.expect_eq_sum_div_card,gridCenters,
    Finset.sum_image (fun i _ j _ h =>gridCenter_injective hA h)]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  ring

def ScaledWave.child {Cp a₀ : ℝ} (D : ScaledWave Cp a₀) {A : ℕ} (hA : 2≤A)
    (i : GridIndex A) (hbottom : a₀≤D.K/(A:ℝ))
    (hm0 : centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹≠0)
    (hmt : centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹)≠⊤) :
    ScaledWave Cp a₀ where
  p := D.p ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹
  U := D.U ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹
  K := D.K/(A:ℝ)
  frequency_lower := hbottom
  smooth_p := D.smooth_p.comp (smooth_rescaleMap _ _).contDiffOn
    (rescaleMap_mapsTo (gridCenter_norm (by omega) i) (by positivity)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)))
  smooth_U := D.smooth_U.comp (smooth_rescaleMap _ _).contDiffOn
    (rescaleMap_mapsTo (gridCenter_norm (by omega) i) (by positivity)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)))
  coefficient_bound := fun x hx => D.coefficient_bound _
    (rescaleMap_mapsTo (gridCenter_norm (by omega) i) (by positivity)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx)
  derivative_bound := by
    intro j x hx
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have hmap := rescaleMap_mapsTo (gridCenter_norm (by omega : 0<A) i) (by positivity : 0≤(A:ℝ)⁻¹)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx
    rw [partial_rescale_local Metric.isOpen_ball D.smooth_p _ _ x hmap j,
      abs_mul,abs_of_pos (inv_pos.mpr (by positivity : 0<(A:ℝ)))]
    have hd := D.derivative_bound j _ hmap
    have hi : (A:ℝ)⁻¹≤1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
    calc
      _ ≤ 1*|coordPartial D.p j (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)| :=
        mul_le_mul_of_nonneg_right hi (abs_nonneg _)
      _ ≤ Cp := by simpa using hd
  equation := by
    intro x hx
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have hmap := rescaleMap_mapsTo (gridCenter_norm (by omega : 0<A) i) (by positivity : 0≤(A:ℝ)⁻¹)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx
    rw [laplacian_rescale_local Metric.isOpen_ball D.smooth_U _ _ x hmap]
    dsimp only [Function.comp_apply]
    have he := D.equation _ hmap
    calc
      _ = (A:ℝ)⁻¹^2*(euclideanLaplacian D.U (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)+
        D.K^2*D.p (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)*D.U (rescaleMap (gridCenter A i) (A:ℝ)⁻¹ x)) := by ring
      _ = 0 := by rw [he,mul_zero]
  inner_nonzero := by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have he := centeredMass_rescale 0 D.U (gridCenter A i) 0
      (inv_pos.mpr (by positivity : 0<(A:ℝ))) 1
    simp only [smul_zero,rescaleMap,add_zero,mul_one] at he
    rw [he]
    exact mul_ne_zero (by simp [show A≠0 by omega]) hm0
  outer_finite := by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have he := centeredMass_rescale 0 D.U (gridCenter A i) 0
      (inv_pos.mpr (by positivity : 0<(A:ℝ))) 1000
    simp only [smul_zero,rescaleMap,add_zero] at he
    rw [he]
    exact ENNReal.mul_ne_top (by simp) (by simpa [mul_comm] using hmt)
  side := D.side/(A:ℝ)
  side_pos := div_pos D.side_pos (by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    linarith)
  side_le_one := by
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    exact (div_le_self D.side_pos.le (by linarith)).trans D.side_le_one
  physical_derivative := by
    intro j x hx
    have hAr : (2:ℝ)≤A := by exact_mod_cast hA
    have hmap := rescaleMap_mapsTo (gridCenter_norm (by omega : 0<A) i) (by positivity : 0≤(A:ℝ)⁻¹)
      ((inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; exact_mod_cast hA)) hx
    rw [partial_rescale_local Metric.isOpen_ball D.smooth_p _ _ x hmap j,
      abs_mul,abs_of_pos (inv_pos.mpr (by positivity : 0<(A:ℝ)))]
    calc
      _ ≤ (A:ℝ)⁻¹*(Cp*D.side) := mul_le_mul_of_nonneg_left
        (D.physical_derivative j _ hmap) (by positivity)
      _ = Cp*(D.side/(A:ℝ)) := by ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma ScaledWave.child_growth {Cp a₀ : ℝ} (D : ScaledWave Cp a₀) {A : ℕ} (hA : 2≤A)
    (i : GridIndex A) (hbottom : a₀≤D.K/(A:ℝ))
    (hm0 : centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹≠0)
    (hmt : centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹)≠⊤) (b : Plane) :
    (D.child hA i hbottom hm0 hmt).growth b=
      massExcess (centeredMass (D.K • b) D.U (gridCenter A i) (1000*(A:ℝ)⁻¹))
        (centeredMass (D.K • b) D.U (gridCenter A i) (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹) := by
  have hAr : 0<(A:ℝ) := by exact_mod_cast (show 0<A by omega)
  have he:= centered_excess_rescale (D.K • b) D.U (gridCenter A i) 0 (inv_pos.mpr hAr) 1000 1
  have hs : (A:ℝ)⁻¹ • (D.K • b)=(D.K/(A:ℝ)) • b := by rw [smul_smul]; congr 1; ring
  simp only [hs,rescaleMap,smul_zero,add_zero,mul_one] at he
  dsimp only [UnitWave.growth,UnitWave.excess,ScaledWave.child]
  rw [he]
  simp only [div_eq_mul_inv,mul_comm]

def GridChild {Cp a₀ : ℝ} (A : ℕ) (D E : ScaledWave Cp a₀) (i : GridIndex A) : Prop :=
  E.p=D.p ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹ ∧
  E.U=D.U ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹ ∧
  E.K=D.K/(A:ℝ) ∧ E.side=D.side/(A:ℝ)

def DescentRule (A : ℕ) (Cp a₀ C₀ C₁ L : ℝ) : Prop :=
  ∀ (D : ScaledWave Cp a₀) (b : Plane), a₀≤D.K/(A:ℝ) →
    (L<D.growth 0 ∨ L<‖b‖) →
    ∃(E : GridIndex A → ScaledWave Cp a₀) (b' : GridIndex A → Plane),
      (∀i,GridChild A D (E i) i) ∧
      (𝔼 i,‖b' i-b‖)≤C₁*(D.growth b+(C₀/D.K+D.side)) ∧
      (𝔼 i,(E i).growth (b' i))≤(D.growth b+(C₀/D.K+D.side))/2

theorem actual_descent_rule : ∃A : ℕ,10000<A ∧ ∃C₁ : ℝ,0<C₁ ∧
    ∀Cp : ℝ,0≤Cp → ∃C₀ L : ℝ,1≤C₀ ∧ 0<L ∧
    ∀a₀ : ℝ,0<a₀ → DescentRule A Cp a₀ C₀ C₁ L := by
  obtain ⟨A,hA,C₁,hC₁,hstep⟩ := one_step_descent
  refine ⟨A,hA,C₁,hC₁,?_⟩
  intro Cp hCp
  obtain ⟨C₀,L,hC₀,hL,hstep⟩ := hstep Cp hCp
  refine ⟨C₀,L,hC₀,hL,?_⟩
  intro a₀ ha₀ D b hbottom hlarge
  have hK : 0<D.K := ha₀.trans_le D.frequency_lower
  obtain ⟨b',hinc,hfinite,hdec⟩ := hstep D.p D.U b D.K D.side D.smooth_p D.smooth_U hK
    D.side_pos.le D.coefficient_bound D.physical_derivative D.equation D.inner_nonzero D.outer_finite
    (by simpa only [UnitWave.growth,UnitWave.excess,smul_zero] using hlarge)
  have hmem (i : GridIndex A) : gridCenter A i∈gridCenters A := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hm0 (i : GridIndex A) : centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹≠0 :=
    centeredMass_ne_zero_of (hfinite _ (hmem i)).1
  have hmt (i : GridIndex A) : centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹)≠⊤ :=
    centeredMass_ne_top_of (hfinite _ (hmem i)).2
  let E (i : GridIndex A) := D.child (by omega : 2≤A) i hbottom (hm0 i) (hmt i)
  refine ⟨E,(fun i =>b' (gridCenter A i)),fun i =>⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · rw [grid_expect (by omega : 0<A) (fun y =>‖b' y-b‖)]
    exact hinc
  · have hg (i : GridIndex A) := D.child_growth (by omega : 2≤A) i hbottom (hm0 i) (hmt i) (b' (gridCenter A i))
    simp_rw [show ∀i,(E i).growth (b' (gridCenter A i))=
      massExcess (centeredMass (D.K • b' (gridCenter A i)) D.U (gridCenter A i) (1000*(A:ℝ)⁻¹))
        (centeredMass (D.K • b' (gridCenter A i)) D.U (gridCenter A i) (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹) from hg]
    rw [grid_expect (by omega : 0<A) (fun y =>
      massExcess (centeredMass (D.K • b' y) D.U y (1000*(A:ℝ)⁻¹))
        (centeredMass (D.K • b' y) D.U y (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹))]
    exact hdec

end SharpNodal.Profiles
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SharpNodal.Descent.Tree
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def ScaledFloors (A C₀ K s : ℝ) : ℕ → Tree ι → Prop
  | _, .stop _ => True
  | 0, .step _ _ => False
  | n+1, .step a t => a.floor=C₀/K+s ∧ ∀i,ScaledFloors A C₀ (K/A) (s/A) n (t i)

lemma scaled_floor_bound {A C₀ : ℝ} (hA : 2≤A) (hC : 0≤C₀) (n : ℕ)
    {K s : ℝ} (hK : 0 < K) (hs : 0 ≤ s) (t : Tree ι) (ht : ScaledFloors A C₀ K s n t) :
    t.floorCost≤(2*A^n-1)*C₀/K+2*s := by
  have hApos : 0<A := by linarith
  have hAp : 1≤A^n := one_le_pow₀ (by linarith : (1:ℝ)≤A)
  induction n generalizing K s t with
  | zero =>
    cases t with
    | stop a => simp only [floorCost,pow_zero]; positivity
    | step a t => exact ht.elim
  | succ n ih =>
    cases t with
    | stop a =>
      change 0≤_
      have hh : 0≤2*A^(n+1)-1 := by linarith
      positivity
    | step a t =>
      have hb (i : ι) := ih (div_pos hK hApos) (div_nonneg hs hApos.le) (t i) (ht.2 i) (one_le_pow₀ (by linarith : (1:ℝ)≤A))
      have he := Finset.expect_le Finset.univ_nonempty (fun i _ => hb i)
      change a.floor+(𝔼 i,floorCost (t i))≤_
      rw [ht.1]
      apply le_trans (show C₀/K+s+(𝔼 i,floorCost (t i)) ≤
        C₀/K+s+((2*A^n-1)*C₀/(K/A)+2*(s/A)) from by linarith only [he])
      have hCs : 0≤C₀/K := div_nonneg hC hK.le
      have hsA : s / A ≤ s / 2 := div_le_div_of_nonneg_left hs (by norm_num) hA
      have hCA : C₀/K*2≤C₀/K*A := mul_le_mul_of_nonneg_left hA hCs
      have heq : (2*A^n-1)*C₀/(K/A)=(2*A^(n+1)-A)*(C₀/K) := by
        rw [pow_succ]
        field_simp
      rw [heq]
      change C₀/K+s+((2*A^(n+1)-A)*(C₀/K)+2*(s/A))≤(2*A^(n+1)-1)*C₀/K+2*s
      rw [mul_div_assoc]
      nlinarith only [hsA,hCA]

lemma physical_floor_bound {A C₀ a₀ K s : ℝ} (hA : 2≤A) (hC : 0≤C₀) (ha : 0<a₀)
    (hK : 0 < K) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ)
    (hbottom : a₀≤K/A^n) {t : Tree ι} (ht : ScaledFloors A C₀ K s n t) :
    t.floorCost≤2*(C₀/a₀+1) := by
  have hAp : 0<A^n := pow_pos (by linarith : (0:ℝ)<A) n
  have hkbottom := (le_div_iff₀ hAp).mp hbottom
  have hratio : C₀*A^n/K≤C₀/a₀ := by
    apply (div_le_div_iff₀ hK ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hkbottom hC]
  have hb := scaled_floor_bound hA hC n hK hs t ht
  have hCK : 0≤C₀/K := div_nonneg hC hK.le
  have he : (2*A^n-1)*C₀/K=2*(C₀*A^n/K)-C₀/K := by ring
  rw [he] at hb
  linarith

end SharpNodal.Descent.Tree

noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace SharpNodal.Profiles

inductive WaveTree (A : ℕ) (Cp a₀ : ℝ) where
  | stop (wave : ScaledWave Cp a₀) (tilt : Plane)
  | step (wave : ScaledWave Cp a₀) (tilt : Plane) (children : GridIndex A → WaveTree A Cp a₀)

namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

def rootWave : WaveTree A Cp a₀ → ScaledWave Cp a₀
  | .stop D _ => D
  | .step D _ _ => D

def rootTilt : WaveTree A Cp a₀ → Plane
  | .stop _ b => b
  | .step _ b _ => b

def label (C₀ : ℝ) (D : ScaledWave Cp a₀) (b : Plane) : Descent.Label :=
  ⟨D.growth b,b,C₀/D.K+D.side⟩

def numerical (C₀ : ℝ) : WaveTree A Cp a₀ → Descent.Tree (GridIndex A)
  | .stop D b => .stop (label C₀ D b)
  | .step D b t => .step (label C₀ D b) (fun i => numerical C₀ (t i))

lemma numerical_root (C₀ : ℝ) (t : WaveTree A Cp a₀) :
    (t.numerical C₀).root=label C₀ t.rootWave t.rootTilt := by cases t <;> rfl

def Coherent : ℕ → WaveTree A Cp a₀ → Prop
  | _, .stop _ _ => True
  | 0, .step _ _ _ => False
  | n+1, .step D _ t => ∀i,GridChild A D (t i).rootWave i ∧ Coherent n (t i)

def Stopped (C₀ : ℝ) (P : Descent.Label → Prop) : ℕ → WaveTree A Cp a₀ → Prop
  | 0, .stop _ _ => True
  | _+1, .stop D b => ¬P (label C₀ D b)
  | 0, .step _ _ _ => False
  | n+1, .step D b t => P (label C₀ D b) ∧ ∀i,Stopped C₀ P n (t i)

lemma coherent_floors (C₀ : ℝ) {n : ℕ} {t : WaveTree A Cp a₀} (ht : Coherent n t) :
    Descent.Tree.ScaledFloors (A:ℝ) C₀ t.rootWave.K t.rootWave.side n (t.numerical C₀) := by
  induction n generalizing t with
  | zero => cases t with
    | stop D b => trivial
    | step D b t => exact ht.elim
  | succ n ih => cases t with
    | stop D b => trivial
    | step D b t =>
      refine ⟨rfl,fun i =>?_⟩
      have hh := ih (ht i).2
      rw [(ht i).1.2.2.1,(ht i).1.2.2.2] at hh
      exact hh

lemma label_nonnegative (ha₀ : 0<a₀) {C₀ : ℝ} (hC₀ : 0≤C₀)
    (D : ScaledWave Cp a₀) (b : Plane) :
    0≤(label C₀ D b).mass ∧ 0≤(label C₀ D b).floor := by
  have hK : 0<D.K := ha₀.trans_le D.frequency_lower
  exact ⟨div_nonneg (D.excess_nonneg b) hK.le,add_nonneg (div_nonneg hC₀ hK.le) D.side_pos.le⟩

theorem build_stopped {C₀ C₁ L : ℝ} (hA : 2≤A) (ha₀ : 0<a₀) (hC₀ : 0≤C₀)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) (P : Descent.Label → Prop)
    (hcontinue : ∀(D : ScaledWave Cp a₀) (b : Plane),P (label C₀ D b) → L<D.growth 0 ∨ L<‖b‖)
    (n : ℕ) (D : ScaledWave Cp a₀) (b : Plane) (hbottom : a₀≤D.K/(A:ℝ)^n) :
    ∃t : WaveTree A Cp a₀,t.rootWave=D ∧ t.rootTilt=b ∧ Coherent n t ∧
      Descent.Tree.Valid C₁ (t.numerical C₀) ∧ Stopped C₀ P n t := by
  classical
  have hAr : 2≤(A:ℝ) := by exact_mod_cast hA
  have hArpos : 0<(A:ℝ) := by linarith
  induction n generalizing D b with
  | zero =>
    exact ⟨.stop D b,rfl,rfl,trivial,label_nonnegative ha₀ hC₀ D b,trivial⟩
  | succ n ih =>
    by_cases hP : P (label C₀ D b)
    · have hid : (D.K/(A:ℝ))/(A:ℝ)^n=D.K/(A:ℝ)^(n+1) := by rw [pow_succ]; ring
      have hnext : a₀≤D.K/(A:ℝ) := by
        have hpow : 1≤(A:ℝ)^n := one_le_pow₀ (by linarith)
        have hh := (le_div_iff₀ (pow_pos hArpos n)).mp (hid.symm ▸ hbottom)
        calc
          a₀ ≤ a₀*(A:ℝ)^n := le_mul_of_one_le_right ha₀.le hpow
          _ ≤ _ := hh
      obtain ⟨E,b',hchild,hinc,hdec⟩ := hrule D b hnext (hcontinue D b hP)
      have hbot (i : GridIndex A) : a₀≤(E i).K/(A:ℝ)^n := by rw [(hchild i).2.2.1,hid]; exact hbottom
      choose t hroot htilt hcoh hvalid hstop using (fun i =>ih (E i) (b' i) (hbot i))
      refine ⟨.step D b t,rfl,rfl,?_,?_,⟨hP,hstop⟩⟩
      · intro i
        rw [hroot i]
        exact ⟨hchild i,hcoh i⟩
      · refine ⟨(label_nonnegative ha₀ hC₀ D b).1,(label_nonnegative ha₀ hC₀ D b).2,?_,?_,hvalid⟩
        · simpa only [numerical_root,hroot,htilt,label] using hdec
        · simpa only [numerical_root,hroot,htilt,label] using hinc
    · exact ⟨.stop D b,rfl,rfl,trivial,label_nonnegative ha₀ hC₀ D b,hP⟩

end WaveTree
end SharpNodal.Profiles

noncomputable section
open scoped BigOperators
namespace SharpNodal.Profiles
open WaveTree

lemma stable_band_large_slope {Cp a₀ L Bstar η γ : ℝ} (hη : 0<η)
    (hγhalf : γ≤1/2) (hγη : γ≤η/2)
    (hlarge : ∀(D : UnitWave Cp a₀) (b : Plane),Bstar≤‖b‖ →
      D.growth b≤η*‖b‖ → L<D.growth 0)
    {b₀ : Plane} (hB : 0<‖b₀‖) (hBstar : 2*Bstar≤‖b₀‖)
    (D : ScaledWave Cp a₀) (b : Plane)
    (hgood : D.growth b<γ*‖b₀‖ ∧ ‖b-b₀‖<γ*‖b₀‖) : L<D.growth 0 := by
  have htri : ‖b₀‖≤‖b-b₀‖+‖b‖ := by
    calc
      ‖b₀‖=‖(b₀-b)+b‖ := by rw [sub_add_cancel]
      _ ≤ ‖b₀-b‖+‖b‖ := norm_add_le _ _
      _ = ‖b-b₀‖+‖b‖ := by rw [norm_sub_rev]
  have hc : ‖b₀‖/2≤‖b‖ := by nlinarith only [htri,hgood.2,hγhalf,hB]
  apply hlarge D.toUnitWave b (by linarith only [hc,hBstar])
  calc
    D.growth b ≤ γ*‖b₀‖ := hgood.1.le
    _ ≤ (η/2)*‖b₀‖ := mul_le_mul_of_nonneg_right hγη hB.le
    _ ≤ η*‖b‖ := by nlinarith only [hc,hη]

theorem actual_tree_stability {A : ℕ} {Cp a₀ C₀ C₁ L : ℝ} (hA : 2≤A)
    (hCp : 0≤Cp) (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) :
    ∃P σ γ : ℝ,1≤P ∧ 0<σ ∧ 0<γ ∧
    ∀(D : ScaledWave Cp a₀) (b : Plane) (n : ℕ),
      a₀≤D.K/(A:ℝ)^n → P≤‖b‖ → D.growth b≤σ*‖b‖ →
      ∃t : WaveTree A Cp a₀,t.rootWave=D ∧ t.rootTilt=b ∧ t.Coherent n ∧
        Descent.Tree.Valid C₁ (t.numerical C₀) ∧
        t.Stopped C₀ (fun a => a.mass<γ*‖b‖ ∧ ‖a.tilt-b‖<γ*‖b‖) n ∧
        (3:ℝ)/4≤Descent.Tree.goodProb (fun a => a.mass<γ*‖b‖ ∧ ‖a.tilt-b‖<γ*‖b‖) (t.numerical C₀) ∧
        ∀(E : ScaledWave Cp a₀) (c : Plane),
          E.growth c<γ*‖b‖ ∧ ‖c-b‖<γ*‖b‖ → L<E.growth 0 := by
  classical
  have : NeZero A := ⟨by omega⟩
  obtain ⟨Bstar,η,hBstar,hη,hlarge⟩ := large_slope_forces_growth hCp ha₀ L hL
  let γ := min (1/4) (η/4)
  have hγ : 0<γ := lt_min (by norm_num) (by positivity)
  have hγhalf : γ≤1/2 := (min_le_left _ _).trans (by norm_num)
  have hγη : γ≤η/2 := (min_le_right _ _).trans (by linarith)
  let F := 2*(C₀/a₀+1)
  have hF : 0≤F := by dsimp [F]; positivity
  let Cst := 2*(1+C₁)+(1+2*C₁)*F
  have hCst : 0<Cst := by dsimp [Cst]; positivity
  let σ := γ/(16*Cst)
  let P := max 1 (max (2*Bstar) (16*Cst/γ))
  have hP1 : 1≤P := le_max_left _ _
  have hσ : 0<σ := div_pos hγ (by positivity)
  refine ⟨P,σ,γ,hP1,hσ,hγ,?_⟩
  intro D b n hbottom hPb hm
  have hB : 0<‖b‖ := (by norm_num : (0:ℝ)<1).trans_le (hP1.trans hPb)
  have hBP : 2*Bstar≤‖b‖ := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hPb
  have hBlower : 16*Cst/γ≤‖b‖ := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hPb
  have hgood (E : ScaledWave Cp a₀) (c : Plane)
      (hc : E.growth c<γ*‖b‖ ∧ ‖c-b‖<γ*‖b‖) : L<E.growth 0 :=
    stable_band_large_slope hη hγhalf hγη hlarge hB hBP E c hc
  obtain ⟨t,hroot,htilt,hcoh,hvalid,hstop⟩ := WaveTree.build_stopped hA ha₀ hC₀ hrule
    (fun a =>a.mass<γ*‖b‖ ∧ ‖a.tilt-b‖<γ*‖b‖)
    (fun E c hc => Or.inl (hgood E c hc)) n D b hbottom
  refine ⟨t,hroot,htilt,hcoh,hvalid,hstop,?_,hgood⟩
  have hfloor := Descent.Tree.physical_floor_bound (by exact_mod_cast hA) hC₀ ha₀
    (ha₀.trans_le D.frequency_lower) D.side_pos.le D.side_le_one n hbottom
    (by simpa only [hroot] using WaveTree.coherent_floors C₀ hcoh)
  have hinv : 1/‖b‖≤γ/(16*Cst) := by
    apply (div_le_div_iff₀ hB (by positivity)).mpr
    have hh := (div_le_iff₀ hγ).mp hBlower
    nlinarith only [hh]
  have hσid : Cst*σ=γ/16 := by dsimp [σ]; field_simp
  have hsmall : Cst*(σ+1/‖b‖)≤γ/4 := by
    have hh := mul_le_mul_of_nonneg_left hinv hCst.le
    change Cst*(1/‖b‖)≤Cst*σ at hh
    rw [hσid] at hh
    nlinarith only [hh,hσid,hγ]
  have hh := Descent.Tree.stable_probability hC₁ hF hγ hB hσ.le hvalid hfloor
    (by simpa only [numerical_root,hroot,htilt,label] using hm) hsmall
  simpa only [numerical_root,hroot,htilt,label] using hh

end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
