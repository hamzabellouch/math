import OAI.Analysis.AllenCahn.JetProducts
import OAI.Analysis.AllenCahn.Reach

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ENNReal

lemma finite_chord_bounds {n : ℕ} {Γ : ℝ → ℝ} {v : Space n → ℝ}
    (hΓ : ∀ s, 0<s → s≤1 → s⁻¹≤Γ s) {z y : Space n}
    (hz : z∈regularZeroSet v) {b : ℝ} (_hb : 0≤b)
    (hv : reachChordValue Γ v z y<ENNReal.ofReal b) :
    y≠z ∧ 0<chordAngle v z y ∧
      ‖y-z‖*Γ (chordAngle v z y)<b ∧
      ‖y-z‖≤‖y-z‖*Γ (chordAngle v z y) ∧
      ‖y-z‖≤b*chordAngle v z y := by
  have hh : ¬(y=z ∨ chordAngle v z y=0) := by
    intro H
    simp [reachChordValue,H] at hv
  obtain ⟨hy,ha⟩ := not_or.mp hh
  have hap : 0<chordAngle v z y := lt_of_le_of_ne (abs_nonneg _) (Ne.symm ha)
  have hal := chordAngle_le_one hz hy
  have hgb := hΓ _ hap hal
  have hg1 : 1≤Γ (chordAngle v z y) := (one_le_inv₀ hap).mpr hal |>.trans hgb
  have hraw : ‖y-z‖*Γ (chordAngle v z y)<b := by
    simp only [reachChordValue,hh,ite_false] at hv
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp hv).1
  have hnorm : ‖y-z‖≤‖y-z‖*Γ (chordAngle v z y) := by
    nlinarith [norm_nonneg (y-z)]
  have hinv := mul_le_mul_of_nonneg_left hgb (norm_nonneg (y-z))
  have hh' := (div_le_iff₀ hap).mp (by simpa [div_eq_mul_inv] using hinv)
  refine ⟨hy,hap,hraw,hnorm,?_⟩
  exact hh'.trans (mul_le_mul_of_nonneg_right hraw.le hap.le)

def DiagonalActive {n : ℕ} (Γ : ℝ → ℝ) (v : Space n → ℝ) (z : Space n) : Prop :=
  ∃ y : ℕ → Space n,
    (∀ k, v (y k)=0 ∧ y k≠z ∧ 0<chordAngle v z (y k)) ∧
    Tendsto y atTop (𝓝 z) ∧
    Tendsto (fun k=>‖y k-z‖*Γ (chordAngle v z (y k))) atTop
      (𝓝 (penalizedReach Γ v z).toReal)

lemma exists_reach_minimizing_sequence {n : ℕ} {Γ : ℝ → ℝ} {v : Space n → ℝ}
    (hΓ : ∀ s, 0<s → s≤1 → s⁻¹≤Γ s) {z : Space n}
    (hz : z∈regularZeroSet v) (hd : penalizedReach Γ v z≠⊤) :
    ∃ y : ℕ → Space n,
      (∀ k, v (y k)=0 ∧ y k≠z ∧ 0<chordAngle v z (y k)) ∧
      (∀ k, ‖y k-z‖≤(penalizedReach Γ v z).toReal+1) ∧
      (∀ k, ‖y k-z‖≤((penalizedReach Γ v z).toReal+1)*chordAngle v z (y k)) ∧
      Tendsto (fun k=>‖y k-z‖*Γ (chordAngle v z (y k))) atTop
        (𝓝 (penalizedReach Γ v z).toReal) := by
  classical
  let d := (penalizedReach Γ v z).toReal
  have hd0 : 0≤d := ENNReal.toReal_nonneg
  have H (k : ℕ) : ∃ y : {y : Space n // v y=0},
      reachChordValue Γ v z y<ENNReal.ofReal (d+((k : ℝ)+1)⁻¹) := by
    apply iInf_lt_iff.mp
    change penalizedReach Γ v z<_
    rw [←ENNReal.ofReal_toReal hd]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    exact lt_add_of_pos_right _ (by positivity)
  choose y hy using H
  let Y : ℕ → Space n := fun k=>(y k).val
  have he (k : ℕ) : 0<((k : ℝ)+1)⁻¹ := by positivity
  have he1 (k : ℕ) : ((k : ℝ)+1)⁻¹≤1 := by
    exact (inv_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) k])
  have hb (k : ℕ) := finite_chord_bounds hΓ hz (by positivity : 0≤d+((k : ℝ)+1)⁻¹) (hy k)
  refine ⟨Y,fun k=>⟨(y k).property,(hb k).1,(hb k).2.1⟩,?_,?_,?_⟩
  · intro k
    exact (hb k).2.2.2.1.trans ((hb k).2.2.1.le.trans (by linarith [he1 k]))
  · intro k
    exact (hb k).2.2.2.2.trans
      (mul_le_mul_of_nonneg_right (by linarith [he1 k]) (hb k).2.1.le)
  · have hlo (k : ℕ) : d≤‖Y k-z‖*Γ (chordAngle v z (Y k)) := by
      have hi := iInf_le (fun y : {y : Space n // v y=0}=>reachChordValue Γ v z y) (y k)
      change penalizedReach Γ v z≤reachChordValue Γ v z (Y k) at hi
      have hy0 : Y k≠z := (hb k).1
      have ha0 : chordAngle v z (Y k)≠0 := ne_of_gt (hb k).2.1
      simp only [reachChordValue,hy0,ha0,or_self,ite_false] at hi
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
      rw [ENNReal.toReal_ofReal ((norm_nonneg _).trans (hb k).2.2.2.1)] at hh
      exact hh
    have hhi (k : ℕ) : ‖Y k-z‖*Γ (chordAngle v z (Y k))≤d+((k : ℝ)+1)⁻¹ := (hb k).2.2.1.le
    have hlim : Tendsto (fun k : ℕ=>d+((k : ℝ)+1)⁻¹) atTop (𝓝 d) := by
      simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo hhi

theorem reach_active_contact {n : ℕ} {Γ : ℝ → ℝ} {v : Space n → ℝ}
    (hv : Continuous v) (hΓ : ∀ s, 0<s → s≤1 → s⁻¹≤Γ s)
    (hΓc : ContinuousOn Γ (Set.Ioc (0 : ℝ) 1)) {z : Space n}
    (hz : z∈regularZeroSet v) (hd : penalizedReach Γ v z≠⊤) :
    (∃ y, OffDiagonalActive Γ v z y) ∨ DiagonalActive Γ v z := by
  obtain ⟨Y,hY,hB,hC,hV⟩ := exists_reach_minimizing_sequence hΓ hz hd
  let d := (penalizedReach Γ v z).toReal
  have hd0 : 0≤d := ENNReal.toReal_nonneg
  obtain ⟨y,hyB,φ,hφ,hy⟩ := (isCompact_closedBall z (d+1)).tendsto_subseq (x:=Y)
    (fun k=>by simpa only [Metric.mem_closedBall,dist_eq_norm] using hB k)
  have hzero : v y=0 := by
    apply (isClosed_eq hv continuous_const).mem_of_tendsto hy
    exact Filter.Eventually.of_forall (fun k=>(hY (φ k)).1)
  by_cases hyz : y=z
  · right
    refine ⟨Y ∘ φ,fun k=>hY (φ k),?_,?_⟩
    · simpa [hyz] using hy
    · exact hV.comp hφ.tendsto_atTop
  · left
    have halim := (chordAngle_continuousAt v hyz).tendsto.comp hy
    have hnlim := (hy.sub (tendsto_const_nhds (x:=z))).norm
    have hcone : ‖y-z‖≤(d+1)*chordAngle v z y :=
      le_of_tendsto_of_tendsto hnlim (tendsto_const_nhds.mul halim)
        (Filter.Eventually.of_forall (fun k=>hC (φ k)))
    have hap : 0<chordAngle v z y := by
      have hlp : 0<‖y-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
      by_contra H
      have hle := le_of_not_gt H
      nlinarith
    have hal : chordAngle v z y≤1 := chordAngle_le_one hz hyz
    have halim' : Tendsto (fun k=>chordAngle v z (Y (φ k))) atTop
        (𝓝[Set.Ioc (0 : ℝ) 1] (chordAngle v z y)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨halim,Filter.Eventually.of_forall (fun k=>
        ⟨(hY (φ k)).2.2,chordAngle_le_one hz (hY (φ k)).2.1⟩)⟩
    have hglim := (hΓc _ ⟨hap,hal⟩).tendsto.comp halim'
    have he : ‖y-z‖*Γ (chordAngle v z y)=d :=
      tendsto_nhds_unique (hnlim.mul hglim) (hV.comp hφ.tendsto_atTop)
    refine ⟨y,hz,hzero,hyz,hap,?_⟩
    simp only [reachChordValue,hyz,ne_of_gt hap,or_self,ite_false,he]
    exact ENNReal.ofReal_toReal hd

theorem diagonal_contact_tangent_realization {n : ℕ} {Γ : ℝ → ℝ}
    {v : Space n → ℝ} (hU : ContDiff ℝ 2 (inverseProfile v))
    {z : Space n} (hz : z∈regularZeroSet v) (hd : DiagonalActive Γ v z) :
    ∃ (Y : ℕ → Space n) (e : Space n),
      (∀ k, v (Y k)=0 ∧ Y k≠z ∧ 0<chordAngle v z (Y k)) ∧
      Tendsto Y atTop (𝓝 z) ∧
      Tendsto (fun k=>‖Y k-z‖*Γ (chordAngle v z (Y k))) atTop
        (𝓝 (penalizedReach Γ v z).toReal) ∧
      ‖e‖=1 ∧ inner ℝ (interfaceNormal v z) e=0 ∧
      Tendsto (fun k=>chordDirection z (Y k)) atTop (𝓝 e) := by
  obtain ⟨Y,hY,ht,hval⟩ := hd
  obtain ⟨e,he,φ,hφ,het⟩ := (isCompact_sphere (0 : Space n) 1).tendsto_subseq
    (x:=fun k=>chordDirection z (Y k)) (fun k=>by
      simpa only [Metric.mem_sphere,dist_zero_right] using chordDirection_norm (hY k).2.1)
  have he1 : ‖e‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using he
  obtain ⟨r,B,hr,hB,hbound⟩ := regular_zero_local_chord_bound hU hz
  have hev : ∀ᶠ k in atTop, chordAngle v z (Y k)≤B*‖Y k-z‖ := by
    filter_upwards [ht.eventually (Metric.ball_mem_nhds _ hr)] with k hk
    have H := hbound _ hk (hY k).1
    have heq := chordAngle_mul_length v (hY k).2.1
    apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (hY k).2.1))).mp
    nlinarith
  have ha : Tendsto (fun k=>chordAngle v z (Y k)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using tendsto_const_nhds.mul (ht.sub (tendsto_const_nhds (x:=z))).norm)
      (Filter.Eventually.of_forall (fun k=>abs_nonneg _)) hev
  have htan : inner ℝ (interfaceNormal v z) e=0 := by
    apply abs_eq_zero.mp
    exact tendsto_nhds_unique
      ((tendsto_const_nhds.inner het).abs) (ha.comp hφ.tendsto_atTop)
  exact ⟨Y ∘ φ,e,fun k=>hY (φ k),ht.comp hφ.tendsto_atTop,
    hval.comp hφ.tendsto_atTop,he1,htan,het⟩

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ENNReal
open Filter Topology Asymptotics

lemma second_order_remainder {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (z : Space n) :
    (fun x=>f x-f z-fderiv ℝ f z (x-z)-
      (1/2 : ℝ)*(fderiv ℝ (fderiv ℝ f) z (x-z)) (x-z))
      =o[𝓝 z] (fun x=>‖x-z‖^2) := by
  let H := fderiv ℝ (fderiv ℝ f) z
  let g : Space n → ℝ := fun x=>f x-f z-fderiv ℝ f z (x-z)-
      (1/2 : ℝ)*H (x-z) (x-z)
  let g' : Space n → (Space n →L[ℝ] ℝ) := fun x=>fderiv ℝ f x-fderiv ℝ f z-H (x-z)
  have hsym : ∀ a b, H a b=H b a := hf.contDiffAt (x:=z) |>.isSymmSndFDerivAt (by norm_num)
  have hd (x : Space n) : HasFDerivAt g (g' x) x := by
    have hlin := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const z
    have hquad := ((H.hasFDerivAt.comp x hlin).clm_apply hlin).const_mul (1/2 : ℝ)
    have h := (((hf.differentiable (by norm_num) x).hasFDerivAt.sub_const (f z)).sub
      ((fderiv ℝ f z).hasFDerivAt.comp x hlin)).sub hquad
    convert h using 1 <;> try rfl
    ext a
    simp only [g',sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,smul_apply,smul_eq_mul,
      add_apply,ContinuousLinearMap.flip_apply]
    simp only [Function.comp_apply,id_eq]
    rw [hsym a (x-z)]
    ring
  have hfder : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hsmall : g' =o[𝓝 z] (fun x=>‖x-z‖^1) := by
    simpa only [pow_one] using
      (hfder.differentiable (by norm_num) z).hasFDerivAt.isLittleO.norm_right
  have hp := convex_univ.isLittleO_pow_succ (Set.mem_univ z)
    (fun x _=>(hd x).hasFDerivWithinAt) (n:=1) (by simpa using hsmall)
  simpa [g,sub_self,map_zero] using hp

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ENNReal

theorem diagonal_active_curvature {n : ℕ} {Γ : ℝ → ℝ} {v : Space n → ℝ}
    (hU : ContDiff ℝ 2 (inverseProfile v))
    {s₀ : ℝ} (hs₀ : 0<s₀) (hΓ : ∀ s, 0<s → s<s₀ → Γ s=1/s)
    {z : Space n} (hz : z∈regularZeroSet v) (hd : DiagonalActive Γ v z) :
    ∃ e : Space n, ‖e‖=1 ∧ inner ℝ (interfaceNormal v z) e=0 ∧
      (penalizedReach Γ v z).toReal *
        |(fderiv ℝ (fderiv ℝ (inverseProfile v)) z e) e| =
          2*‖gradient (inverseProfile v) z‖ := by
  obtain ⟨Y,e,hY,ht,hval,he1,hetan,he⟩ :=
    diagonal_contact_tangent_realization hU hz hd
  let U := inverseProfile v
  let p := ‖gradient U z‖
  let H := fderiv ℝ (fderiv ℝ U) z
  let E : ℕ → Space n := fun k=>chordDirection z (Y k)
  let r : ℕ → ℝ := fun k=>‖Y k-z‖
  have hp : 0<p := norm_pos_iff.mpr hz.2
  have hr (k : ℕ) : r k≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hY k).2.1)
  have hUz : U z=0 := by simp [U,inverseProfile,hz.1]
  have hUy (k : ℕ) : U (Y k)=0 := by simp [U,inverseProfile,(hY k).1]
  have hHlim : Tendsto (fun k=>H (E k) (E k)) atTop (𝓝 (H e e)) := by
    exact ((H.continuous.clm_apply continuous_id).tendsto e).comp he
  have hid (k : ℕ) :
      (U (Y k)-U z-fderiv ℝ U z (Y k-z)-(1/2 : ℝ)*H (Y k-z) (Y k-z))/(r k)^2 =
        -p*(inner ℝ (interfaceNormal v z) (E k)/r k)-(1/2 : ℝ)*H (E k) (E k) := by
    rw [hUy,hUz]
    simp only [E,chordDirection,interfaceNormal,inner_smul_left,inner_smul_right,
      inner_gradient_left,conj_trivial,map_smul,smul_apply,smul_eq_mul]
    change (0-0-fderiv ℝ U z (Y k-z)-1/2*H (Y k-z) (Y k-z))/(r k)^2 =
      -p*((r k)⁻¹*(p⁻¹*fderiv ℝ U z (Y k-z))/r k)-
        1/2*((r k)⁻¹*((r k)⁻¹*H (Y k-z) (Y k-z)))
    field_simp [hr k,ne_of_gt hp]; ring
  have herr := ((second_order_remainder hU z).tendsto_div_nhds_zero).comp ht
  have herr' : Tendsto (fun k=>-p*(inner ℝ (interfaceNormal v z) (E k)/r k)-
      (1/2 : ℝ)*H (E k) (E k)) atTop (𝓝 0) := by
    exact herr.congr (fun k=>hid k)
  have hsigned : Tendsto (fun k=>inner ℝ (interfaceNormal v z) (E k)/r k) atTop
      (𝓝 (-(H e e)/(2*p))) := by
    have hh := (herr'.add ((tendsto_const_nhds (x:=(1/2 : ℝ))).mul hHlim)).div_const (-p)
    convert hh using 1
    · ext k
      field_simp [ne_of_gt hp]; ring
    · field_simp [ne_of_gt hp]; ring_nf
  have hratio : Tendsto (fun k=>chordAngle v z (Y k)/r k) atTop
      (𝓝 (|H e e|/(2*p))) := by
    simpa only [r,chordAngle,E,abs_div,abs_of_nonneg (norm_nonneg _),abs_neg,abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ)<2),abs_of_pos hp] using hsigned.abs
  have ha : Tendsto (fun k=>chordAngle v z (Y k)) atTop (𝓝 0) := by
    have hi : Tendsto (fun k=>inner ℝ (interfaceNormal v z) (chordDirection z (Y k)))
        atTop (𝓝 (inner ℝ (interfaceNormal v z) e)) := tendsto_const_nhds.inner he
    simpa only [chordAngle,hetan,abs_zero] using hi.abs
  have hv : ∀ᶠ k in atTop,
      (r k*Γ (chordAngle v z (Y k)))*(chordAngle v z (Y k)/r k)=1 := by
    filter_upwards [ha.eventually (gt_mem_nhds hs₀)] with k hk
    rw [hΓ _ (hY k).2.2 hk]
    field_simp [hr k,ne_of_gt (hY k).2.2]
  have hprod : (penalizedReach Γ v z).toReal * (|H e e|/(2*p))=1 :=
    tendsto_nhds_unique (hval.mul hratio) (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hv))
  refine ⟨e,he1,hetan,?_⟩
  have hh := (div_eq_iff (by positivity : 2*p≠0)).mp
    (by simpa only [←mul_div_assoc] using hprod)
  simpa only [one_mul] using hh

end DeGiorgi
end

end OAI
