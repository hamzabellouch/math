import OAI.Geometry.PlaneColoring.Coloring

namespace OAI

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
abbrev RealPlane := ℝ × ℝ
def circleSum (r : ℝ) (p : RealPlane) : RealPlane :=
  (r*Real.cos p.1+Real.cos p.2,r*Real.sin p.1+Real.sin p.2)
def circleSumDeriv (r : ℝ) (p : RealPlane) : RealPlane →L[ℝ] RealPlane :=
  (r • ((-Real.sin p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (-Real.sin p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
  (r • (Real.cos p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    Real.cos p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
lemma circleSum_strict (r : ℝ) (p : RealPlane) : HasStrictFDerivAt (circleSum r) (circleSumDeriv r p) p := by
  have hc1 := (Real.hasStrictDerivAt_cos p.1).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt
  have hc2 := (Real.hasStrictDerivAt_cos p.2).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt
  have hs1 := (Real.hasStrictDerivAt_sin p.1).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt
  have hs2 := (Real.hasStrictDerivAt_sin p.2).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt
  exact ((hc1.const_smul r).add hc2).prodMk ((hs1.const_smul r).add hs2)
lemma circleSum_continuous (r : ℝ) : Continuous (circleSum r) :=
  continuous_iff_continuousAt.mpr fun p => (circleSum_strict r p).continuousAt
lemma circleSumDeriv_injective {r : ℝ} {p : RealPlane} (h : r*Real.sin (p.2-p.1) ≠ 0) :
    Function.Injective (circleSumDeriv r p) := by
  apply (circleSumDeriv r p).toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  change r * (-Real.sin p.1 * q.1) + -Real.sin p.2 * q.2 = 0 at h1
  change r * (Real.cos p.1 * q.1) + Real.cos p.2 * q.2 = 0 at h2
  have ha : r*Real.sin (p.2-p.1)*q.1=0 := by
    rw [Real.sin_sub]
    linear_combination Real.cos p.2*h1+Real.sin p.2*h2
  have hb : r*Real.sin (p.2-p.1)*q.2=0 := by
    rw [Real.sin_sub]
    linear_combination -(r*Real.cos p.1)*h1-(r*Real.sin p.1)*h2
  exact Prod.ext ((mul_eq_zero.mp ha).resolve_left h) ((mul_eq_zero.mp hb).resolve_left h)
def circleSumDerivEquiv {r : ℝ} {p : RealPlane} (h : r*Real.sin (p.2-p.1) ≠ 0) :
    RealPlane ≃L[ℝ] RealPlane :=
  ContinuousLinearEquiv.ofBijective (circleSumDeriv r p)
    (LinearMap.ker_eq_bot.mpr (circleSumDeriv_injective h))
    (LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (circleSumDeriv_injective h)))
lemma circleSum_local_antilipschitz {r : ℝ} {p : RealPlane} (h : r*Real.sin (p.2-p.1) ≠ 0) :
    ∃ s : Set RealPlane, IsOpen s ∧ p ∈ s ∧ ∃ K : ℝ≥0, AntilipschitzWith K (s.domRestrict (circleSum r)) := by
  let L := circleSumDerivEquiv h
  have hd : HasStrictFDerivAt (circleSum r) (L : RealPlane →L[ℝ] RealPlane) p := circleSum_strict r p
  obtain ⟨s,hp,hs,ha⟩ := hd.approximates_deriv_on_open_nhds
  refine ⟨s,hs,hp,_,ha.antilipschitz ?_⟩
  right
  have hpos := L.subsingleton_or_nnnorm_symm_pos.resolve_left (not_subsingleton RealPlane)
  exact half_lt_self (inv_pos.mpr hpos)
lemma realDirection_lipschitz : LipschitzWith 1 (fun t : ℝ => (Real.cos t,Real.sin t)) := by
  simpa using Real.lipschitzWith_cos.prodMk Real.lipschitzWith_sin
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
def circleInverseHomeo : OpenPartialHomeomorph RealPlane RealPlane :=
  (show HasStrictFDerivAt (circleSum 1)
    (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
    (t,u) from circleSum_strict 1 (t,u)).toOpenPartialHomeomorph (circleSum 1)
def circleInverse : RealPlane → RealPlane := by
  classical
  exact (circleInverseHomeo h).target.piecewise (circleInverseHomeo h).symm (fun _ => 0)
lemma circleInverse_measurable : Measurable (circleInverse h) := by
  classical
  exact (circleInverseHomeo h).continuousOn_invFun.measurable_piecewise continuous_const.continuousOn
    (circleInverseHomeo h).open_target.measurableSet
lemma circleInverse_eq {q : RealPlane} (hq : q ∈ (circleInverseHomeo h).target) :
    circleInverse h q=(circleInverseHomeo h).symm q := by simp [circleInverse,hq]
lemma circleInverse_at : circleInverse h (circleSum 1 (t,u))=(t,u) := by
  have hd : HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
      (t,u) := circleSum_strict 1 (t,u)
  rw [circleInverse_eq h hd.image_mem_toOpenPartialHomeomorph_target]
  exact hd.localInverse_apply_image
lemma circleInverse_continuousAt {q : RealPlane} (hq : q ∈ (circleInverseHomeo h).target) :
    ContinuousAt (circleInverse h) q := by
  apply ((circleInverseHomeo h).continuousAt_symm hq).congr_of_eventuallyEq
  filter_upwards [(circleInverseHomeo h).open_target.mem_nhds hq] with y hy
  exact circleInverse_eq h hy
lemma circleInverse_strict : HasStrictFDerivAt (circleInverse h)
    ((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm : RealPlane →L[ℝ] RealPlane)
      (circleSum 1 (t,u)) := by
  have hd : HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
      (t,u) := circleSum_strict 1 (t,u)
  apply hd.to_localInverse.congr_of_eventuallyEq
  filter_upwards [(circleInverseHomeo h).open_target.mem_nhds hd.image_mem_toOpenPartialHomeomorph_target] with q hq
  exact (circleInverse_eq h hq).symm
lemma circleInverse_right {q : RealPlane} (hq : q ∈ (circleInverseHomeo h).target) :
    circleSum 1 (circleInverse h q)=q := by
  rw [circleInverse_eq h hq]
  exact (circleInverseHomeo h).right_inv hq
lemma circleInverse_regular :
    ∀ᶠ q in 𝓝 (circleSum 1 (t,u)), Real.sin ((circleInverse h q).2-(circleInverse h q).1) ≠ 0 := by
  have hc := (Real.continuous_sin.continuousAt.comp
    ((circleInverse_strict h).continuousAt.snd.sub (circleInverse_strict h).continuousAt.fst))
  have hh : Real.sin ((circleInverse h (circleSum 1 (t,u))).2-(circleInverse h (circleSum 1 (t,u))).1) ≠ 0 := by
    rwa [circleInverse_at h]
  exact hc.eventually_ne hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma triangular_injective (L : E × ℝ →L[ℝ] ℝ) (hc : L (0,1) ≠ 0) :
    Function.Injective ((ContinuousLinearMap.fst ℝ E ℝ).prod L) := by
  intro a b hab
  change (a.1,L a)=(b.1,L b) at hab
  have hab₁ := congrArg (fun q : E × ℝ => q.1) hab
  have hab₂ := congrArg (fun q : E × ℝ => q.2) hab
  dsimp only at hab₁ hab₂
  have he : a-b=(0,a.2-b.2) := Prod.ext (by simp [hab₁]) rfl
  have hz : L (0,a.2-b.2)=0 := by rw [← he,map_sub,hab₂,sub_self]
  have hm : L (0,a.2-b.2)=(a.2-b.2)*L (0,1) := by
    have h : (0,a.2-b.2)=(a.2-b.2) • ((0,1) : E × ℝ) := by ext <;> simp
    rw [h,map_smul,smul_eq_mul]
  rw [hm] at hz
  exact Prod.ext hab₁ (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc))
omit [CompleteSpace E] in
lemma triangular_surjective (L : E × ℝ →L[ℝ] ℝ) (hc : L (0,1) ≠ 0) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ E ℝ).prod L) := by
  intro b
  refine ⟨(b.1,(b.2-L (b.1,0))/L (0,1)),Prod.ext rfl ?_⟩
  change L (b.1,(b.2-L (b.1,0))/L (0,1))=b.2
  have h (r : ℝ) : L (b.1,r)=L (b.1,0)+r*L (0,1) := by
    have he : (b.1,r)=(b.1,0)+r • ((0,1) : E × ℝ) := by ext <;> simp
    rw [he,map_add,map_smul,smul_eq_mul]
  rw [h,div_mul_cancel₀ _ hc]
  ring
/-- Joint strict differentiability and a nonzero fiber derivative give one inverse
Lipschitz bound simultaneously for every nearby parameter. -/
lemma strict_fiber_uniform_antilipschitz {S : E × ℝ → ℝ} {L : E × ℝ →L[ℝ] ℝ}
    {p : E} {t : ℝ} (hS : HasStrictFDerivAt S L (p,t)) (hc : L (0,1) ≠ 0) :
    ∃ P : Set E, ∃ I : Set ℝ, IsOpen P ∧ p ∈ P ∧ IsOpen I ∧ t ∈ I ∧
      ∃ K : ℝ≥0, ∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun u => S (q,u))) := by
  let T := (ContinuousLinearMap.fst ℝ E ℝ).prod L
  let H : E × ℝ → E × ℝ := fun q => (q.1,S q)
  let Q : (E × ℝ) ≃L[ℝ] (E × ℝ) := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr (triangular_injective L hc))
    (LinearMap.range_eq_top.mpr (triangular_surjective L hc))
  have hd : HasStrictFDerivAt H (Q : E × ℝ →L[ℝ] E × ℝ) (p,t) :=
    hasStrictFDerivAt_fst.prodMk hS
  obtain ⟨V,hpt,hVo,hA⟩ := hd.approximates_deriv_on_open_nhds
  have hK := hA.antilipschitz (Or.inr (half_lt_self (inv_pos.mpr
    (Q.subsingleton_or_nnnorm_symm_pos.resolve_left (not_subsingleton (E × ℝ))))))
  obtain ⟨P,hP,I,hI,hsub⟩ := mem_nhds_prod_iff.mp (hVo.mem_nhds hpt)
  obtain ⟨P',hP'P,hP'o,hp⟩ := mem_nhds_iff.mp hP
  obtain ⟨I',hI'I,hI'o,ht⟩ := mem_nhds_iff.mp hI
  refine ⟨P',I',hP'o,hp,hI'o,ht,(‖(Q.symm : (E × ℝ) →L[ℝ] (E × ℝ))‖₊⁻¹ - ‖(Q.symm : (E × ℝ) →L[ℝ] (E × ℝ))‖₊⁻¹ / 2)⁻¹,?_⟩
  intro q hq
  apply AntilipschitzWith.of_le_mul_dist
  intro a b
  have ha : (q,a.1) ∈ V := hsub ⟨hP'P hq,hI'I a.2⟩
  have hb : (q,b.1) ∈ V := hsub ⟨hP'P hq,hI'I b.2⟩
  have h := hK.le_mul_dist ⟨(q,a.1),ha⟩ ⟨(q,b.1),hb⟩
  simpa only [Subtype.dist_eq,domRestrict,H,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using h
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
abbrev CircleParameter := RealPlane × ℝ
abbrev CircleJet := CircleParameter × ℝ
def jetCenter : CircleJet →L[ℝ] RealPlane :=
  (ContinuousLinearMap.fst ℝ RealPlane ℝ).comp (ContinuousLinearMap.fst ℝ CircleParameter ℝ)
def jetRadius : CircleJet →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ RealPlane ℝ).comp (ContinuousLinearMap.fst ℝ CircleParameter ℝ)
def jetAngle : CircleJet →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ CircleParameter ℝ
def circleTarget (q : CircleJet) : RealPlane := q.1.1+q.1.2 • (Real.cos q.2,Real.sin q.2)
def circleTargetDeriv (q : CircleJet) : CircleJet →L[ℝ] RealPlane :=
  jetCenter + (q.1.2 • (((-Real.sin q.2) • jetAngle).prod (Real.cos q.2 • jetAngle)) +
    jetRadius.smulRight (Real.cos q.2,Real.sin q.2))
lemma circleTarget_strict (q : CircleJet) : HasStrictFDerivAt circleTarget (circleTargetDeriv q) q := by
  have hc := (Real.hasStrictDerivAt_cos q.2).comp_hasStrictFDerivAt q jetAngle.hasStrictFDerivAt
  have hs := (Real.hasStrictDerivAt_sin q.2).comp_hasStrictFDerivAt q jetAngle.hasStrictFDerivAt
  exact jetCenter.hasStrictFDerivAt.add (jetRadius.hasStrictFDerivAt.smul (hc.prodMk hs))
lemma circleTarget_continuous : Continuous circleTarget :=
  continuous_iff_continuousAt.mpr fun q => (circleTarget_strict q).continuousAt
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
def circleEndpoint (q : CircleJet) : ℝ := (circleInverse h (circleTarget q)).1
def circleEndpointDeriv (q : CircleJet) : CircleJet →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm : RealPlane →L[ℝ] RealPlane).comp
      (circleTargetDeriv q))
lemma circleEndpoint_measurable : Measurable (circleEndpoint h) :=
  measurable_fst.comp ((circleInverse_measurable h).comp circleTarget_continuous.measurable)
lemma circleEndpoint_strict {q : CircleJet} (he : circleTarget q=circleSum 1 (t,u)) :
    HasStrictFDerivAt (circleEndpoint h) (circleEndpointDeriv h q) q := by
  have hi := circleInverse_strict h
  rw [← he] at hi
  exact hasStrictFDerivAt_fst.comp q (hi.comp q (circleTarget_strict q))
lemma inverse_tangent_first_ne {a : ℝ} (ha : Real.sin (a-u) ≠ 0) :
    ((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm
      (-Real.sin a,Real.cos a)).1 ≠ 0 := by
  let L := circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)
  let q := L.symm (-Real.sin a,Real.cos a)
  intro hq
  have he : circleSumDeriv 1 (t,u) q=(-Real.sin a,Real.cos a) := L.apply_symm_apply _
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  change q.1=0 at hq
  change 1*(-Real.sin t*q.1) + -Real.sin u*q.2 = -Real.sin a at h₁
  change 1*(Real.cos t*q.1) + Real.cos u*q.2 = Real.cos a at h₂
  simp only [hq,mul_zero,zero_add] at h₁ h₂
  apply ha
  rw [Real.sin_sub]
  linear_combination (Real.cos u)*h₁+(Real.sin u)*h₂
lemma circleEndpoint_fiber_ne {q : CircleJet} (hr : q.1.2=1) (ha : Real.sin (q.2-u) ≠ 0) :
    circleEndpointDeriv h q (0,1) ≠ 0 := by
  have he : circleTargetDeriv q (0,1)=(-Real.sin q.2,Real.cos q.2) := by
    simp [circleTargetDeriv,jetCenter,jetRadius,jetAngle,hr]
  change (((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm
    (circleTargetDeriv q (0,1))).1) ≠ 0
  rw [he]
  exact inverse_tangent_first_ne h ha
lemma circleEndpoint_uniform {p : CircleParameter} {a : ℝ}
    (he : circleTarget (p,a)=circleSum 1 (t,u)) (hr : p.2=1) (ha : Real.sin (a-u) ≠ 0) :
    ∃ P : Set CircleParameter, ∃ I : Set ℝ, IsOpen P ∧ p ∈ P ∧ IsOpen I ∧ a ∈ I ∧
      ∃ K : ℝ≥0, ∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun v => circleEndpoint h (q,v))) :=
  strict_fiber_uniform_antilipschitz (circleEndpoint_strict h he) (circleEndpoint_fiber_ne h hr ha)
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
lemma circleEndpoint_good_neighborhood {p : CircleParameter} {a : ℝ}
    (he : circleTarget (p,a)=circleSum 1 (t,u)) (hr : p.2=1) (ha : Real.sin (a-u) ≠ 0) :
    ∃ P : Set CircleParameter, ∃ I : Set ℝ, IsOpen P ∧ p ∈ P ∧ IsOpen I ∧ a ∈ I ∧
      I ⊆ Ioc (a-Real.pi) (a-Real.pi+2*Real.pi) ∧
      ∃ K : ℝ≥0, (∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun v => circleEndpoint h (q,v)))) ∧
        ∀ q ∈ P, ∀ v ∈ I,
          circleTarget (q,v) ∈ (circleInverseHomeo h).target ∧
          Real.sin ((circleInverse h (circleTarget (q,v))).2-(circleInverse h (circleTarget (q,v))).1) ≠ 0 ∧
          circleEndpoint h (q,v) ∈ Metric.closedBall t 1 := by
  obtain ⟨P₀,I₀,hP₀,hp₀,hI₀,ha₀,K,hK⟩ := circleEndpoint_uniform h he hr ha
  have hc : ContinuousAt circleTarget (p,a) := circleTarget_continuous.continuousAt
  have hi := (circleEndpoint_strict h he).continuousAt
  have hs : ∀ᶠ w in 𝓝 (p,a), circleEndpoint h w ∈ Metric.ball t 1 := by
    have hb : Metric.ball t 1 ∈ 𝓝 (circleEndpoint h (p,a)) := by
      have ht : circleEndpoint h (p,a)=t := by simp [circleEndpoint,he,circleInverse_at]
      rw [ht]
      exact Metric.ball_mem_nhds _ (by norm_num)
    exact hi hb
  have ht : ∀ᶠ w in 𝓝 (p,a), circleTarget w ∈ (circleInverseHomeo h).target := by
    apply hc
    rw [he]
    exact (circleInverseHomeo h).open_target.mem_nhds
      ((show HasStrictFDerivAt (circleSum 1)
        (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
        (t,u) from circleSum_strict 1 (t,u)).image_mem_toOpenPartialHomeomorph_target)
  have hn : ∀ᶠ w in 𝓝 (p,a), Real.sin ((circleInverse h (circleTarget w)).2-(circleInverse h (circleTarget w)).1) ≠ 0 := by
    exact hc.eventually (by simpa only [he] using circleInverse_regular h)
  obtain ⟨P₁,hP₁,I₁,hI₁,hsub⟩ := mem_nhds_prod_iff.mp (ht.and (hn.and hs))
  obtain ⟨P₂,hP₂,hP₂o,hp₂⟩ := mem_nhds_iff.mp hP₁
  obtain ⟨I₂,hI₂,hI₂o,ha₂⟩ := mem_nhds_iff.mp hI₁
  let P := P₀ ∩ P₂
  let I := I₀ ∩ I₂ ∩ Ioo (a-Real.pi) (a+Real.pi)
  refine ⟨P,I,hP₀.inter hP₂o,⟨hp₀,hp₂⟩,(hI₀.inter hI₂o).inter isOpen_Ioo,
    ⟨⟨ha₀,ha₂⟩,by constructor <;> linarith [Real.pi_pos]⟩,?_,K,?_,?_⟩
  · intro v hv
    exact ⟨hv.2.1,by linarith [hv.2.2]⟩
  · intro q hq
    apply AntilipschitzWith.of_le_mul_dist
    intro v w
    exact (hK q hq.1).le_mul_dist ⟨v.1,v.2.1.1⟩ ⟨w.1,w.2.1.1⟩
  · intro q hq v hv
    have hh := hsub (show (q,v) ∈ P₁ ×ˢ I₁ from ⟨hP₂ hq.2,hI₂ hv.1.2⟩)
    exact ⟨hh.1,hh.2.1,Metric.ball_subset_closedBall hh.2.2⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
def angleChart (p : RealPlane) : Angles × Angles := ((p.1 : Angles),(p.2 : Angles))
def angleChartMeasure : Measure RealPlane :=
  volume.restrict (Ioc (0 : ℝ) (2*Real.pi) ×ˢ Ioc (0 : ℝ) (2*Real.pi))
lemma angleChartMeas_le : angleChartMeasure ≤ volume := Measure.restrict_le_self
instance : IsFiniteMeasure angleChartMeasure := by
  change IsFiniteMeasure (volume.restrict _)
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  apply (measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)).trans_lt
  exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
lemma angleChart_preserving : MeasurePreserving angleChart angleChartMeasure
    ((volume : Measure Angles).prod volume) := by
  have h := (AddCircle.measurePreserving_mk (2*Real.pi) 0).prod
    (AddCircle.measurePreserving_mk (2*Real.pi) 0)
  convert h using 1
  · rfl
  · simp only [angleChartMeasure,zero_add,Measure.prod_restrict,← Measure.volume_eq_prod]
lemma angleChart_measure : (angleChartMeasure.map angleChart) =
    (ENNReal.ofReal (2*Real.pi))^2 • angularMeasure.prod angularMeasure := by
  rw [angleChart_preserving.map_eq,AddCircle.volume_eq_smul_haarAddCircle,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,pow_two]
  rfl
lemma integral_angular_eq_chart {f : Angles × Angles → ℝ} (hf : Measurable f) :
    (∫ p, f p ∂angularMeasure.prod angularMeasure) =
      ((2*Real.pi)^2)⁻¹ * ∫ q, f (angleChart q) ∂angleChartMeasure := by
  have h := integral_map (μ := angleChartMeasure) angleChart_preserving.measurable.aemeasurable hf.aestronglyMeasurable
  rw [angleChart_measure,integral_smul_measure,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi),smul_eq_mul] at h
  rw [← h]
  field_simp
lemma direction_realPlane (t : ℝ) : Complex.equivRealProdCLM (direction (t : Angles)) =
    (Real.cos t,Real.sin t) := by
  rw [direction_real,Circle.coe_exp,Complex.exp_mul_I]
  ext <;> simp [Complex.cos_ofReal_re,Complex.sin_ofReal_re]
lemma circleSum_chart (x : ℂ) (r : ℝ) (q : RealPlane) :
    Complex.equivRealProdCLM (x+(r : ℂ)*direction (angleChart q).1+direction (angleChart q).2) =
      Complex.equivRealProdCLM x+circleSum r q := by
  change Complex.equivRealProdCLM (x+(r : ℂ)*direction (q.1 : Angles)+direction (q.2 : Angles)) = _
  rw [map_add,map_add]
  have h : (r : ℂ)*direction (q.1 : Angles) = r • direction (q.1 : Angles) := by simp
  rw [h,map_smul,direction_realPlane,direction_realPlane]
  ext <;> simp [circleSum,add_assoc]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma volume_preimage_bound {F : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (A : Set (ℝ × ℝ)) :
    volume (F ⁻¹' A ∩ s) ≤ (K : ENNReal)^2 * volume A := by
  have he : Subtype.val '' ((s.domRestrict F) ⁻¹' A) = F ⁻¹' A ∩ s := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩; exact ⟨hq,q.2⟩
    · rintro ⟨hp,hs⟩; exact ⟨⟨p,hs⟩,hp,rfl⟩
  have hi := (isometry_subtype_coe : Isometry (Subtype.val : s → ℝ × ℝ)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ)≤2)) ((s.domRestrict F) ⁻¹' A)
  have ha := hF.hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤2) A
  rw [he,hausdorffMeasure_prod_real] at hi
  rw [← hi,hausdorffMeasure_prod_real,ENNReal.rpow_two] at ha
  exact ha
lemma map_restrict_volume_le {F : ℝ × ℝ → ℝ × ℝ} (hm : Measurable F)
    {s B : Set (ℝ × ℝ)} (_hB : MeasurableSet B) {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (himage : MapsTo F s B) :
    (volume.restrict s).map F ≤ ((K^2 : ℝ≥0) : ENNReal) • volume.restrict B := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hm hA,Measure.restrict_apply (hm hA),Measure.smul_apply,
    Measure.restrict_apply hA,smul_eq_mul,ENNReal.coe_pow]
  have he : F ⁻¹' A ∩ s = F ⁻¹' (A ∩ B) ∩ s := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1,himage hx.2⟩,hx.2⟩,fun hx => ⟨hx.1.1,hx.2⟩⟩
  rw [he]
  exact volume_preimage_bound hF (A ∩ B)
lemma antilipschitz_small_perturbation {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace X] {F G : X → E} {K L : ℝ≥0} (hf : AntilipschitzWith K F)
    (hg : LipschitzWith L G) {a : ℝ} (ha : (K : ℝ)*‖a‖*(L : ℝ) ≤ 1/2) :
    AntilipschitzWith (2*K) (fun x => F x+a • G x) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h1 := hf.le_mul_dist x y
  have h2 := hg.dist_le_mul x y
  have h3 : dist (F x) (F y) ≤ dist (F x+a • G x) (F y+a • G y) + ‖a‖*dist (G x) (G y) := by
    simpa only [add_sub_cancel_right,dist_smul₀] using
      dist_sub_sub_le (F x+a • G x) (a • G x) (F y+a • G y) (a • G y)
  have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg a)
  have h5 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add_right h4 _)) K.2
  have h6 := mul_le_mul_of_nonneg_right ha (dist_nonneg (x := x) (y := y))
  simp only [NNReal.coe_mul,NNReal.coe_ofNat]
  nlinarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma realDirection_norm_le (t : ℝ) : ‖(Real.cos t,Real.sin t)‖ ≤ (1 : ℝ) := by
  rw [Prod.norm_def,max_le_iff]
  exact ⟨by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one t,
    by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one t⟩
lemma circleSum_decompose (r : ℝ) (q : RealPlane) :
    circleSum r q = r • (Real.cos q.1,Real.sin q.1) + (Real.cos q.2,Real.sin q.2) := rfl
lemma circleSum_norm_le (r : ℝ) (q : RealPlane) : ‖circleSum r q‖ ≤ |r|+1 := by
  rw [circleSum_decompose]
  calc
    _ ≤ ‖r • (Real.cos q.1,Real.sin q.1)‖+‖(Real.cos q.2,Real.sin q.2)‖ := norm_add_le _ _
    _ ≤ |r| * 1+1 := by rw [norm_smul]; exact add_le_add (mul_le_mul_of_nonneg_left (realDirection_norm_le _) (norm_nonneg r)) (realDirection_norm_le _)
    _ = _ := by ring
lemma circleSum_perturb_identity (r : ℝ) (q : RealPlane) :
    circleSum r q = circleSum 1 q + (r-1) • (Real.cos q.1,Real.sin q.1) := by
  apply Prod.ext
  · change r*Real.cos q.1+Real.cos q.2 = 1*Real.cos q.1+Real.cos q.2+(r-1)*Real.cos q.1
    ring
  · change r*Real.sin q.1+Real.sin q.2 = 1*Real.sin q.1+Real.sin q.2+(r-1)*Real.sin q.1
    ring
lemma circleSum_parameter_tendsto {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (q : RealPlane) :
    Tendsto (fun n => circleSum (r n) q) atTop (𝓝 (circleSum 1 q)) := by
  exact (hr.mul_const (Real.cos q.1) |>.add_const (Real.cos q.2)).prodMk_nhds
    (hr.mul_const (Real.sin q.1) |>.add_const (Real.sin q.2))
lemma circleSum_eventual_image {r : ℕ → ℝ} {y : ℕ → RealPlane} {x : RealPlane}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x)) :
    ∀ᶠ n in atTop, ∀ q, y n+circleSum (r n) q ∈ Metric.closedBall x 4 := by
  filter_upwards [hr.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ)<1)),
    hy.eventually (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1))] with n hn hyn
  intro q
  have hh := circleSum_norm_le (r n) q
  have hb : |r n| ≤ 2 := by
    have ht := norm_le_norm_sub_add (r n) (1 : ℝ)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_one] at ht
    rw [Real.dist_eq] at hn
    linarith
  rw [Metric.mem_closedBall]
  calc
    _ ≤ dist (y n+circleSum (r n) q) (y n)+dist (y n) x := dist_triangle _ _ _
    _ = ‖circleSum (r n) q‖+dist (y n) x := by rw [dist_eq_norm,add_sub_cancel_left]
    _ ≤ 4 := by linarith
lemma circleSum_limit_image (x q : RealPlane) : x+circleSum 1 q ∈ Metric.closedBall x 4 := by
  rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left]
  have hh := circleSum_norm_le 1 q
  norm_num at hh
  linarith
lemma circleSum_eventual_antilipschitz {V : Set RealPlane} {K : ℝ≥0}
    (hK : AntilipschitzWith K (V.domRestrict (circleSum 1)))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (y : ℕ → RealPlane) :
    ∀ᶠ n in atTop, AntilipschitzWith (2*K) (V.domRestrict (fun q => y n+circleSum (r n) q)) := by
  have hD : LipschitzWith 1 (fun q : V => (Real.cos q.1.1,Real.sin q.1.1)) := by
    have hf : LipschitzWith 1 (fun q : V => q.1.1) := LipschitzWith.of_dist_le_mul (fun q p => by
      simp only [NNReal.coe_one,one_mul]
      exact le_max_left _ _)
    simpa only [Function.comp_def,one_mul] using realDirection_lipschitz.comp hf
  have ht : Tendsto (fun n => (K : ℝ)*‖r n-1‖) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => r n-1) atTop (𝓝 0) := by simpa using hr.sub_const 1
    simpa using hh.norm.const_mul (K : ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with n hn
  have ha := antilipschitz_small_perturbation hK hD (a := r n-1) (by simpa using le_of_lt hn)
  apply AntilipschitzWith.of_le_mul_dist
  intro q p
  have hh := ha.le_mul_dist q p
  simpa only [Set.domRestrict_apply,dist_add_left,← circleSum_perturb_identity] using hh
lemma circleSum_limit_antilipschitz {V : Set RealPlane} {K : ℝ≥0}
    (hK : AntilipschitzWith K (V.domRestrict (circleSum 1))) (x : RealPlane) :
    AntilipschitzWith (2*K) (V.domRestrict (fun q => x+circleSum 1 q)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro q p
  have hh := hK.le_mul_dist q p
  simpa only [Set.domRestrict_apply,dist_add_left] using hh.trans
    (mul_le_mul_of_nonneg_right (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; linarith [K.2] : (K : ℝ)≤ ((2*K : ℝ≥0) : ℝ)) dist_nonneg)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma measure_null_of_locally_null_on_conull {X : Type*} [TopologicalSpace X]
    [HereditarilyLindelofSpace X] [MeasurableSpace X] {μ : Measure X} {R A : Set X}
    (hR : μ Rᶜ = 0) (h : ∀ x ∈ R, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ μ (A ∩ V) = 0) :
    μ A = 0 := by
  classical
  choose V hVo hxV hV0 using (fun x : R => h x.1 x.2)
  obtain ⟨t,ht,hcov⟩ := (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover V hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have hu : μ (⋃ i ∈ t, A ∩ V i) = 0 := (measure_biUnion_null_iff ht).mpr (fun i _ => hV0 i)
  apply measure_mono_null (t := Rᶜ ∪ ⋃ i ∈ t, A ∩ V i) _ (measure_union_null hR hu)
  intro x hx
  by_cases hr : x ∈ R
  · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcov hr)
    exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,hx,hxi⟩)
  · exact Or.inl hr
lemma circleSum_regular_ae : ∀ᵐ p : RealPlane ∂volume, Real.sin (p.2-p.1) ≠ 0 := by
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · exact Eventually.of_forall fun t => by
      have hs : {s : ℝ | Real.sin (s-t)=0} ⊆ Set.range (fun n : ℤ => t+n*Real.pi) := by
        intro s h
        obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp h
        exact ⟨n,by linarith⟩
      change volume {s : ℝ | ¬ Real.sin (s-t) ≠ 0} = 0
      simpa only [not_not] using measure_mono_null hs ((countable_range _).measure_zero volume)
  · exact (measurableSet_eq_fun (Real.measurable_sin.comp (measurable_snd.sub measurable_fst)) measurable_const).compl
lemma circleSum_preimage_null {r : ℝ} (hr : r ≠ 0) {A : Set RealPlane} (hA : volume A=0) :
    volume (circleSum r ⁻¹' A)=0 := by
  apply measure_null_of_locally_null_on_conull (μ := (volume : Measure RealPlane))
    (R := {p : RealPlane | Real.sin (p.2-p.1) ≠ 0}) (A := circleSum r ⁻¹' A) circleSum_regular_ae
  intro p hp
  obtain ⟨s,hso,hps,K,hK⟩ := circleSum_local_antilipschitz (mul_ne_zero hr hp)
  refine ⟨s,hso,hps,?_⟩
  have hh := volume_preimage_bound hK A
  rw [hA,mul_zero] at hh
  exact nonpos_iff_eq_zero.mp hh
lemma circleSum_quasiMeasurePreserving {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (circleSum r) volume volume := by
  refine ⟨(circleSum_continuous r).measurable,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply (circleSum_continuous r).measurable hA]
  exact circleSum_preimage_null hr hz
end EuclideanFiveColor
end

end OAI
