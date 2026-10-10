import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set Filter Topology
open scoped OnePoint

namespace CannonMobius
abbrev Sphere := OnePoint ℂ

def inv (p : Sphere) : Sphere :=
  p.elim ((0:ℂ):Sphere) (fun z => if z=0 then ∞ else (z⁻¹:ℂ))

@[simp] lemma inv_infty : inv ∞=((0:ℂ):Sphere) := rfl
@[simp] lemma inv_zero : inv ((0:ℂ):Sphere)=∞ := by simp [inv]
lemma inv_coe {z : ℂ} (hz : z ≠ 0) : inv (z:Sphere)=(z⁻¹:ℂ) := by simp [inv,hz]

lemma inv_involutive : Function.Involutive inv := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z=0
    · simp [hz]
    · rw [inv_coe hz,inv_coe (inv_ne_zero hz),inv_inv]

lemma continuous_inv : Continuous inv := by
  rw [OnePoint.continuous_iff]
  constructor
  · have ht : Tendsto (fun z : ℂ => ((z⁻¹:ℂ):Sphere)) (coclosedCompact ℂ)
        (𝓝 ((0:ℂ):Sphere)) := by
      apply OnePoint.continuous_coe.continuousAt.tendsto.comp
      simpa only [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded : Tendsto Inv.inv (Bornology.cobounded ℂ) (𝓝 (0:ℂ)))
    apply ht.congr'
    have hn : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
      rw [coclosedCompact_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact
    filter_upwards [hn] with z hz
    exact (inv_coe hz).symm
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z=0
    · subst z
      have ht : Tendsto (fun z : ℂ => ((z⁻¹:ℂ):Sphere)) (𝓝[≠] (0:ℂ)) (𝓝 ∞) := by
        apply OnePoint.tendsto_coe_infty.comp
        simpa only [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact] using
          (tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[≠] (0:ℂ)) (Bornology.cobounded ℂ))
      have hcon : Tendsto (fun z : ℂ => inv (z:Sphere)) (𝓝[≠] (0:ℂ)) (𝓝 ∞) := ht.congr'
        (Filter.Eventually.mono self_mem_nhdsWithin (fun z hz => (inv_coe hz).symm))
      have hw : ContinuousWithinAt (fun z : ℂ => inv (z:Sphere)) (univ \ {0}) 0 := by
        simpa only [ContinuousWithinAt,compl_eq_univ_sdiff,inv_zero] using hcon
      exact (continuousWithinAt_univ _ _).mp (continuousWithinAt_sdiff_self.mp hw)
    · apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact inv_coe hw

def inversion : Sphere ≃ₜ Sphere where
  toFun := inv
  invFun := inv
  left_inv := inv_involutive
  right_inv := inv_involutive
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

def sphereHomeomorph : Sphere ≃ₜ
    {x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere 0 1} :=
  onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
end CannonMobius

noncomputable section
open Set Filter Topology

namespace CannonConformal

lemma homeomorph_tendsto_cobounded (f : ℂ ≃ₜ ℂ) :
    Tendsto f (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  simpa only [Metric.cobounded_eq_cocompact] using f.isClosedEmbedding.tendsto_cocompact

def inverted (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z⁻¹)⁻¹

lemma inverted_zero {f : ℂ → ℂ} (h0 : f 0=0) : inverted f 0=0 := by
  simp [inverted,h0]

lemma inverted_continuousAt_zero (f : ℂ ≃ₜ ℂ) (h0 : f 0=0) :
    ContinuousAt (inverted f) 0 := by
  have ht : Tendsto (inverted f) (𝓝[≠] (0:ℂ)) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp ((homeomorph_tendsto_cobounded f).comp tendsto_inv₀_nhdsNE_zero)
  have hw : ContinuousWithinAt (inverted f) (univ \ {0}) 0 := by
    simpa only [ContinuousWithinAt,compl_eq_univ_sdiff,inverted_zero h0] using ht
  exact (continuousWithinAt_univ _ _).mp (continuousWithinAt_sdiff_self.mp hw)

lemma inverted_differentiable (f : ℂ ≃ₜ ℂ) (h0 : f 0=0)
    (hf : Differentiable ℂ f) : Differentiable ℂ (inverted f) := by
  have hn (z : ℂ) (hz : z ≠ 0) : f z⁻¹ ≠ 0 := by
    intro hh
    exact (inv_ne_zero hz) (f.injective (hh.trans h0.symm))
  have hp (z : ℂ) (hz : z ≠ 0) : DifferentiableAt ℂ (inverted f) z :=
    ((hf z⁻¹).comp z (differentiableAt_id.inv hz)).inv (hn z hz)
  intro z
  by_cases hz : z=0
  · subst z
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (show ∀ᶠ z : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ (inverted f) z from
        Filter.Eventually.mono self_mem_nhdsWithin (fun z hz => hp z hz))
      (inverted_continuousAt_zero f h0)).differentiableAt
  · exact hp z hz

lemma inverted_leftInverse (f : ℂ ≃ₜ ℂ) :
    Function.LeftInverse (inverted f.symm) (inverted f) := by
  intro z
  simp [inverted]

theorem biholomorphic_fix_zero_linear (f : ℂ ≃ₜ ℂ) (h0 : f 0=0)
    (hf : Differentiable ℂ f) (hfi : Differentiable ℂ f.symm) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z, f z=a*z := by
  let g := inverted f
  let gi := inverted f.symm
  have h0i : f.symm 0=0 := f.injective (by simp [h0])
  have hg : Differentiable ℂ g := inverted_differentiable f h0 hf
  have hgi : Differentiable ℂ gi := inverted_differentiable f.symm h0i hfi
  have hg0 : g 0=0 := inverted_zero h0
  have hcomp : gi ∘ g=id := funext (inverted_leftInverse f)
  have hd := (hgi (g 0)).hasDerivAt.comp 0 (hg 0).hasDerivAt
  have ha : deriv g 0 ≠ 0 := by
    have hh : deriv gi (g 0)*deriv g 0=1 := by
      rw [hcomp] at hd
      exact hd.unique (hasDerivAt_id 0)
    intro he
    rw [he,mul_zero] at hh
    exact zero_ne_one hh
  let a : ℂ := (deriv g 0)⁻¹
  have hds : Differentiable ℂ (dslope f 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (by simp)).mpr hf.differentiableOn)
  have ht : Tendsto (fun z : ℂ => (dslope g 0 z⁻¹)⁻¹)
      (Bornology.cobounded ℂ) (𝓝 a) := by
    have hh := (continuousAt_dslope_same.mpr (hg 0)).tendsto.comp tendsto_inv₀_cobounded
    rw [dslope_same] at hh
    exact hh.inv₀ ha
  have heq : (fun z : ℂ => (dslope g 0 z⁻¹)⁻¹) =ᶠ[Bornology.cobounded ℂ]
      dslope f 0 := by
    have hn : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact
    filter_upwards [hn] with z hz
    have hfz : f z ≠ 0 := fun hh => hz (f.injective (hh.trans h0.symm))
    rw [dslope_of_ne _ (inv_ne_zero hz),dslope_of_ne _ hz]
    simp only [slope,g,inverted,inv_inv,inv_zero,h0,vsub_eq_sub,sub_zero,smul_eq_mul]
    field_simp
  have ht' : Tendsto (dslope f 0) (cocompact ℂ) (𝓝 a) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact ht.congr' heq
  refine ⟨a,inv_ne_zero ha,?_⟩
  intro z
  have hh := hds.apply_eq_of_tendsto_cocompact z ht'
  by_cases hz : z=0
  · simp [hz,h0]
  · rw [dslope_of_ne _ hz] at hh
    simp only [slope,h0,vsub_eq_sub,sub_zero,smul_eq_mul] at hh
    calc
      f z = z*(z⁻¹*f z) := by rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul]
      _ = a*z := by rw [hh,mul_comm]

theorem biholomorphic_affine (f : ℂ ≃ₜ ℂ)
    (hf : Differentiable ℂ f) (hfi : Differentiable ℂ f.symm) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z=a*z+b := by
  let h := f.trans (Homeomorph.addRight (-f 0))
  have h0 : h 0=0 := by simp [h]
  have hd : Differentiable ℂ h := hf.add_const (-f 0)
  have hdi : Differentiable ℂ h.symm := by
    change Differentiable ℂ (fun z => f.symm (z + -(-f 0)))
    simpa only [neg_neg,Function.comp_def,id_eq] using
      hfi.comp (differentiable_id.add_const (f 0))
  obtain ⟨a,ha,he⟩ := biholomorphic_fix_zero_linear h h0 hd hdi
  refine ⟨a,f 0,ha,?_⟩
  intro z
  have hh := he z
  change f z + -(f 0)=a*z at hh
  linear_combination hh
end CannonConformal

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

def coordinate (p : Sphere) : ℂ := p.elim 0 id
@[simp] lemma coordinate_coe (z : ℂ) : coordinate (z:Sphere)=z := rfl
@[simp] lemma coordinate_infty : coordinate ∞=0 := rfl
lemma coe_coordinate {p : Sphere} (hp : p ≠ ∞) : (coordinate p:Sphere)=p := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => rfl

lemma continuousAt_coordinate {p : Sphere} (hp : p ≠ ∞) : ContinuousAt coordinate p := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => exact OnePoint.continuousAt_coe.mpr continuousAt_id

lemma coe_map_ne_infty (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) (z : ℂ) : f (z:Sphere) ≠ ∞ :=
  fun he => OnePoint.coe_ne_infty z (f.injective (he.trans hf.symm))

lemma symm_infty (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) : f.symm ∞=∞ := by
  apply f.injective
  rw [f.apply_symm_apply,hf]

def finiteRestriction (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) : ℂ ≃ₜ ℂ where
  toFun z := coordinate (f (z:Sphere))
  invFun z := coordinate (f.symm (z:Sphere))
  left_inv z := by
    change coordinate (f.symm (coordinate (f (z:Sphere)):Sphere))=z
    rw [coe_coordinate (coe_map_ne_infty f hf z),f.symm_apply_apply,coordinate_coe]
  right_inv z := by
    change coordinate (f (coordinate (f.symm (z:Sphere)):Sphere))=z
    rw [coe_coordinate (coe_map_ne_infty f.symm (symm_infty f hf) z),f.apply_symm_apply,coordinate_coe]
  continuous_toFun := continuous_iff_continuousAt.mpr (fun z =>
    ContinuousAt.comp (f := fun w : ℂ => f (w:Sphere)) (x := z)
      (continuousAt_coordinate (coe_map_ne_infty f hf z))
      (f.continuous.comp OnePoint.continuous_coe).continuousAt)
  continuous_invFun := continuous_iff_continuousAt.mpr (fun z =>
    ContinuousAt.comp (f := fun w : ℂ => f.symm (w:Sphere)) (x := z)
      (continuousAt_coordinate (coe_map_ne_infty f.symm (symm_infty f hf) z))
      (f.symm.continuous.comp OnePoint.continuous_coe).continuousAt)

lemma restriction_extension (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) :
    (finiteRestriction f hf).onePointCongr=f := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => exact hf.symm
  | coe z => exact coe_coordinate (coe_map_ne_infty f hf z)

def chart : Bool → Sphere ≃ₜ Sphere
  | false => 1
  | true => inversion

lemma chart_involutive (b : Bool) (p : Sphere) : chart b (chart b p)=p := by
  cases b
  · rfl
  · exact inv_involutive p

@[simp] lemma coordinate_inv_coe (z : ℂ) : coordinate (inv (z:Sphere))=z⁻¹ := by
  by_cases hz : z=0
  · simp [hz]
  · rw [inv_coe hz,coordinate_coe]

def inChart (s t : Bool) (f : Sphere ≃ₜ Sphere) (z : ℂ) : ℂ :=
  coordinate (chart t (f (chart s (z:Sphere))))
def chartDomain (s t : Bool) (f : Sphere ≃ₜ Sphere) : Set ℂ :=
  {z | chart t (f (chart s (z:Sphere))) ≠ ∞}

lemma isOpen_chartDomain (s t : Bool) (f : Sphere ≃ₜ Sphere) : IsOpen (chartDomain s t f) :=
  isOpen_compl_singleton.preimage ((chart t).continuous.comp
    (f.continuous.comp ((chart s).continuous.comp OnePoint.continuous_coe)))

def IsAnalytic (f : Sphere ≃ₜ Sphere) : Prop :=
  ∀ s t, DifferentiableOn ℂ (inChart s t f) (chartDomain s t f)

lemma analytic_differentiableAt {f : Sphere ≃ₜ Sphere} (hf : IsAnalytic f)
    (s t : Bool) {z : ℂ} (hz : z ∈ chartDomain s t f) :
    DifferentiableAt ℂ (inChart s t f) z :=
  (hf s t z hz).differentiableAt ((isOpen_chartDomain s t f).mem_nhds hz)

lemma isAnalytic_mul {f g : Sphere ≃ₜ Sphere} (hf : IsAnalytic f) (hg : IsAnalytic g) :
    IsAnalytic (f*g) := by
  classical
  intro s t z hz
  let p := g (chart s (z:Sphere))
  let u : Bool := if p=∞ then true else false
  have hu : chart u p ≠ ∞ := by
    by_cases hp : p=∞
    · dsimp [u]
      rw [ite_eq_left hp]
      change inv p ≠ ∞
      rw [hp,inv_infty]
      exact OnePoint.coe_ne_infty 0
    · simp [u,hp,chart]
  have hgdom : z ∈ chartDomain s u g := hu
  have he : chart u (inChart s u g z : Sphere)=p := by
    change chart u (coordinate (chart u p):Sphere)=p
    rw [coe_coordinate hu,chart_involutive]
  have hfdom : inChart s u g z ∈ chartDomain u t f := by
    change chart t (f (chart u (inChart s u g z:Sphere))) ≠ ∞
    rw [he]
    exact hz
  have hd := (analytic_differentiableAt hf u t hfdom).comp z
    (analytic_differentiableAt hg s u hgdom)
  apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  have hn : ∀ᶠ w in 𝓝 z, w ∈ chartDomain s u g := (isOpen_chartDomain s u g).mem_nhds hgdom
  filter_upwards [hn] with w hw
  change coordinate (chart t (f (g (chart s (w:Sphere)))) )=
    coordinate (chart t (f (chart u (coordinate (chart u (g (chart s (w:Sphere)))):Sphere))))
  rw [coe_coordinate hw,chart_involutive]

lemma restriction_differentiable (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞)
    (ha : IsAnalytic f) : Differentiable ℂ (finiteRestriction f hf) := by
  intro z
  exact analytic_differentiableAt ha false false (coe_map_ne_infty f hf z)

lemma restriction_symm (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) :
    (finiteRestriction f hf).symm=finiteRestriction f.symm (symm_infty f hf) := rfl

theorem analytic_fix_infty_affine (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞)
    (ha : IsAnalytic f) (hi : IsAnalytic f.symm) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, f (z:Sphere)=(a*z+b:ℂ) := by
  obtain ⟨a,b,ha',he⟩ := CannonConformal.biholomorphic_affine (finiteRestriction f hf)
    (restriction_differentiable f hf ha)
    (restriction_differentiable f.symm (symm_infty f hf) hi)
  refine ⟨a,b,ha',?_⟩
  intro z
  have hh := congrArg (fun z : ℂ => (z:Sphere)) (he z)
  exact (coe_coordinate (coe_map_ne_infty f hf z)).symm.trans hh
end CannonMobius

end
end
end
section
noncomputable section
namespace CannonSphereReflection
open Set Metric Topology
open scoped OnePoint

abbrev S := OnePoint ℂ

def reflection : S ≃ₜ S :=
  Complex.conjCLE.toHomeomorph.onePointCongr.trans CannonMobius.inversion

lemma reflection_infty : reflection ∞=((0:ℂ):S) := by
  change CannonMobius.inv ∞=_
  exact CannonMobius.inv_infty
lemma reflection_zero : reflection ((0:ℂ):S)=∞ := by
  change CannonMobius.inv ((starRingEnd ℂ 0:ℂ):S)=_
  simpa only [map_zero] using CannonMobius.inv_zero
lemma reflection_coe {z : ℂ} (hz : z≠0) :
    reflection (z:S)=((starRingEnd ℂ z)⁻¹:ℂ) := by
  change CannonMobius.inv ((starRingEnd ℂ z:ℂ):S)=_
  exact CannonMobius.inv_coe ((map_ne_zero (starRingEnd ℂ)).mpr hz)

lemma reflection_fix {z : ℂ} (hz : z∈sphere (0:ℂ) 1) : reflection (z:S)=(z:S) := by
  have hn : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
  have hne : z≠0 := by intro hh; simp [hh] at hn
  rw [reflection_coe hne,Complex.inv_eq_conj (by simpa using hn)]
  simp

lemma reflection_involutive : Function.Involutive reflection := by
  intro p
  induction p using OnePoint.rec with
  | infty => rw [reflection_infty,reflection_zero]
  | coe z =>
    by_cases hz : z=0
    · subst z; rw [reflection_zero,reflection_infty]
    · rw [reflection_coe hz,reflection_coe (inv_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hz))]
      simp

lemma reflection_image_closedBall :
    reflection '' ((↑) '' closedBall (0:ℂ) 1 : Set S)=
      (((↑) '' ball (0:ℂ) 1 : Set S))ᶜ := by
  ext p
  constructor
  · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩ hp
    obtain ⟨w,hw,he⟩:=hp
    by_cases hz0 : z=0
    · subst z
      rw [reflection_zero] at he
      exact OnePoint.coe_ne_infty w he
    rw [reflection_coe hz0] at he
    have he' : w=(starRingEnd ℂ z)⁻¹ := OnePoint.coe_injective he
    rw [mem_ball,dist_zero_right,he',norm_inv,Complex.norm_conj] at hw
    rw [mem_closedBall,dist_zero_right] at hz
    have hn : 0<‖z‖ := norm_pos_iff.mpr hz0
    have hi : 1≤‖z‖⁻¹ := (one_le_inv₀ hn).mpr hz
    exact (not_lt_of_ge hi) hw
  · intro hp
    have hq : reflection p∈((↑) '' closedBall (0:ℂ) 1 : Set S) := by
      induction p using OnePoint.rec with
      | infty => rw [reflection_infty]; exact ⟨0,by simp,rfl⟩
      | coe z =>
        have hz : 1≤‖z‖ := by
          by_contra hh
          exact hp ⟨z,by simpa only [mem_ball,dist_zero_right] using lt_of_not_ge hh,rfl⟩
        have hz0 : z≠0 := by intro he; norm_num [he] at hz
        rw [reflection_coe hz0]
        refine ⟨(starRingEnd ℂ z)⁻¹,?_,rfl⟩
        rw [mem_closedBall,dist_zero_right,norm_inv,Complex.norm_conj]
        exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).mpr hz
    exact ⟨reflection p,hq,reflection_involutive p⟩
end CannonSphereReflection

end
end
section
noncomputable section
namespace CannonSphereReflection
open Set Metric Topology
open scoped OnePoint

lemma onePoint_image (h : ℂ≃ₜℂ) (A : Set ℂ) :
    h.onePointCongr '' ((↑) '' A : Set S)=((↑) '' (h '' A) : Set S) := by
  rw [image_image,image_image]
  rfl

theorem exists_convex_reflection (K : Set ℂ) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) :
    ∃ J : S≃ₜS,(∀ x∈frontier K,J (x:S)=(x:S)) ∧
      J '' ((↑) '' K : Set S)=(((↑) '' interior K : Set S))ᶜ := by
  obtain ⟨h,hi,hc,hf⟩:=exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hint hK.isBounded
  rw [hK.isClosed.closure_eq] at hc
  let J : S≃ₜS:=h.onePointCongr.trans (reflection.trans h.symm.onePointCongr)
  have hInv : h.symm.onePointCongr '' ((↑) '' ball (0:ℂ) 1 : Set S)=((↑) '' interior K : Set S) := by
    rw [onePoint_image,←hi]
    congr 1
    rw [image_image]
    simp only [h.symm_apply_apply,image_id']
  refine ⟨J,?_,?_⟩
  · intro x hx
    have hh : h x∈sphere (0:ℂ) 1 := by rw [←hf]; exact mem_image_of_mem h hx
    change h.symm.onePointCongr (reflection ((h x:ℂ):S))=(x:S)
    rw [reflection_fix hh]
    change ((h.symm (h x):ℂ):S)=(x:S)
    rw [h.symm_apply_apply]
  · calc
      J '' ((↑) '' K : Set S) = h.symm.onePointCongr ''
          (reflection '' (h.onePointCongr '' ((↑) '' K : Set S))) := by
            simp only [image_image]
            rfl
      _ = _ := by
        rw [onePoint_image,hc,reflection_image_closedBall,
          image_compl_eq h.symm.onePointCongr.bijective,hInv]
end CannonSphereReflection

end
end
end
end

end OAI
