import Mathlib
import OAI.Geometry.Cannon.Conformal.RestrictedSphereAction
import OAI.Geometry.Cannon.Beltrami.GlobalMetricWeakMrmt
import OAI.Geometry.Cannon.Beltrami.Beltrami

namespace OAI

section
section
section
section
section
section
section
noncomputable section
namespace CannonConformal
open Complex

def linearZ (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1-Complex.I*A Complex.I)/2
def linearBar (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1+Complex.I*A Complex.I)/2

lemma linearZBar_apply (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z=linearZ A*z+linearBar A*star z := by
  have hz : z=z.re • (1:ℂ)+z.im • Complex.I := by
    apply Complex.ext <;> simp
  have ha : A z=z.re • A 1+z.im • A Complex.I := by
    conv_lhs => rw [hz]
    rw [map_add,map_smul,map_smul]
  rw [ha]
  apply Complex.ext <;> simp [linearZ,linearBar,Complex.mul_re,Complex.mul_im] <;> ring

lemma linearZ_ne_zero {A : ℂ →L[ℝ] ℂ} (hA : Function.Injective A) {μ : ℂ}
    (hμ : linearBar A=μ*linearZ A) : linearZ A ≠ 0 := by
  intro hz
  have hb : linearBar A=0 := by rw [hμ,hz,mul_zero]
  have ha : A 1=A 0 := by rw [linearZBar_apply,hz,hb]; simp
  exact one_ne_zero (hA ha)

lemma linear_beltrami_evaluate {A : ℂ →L[ℝ] ℂ} {μ : ℂ}
    (hμ : linearBar A=μ*linearZ A) (z : ℂ) :
    Complex.normSq (A z)=Complex.normSq (linearZ A)*evaluate (coefficientForm μ) z.re z.im := by
  rw [linearZBar_apply,hμ]
  have hh : linearZ A*z+μ*linearZ A*star z=linearZ A*(z+μ*star z) := by ring
  rw [hh,map_mul,evaluate_coefficientForm]

lemma coefficient_scale_pos {q : Form} (hq : Positive q) :
    0 < (q 0+q 2+2*Real.sqrt (determinant q))/4 := by
  have hc : 0 < q 2 := by
    have h := hq.2
    have ha := hq.1
    dsimp [determinant] at h
    nlinarith [sq_nonneg (q 1)]
  linarith [Real.sqrt_nonneg (determinant q),hq.1]

theorem beltrami_integrates_form {q : Form} (hq : Positive q)
    {A : ℂ →L[ℝ] ℂ} (hA : Function.Injective A)
    (hμ : linearBar A=beltrami q*linearZ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, Complex.normSq (A z)=c*evaluate q z.re z.im := by
  let s : ℝ := (q 0+q 2+2*Real.sqrt (determinant q))/4
  have hs : 0 < s := coefficient_scale_pos hq
  have hn : 0 < Complex.normSq (linearZ A) := Complex.normSq_pos.mpr (linearZ_ne_zero hA hμ)
  refine ⟨Complex.normSq (linearZ A)/s,div_pos hn hs,?_⟩
  intro z
  have heq : evaluate q z.re z.im=s*evaluate (coefficientForm (beltrami q)) z.re z.im := by
    conv_lhs => rw [coefficient_reconstruction hq]
    exact evaluate_smul _ _ _ _
  rw [linear_beltrami_evaluate hμ,heq]
  field_simp

end CannonConformal

end
end
namespace CannonConformal
open MeasureTheory CannonBeltrami CannonMetricQC

theorem measurable_structure_integration (q : ℂ → Form) (hq : Measurable q)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hl : ∀ z, LowerBound ε (q z)) (hu : ∀ z, UpperBound K (q z)) :
    ∃ C : ℝ, 0 < C ∧ ∃ F : ℂ ≃ₜ ℂ, F 0=0 ∧ F 1=1 ∧
      WeakQS F C ∧ WeakQS F.symm C ∧
      (∀ᵐ z : ℂ, DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
        Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
          Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) := by
  let μ : ℂ → ℂ := fun z => beltrami (q z)
  let k : ℝ := Real.sqrt (1-ε/K)
  have hm : AEStronglyMeasurable μ volume := (measurable_beltrami.comp hq).aestronglyMeasurable
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk1 : k < 1 := (beltrami_uniform_bound hε hK (hl 0) (hu 0)).2
  have hb (z : ℂ) : ‖μ z‖ ≤ k := (beltrami_uniform_bound hε hK (hl z) (hu z)).1
  obtain ⟨C,hC,F,hF0,hF1,hF,hFi,hw⟩ := global_metric_weak_mrmt μ hm hk hk1 hb
  have hbc := metric_weak_beltrami_classical F hC hF μ hm hk hb hw
  have hn := weakQS_ae_bijective_fderiv F hC hC hF hFi
  have hd := weakQS_ae_differentiable F hC hF
  refine ⟨C,hC,F,hF0,hF1,hF,hFi,?_⟩
  filter_upwards [hbc,hn,hd] with z hz hzn hzd
  refine ⟨hzd,hzn,beltrami_integrates_form ?_ hzn.1 ?_⟩
  · constructor
    · have h := hl z 1 0
      simp only [evaluate,one_pow,mul_one,zero_pow (by norm_num : 2 ≠ 0),mul_zero,
        add_zero] at h
      exact hε.trans_le h
    · have h := determinant_ge_sq_lower hε.le (hl z)
      exact (sq_pos_of_pos hε).trans_le h
  · exact hz

end CannonConformal

end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

open Classical

lemma measurable_extend_form {K : Set Sphere} (hK : MeasurableSet K)
    (q : K → Form) (hq : Measurable q) :
    Measurable (fun z : ℂ => if hz : (z:Sphere) ∈ K then q ⟨z,hz⟩ else roundForm) := by
  have hm : Measurable (fun z : ℂ => (z:Sphere)) := OnePoint.continuous_coe.measurable
  have hs : MeasurableSet {z : ℂ | (z:Sphere) ∈ K} := hK.preimage hm
  have h1 : Measurable (fun z : {z : ℂ | (z:Sphere) ∈ K} => q ⟨z.val,z.property⟩) :=
    hq.comp ((hm.comp measurable_subtype_coe).subtype_mk)
  exact h1.dite measurable_const hs

lemma roundForm_bounds {ε K : ℝ} (hε : ε ≤ 1) (hK : 1 ≤ K) :
    LowerBound ε roundForm ∧ UpperBound K roundForm := by
  constructor
  · intro x y
    have hh := mul_le_mul_of_nonneg_right hε (show 0 ≤ x^2+y^2 by positivity)
    simpa [evaluate,roundForm] using hh
  · intro x y
    have hh := mul_le_mul_of_nonneg_right hK (show 0 ≤ x^2+y^2 by positivity)
    simpa [evaluate,roundForm] using hh

theorem controlled_action_structure_integration [Countable Γ]
    (A : Γ →* (Sphere ≃ₜ Sphere)) {η : CannonQM.Distortion}
    (hA : ∀ g, CannonQM.Controlled (A g) η) :
    ∃ q : ℂ → Form, Measurable q ∧
      (∀ z, LowerBound (((1+2*(η 2:ℝ))^2)⁻¹) (q z) ∧ UpperBound ((1+2*(η 2:ℝ))^2) (q z)) ∧
      (∀ g, ∀ᵐ z : ℂ, A g (z:Sphere) ≠ ∞ ∧
        normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false (A g)) z))
          (q (inChart false false (A g) z))=q z) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ F : ℂ ≃ₜ ℂ, F 0=0 ∧ F 1=1 ∧
        WeakQS F C ∧ WeakQS F.symm C ∧
        (∀ᵐ z : ℂ, DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
          Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
            Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) := by
  classical
  obtain ⟨K,hKm,hKae,hKi,hgood,q,hqm,hqb,hqi⟩ := controlled_action_invariant_structure A hA
  let H : ℝ := 1+2*(η 2:ℝ)
  have hH : 1 ≤ H := by
    dsimp [H]
    have := (η 2).coe_nonneg
    linarith
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hH2 : 1 ≤ H^2 := one_le_pow₀ hH
  have hi : (H^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hH2
  let Q : ℂ → Form := fun z => if hz : (z:Sphere) ∈ K then q ⟨z,hz⟩ else roundForm
  have hQm : Measurable Q := measurable_extend_form hKm q hqm
  have hQb (z : ℂ) : LowerBound ((H^2)⁻¹) (Q z) ∧ UpperBound (H^2) (Q z) := by
    dsimp [Q]
    split_ifs with hz
    · exact hqb ⟨z,hz⟩
    · exact roundForm_bounds hi hH2
  have hQeq (z : ℂ) (hz : (z:Sphere) ∈ K) : Q z=q ⟨z,hz⟩ := dite_eq_left hz
  have hQi (g : Γ) : ∀ᵐ z : ℂ, A g (z:Sphere) ≠ ∞ ∧
      normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false (A g)) z))
        (Q (inChart false false (A g) z))=Q z := by
    filter_upwards [ae_sphere_iff.mp hKae] with z hz
    have hg := (hgood (z:Sphere) hz).2 g
    have hgK := (hKi g (z:Sphere)).mpr hz
    have hcoe : (inChart false false (A g) z : Sphere)=A g (z:Sphere) :=
      coe_coordinate hg.1
    refine ⟨hg.1,?_⟩
    rw [hQeq z hz,hQeq _ (hcoe.symm ▸ hgK)]
    have hh := hqi g ⟨z,hz⟩ hgK
    have he : (⟨(inChart false false (A g) z : Sphere), hcoe.symm ▸ hgK⟩ : K) = ⟨A g (z:Sphere),hgK⟩ := Subtype.ext hcoe
    rw [he]
    simpa only [sphereDerivative,coordinate_coe] using hh
  refine ⟨Q,hQm,hQb,hQi,?_⟩
  exact measurable_structure_integration Q hQm (inv_pos.mpr (sq_pos_of_pos hHp))
    (sq_pos_of_pos hHp) (fun z => (hQb z).1) (fun z => (hQb z).2)

end CannonMobius

end
end
section
noncomputable section

noncomputable section
namespace CannonConformal
open scoped RealInnerProductSpace
open CannonMetricQC

lemma isConformalMap_of_normSq (L : ℂ →L[ℝ] ℂ) {c : ℝ} (hc : 0 < c)
    (h : ∀ v : ℂ, Complex.normSq (L v)=c*Complex.normSq v) : IsConformalMap L := by
  apply (isConformalMap_iff L).mpr
  refine ⟨c,hc,fun u v => ?_⟩
  have hn (v : ℂ) : ‖L v‖^2=c*‖v‖^2 := by simpa only [Complex.sq_norm] using h v
  have hu := hn u
  have hv := hn v
  have huv := hn (u+v)
  rw [map_add,norm_add_sq_real,norm_add_sq_real] at huv
  nlinarith

lemma evaluate_pull_derivative (A : ℂ →L[ℝ] ℂ) (q : Form) (v : ℂ) :
    evaluate (pullForm (derivativeMatrix A) q) v.re v.im = evaluate q (A v).re (A v).im := by
  rw [evaluate_pullForm,derivative_apply A v]
  simp [derivativeMatrix,Complex.real_smul,mul_comm]

lemma invariant_form_evaluate {A : ℂ →L[ℝ] ℂ} {p q : Form}
    (hA : Function.Bijective A) (h : normalizedPull (derivativeMatrix A) q=p)
    (v : ℂ) : evaluate q (A v).re (A v).im=|derivativeDet A| *evaluate p v.re v.im := by
  have hh := congrArg (fun t : Form => evaluate t v.re v.im) h
  rw [normalizedPull_apply,evaluate_smul,evaluate_pull_derivative] at hh
  change |derivativeDet A|⁻¹*evaluate q (A v).re (A v).im=evaluate p v.re v.im at hh
  have hz := abs_ne_zero.mpr (derivativeDet_ne_zero hA)
  calc
    _ = |derivativeDet A| *(|derivativeDet A|⁻¹*evaluate q (A v).re (A v).im) := by
      rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul]
    _ = _ := by rw [hh]

theorem integrated_invariant_form_conformal
    (A P Q R : ℂ →L[ℝ] ℂ) (p q : Form) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hA : Function.Bijective A)
    (hInv : P.comp R=ContinuousLinearMap.id ℝ ℂ)
    (hI : normalizedPull (derivativeMatrix A) q=p)
    (hP : ∀ v : ℂ, Complex.normSq (P v)=c*evaluate p v.re v.im)
    (hQ : ∀ v : ℂ, Complex.normSq (Q v)=d*evaluate q v.re v.im) :
    IsConformalMap (Q.comp (A.comp R)) := by
  have ha : 0 < |derivativeDet A| := abs_pos.mpr (derivativeDet_ne_zero hA)
  apply isConformalMap_of_normSq _ (div_pos (mul_pos hd ha) hc)
  intro v
  have hv : P (R v)=v := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hInv
  have hp := hP (R v)
  rw [hv] at hp
  change Complex.normSq (Q (A (R v)))=(d*|derivativeDet A|/c)*Complex.normSq v
  rw [hQ,invariant_form_evaluate hA hI,hp]
  field_simp

end CannonConformal

end
end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal
open scoped OnePoint

lemma coordinate_onePoint (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0) (p : Sphere) :
    coordinate (F.onePointCongr p)=F (coordinate p) := by
  induction p using OnePoint.rec with
  | infty => simpa [coordinate] using hF0.symm
  | coe z => rfl

lemma chart_conjugate_onePoint (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0) (f : Sphere ≃ₜ Sphere) :
    inChart false false (F.onePointCongr*f*F.onePointCongr.symm)=
      fun z => F (inChart false false f (F.symm z)) := by
  funext z
  exact coordinate_onePoint F hF0 (f (F.symm z : Sphere))

theorem integrated_conjugate_ae_conformal
    (f : Sphere ≃ₜ Sphere) {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η)
    (q : ℂ → Form)
    (hI : ∀ᵐ z : ℂ, normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false f) z))
      (q (inChart false false f z))=q z)
    (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0) {C : ℝ} (hC : 0 < C)
    (hF : WeakQS F C) (hFi : WeakQS F.symm C)
    (hD : ∀ᵐ z : ℂ, DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
      Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
        Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) :
    ∀ᵐ y : ℂ, DifferentiableAt ℝ (inChart false false (F.onePointCongr*f*F.onePointCongr.symm)) y ∧
      IsConformalMap (fderiv ℝ (inChart false false (F.onePointCongr*f*F.onePointCongr.symm)) y) := by
  have hcore : ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z ∧
      Function.Bijective (fderiv ℝ (inChart false false f) z) ∧
      normalizedPull (derivativeMatrix (fderiv ℝ (inChart false false f) z))
        (q (inChart false false f z))=q z ∧
      (DifferentiableAt ℝ (F : ℂ → ℂ) z ∧
        Function.Bijective (fderiv ℝ (F : ℂ → ℂ) z) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ, Complex.normSq (fderiv ℝ (F : ℂ → ℂ) z v)=c*evaluate (q z) v.re v.im) ∧
      (DifferentiableAt ℝ (F : ℂ → ℂ) (inChart false false f z) ∧
        Function.Bijective (fderiv ℝ (F : ℂ → ℂ) (inChart false false f z)) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ, Complex.normSq (fderiv ℝ (F : ℂ → ℂ) (inChart false false f z) v)=
          c*evaluate (q (inChart false false f z)) v.re v.im) := by
    filter_upwards [controlled_sphere_ae_differentiable f hf,
      controlled_sphere_ae_bijective_fderiv f hf,hI,hD,controlled_chart_ae_pullback f hf hD]
      with z hz hn hi hd he
    exact ⟨hz,hn,hi,hd,he⟩
  have hm := weakQS_quasiMeasurePreserving F.symm hC hF
  filter_upwards [hm.ae hcore,weakQS_ae_differentiable F.symm hC hFi] with y hy hiy
  rcases hy with ⟨hdy,hay,hiyq,hpy,hqy⟩
  rcases hpy with ⟨hp,hpn,c,hc,hpc⟩
  rcases hqy with ⟨hq,hqn,d,hd,hqd⟩
  have hId : (fderiv ℝ (F : ℂ → ℂ) (F.symm y)).comp
      (fderiv ℝ (F.symm : ℂ → ℂ) y)=ContinuousLinearMap.id ℝ ℂ := by
    have hh := hp.hasFDerivAt.comp y hiy.hasFDerivAt
    have he : (F : ℂ → ℂ) ∘ (F.symm : ℂ → ℂ)=id := by funext z; exact F.apply_symm_apply z
    rw [he] at hh
    exact hh.unique (hasFDerivAt_id y)
  have hchain := hq.hasFDerivAt.comp y (hdy.hasFDerivAt.comp y hiy.hasFDerivAt)
  have hnorm := integrated_invariant_form_conformal
    (fderiv ℝ (inChart false false f) (F.symm y))
    (fderiv ℝ (F : ℂ → ℂ) (F.symm y))
    (fderiv ℝ (F : ℂ → ℂ) (inChart false false f (F.symm y)))
    (fderiv ℝ (F.symm : ℂ → ℂ) y) (q (F.symm y)) (q (inChart false false f (F.symm y)))
    hc hd hay hId hiyq hpc hqd
  rw [chart_conjugate_onePoint F hF0 f]
  exact ⟨hchain.differentiableAt,hchain.fderiv ▸ hnorm⟩

end CannonMobius

end
end
end
end
end

end OAI
