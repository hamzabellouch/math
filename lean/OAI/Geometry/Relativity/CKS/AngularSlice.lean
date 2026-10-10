import OAI.Geometry.Relativity.CKS.CKSSourceMass

namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
abbrev AP := CKSAngularGeometry.Point
abbrev MP := CKSMixedGeometry.Point
abbrev A := Fin 2

 def injection : AP →L[ℝ] MP :=
  ContinuousLinearMap.pi (fun i => Fin.cases 0 (fun a => ContinuousLinearMap.proj a) i)
def slice (r : ℝ) (x : AP) : MP := Pi.single 0 r+injection x

@[simp] lemma injection_zero (x : AP) : injection x 0=0 := rfl
@[simp] lemma injection_succ (x : AP) (a : A) : injection x a.succ=x a := rfl
@[simp] lemma slice_zero (r : ℝ) (x : AP) : slice r x 0=r := by simp [slice]
@[simp] lemma slice_succ (r : ℝ) (x : AP) (a : A) : slice r x a.succ=x a := by simp [slice]

lemma injection_basis (a : A) : injection (CKSAngularGeometry.basis a)=CKSMixedGeometry.basis a.succ := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [CKSMixedGeometry.basis]
  · simp [CKSAngularGeometry.basis,CKSMixedGeometry.basis,Pi.single_apply]

lemma slice_hasFDerivAt (r : ℝ) (x : AP) : HasFDerivAt (slice r) injection x :=
  injection.hasFDerivAt.const_add _
lemma slice_smooth (r : ℝ) : ContDiff ℝ ∞ (slice r) :=
  contDiff_const.add injection.contDiff

lemma D_slice (a : A) (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : DifferentiableAt ℝ f (slice r x)) :
    D (CKSAngularGeometry.basis a) (fun y => f (slice r y)) x=
      D (CKSMixedGeometry.basis a.succ) f (slice r x) := by
  unfold D
  erw [fderiv_comp x hf (slice_hasFDerivAt r x).differentiableAt,
    (slice_hasFDerivAt r x).fderiv,ContinuousLinearMap.comp_apply,injection_basis]

 def restrictJet (p : CKSMixedGeometry.ScalarJet) : CKSAngularGeometry.ScalarJet :=
  (p.1,fun a => p.2.1 a.succ,fun a b => p.2.2 a.succ b.succ)
 def restrictThree (p : CKSMixedGeometry.ScalarThreeJet) : CKSAngularGeometry.ScalarThreeJet :=
  (restrictJet p.1,fun a => restrictJet (p.2 a.succ))

lemma actualScalarJet_slice (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 2 f (slice r x)) :
    CKSAngularGeometry.actualScalarJet (fun y => f (slice r y)) x=
      restrictJet (CKSMixedGeometry.actualScalarJet f (slice r x)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a; exact D_slice a r (hf.differentiableAt (by norm_num))
  · funext a b
    have he : D (CKSAngularGeometry.basis b) (fun y => f (slice r y)) =ᶠ[𝓝 x]
        (fun y => D (CKSMixedGeometry.basis b.succ) f (slice r y)) := by
      have hn := (slice_smooth r).continuous.continuousAt.tendsto.eventually (hf.eventually (by simp))
      filter_upwards [hn] with y hy
      exact D_slice b r (hy.differentiableAt (by norm_num))
    change D (CKSAngularGeometry.basis a) (D (CKSAngularGeometry.basis b) (fun y => f (slice r y))) x=_
    rw [D_congr he]
    exact D_slice a r ((contDiffAt_D hf (m:=1) (by norm_num) _).differentiableAt (by norm_num))

lemma actualThreeJet_slice (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 3 f (slice r x)) :
    CKSAngularGeometry.actualThreeJet (fun y => f (slice r y)) x=
      restrictThree (CKSMixedGeometry.actualThreeJet f (slice r x)) := by
  apply Prod.ext (actualScalarJet_slice r (hf.of_le (by norm_num)))
  funext a
  have he : D (CKSAngularGeometry.basis a) (fun y => f (slice r y)) =ᶠ[𝓝 x]
      (fun y => D (CKSMixedGeometry.basis a.succ) f (slice r y)) := by
    have hn := (slice_smooth r).continuous.continuousAt.tendsto.eventually (hf.eventually (by simp))
    filter_upwards [hn] with y hy
    exact D_slice a r (hy.differentiableAt (by norm_num))
  change CKSAngularGeometry.actualScalarJet (D (CKSAngularGeometry.basis a) (fun y => f (slice r y))) x=_
  rw [CKSAngularGeometry.actualScalarJet_congr he]
  exact actualScalarJet_slice r (contDiffAt_D hf (m:=2) (by norm_num) _)

lemma restrictJet_norm (p : CKSMixedGeometry.ScalarJet) : ‖restrictJet p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨norm_fst_le p, norm_prod_le_iff.mpr ⟨?_,?_⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro a
    exact (norm_le_pi_norm p.2.1 a.succ).trans ((norm_fst_le p.2).trans (norm_snd_le p))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro b
    exact ((norm_le_pi_norm (p.2.2 a.succ) b.succ).trans (norm_le_pi_norm p.2.2 a.succ)).trans
      ((norm_snd_le p.2).trans (norm_snd_le p))

lemma restrictThree_norm (p : CKSMixedGeometry.ScalarThreeJet) : ‖restrictThree p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨(restrictJet_norm p.1).trans (norm_fst_le p),?_⟩
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
  intro a
  exact (restrictJet_norm (p.2 a.succ)).trans ((norm_le_pi_norm p.2 a.succ).trans (norm_snd_le p))

lemma angular_twojet_le_mixed (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 2 f (slice r x)) :
    ‖CKSAngularGeometry.actualScalarJet (fun y => f (slice r y)) x‖ ≤
      ‖CKSMixedGeometry.actualScalarJet f (slice r x)‖ := by
  rw [actualScalarJet_slice r hf]; exact restrictJet_norm _
lemma angular_threejet_le_mixed (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 3 f (slice r x)) :
    ‖CKSAngularGeometry.actualThreeJet (fun y => f (slice r y)) x‖ ≤
      ‖CKSMixedGeometry.actualThreeJet f (slice r x)‖ := by
  rw [actualThreeJet_slice r hf]; exact restrictThree_norm _

end
end CKSAngularSlice

end

end OAI
