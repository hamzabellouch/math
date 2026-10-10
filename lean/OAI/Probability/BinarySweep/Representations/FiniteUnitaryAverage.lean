import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicMoment
import OAI.Probability.BinarySweep.Processes.CoordinateLayerEdgeSwap

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def complexAverage (ρ : Representation ℂ G V) (p : G → ℂ) : V →L[ℂ] V :=
  (Irrep.groupAverage ρ p).toContinuousLinearMap

lemma complexAverage_apply (ρ : Representation ℂ G V) (p : G → ℂ) (v : V) :
    complexAverage ρ p v = ∑ g, p g • ρ g v := by
  simp [complexAverage,Irrep.groupAverage]

lemma complexAverage_norm_apply (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (p : G → ℂ) (v : V) :
    ‖complexAverage ρ p v‖ ≤ (∑g, ‖p g‖)*‖v‖ := by
  rw [complexAverage_apply,Finset.sum_mul]
  exact (norm_sum_le _ _).trans_eq (by simp [norm_smul,hρ])

lemma realAverage_contraction (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v‖ ≤ ‖v‖ := by
  have he : (∑g, ‖(p g:ℂ)‖)=1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp.1 _)] using hp.2
  simpa only [he,one_mul] using complexAverage_norm_apply ρ hρ (fun g => (p g:ℂ)) v

lemma complexAverage_sub (ρ : Representation ℂ G V) (p q : G → ℂ) :
    complexAverage ρ (fun g => p g-q g)=complexAverage ρ p-complexAverage ρ q := by
  ext v
  simp [complexAverage_apply,sub_smul,Finset.sum_sub_distrib]

lemma complexAverage_convolution (ρ : Representation ℂ G V) (p q : G → ℝ) :
    complexAverage ρ (fun g => (convolution p q g:ℂ)) =
      complexAverage ρ (fun g => (p g:ℂ))*complexAverage ρ (fun g => (q g:ℂ)) := by
  ext v
  calc
    _ = ∑ x, ∑ y, (p x:ℂ) • (q y:ℂ) • ρ (x*y) v := by
      rw [complexAverage_apply]
      simp only [convolution,Complex.ofReal_sum,Finset.sum_smul,
        Complex.ofReal_mul,mul_smul]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Equiv.coe_mulLeft,inv_mul_cancel_left] using
        (Equiv.sum_comp (Equiv.mulLeft x)
          (fun y => (p x:ℂ) • (q (x⁻¹*y):ℂ) • ρ y v)).symm
    _ = _ := by
      rw [mul_apply_eq_comp,complexAverage_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [complexAverage_apply,map_sum,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [map_smul,map_mul,Module.End.mul_apply]

lemma complexAverage_pointMass (ρ : Representation ℂ G V) :
    complexAverage ρ (fun g => (pointMassOne g:ℂ))=1 := by
  ext v
  simp [complexAverage_apply,pointMassOne]

lemma complexAverage_power (ρ : Representation ℂ G V) (p : G → ℝ) (n : ℕ) :
    complexAverage ρ (fun g => (convolutionPower p n g:ℂ))=
      (complexAverage ρ (fun g => (p g:ℂ)))^n := by
  induction n with
  | zero => exact complexAverage_pointMass ρ
  | succ n ih => rw [convolutionPower,complexAverage_convolution,ih,pow_succ']

lemma complexAverage_uniform_left (ρ : Representation ℂ G V) (g : G) (v : V) :
    ρ g (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  simp only [complexAverage_apply,map_sum,map_smul,←Module.End.mul_apply,←map_mul,uniformLaw]
  simpa only [Equiv.coe_mulLeft,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.mulLeft g) (fun x => ((Fintype.card G:ℝ)⁻¹:ℂ) • ρ x v)

lemma complexAverage_uniform_right (ρ : Representation ℂ G V) (g : G) (v : V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ)) (ρ g v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  simp only [complexAverage_apply,←Module.End.mul_apply,←map_mul,uniformLaw]
  simpa only [Equiv.coe_mulRight,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.mulRight g) (fun x => ((Fintype.card G:ℝ)⁻¹:ℂ) • ρ x v)

lemma complexAverage_uniform_idem (ρ : Representation ℂ G V) (v : V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))
      (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v) =
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  rw [complexAverage_apply]
  simp only [complexAverage_uniform_left,←Finset.sum_smul,←Complex.ofReal_sum,uniformLaw_sum,
    Complex.ofReal_one,one_smul]

lemma complexAverage_uniform_inner (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (v w : V) :
    inner ℂ (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v) w =
      inner ℂ v (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) w) := by
  simp only [complexAverage_apply,inner_sum,inner_smul_left, sum_inner,
    inner_smul_right,Complex.conj_ofReal]
  have he (g : G) : inner ℂ (ρ g v) w=inner ℂ v (ρ g⁻¹ w) := by
    rw [←LinearMap.adjoint_inner_right,Irrep.unitary_rep_adjoint ρ hρ]
  simp_rw [he]
  simpa only [uniformLaw,Equiv.inv_apply,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.inv G) (fun g => ((Fintype.card G:ℝ)⁻¹:ℂ)*inner ℂ v (ρ g w))

lemma complexAverage_variance (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    ∑g, p g * ‖ρ g v-complexAverage ρ (fun g => (p g:ℂ)) v‖^2 =
      ‖v‖^2-‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 := by
  let B := complexAverage ρ (fun g => (p g:ℂ))
  have hi : ∑g, p g * (inner ℂ (ρ g v) (B v)).re=‖B v‖^2 := by
    have he : ∑g, (p g:ℂ)*inner ℂ (ρ g v) (B v)=inner ℂ (B v) (B v) := by
      rw [show B v=∑g, (p g:ℂ) • ρ g v from complexAverage_apply ρ _ v]
      rw [sum_inner]
      simp only [inner_smul_left,Complex.conj_ofReal]
    have hre := congrArg Complex.re he
    have hsq : (inner ℂ (B v) (B v)).re=‖B v‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (B v)
    rw [hsq] at hre
    simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,inner_self_eq_norm_sq] using hre
  simp only [@norm_sub_sq ℂ V _ _,hρ,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [←Finset.sum_mul,hp.2,one_mul,←Finset.sum_mul,hp.2,one_mul]
  have hs : (∑g, p g*(2*(inner ℂ (ρ g v) (B v)).re))=2*‖B v‖^2 := by
    rw [←hi,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  change ‖v‖^2-(∑g, p g*(2*(inner ℂ (ρ g v) (B v)).re))+‖B v‖^2=_
  rw [hs]
  ring

lemma realAverage_identity_defect (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    p 1*‖v-complexAverage ρ (fun g => (p g:ℂ)) v‖^2 ≤
      ‖v‖^2-‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 := by
  rw [←complexAverage_variance ρ hρ hp]
  simpa only [map_one,Module.End.one_apply] using Finset.single_le_sum (fun g _ => mul_nonneg (hp.1 g)
    (sq_nonneg ‖ρ g v-complexAverage ρ (fun g => (p g:ℂ)) v‖))
    (Finset.mem_univ (1:G))

end BinaryCoordinateSweeps

end

end OAI
