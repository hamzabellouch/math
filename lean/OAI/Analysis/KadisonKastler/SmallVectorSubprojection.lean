import OAI.Analysis.KadisonKastler.TypeIIIPrescribedRank
import OAI.Analysis.KadisonKastler.VectorSupportProjection

namespace OAI

/-! # Small positive vector-state cuts in type III algebras

Restricting to the vector support makes every nonzero subprojection have
positive weight. Repeated proper splitting then makes that weight small.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vector_projection_sub_weight (p q : AlgebraProjection M) (hqp : q ≤ p) (η : H) :
    ‖q.val.val η‖^2+‖(p.val-q.val).val η‖^2=‖p.val.val η‖^2 := by
  have hzero : q.val*(p.val-q.val)=0 := by
    rw [mul_sub,projection_mul_of_le hqp,q.property.isIdempotentElem.eq,sub_self]
  have horth : inner ℂ (q.val.val η) ((p.val-q.val).val η)=0 :=
    inner_eq_zero_of_selfAdjoint_mul_eq_zero _ _
      (q.property.map M.toStarSubalgebra.subtype).isSelfAdjoint
      (congrArg Subtype.val hzero) η η
  have he := norm_add_sq (𝕜 := ℂ) (q.val.val η) ((p.val-q.val).val η)
  have hv : q.val.val η+(p.val-q.val).val η=p.val.val η := by
    change q.val.val η+(p.val.val η-q.val.val η)=p.val.val η
    abel
  rw [horth,map_zero,mul_zero,add_zero,hv] at he
  exact he.symm

theorem TypeIIIFactor.exists_half_vector_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (η : H) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ ‖q.val.val η‖^2 ≤ ‖p.val.val η‖^2/2 := by
  obtain ⟨q,hqp,hq0,hqne⟩ := hM.exists_proper_subprojection p hp
  by_cases hh : ‖q.val.val η‖^2 ≤ ‖p.val.val η‖^2/2
  · exact ⟨q,hqp,hq0,hh⟩
  · let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hqp⟩
    have hrp : r ≤ p := by
      change p.val*(p.val-q.val)=p.val-q.val
      rw [mul_sub,p.property.isIdempotentElem.eq,hqp]
    refine ⟨r,hrp,?_,?_⟩
    · exact sub_ne_zero.mpr (Ne.symm hqne)
    · have he := vector_projection_sub_weight p q hqp η
      change ‖(p.val-q.val).val η‖^2 ≤ _
      linarith

theorem TypeIIIFactor.exists_geometric_vector_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (η : H) (n : ℕ) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧
      ‖q.val.val η‖^2 ≤ (1/2 : ℝ)^n*‖p.val.val η‖^2 := by
  induction n with
  | zero => exact ⟨p,le_rfl,hp,by simp⟩
  | succ n ih =>
    obtain ⟨q,hqp,hq0,hqw⟩ := ih
    obtain ⟨r,hrq,hr0,hrw⟩ := hM.exists_half_vector_subprojection q hq0 η
    refine ⟨r,hrq.trans hqp,hr0,?_⟩
    calc
      _ ≤ ‖q.val.val η‖^2/2 := hrw
      _ ≤ ((1/2 : ℝ)^n*‖p.val.val η‖^2)/2 := div_le_div_of_nonneg_right hqw (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem TypeIIIFactor.exists_small_positive_vector_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (η : H) (hp : 0 < ‖p.val.val η‖^2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ 0 < ‖q.val.val η‖^2 ∧ ‖q.val.val η‖^2 < ε := by
  let ζ := p.val.val η
  let e := vectorSupportProjection M ζ
  have hep : e ≤ p := by
    have he := vectorSupport_minimal M ζ p (by
      change p.val.val (p.val.val η)=p.val.val η
      exact congrArg (fun a : Algebra M => a.val η) p.property.isIdempotentElem.eq)
    have hs := congrArg star he
    have hes := (e.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
    have hps := (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
    change star e.val.val=e.val.val at hes
    change star p.val.val=p.val.val at hps
    apply Subtype.ext
    change p.val.val*e.val.val=e.val.val
    change star (e.val.val*p.val.val)=star e.val.val at hs
    rw [star_mul,hps,hes] at hs
    exact hs
  have he0 : e.val ≠ 0 := by
    intro hz
    have he := vectorSupportProjection_apply M ζ
    change e.val.val ζ=ζ at he
    rw [hz] at he
    have hζ : ζ=0 := by simpa using he.symm
    change 0 < ‖ζ‖^2 at hp
    simp [hζ] at hp
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n*‖e.val.val η‖^2) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).mul_const (‖e.val.val η‖^2)
  obtain ⟨n,hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  obtain ⟨q,hqe,hq0,hqw⟩ := hM.exists_geometric_vector_subprojection e he0 η n
  have hqp := hqe.trans hep
  refine ⟨q,hqp,?_,hqw.trans_lt hn⟩
  apply sq_pos_of_ne_zero
  intro hz
  have hqη : q.val.val η=0 := norm_eq_zero.mp hz
  apply hq0
  apply vectorSupport_faithful_corner M ζ q.val
  · exact congrArg Subtype.val (projection_mul_of_le hqe)
  · change q.val.val (p.val.val η)=0
    have he := congrArg (fun a : Algebra M => a.val η) (projection_mul_of_le hqp)
    exact he.trans hqη

end

end KadisonKastler

end OAI
