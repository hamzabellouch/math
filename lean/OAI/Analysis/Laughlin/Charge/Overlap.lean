import OAI.Analysis.Laughlin.Charge.FiniteGap
import OAI.Analysis.Laughlin.Charge.Comparison

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators InnerProductSpace

noncomputable def weightedCreate (Q : ℕ) (c : Fin (Q+1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, c i • create i

noncomputable def weightedAnnihilate (Q : ℕ) (c : Fin (Q+1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, star (c i) • annihilate i

theorem weighted_adjoint (Q : ℕ) (c : Fin (Q+1) → ℂ) (u v : Space Q) :
    occupationInner Q (weightedCreate Q c u) v=
      occupationInner Q u (weightedAnnihilate Q c v) := by
  simp only [weightedCreate,weightedAnnihilate,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,create_annihilate_adjoint]

theorem weighted_adjoint_rev (Q : ℕ) (c : Fin (Q+1) → ℂ) (u v : Space Q) :
    occupationInner Q (weightedAnnihilate Q c u) v=
      occupationInner Q u (weightedCreate Q c v) := by
  have h := congrArg star (weighted_adjoint Q c v u)
  simpa only [occupationInner_star] using h.symm

theorem weighted_car (Q : ℕ) (c : Fin (Q+1) → ℂ) :
    weightedAnnihilate Q c * weightedCreate Q c + weightedCreate Q c * weightedAnnihilate Q c =
      ((∑ i, ‖c i‖^2 : ℝ) : ℂ) • (1 : Module.End ℂ (Space Q)) := by
  have hs : weightedAnnihilate Q c * weightedCreate Q c +
      weightedCreate Q c * weightedAnnihilate Q c =
      ∑ i, ∑ j, (star (c i)*c j) • (annihilate i*create j+create j*annihilate i) := by
    simp only [weightedAnnihilate,weightedCreate,Finset.sum_mul,Finset.mul_sum,
      smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul,smul_add,Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
  rw [hs]
  simp only [mixed_car,ite_smul,one_smul,zero_smul,smul_ite,smul_zero,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.sum_smul,Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (starRingEnd ℂ) (c i)*c i=((‖c i‖^2 : ℝ) : ℂ)
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]

theorem weighted_norm_identity (Q : ℕ) (c : Fin (Q+1) → ℂ) (v : Space Q) :
    occupationNormSq Q (weightedCreate Q c v)+occupationNormSq Q (weightedAnnihilate Q c v)=
      (∑ i, ‖c i‖^2)*occupationNormSq Q v := by
  apply Complex.ofReal_injective
  push_cast
  rw [← occupationInner_self,← occupationInner_self,← occupationInner_self,
    weighted_adjoint,weighted_adjoint_rev,← occupationInner_add_right,
    ← occupationInner_smul_right]
  congr 1
  simpa only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.smul_apply,
    Module.End.one_apply,Complex.ofReal_sum,Complex.ofReal_pow] using
    LinearMap.congr_fun (weighted_car Q c) v

theorem occupation_cauchy_sq (Q : ℕ) (x y : Space Q) :
    ‖occupationInner Q x y‖^2≤occupationNormSq Q x*occupationNormSq Q y := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (occupationEuclidean Q x) (occupationEuclidean Q y)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h
  rw [occupationEuclidean_inner,mul_pow,occupationEuclidean_norm,occupationEuclidean_norm] at hs
  exact hs

theorem creation_frame_bound (Q : ℕ) (v x : Space Q) :
    (∑ i : Fin (Q+1), ‖occupationInner Q v (annihilate i x)‖^2)≤
      occupationNormSq Q v*occupationNormSq Q x := by
  let c := fun i : Fin (Q+1) => occupationInner Q v (annihilate i x)
  let S : ℝ := ∑ i, ‖c i‖^2
  let z := weightedCreate Q c v
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hz : occupationNormSq Q z≤S*occupationNormSq Q v := by
    have h := weighted_norm_identity Q c v
    have hp := occupationNormSq_nonneg Q (weightedAnnihilate Q c v)
    change occupationNormSq Q z+occupationNormSq Q (weightedAnnihilate Q c v)=
      S*occupationNormSq Q v at h
    linarith
  have hi : occupationInner Q z x=(S : ℂ) := by
    simp only [z,weightedCreate,LinearMap.sum_apply,LinearMap.smul_apply,
      occupationInner_sum_left,occupationInner_smul_left,create_annihilate_adjoint]
    change (∑ i, star (c i)*c i)=(S : ℂ)
    simp only [S,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (starRingEnd ℂ) (c i)*c i=((‖c i‖^2 : ℝ) : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  have hc := occupation_cauchy_sq Q z x
  rw [hi,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hS] at hc
  have hm := mul_le_mul_of_nonneg_right hz (occupationNormSq_nonneg Q x)
  change S≤occupationNormSq Q v*occupationNormSq Q x
  by_cases hs : S=0
  · rw [hs]
    exact mul_nonneg (occupationNormSq_nonneg Q v) (occupationNormSq_nonneg Q x)
  · have hp : 0<S := lt_of_le_of_ne hS (Ne.symm hs)
    have htrans := hc.trans hm
    rw [pow_two,mul_assoc] at htrans
    exact le_of_mul_le_mul_left htrans hp

theorem annihilator_frame_bound (Q : ℕ) (v x : Hilbert Q) :
    (∑ i : Fin (Q+1), ‖inner ℂ v (annihilator Q i x)‖^2)≤‖v‖^2*‖x‖^2 := by
  obtain ⟨u,rfl⟩ := (occupationEuclidean Q).surjective v
  obtain ⟨y,rfl⟩ := (occupationEuclidean Q).surjective x
  simpa only [annihilator,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply,occupationEuclidean_inner,occupationEuclidean_norm] using
    creation_frame_bound Q u y

theorem unit_generator {Q : ℕ} (K : Submodule ℂ (Hilbert Q)) (hK : Module.finrank ℂ K=1) :
    ∃ v : Hilbert Q, ‖v‖^2=1 ∧ K=ℂ ∙ v := by
  have hpos : 0<Module.finrank ℂ K := by omega
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv0 : (v : Hilbert Q)≠0 := by intro h; exact hv (Subtype.ext h)
  let u : Hilbert Q := (‖(v : Hilbert Q)‖ : ℂ)⁻¹ • (v : Hilbert Q)
  have huK : u ∈ K := K.smul_mem _ v.property
  have hu0 : u≠0 := smul_ne_zero (inv_ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr hv0))) hv0
  refine ⟨u,?_,?_⟩
  · dsimp [u]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    norm_num
  · exact eq_span_singleton_of_mem_of_finrank_eq_one hK huK hu0

theorem lnwyRankOneInput : LNWYRankOneInput := by
  intro Q n hline x hx
  obtain ⟨v,hv,hspan⟩ := unit_generator (groundKernel Q n) hline
  unfold groundOverlap
  have heq (i : Fin (Q+1)) : ‖(groundKernel Q n).starProjection (annihilator Q i x)‖^2=
      ‖inner ℂ v (annihilator Q i x)‖^2 := by
    simp only [hspan]
    rw [Submodule.starProjection_singleton, hv]
    simp [norm_smul,mul_pow,hv]
  simp_rw [heq]
  have h := annihilator_frame_bound Q v x
  simpa only [hv,hx.2,one_mul] using h

end Laughlin.Charge

end OAI
