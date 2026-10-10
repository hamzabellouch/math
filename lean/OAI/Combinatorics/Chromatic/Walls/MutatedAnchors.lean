import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationLogCompletion
import OAI.Combinatorics.Chromatic.GradedAlgebra.RealRootCoordinates

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)

omit [FiniteDimensional ℝ E] in
lemma mutated_degree_covector (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃J:Module.Dual ℝ E,∀i,J (e (simpleRoot (mutatedRoots Ω C pc) i))=1 := by
  classical
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  let w:I → ℝ:=fun i=>if i=pc then -1 else 1+(max 0 (-mutationPairing Ω C pc i):ℤ)
  let J:Module.Dual ℝ E:=∑i,w i • (LinearMap.proj i).comp D
  have hj (i:I):J (e (simpleRoot C i))=w i:=by
    simp only [J,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      real_coordinate_simple C e D hD,LinearMap.proj_apply,smul_eq_mul,Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [hji]
    · simp
  refine ⟨J,fun i=>?_⟩
  by_cases hi:i=pc
  · subst i
    rw [mutatedRoot_p,map_neg,map_neg,hj]
    simp [w]
  · rw [mutatedRoot_off Ω C pc i hi,map_add,map_zsmul,map_add,map_zsmul,hj,hj]
    simp [w,hi,zsmul_eq_mul]

omit [FiniteDimensional ℝ E] in
lemma covector_root_pos (J:Module.Dual ℝ E)
    (hJ:∀i,0<J (e (simpleRoot C i))) {n:ℕ} (hn:0<n) {m:M} (hm:HasRootDegree C n m) :
    0<J (e m) := by
  obtain ⟨a,ha,rfl⟩:=hm
  rw [coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,zsmul_eq_mul]
  have hp:∃i,0<a i:=by
    by_contra H
    push Not at H
    have hh:(∑i,a i)≤0:=Finset.sum_nonpos (fun i _=>H i)
    rw [ha] at hh
    omega
  obtain ⟨i,hi⟩:=hp
  exact Finset.sum_pos' (fun j _=>mul_nonneg (by exact_mod_cast Nat.zero_le (a j)) (hJ j).le)
    ⟨i,Finset.mem_univ i,mul_pos (by exact_mod_cast hi) (hJ i)⟩

include hS in
lemma mutated_regular_anchors (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃a b:Module.Dual ℝ E,RegularCovector C e a ∧ RegularCovector C e b ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        0<realMutationCovector e S (simpleRoot C pc) a (e m)) ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        realMutationCovector e S (simpleRoot C pc) b (e m)<0) := by
  classical
  obtain ⟨J,hJ⟩:=mutated_degree_covector Ω C pc e hC
  have hJp:J (e (simpleRoot C pc))= -1:=by
    have H:=hJ pc
    rw [mutatedRoot_p,map_neg,map_neg] at H
    linarith
  let K:=realShearCovectorInverse e S (simpleRoot C pc) J
  have hK:realShearCovector e S (simpleRoot C pc) K=J:=
    realShearCovector_right_inverse e S _ hS J
  let P:=Finset.univ.image (fun i=>realShearVector e S (simpleRoot C pc)
    (e (simpleRoot (mutatedRoots Ω C pc) i)))
  let Q:=Finset.univ.image (fun i=>e (simpleRoot (mutatedRoots Ω C pc) i))
  obtain ⟨a,HA,_,Sa⟩:=regular_covector_with_signs C e ∅ (insert (e (simpleRoot C pc)) P) K
  obtain ⟨b,HB,_,Sb⟩:=regular_covector_with_signs C e ∅ (insert (e (simpleRoot C pc)) Q) (-J)
  have hap:a (e (simpleRoot C pc))<0:=by
    apply (Sa _ (Finset.mem_insert_self _ _)).2
    rw [realShearCovectorInverse_at_p e S _ hS J,hJp]
    norm_num
  have hbp:0<b (e (simpleRoot C pc)):=by
    apply (Sb _ (Finset.mem_insert_self _ _)).1
    simp [hJp]
  have ha:∀i,0<realMutationCovector e S (simpleRoot C pc) a
      (e (simpleRoot (mutatedRoots Ω C pc) i)):=by
    intro i
    rw [realMutationCovector,ite_eq_right (not_le_of_gt hap),realShearCovector_eval]
    apply (Sa _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))).1
    rw [←realShearCovector_eval,hK,hJ]
    norm_num
  have hb:∀i,0<(-realMutationCovector e S (simpleRoot C pc) b)
      (e (simpleRoot (mutatedRoots Ω C pc) i)):=by
    intro i
    rw [realMutationCovector,ite_eq_left hbp.le,LinearMap.neg_apply]
    apply neg_pos.mpr
    apply (Sb _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))).2
    simp [hJ]
  refine ⟨a,b,HA,HB,fun n hn m hm=>covector_root_pos _ e _ ha hn hm,?_⟩
  intro n hn m hm
  have H:=covector_root_pos _ e _ hb hn hm
  simpa only [LinearMap.neg_apply,neg_pos] using H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))

lemma onPositiveRay_real_span {r p:M} (H:OnPositiveRay r p) :
    e p∈Submodule.span ℝ {e r} := by
  obtain ⟨a,b,ha,hb,H⟩:=H
  have HH:(a:ℝ) • e p=(b:ℝ) • e r:=by
    simpa only [map_nsmul,Nat.cast_smul_eq_nsmul] using congrArg e H
  refine Submodule.mem_span_singleton.mpr ⟨(a:ℝ)⁻¹*(b:ℝ),?_⟩
  rw [mul_smul,←HH,inv_smul_smul₀ (by exact_mod_cast (Nat.ne_of_gt ha))]

include he hS hcomp in
lemma nonpure_preimage_off_line (J:Module.Dual ℝ E)
    (hJ:∀i,J (e (simpleRoot (mutatedRoots Ω C pc) i))=1)
    (r:M) (d:ℕ) (hd:0<d)
    (hr:HasRootDegree (mutatedRoots Ω C pc) d (mutationIncomingLabel Ω (simpleRoot C pc) r))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    e (simpleRoot C pc)∉Submodule.span ℝ {e r} := by
  intro H
  obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp H
  have hp:Ω (simpleRoot C pc) r=0:=by
    have HH:(Ω (simpleRoot C pc) r:ℝ)=0:=by
      rw [←hcomp,←ha,map_smul,LinearMap.smul_apply,hS,smul_zero]
    exact_mod_cast HH
  have hh:mutationIncomingLabel Ω (simpleRoot C pc) r=r:=
    mutationIncomingLabel_nonnegative Ω _ r (by omega)
  apply hn
  apply positive_ray_of_mem_span e he (mutatedRoots Ω C pc) J
    (fun n m hm=>covector_root_eval _ e J hJ hm) _ _ d 1 hd (by omega) hr
    (simpleRoot_degree _ pc)
  rw [hh,mutatedRoot_p,map_neg]
  exact Submodule.neg_mem _ H

include he hS hcomp in
lemma nonpure_preimage_geometry (J:Module.Dual ℝ E)
    (hJ:∀i,J (e (simpleRoot (mutatedRoots Ω C pc) i))=1)
    (r:M) (d:ℕ) (hd:0<d)
    (hr:HasRootDegree (mutatedRoots Ω C pc) d (mutationIncomingLabel Ω (simpleRoot C pc) r))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    e r≠0 ∧ e (simpleRoot C pc)∉Submodule.span ℝ {e r} ∧
      ¬OnPositiveRay r (simpleRoot C pc) := by
  have HP:=nonpure_preimage_off_line Ω C pc e he S hS hcomp J hJ r d hd hr hn
  refine ⟨?_,HP,fun H=>HP (onPositiveRay_real_span e H)⟩
  intro H
  have hr0:r=0:=he (H.trans (map_zero e).symm)
  have hh:mutationIncomingLabel Ω (simpleRoot C pc) r=0:=by simp [hr0,mutationIncomingLabel]
  have HJ:=covector_root_eval _ e J hJ hr
  rw [hh,map_zero,map_zero] at HJ
  have : (d:ℝ)>0:=by exact_mod_cast hd
  linarith
end
end ElementaryPositivity.QuantumTorus

end

end OAI
