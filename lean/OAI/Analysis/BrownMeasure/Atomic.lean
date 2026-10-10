import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
namespace PolarStructure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
abbrev Op := H →L[ℂ] H

def generated (S : Set (Op (H:=H))) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)
  centralizer_centralizer' := by
    have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
        Set.centralizer (Set.centralizer (S ∪ star S)) :=
      StarSubalgebra.coe_centralizer_centralizer ℂ S
    rw [he]
    simp

def MinimalProjection (M : VonNeumannAlgebra H) (p : Op (H:=H)) : Prop :=
  p ∈ M ∧ IsStarProjection p ∧ p≠0 ∧
    ∀ q∈M, IsStarProjection q → q*p=q → q=0 ∨ q=p

def Atomic (M : VonNeumannAlgebra H) : Prop :=
  ∀ p∈M, IsStarProjection p → p≠0 →
    ∃ q, MinimalProjection M q ∧ q*p=q

def jointSpace (A : ι → Op (H:=H)) (r : ι → ℝ) : Submodule ℂ H where
  carrier := {x | ∀ i,A i x=(r i:ℂ) • x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; simp [map_add,hx i,hy i,smul_add]
  smul_mem' := by
    intro c x hx i
    change A i (c • x)=(r i:ℂ) • (c • x)
    rw [map_smul,hx i,smul_smul,smul_smul,mul_comm]

omit [CompleteSpace H] in
@[simp] lemma mem_jointSpace (A : ι → Op (H:=H)) (r : ι → ℝ) (x : H) :
    x∈jointSpace A r ↔ ∀ i,A i x=(r i:ℂ) • x := Iff.rfl
omit [CompleteSpace H] in
lemma jointSpace_closed (A : ι → Op (H:=H)) (r : ι → ℝ) :
    IsClosed (jointSpace A r : Set H) := by
  change IsClosed {x | ∀ i,A i x=(r i:ℂ) • x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i=>isClosed_eq (A i).continuous (continuous_const.smul continuous_id))
instance jointSpace_complete (A : ι → Op (H:=H)) (r : ι → ℝ) : CompleteSpace (jointSpace A r) :=
  (jointSpace_closed A r).completeSpace_coe

def JointPurePoint (A : ι → Op (H:=H)) : Prop :=
  (Submodule.span ℂ {x | ∃ r : ι → ℝ,x∈jointSpace A r}).topologicalClosure=⊤

lemma projection_commutes_of_invariant (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : Op (H:=H)) (hT : ∀ x∈K,T x∈K) (hTstar : ∀ x∈K,star T x∈K) :
    T*K.starProjection=K.starProjection*T := by
  ext x
  symm
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (K.starProjection_apply_mem x)
  · intro w hw
    change inner ℂ (T x-T (K.starProjection x)) w=0
    rw [← map_sub,← ContinuousLinearMap.adjoint_inner_right]
    exact K.starProjection_inner_eq_zero x _ (hTstar w hw)

lemma commutant_preserves (A : ι → Op (H:=H)) (r : ι → ℝ) (T : Op (H:=H))
    (hT : T∈StarSubalgebra.centralizer ℂ (Set.range A)) :
    ∀ x∈jointSpace A r,T x∈jointSpace A r := by
  intro x hx i
  have ht := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT (A i) ⟨i,rfl⟩).1
  have he := congrArg (fun S : Op (H:=H)=>S x) ht
  simpa only [mul_apply_eq_comp,hx i,map_smul] using he

lemma jointProjection_mem (A : ι → Op (H:=H)) (r : ι → ℝ) :
    (jointSpace A r).starProjection∈generated (Set.range A) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro T hT
  have hs := star_mem hT
  exact ⟨projection_commutes_of_invariant _ T (commutant_preserves A r T hT)
    (commutant_preserves A r (star T) hs),
    projection_commutes_of_invariant _ (star T) (commutant_preserves A r (star T) hs)
      (by simpa only [star_star] using commutant_preserves A r T hT)⟩

lemma rankOne_commutes (A : ι → Op (H:=H)) (hA : ∀ i,IsSelfAdjoint (A i))
    (r : ι → ℝ) {v w : H} (hv : v∈jointSpace A r) (hw : w∈jointSpace A r) :
    rankOne ℂ v w∈StarSubalgebra.centralizer ℂ (Set.range A) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨i,rfl⟩
  have h : A i * rankOne ℂ v w=rankOne ℂ v w*A i := by
    ext x
    simp only [mul_apply_eq_comp,rankOne_apply,map_smul,hv i]
    have he : inner ℂ w (A i x)=(r i:ℂ)*inner ℂ w x := by
      rw [← ContinuousLinearMap.adjoint_inner_left]
      change inner ℂ ((star (A i)) w) x=_
      rw [hA i,hw i,inner_smul_left]
      simp
    rw [he,smul_smul,mul_comm]
  exact ⟨h,by simpa only [(hA i).star_eq] using h⟩

lemma generated_scalar_on_joint (A : ι → Op (H:=H)) (hA : ∀ i,IsSelfAdjoint (A i))
    (r : ι → ℝ) {p : Op (H:=H)} (hp : p∈generated (Set.range A))
    {u : H} (hu : u∈jointSpace A r) (hu0 : u≠0) :
    ∃ c : ℂ, ∀ v∈jointSpace A r,p v=c • v := by
  let a : ℂ := inner ℂ u u
  have ha : a≠0 := by simpa [a,inner_self_eq_zero] using hu0
  refine ⟨a⁻¹*inner ℂ u (p u),?_⟩
  intro v hv
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hp (rankOne ℂ v u)
    (rankOne_commutes A hA r hv hu)).1
  have he := congrArg (fun S : Op (H:=H)=>S u) hc
  change inner ℂ u (p u) • v=p (inner ℂ u u • v) at he
  rw [map_smul] at he
  have hh := congrArg (fun x : H=>a⁻¹ • x) he
  simp only [smul_smul] at hh
  change (a⁻¹*inner ℂ u (p u)) • v=(a⁻¹*a) • p v at hh
  simpa only [inv_mul_cancel₀ ha,one_smul] using hh.symm

lemma projection_scalar_zero_or_one {p : Op (H:=H)} (hp : IsStarProjection p)
    {u : H} (hu : u≠0) {c : ℂ} (hc : p u=c • u) : c=0 ∨ c=1 := by
  have he := congrArg (fun S : Op (H:=H)=>S u) hp.isIdempotentElem.eq
  change p (p u)=p u at he
  rw [hc,map_smul,hc,smul_smul] at he
  have h : (c*c-c) • u=0 := by rw [sub_smul,he,sub_self]
  have hz : c*(c-1)=0 := by
    have hh := (smul_eq_zero.mp h).resolve_right hu
    linear_combination hh
  exact (mul_eq_zero.mp hz).imp id (fun h=>sub_eq_zero.mp h)

lemma jointProjection_minimal (A : ι → Op (H:=H)) (hA : ∀ i,IsSelfAdjoint (A i))
    (r : ι → ℝ) {u : H} (hu : u∈jointSpace A r) (hu0 : u≠0) :
    MinimalProjection (generated (Set.range A)) (jointSpace A r).starProjection := by
  refine ⟨jointProjection_mem A r,isStarProjection_starProjection,?_,?_⟩
  · intro h0
    have he := congrArg (fun S : Op (H:=H)=>S u) h0
    rw [(jointSpace A r).starProjection_eq_self_iff.mpr hu] at he
    exact hu0 he
  · intro q hq hqpr hqp
    obtain ⟨c,hc⟩ := generated_scalar_on_joint A hA r hq hu hu0
    rcases projection_scalar_zero_or_one hqpr hu0 (hc u hu) with hc0|hc1
    · left
      ext x
      have he := congrArg (fun S : Op (H:=H)=>S x) hqp
      change q ((jointSpace A r).starProjection x)=q x at he
      rw [hc _ ((jointSpace A r).starProjection_apply_mem x),hc0,zero_smul] at he
      exact he.symm
    · right
      ext x
      have he := congrArg (fun S : Op (H:=H)=>S x) hqp
      change q ((jointSpace A r).starProjection x)=q x at he
      rw [hc _ ((jointSpace A r).starProjection_apply_mem x),hc1,one_smul] at he
      exact he.symm

omit [CompleteSpace H] in
lemma exists_joint_not_killed (A : ι → Op (H:=H)) (hA : JointPurePoint A)
    {p : Op (H:=H)} (hp : p≠0) : ∃ (r : ι → ℝ) (u : H),u∈jointSpace A r ∧ p u≠0 := by
  by_contra hn
  have hh : ∀ r u,u∈jointSpace A r → p u=0 := by simpa using hn
  have hle : Submodule.span ℂ {x | ∃ r : ι → ℝ,x∈jointSpace A r}≤p.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨r,hr⟩
    exact hh r x hr
  have ht := Submodule.topologicalClosure_minimal _ hle p.isClosed_ker
  rw [hA] at ht
  apply hp
  ext x
  exact ht (Submodule.mem_top)

theorem atomic_of_jointPurePoint (A : ι → Op (H:=H)) (hA : ∀ i,IsSelfAdjoint (A i))
    (hpoint : JointPurePoint A) : Atomic (generated (Set.range A)) := by
  intro p hp hppr hp0
  obtain ⟨r,u,hu,hpu⟩ := exists_joint_not_killed A hpoint hp0
  have hu0 : u≠0 := by intro hz; exact hpu (hz ▸ map_zero p)
  obtain ⟨c,hc⟩ := generated_scalar_on_joint A hA r hp hu hu0
  have hc1 : c=1 := (projection_scalar_zero_or_one hppr hu0 (hc u hu)).resolve_left
    (fun hz=>hpu (by rw [hc u hu,hz,zero_smul]))
  refine ⟨(jointSpace A r).starProjection,jointProjection_minimal A hA r hu hu0,?_⟩
  have he : p*(jointSpace A r).starProjection=(jointSpace A r).starProjection := by
    ext x
    change p ((jointSpace A r).starProjection x)=_
    rw [hc _ ((jointSpace A r).starProjection_apply_mem x),hc1,one_smul]
  have hh := congrArg star he
  simpa only [star_mul,hppr.isSelfAdjoint.star_eq,(isSelfAdjoint_starProjection (jointSpace A r)).star_eq] using hh
end PolarStructure
end

end OAI
