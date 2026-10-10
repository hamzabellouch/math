import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.OperatorAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.Kaplansky

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance kaplanskySelfAdjointRealInnerProductSpace : InnerProductSpace ℝ H :=
  InnerProductSpace.rclikeToReal ℂ H

def selfAdjointOrbit (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : Submodule ℝ H where
  carrier := {y | ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧ a x=y}
  zero_mem' := ⟨0,S.zero_mem,IsSelfAdjoint.zero _,rfl⟩
  add_mem' := by
    rintro y z ⟨a,ha,hsa,rfl⟩ ⟨b,hb,hsb,rfl⟩
    exact ⟨a+b,S.add_mem ha hb,hsa.add hsb,rfl⟩
  smul_mem' := by
    rintro c y ⟨a,ha,hsa,rfl⟩
    refine ⟨c • a,?_,(IsSelfAdjoint.all c).smul hsa,rfl⟩
    simpa only [Complex.coe_smul] using S.smul_mem ha (c:ℂ)

def symmetrize (a : H →L[ℂ] H) : H →L[ℂ] H := (1/2:ℝ) • (a+star a)

lemma symmetrize_selfAdjoint (a : H →L[ℂ] H) : IsSelfAdjoint (symmetrize a) := by
  simp [IsSelfAdjoint,symmetrize,star_smul,add_comm]

lemma symmetrize_eq {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) : symmetrize a=a := by
  rw [symmetrize,ha.star_eq,←two_smul ℝ a,smul_smul]
  norm_num

lemma symmetrize_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) {a : H →L[ℂ] H} (ha : a∈S) :
    symmetrize a∈S := by
  have h := S.smul_mem (S.add_mem ha (S.star_mem' ha)) ((1/2:ℝ):ℂ)
  simpa only [symmetrize, Complex.coe_smul] using h

def pair (x y : H) : SumSpace (H:=H) (Fin 2) := WithLp.toLp 2 ![x,y]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp] lemma pair_zero (x y : H) : pair x y 0=x := rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp] lemma pair_one (x y : H) : pair x y 1=y := rfl

lemma crossed_pairing (a : H →L[ℂ] H) (x z : H) :
    inner ℝ (pair z x) (diagonal (H:=H) (Fin 2) a (pair x z))=
      2*inner ℝ z (symmetrize a x) := by
  change (inner ℂ (pair z x) (diagonal (H:=H) (Fin 2) a (pair x z))).re =
    2 * (inner ℂ z (symmetrize a x)).re
  simp only [PiLp.inner_apply,Fin.sum_univ_two,diagonal_apply,pair_zero,pair_one,
    symmetrize,smul_apply,add_apply]
  rw [←Complex.coe_smul,inner_smul_right,inner_add_right]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.add_re]
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  have hi := inner_re_symm (𝕜:=ℂ) (a z) x
  dsimp only [RCLike.re_eq_complex_re] at hi
  simpa only [smul_eq_mul] using (by linarith :
    (inner ℂ z (a x)).re + (inner ℂ x (a z)).re =
    2 * ((1/2:ℝ) * ((inner ℂ z (a x)).re + (inner ℂ (a z) x).re)))

lemma selfAdjoint_mem_orbit_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (x : H) :
    T x∈(selfAdjointOrbit S x).topologicalClosure := by
  rw [←Submodule.orthogonal_orthogonal_eq_closure]
  intro z hz
  let X := pair x z
  let Z := pair z x
  have horbit : ∀ b : H →L[ℂ] H, b∈S →
      inner ℝ Z (diagonal (H:=H) (Fin 2) b X)=0 := by
    intro b hb
    rw [crossed_pairing]
    have he := hz (symmetrize b x)
      ⟨symmetrize b,symmetrize_mem S hb,symmetrize_selfAdjoint b,rfl⟩
    rw [real_inner_comm] at he
    rw [he,mul_zero]
  have hcl := bicommutant_mem_cyclicSubspace (S.map (diagonal (H:=H) (Fin 2)))
    (diagonal_bicommutant (Fin 2) S hT) X
  change diagonal (H:=H) (Fin 2) T X∈closure
    (orbitSubmodule (S.map (diagonal (H:=H) (Fin 2))) X : Set (SumSpace (H:=H) (Fin 2))) at hcl
  have hzT : inner ℝ Z (diagonal (H:=H) (Fin 2) T X)=0 := by
    apply (closure_minimal ?_ (isClosed_eq (continuous_const.inner continuous_id) continuous_const)) hcl
    rintro y ⟨a,⟨b,hb,rfl⟩,rfl⟩
    exact horbit b hb
  rw [crossed_pairing] at hzT
  have hs : symmetrize T=T := symmetrize_eq hsT
  rw [hs] at hzT
  linarith

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem selfAdjoint_finite_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (x : SumSpace (H:=H) ι) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧
      ‖diagonal (H:=H) ι a x-diagonal (H:=H) ι T x‖<ε := by
  have h := selfAdjoint_mem_orbit_closure (S.map (diagonal (H:=H) ι))
    (diagonal_bicommutant ι S hT) (hsT.map (diagonal (H:=H) ι)) x
  change diagonal (H:=H) ι T x∈closure
    (selfAdjointOrbit (S.map (diagonal (H:=H) ι)) x : Set (SumSpace (H:=H) ι)) at h
  obtain ⟨y,⟨a,⟨b,hb,hba⟩,hsa,hay⟩,hy⟩ := Metric.mem_closure_iff.mp h ε hε
  
  refine ⟨symmetrize b,symmetrize_mem S hb,symmetrize_selfAdjoint b,?_⟩
  change diagonal (H:=H) ι b=a at hba
  have he : diagonal (H:=H) ι (symmetrize b)=a := by
    have : diagonal (H:=H) ι (symmetrize b)=symmetrize (diagonal (H:=H) ι b) := by
      have hs : diagonal (H:=H) ι (star b)=star (diagonal (H:=H) ι b) := map_star _ _
      rw [symmetrize,symmetrize,←hs]
      ext v i
      simp only [diagonal_apply,smul_apply,add_apply,PiLp.smul_apply,PiLp.add_apply]
    rw [this,hba,symmetrize_eq hsa]
  rw [he,hay]
  rwa [dist_eq_norm,norm_sub_rev] at hy

end Kadison.Kaplansky

end

end
end

end OAI
