import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.RationalStarExtension

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

local instance : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B

local instance : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp

local instance : StarModule ℚ B where
  star_smul r b := by
    change star ((r:ℂ) • b)=((star r:ℚ):ℂ) • star b
    simp

variable (S : StarSubalgebra ℚ A)
  (hd : DenseRange (fun a : S => (a:A)))
  (φ : S →⋆ₐ[ℚ] B) (hb : ∀ a : S,‖φ a‖≤‖(a:A)‖)

def raw : S →L[ℚ] B := φ.toAlgHom.toLinearMap.mkContinuous 1 (by
  intro a
  simpa using hb a)

def lift : A →L[ℚ] B := (raw S φ hb).extend S.toSubalgebra.toSubmodule.subtypeL

include hd in
lemma lift_subtype (a : S) : lift S φ hb (a:A)=φ a :=
  ContinuousLinearMap.extend_eq _ hd isUniformEmbedding_subtype_val.isUniformInducing a

include hd in
lemma lift_norm (a : A) : ‖lift S φ hb a‖≤‖a‖ := by
  refine hd.induction_on (p:=fun x => ‖lift S φ hb x‖≤‖x‖) a
    (isClosed_le (lift S φ hb).continuous.norm continuous_norm) ?_
  intro b
  rw [lift_subtype S hd φ hb]
  exact hb b

def realLift : A →L[ℝ] B :=
  (lift S φ hb).toLinearMap.toAddMonoidHom.toRealLinearMap (lift S φ hb).continuous

include hd hb in
theorem exists_complex_extension (hI : Complex.I • (1:A)∈S)
    (hφI : φ ⟨Complex.I • (1:A),hI⟩=Complex.I • (1:B)) :
    ∃ Φ : A →⋆ₐ[ℂ] B,(∀ a : S,Φ (a:A)=φ a) ∧ (∀ a : A,‖Φ a‖≤‖a‖) := by
  let L := realLift S φ hb
  have hsub (a : S) : L (a:A)=φ a := lift_subtype S hd φ hb a
  have hLI (a : A) : L (Complex.I • a)=Complex.I • L a := by
    refine hd.induction_on (p:=fun x => L (Complex.I • x)=Complex.I • L x) a (isClosed_eq
      (L.continuous.comp (continuous_const.smul continuous_id))
      (continuous_const.smul L.continuous)) ?_
    intro a
    let i : S := ⟨Complex.I • (1:A),hI⟩
    have he : Complex.I • (a:A)=((i*a:S):A) := by simp [i]
    rw [he,hsub,map_mul,hsub]
    change φ ⟨Complex.I • (1:A),hI⟩*φ a=Complex.I • φ a
    rw [hφI]
    simp
  have hsmul (z : ℂ) (a : A) : L (z • a)=z • L a := by
    rw [←Complex.re_add_im z,add_smul,map_add,add_smul,mul_smul,mul_smul]
    have hr (r : ℝ) (x : A) : L ((r:ℂ) • x)=(r:ℂ) • L x := by
      change L (r • x)=r • L x
      exact map_smul L r x
    rw [hr,hr,hLI]
  have hmul (a b : A) : L (a*b)=L a*L b := by
    refine hd.induction_on (p:=fun x => L (x*b)=L x*L b) a
      (isClosed_eq (L.continuous.comp (continuous_id.mul continuous_const))
        (L.continuous.mul continuous_const)) ?_
    intro a
    refine hd.induction_on (p:=fun x => L ((a:A)*x)=L (a:A)*L x) b
      (isClosed_eq (L.continuous.comp (continuous_const.mul continuous_id))
        (continuous_const.mul L.continuous)) ?_
    intro b
    change L ((a*b:S):A)=L (a:A)*L (b:A)
    rw [hsub,hsub,hsub,map_mul]
  have hstar (a : A) : L (star a)=star (L a) := by
    refine hd.induction_on (p:=fun x => L (star x)=star (L x)) a
      (isClosed_eq (L.continuous.comp continuous_star) L.continuous.star) ?_
    intro a
    change L ((star a:S):A)=star (L (a:A))
    rw [hsub,hsub,map_star]
  have hone : L (1:A)=1 := by
    change L ((1:S):A)=1
    rw [hsub,map_one]
  let Φ : A →⋆ₐ[ℂ] B :=
    { toAlgHom :=
      { toFun := L
        map_one' := hone
        map_mul' := hmul
        map_zero' := map_zero L
        map_add' := map_add L
        commutes' := by
          intro z
          change L (algebraMap ℂ A z)=algebraMap ℂ B z
          rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,hsmul,hone] }
      map_star' := hstar }
  exact ⟨Φ,hsub,lift_norm S hd φ hb⟩

end Kadison.RationalStarExtension

end

end
end

end OAI
