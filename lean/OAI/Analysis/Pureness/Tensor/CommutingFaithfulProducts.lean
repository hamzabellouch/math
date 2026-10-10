import OAI.Analysis.Pureness.Cuntz.MatrixSimplicity

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A B N : Type*}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]

def commutingMultiplierIdeal (φ : A →⋆ₐ[ℂ] N) (b : N)
    (hc : ∀ a, Commute (φ a) b) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a | φ a*b=0}
    (by simp)
    (by
      intro a c ha hc'
      change φ a*b=0 at ha
      change φ c*b=0 at hc'
      change φ (a+c)*b=0
      rw [map_add,add_mul,ha,hc',add_zero])
    (by
      intro a ha
      change φ a*b=0 at ha
      change φ (-a)*b=0
      rw [map_neg,neg_mul,ha,neg_zero])
    (by
      intro a c hc'
      change φ (a*c)*b=0
      rw [map_mul,mul_assoc,hc',mul_zero])
    (by
      intro a c ha
      change φ (a*c)*b=0
      rw [map_mul,mul_assoc,(hc c).eq,← mul_assoc,ha,zero_mul])

lemma commutingMultiplierIdeal_closed (φ : A →⋆ₐ[ℂ] N) (b : N)
    (hc : ∀ a, Commute (φ a) b) :
    IsClosed (commutingMultiplierIdeal φ b hc : Set A) := by
  have hcont : Continuous φ :=
    (φ.toLinearMap.mkContinuous 1 (fun a => by
      simpa using NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom a)).continuous
  simpa only [commutingMultiplierIdeal,TwoSidedIdeal.coe_mk',Pi.mul_apply] using
    (isClosed_eq (hcont.mul continuous_const)
      (continuous_const : Continuous (fun _ : A => (0 : N))))

theorem commuting_embeddings_mul_eq_zero_iff (hsimple : TopologicallySimple A)
    (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
    (hψ : Function.Injective ψ)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    φ a*ψ b=0 ↔ a=0 ∨ b=0 := by
  constructor
  · intro hab
    let I := commutingMultiplierIdeal φ (ψ b) (fun c => hc c b)
    rcases hsimple I (commutingMultiplierIdeal_closed φ (ψ b) (fun c => hc c b)) with hz | ht
    · left
      have ha : a ∈ I := by
        simpa only [I,commutingMultiplierIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq] using hab
      rw [hz] at ha
      simpa using ha
    · right
      have h1 : (1 : A) ∈ I := by rw [ht]; trivial
      have hh : φ 1*ψ b=0 := by
        simpa only [I,commutingMultiplierIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq] using h1
      rw [map_one,one_mul] at hh
      apply hψ
      simpa using hh
  · rintro (rfl | rfl) <;> simp
end CuntzPureness

end

end OAI
