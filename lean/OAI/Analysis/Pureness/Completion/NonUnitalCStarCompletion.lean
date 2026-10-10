import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Module.Completion

namespace OAI
noncomputable section
namespace CuntzPureness
open UniformSpace Function Topology
open UniformSpace.Completion
variable (E : Type*) [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
  [NormedSpace ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E]

instance nonUnitalCompletionMul : Mul (Completion E) :=
  ⟨curry <| (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
    ((↑) ∘ uncurry (· * · : E → E → E))⟩

omit [StarRing E] [CStarRing E] [NormedSpace ℂ E] [IsScalarTower ℂ E E]
  [SMulCommClass ℂ E E] [StarModule ℂ E] in
lemma completion_coe_mul (a b : E) :
    ((a * b : E) : Completion E) = (a : Completion E) * b :=
  ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    ((continuous_coe _).comp continuous_mul) (a, b)).symm

instance nonUnitalCompletionContinuousMul : ContinuousMul (Completion E) where
  continuous_mul := by
    let m := (AddMonoidHom.mul : E →+ E →+ E).compr₂ toCompl
    have hm : Continuous fun p : E × E => m p.1 p.2 :=
      (continuous_coe _).comp continuous_mul
    have di : IsDenseInducing (toCompl : E → Completion E) := isDenseInducing_coe
    exact (di.extend_Z_bilin di hm :)

instance nonUnitalCompletionNonUnitalRing : NonUnitalRing (Completion E) where
  __ : AddCommGroup (Completion E) := inferInstance
  zero_mul a := Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
    fun a => by rw [← coe_zero, ← completion_coe_mul, zero_mul]
  mul_zero a := Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
    fun a => by rw [← coe_zero, ← completion_coe_mul, mul_zero]
  mul_assoc a b c := Completion.induction_on₃ a b c (isClosed_eq (by fun_prop) (by fun_prop))
    fun a b c => by simp only [← completion_coe_mul, mul_assoc]
  left_distrib a b c := Completion.induction_on₃ a b c (isClosed_eq (by fun_prop) (by fun_prop))
    fun a b c => by simp only [← coe_add, ← completion_coe_mul, mul_add]
  right_distrib a b c := Completion.induction_on₃ a b c (isClosed_eq (by fun_prop) (by fun_prop))
    fun a b c => by simp only [← coe_add, ← completion_coe_mul, add_mul]

instance nonUnitalCompletionNonUnitalNormedRing : NonUnitalNormedRing (Completion E) where
  __ : NormedAddCommGroup (Completion E) := inferInstance
  __ : NonUnitalRing (Completion E) := inferInstance
  norm_mul_le a b := Completion.induction_on₂ a b (isClosed_le (by fun_prop) (by fun_prop))
    fun a b => by simpa only [← completion_coe_mul, norm_coe] using norm_mul_le a b

instance nonUnitalCompletionStar : Star (Completion E) := ⟨Completion.map (star : E → E)⟩

omit [NormedSpace ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E] in
lemma completion_coe_star (a : E) :
    ((star a : E) : Completion E) = star (a : Completion E) :=
  (Completion.map_coe star_isometry.uniformContinuous a).symm

instance nonUnitalCompletionContinuousStar : ContinuousStar (Completion E) :=
  ⟨Completion.continuous_map⟩

instance nonUnitalCompletionStarRing : StarRing (Completion E) where
  star_involutive a := Completion.induction_on a (isClosed_eq (by fun_prop) continuous_id)
    fun a => by simp only [← completion_coe_star, star_star]
  star_mul a b := Completion.induction_on₂ a b (isClosed_eq (by fun_prop) (by fun_prop))
    fun a b => by simp only [← completion_coe_star, ← completion_coe_mul, star_mul]
  star_add a b := Completion.induction_on₂ a b (isClosed_eq (by fun_prop) (by fun_prop))
    fun a b => by simp only [← completion_coe_star, ← coe_add, star_add]

instance nonUnitalCompletionCStarRing : CStarRing (Completion E) where
  norm_mul_self_le a := Completion.induction_on a (isClosed_le (by fun_prop) (by fun_prop))
    fun a => by simpa only [← completion_coe_star, ← completion_coe_mul, norm_coe]
      using CStarRing.norm_mul_self_le a

instance nonUnitalCompletionStarModule : StarModule ℂ (Completion E) where
  star_smul z a := Completion.induction_on a
    (isClosed_eq (continuous_star.comp (continuous_const_smul z))
      ((continuous_const_smul (star z)).comp continuous_star))
    fun a => by simp only [← coe_smul, ← completion_coe_star, star_smul]

instance nonUnitalCompletionScalarTower : IsScalarTower ℂ (Completion E) (Completion E) where
  smul_assoc z a b := Completion.induction_on₂ a b
    (isClosed_eq ((continuous_fst.const_smul z).mul continuous_snd)
      ((continuous_fst.mul continuous_snd).const_smul z))
    fun a b => by
      change (z • (a : Completion E)) * (b : Completion E) = z • ((a : Completion E) * b)
      simp only [← coe_smul, ← completion_coe_mul, smul_mul_assoc]

instance nonUnitalCompletionSMulComm : SMulCommClass ℂ (Completion E) (Completion E) where
  smul_comm z a b := Completion.induction_on₂ a b
    (isClosed_eq ((continuous_fst.mul continuous_snd).const_smul z)
      (continuous_fst.mul (continuous_snd.const_smul z)))
    fun a b => by
      change z • ((a : Completion E) * b) = (a : Completion E) * (z • (b : Completion E))
      simp only [← coe_smul, ← completion_coe_mul, mul_smul_comm]

instance nonUnitalCompletionCStarAlgebra : NonUnitalCStarAlgebra (Completion E) where
end CuntzPureness

end

end OAI
