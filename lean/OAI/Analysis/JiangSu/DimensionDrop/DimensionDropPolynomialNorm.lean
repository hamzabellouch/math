import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropFibreGenerators
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropEndpointGenerators
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropPureFibres
import OAI.Analysis.JiangSu.Excision.PureStateNorming
import OAI.Analysis.JiangSu.CStarAlgebras.StarTerms

namespace OAI

section

noncomputable section
namespace DimensionDropModel
open ConcreteMatrixUnits StarTerms
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev Gen (I : Type*) := (I×I)⊕Unit
 def values (p : I) (t : ℝ) : Gen I→Mat I
  | .inl ij => phi t ij.1 ij.2
  | .inr _ => s p t
 def lowerValues (p : I) : Gen I→CStarMatrix (Option I) (Option I) ℂ
  | .inl ij => unit (some ij.1) (some ij.2)
  | .inr _ => unit (some p) none
 def upperValues : Gen I→CStarMatrix I I ℂ
  | .inl ij => unit ij.1 ij.2
  | .inr _ => 0
lemma amplify_lower (p : I) : (amplify (J := I))∘lowerValues p=values p 0 := by
  funext g; cases g with
  | inl ij => exact (phi_zero ij.1 ij.2).symm
  | inr u => exact (s_zero p).symm
lemma embed_upper (p : I) : upperEmbed∘upperValues=values p 1 := by
  funext g; cases g with
  | inl ij => exact (phi_one ij.1 ij.2).symm
  | inr u => simpa only [Function.comp_apply,upperValues,values,s_one] using map_zero (upperEmbed (I := I))
abbrev Interval := Set.Icc (0:ℝ) 1
lemma continuous_values (p : I) (g : Gen I) : Continuous (fun t : Interval => values p t g) := by
  cases g <;> simp only [values,phi,s] <;> fun_prop
lemma Term.continuous_eval (e : StarTerms.Term (Gen I)) (p : I) :
    Continuous (fun t : Interval => e.eval (values p t)) := by
  induction e with
  | scalar z => exact continuous_const
  | gen g => exact continuous_values p g
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
  | adjoint e he => exact he.star
 def realization (p : I) (e : StarTerms.Term (Gen I)) : C(Interval,Mat I) :=
  ⟨fun t => e.eval (values p t),Term.continuous_eval e p⟩
end DimensionDropModel

namespace DimensionDropRelations.Witness
open DimensionDropModel ConcreteMatrixUnits CurrentMain StarTerms PureStateExcision CompletelyPositiveOperations
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
 def interpret : Gen I→B
  | .inl ij => w.φ (matrixUnit ij.1 ij.2)
  | .inr _ => w.s
lemma lower_interpret (hc : w.parameter=0) : (w.lowerEndpointHom hc)∘lowerValues p=w.interpret := by
  funext g; cases g with
  | inl ij => exact w.lowerEndpointHom_phi hc ij.1 ij.2
  | inr u => exact w.lowerEndpointHom_s hc
lemma upper_interpret (hc : w.parameter=1) : (w.upperEndpointHom hc)∘upperValues=w.interpret := by
  funext g; cases g with
  | inl ij => rfl
  | inr u => simpa only [Function.comp_apply,upperValues,interpret,map_zero] using
      (w.s_eq_zero_of_parameter_one hc).symm
lemma interior_interpret {t : ℝ} (hc : w.parameter=t • (1:B)) (ht0 : 0<t) (ht1 : t<1) :
    (w.interiorHom hc ht0 ht1)∘values p t=w.interpret := by
  funext g; cases g with
  | inl ij => exact w.interiorHom_phi hc ht0 ht1 ij.1 ij.2
  | inr u => exact w.interiorHom_s hc ht0 ht1

 theorem scalar_polynomial_norm {t : ℝ} (hc : w.parameter=t • (1:B))
    (ht0 : 0≤t) (ht1 : t≤1) (e : Term (Gen I)) :
    ‖e.eval w.interpret‖≤‖e.eval (values p t)‖ := by
  let : Nonempty I := ⟨p⟩
  rcases eq_or_lt_of_le ht0 with ht0|ht0
  · subst t
    have hc' : w.parameter=0 := by simpa using hc
    rw [←w.lower_interpret hc',←e.map_eval]
    calc
      ‖w.lowerEndpointHom hc' (e.eval (lowerValues p))‖≤‖e.eval (lowerValues p)‖ :=
        NonUnitalStarAlgHom.norm_apply_le _ _
      _=‖e.eval (values p 0)‖ := by rw [←amplify_norm (J := I),e.map_eval,amplify_lower]
  · rcases lt_or_eq_of_le ht1 with ht1|ht1
    · rw [←w.interior_interpret hc ht0 ht1,←e.map_eval]
      exact NonUnitalStarAlgHom.norm_apply_le _ _
    · subst t
      have hc' : w.parameter=1 := by simpa using hc
      rw [←w.upper_interpret hc',←e.map_eval]
      calc
        ‖w.upperEndpointHom hc' (e.eval upperValues)‖≤‖e.eval (upperValues (I := I))‖ :=
          NonUnitalStarAlgHom.norm_apply_le _ _
        _=‖e.eval (values p 1)‖ := by rw [←upperEmbed_norm,e.map_eval,embed_upper p]

variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
 theorem polynomial_norm_of_generated (hgen : w.generated=⊤) (e : Term (Gen I)) :
    ‖e.eval w.interpret‖≤‖realization p e‖ := by
  by_cases hB : Subsingleton B
  · let := hB
    rw [Subsingleton.elim (e.eval w.interpret) 0,norm_zero]
    exact norm_nonneg (realization p e)
  let : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
  apply norm_le_of_pure_gns (e.eval w.interpret) (norm_nonneg (realization p e))
  intro f hf hpure
  obtain ⟨t,ht0,ht1,ht⟩ := w.pure_scalar_coordinate hgen f hf hpure
  have hi : f.gnsStarAlgHom∘w.interpret=(w.map f.gnsStarAlgHom).interpret := by
    funext g; cases g <;> rfl
  change ‖f.gnsStarAlgHom (e.eval w.interpret)‖≤‖realization p e‖
  rw [e.map_eval,hi]
  exact ((w.map f.gnsStarAlgHom).scalar_polynomial_norm ht ht0 ht1 e).trans
    (ContinuousMap.norm_coe_le_norm (realization p e) ⟨t,ht0,ht1⟩)

end DimensionDropRelations.Witness

end
end

end OAI
