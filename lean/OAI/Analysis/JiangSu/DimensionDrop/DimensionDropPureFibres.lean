import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropRelations

namespace OAI

section

noncomputable section
namespace DimensionDropRelations.Witness
open CompletelyPositiveOperations CurrentMain PureStateExcision
open scoped ComplexOrder CStarAlgebra InnerProductSpace ComplexStarModule

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B D : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {p : I} (w : Witness (B := B) p)

 def map (π : B →⋆ₐ[ℂ] D) : Witness (B := D) p where
  φ := comp (π : B →CP D) w.φ
  contractive M := (NonUnitalStarAlgHom.norm_apply_le π _).trans (w.contractive M)
  orderZero M N := by change π (w.φ M)*π (w.φ N)=π (w.φ (M*N))*π (w.φ 1); rw [←map_mul π,←map_mul π,w.orderZero]
  s := π w.s
  small := by change star (π w.s)*π w.s=1-π (w.φ 1); rw [←map_star,←map_mul,w.small,map_sub,map_one]
  support := by change π (w.φ (matrixUnit p p))*π w.s=π w.s; rw [←map_mul,w.support]

lemma map_parameter (π : B →⋆ₐ[ℂ] D) : (w.map π).parameter=π w.parameter := by
  simp only [parameter,rangeMass,column,map_sub,map_sum,map_mul,map_star]
  rfl

 def generators : Set B := Set.range w.φ∪{w.s}
 def generated : StarSubalgebra ℂ B := (StarAlgebra.adjoin ℂ w.generators).topologicalClosure

lemma parameter_commute_generated (b : B) (hb : b∈w.generated) : Commute w.parameter b := by
  have hset : w.generators⊆(StarSubalgebra.centralizer ℂ {w.parameter} : Set B) := by
    intro a ha
    obtain ⟨M,rfl⟩|ha := ha
    · apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      intro g hg
      have he : g=w.parameter := Set.mem_singleton_iff.mp hg
      subst g
      exact ⟨(w.parameter_matrix M).eq,by rw [w.parameter_star]; exact (w.parameter_matrix M).eq⟩
    · have he : a=w.s := Set.mem_singleton_iff.mp ha
      subst a
      apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      intro g hg
      have he : g=w.parameter := Set.mem_singleton_iff.mp hg
      subst g
      exact ⟨w.parameter_s.eq,by rw [w.parameter_star]; exact w.parameter_s.eq⟩
  have hle : w.generated≤StarSubalgebra.centralizer ℂ {w.parameter} :=
    StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le_iff.mpr hset) (by
      change IsClosed (Set.centralizer ({w.parameter}∪star ({w.parameter})))
      exact Set.isClosed_centralizer _)
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hb) _ (Set.mem_singleton _)).1

variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)

 theorem pure_scalar_coordinate (hgen : w.generated=⊤) (f : B →ₚ[ℂ] ℂ) (hf : f 1=1)
    (hpure : ofPositiveState f hf∈(realStateCarrier (A := B)).extremePoints ℝ) :
    ∃ t : ℝ,0≤t ∧ t≤1 ∧ (w.map f.gnsStarAlgHom).parameter=t • (1:f.GNS →L[ℂ] f.GNS) := by
  have hcomm (a : B) : Commute (f.gnsStarAlgHom w.parameter) (f.gnsStarAlgHom a) := by
    have he := w.parameter_commute_generated a (by rw [hgen]; trivial)
    exact he.map f.gnsStarAlgHom
  obtain ⟨t,ht⟩ := pure_gns_selfadjoint_commutant f hf hpure (f.gnsStarAlgHom w.parameter)
    (w.parameter_nonneg.isSelfAdjoint.map _) hcomm
  have hv : f w.parameter=(t:ℂ) := by
    rw [←Pureness.stateGNS_vector_value,ht,smul_apply,one_apply_eq_self,
      inner_smul_right,inner_self_eq_norm_sq_to_K,Pureness.stateGNSVector_norm f hf]
    simp
  have h0 : 0≤(t:ℂ) := hv ▸ f.map_nonneg w.parameter_nonneg
  have h1 : (t:ℂ)≤1 := by simpa only [hv,hf] using OrderHomClass.monotone f w.parameter_le_one
  refine ⟨t,by exact_mod_cast h0,by exact_mod_cast h1,?_⟩
  rw [w.map_parameter,ht,Complex.coe_smul]

end DimensionDropRelations.Witness

end
end

end OAI
