import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI

section

noncomputable section
namespace NonunitalIntertwining
open scoped CStarAlgebra

variable {B E : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra E]
variable (j : B →⋆ₙₐ[ℂ] E) (hj : Function.Injective j)
variable (hleft : ∀ (e : E) (b : B),e*j b∈Set.range j)
variable (hright : ∀ (b : B) (e : E),j b*e∈Set.range j)

include hleft hright in
lemma ambient_conjugate_mem (u : unitary E) (b : B) :
    (u:E)*j b*star (u:E)∈Set.range j := by
  obtain ⟨c,hc⟩ := hleft (u:E) b
  rw [←hc]
  exact hright c (star (u:E))

def ambientConj (u : unitary E) (b : B) : B :=
  (ambient_conjugate_mem j hleft hright u b).choose

lemma ambientConj_spec (u : unitary E) (b : B) :
    j (ambientConj j hleft hright u b)=(u:E)*j b*star (u:E) :=
  (ambient_conjugate_mem j hleft hright u b).choose_spec

lemma ambientConj_aut_spec (u : unitary E) (b : B) :
    j (ambientConj j hleft hright u b)=Unitary.conjStarAlgAut ℂ E u (j b) :=
  ambientConj_spec j hleft hright u b

def ambientConjHom (u : unitary E) : B →⋆ₙₐ[ℂ] B where
  toFun := ambientConj j hleft hright u
  map_zero' := by apply hj; simp only [ambientConj_aut_spec,map_zero]
  map_add' a b := by apply hj; simp only [ambientConj_aut_spec,map_add]
  map_mul' a b := by apply hj; simp only [ambientConj_aut_spec,map_mul]
  map_star' a := by apply hj; simp only [ambientConj_aut_spec,map_star]
  map_smul' c a := by apply hj; simp only [ambientConj_aut_spec,map_smul,MonoidHom.id_apply]

include hj in
lemma ambientConj_inv (u : unitary E) (b : B) :
    ambientConj j hleft hright u⁻¹ (ambientConj j hleft hright u b)=b := by
  apply hj
  rw [ambientConj_spec,ambientConj_spec]
  change star (u:E)*((u:E)*j b*star (u:E))*star (star (u:E))=j b
  rw [star_star]
  calc
    _=(star (u:E)*(u:E))*j b*(star (u:E)*(u:E)) := by simp only [mul_assoc]
    _=j b := by rw [u.2.1,one_mul,mul_one]

def ambientConjAut (u : unitary E) : B ≃⋆ₐ[ℂ] B :=
  StarAlgEquiv.ofBijective (ambientConjHom j hj hleft hright u)
    ⟨Function.LeftInverse.injective (ambientConj_inv j hj hleft hright u),
      fun b => ⟨ambientConj j hleft hright u⁻¹ b,by
        simpa only [ambientConjHom,NonUnitalStarAlgHom.coe_mk,inv_inv] using ambientConj_inv j hj hleft hright u⁻¹ b⟩⟩

@[simp] lemma ambientConjAut_apply (u : unitary E) (b : B) :
    ambientConjAut j hj hleft hright u b=ambientConj j hleft hright u b := rfl

end NonunitalIntertwining

end
end

end OAI
