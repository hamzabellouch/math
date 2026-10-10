import OAI.Analysis.JiangSu.CStarAlgebras.ContractionLift
import OAI.Analysis.WeakInfiniteness.NuclearTensorMap

namespace OAI

/-! Exact contraction lifting for a surjective nonunital star homomorphism.
Unitization reduces this to the unital contraction lift; the scalar
coordinate of the lifted element is zero. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def unitizedHom (q : A →⋆ₙₐ[ℂ] B) : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ B :=
  Unitization.starLift ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp q)

lemma unitizedHom_coordinates (q : A →⋆ₙₐ[ℂ] B) (x : Unitization ℂ A) :
    (unitizedHom q x).fst = x.fst ∧ (unitizedHom q x).snd = q x.snd := by
  change (algebraMap ℂ (Unitization ℂ B) x.fst +
    (Unitization.inrNonUnitalStarAlgHom ℂ B) (q x.snd)).fst = x.fst ∧
    (algebraMap ℂ (Unitization ℂ B) x.fst +
    (Unitization.inrNonUnitalStarAlgHom ℂ B) (q x.snd)).snd = q x.snd
  simp [Unitization.algebraMap_eq_inl]

lemma unitizedHom_surjective (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) :
    Function.Surjective (unitizedHom q) := by
  intro y
  obtain ⟨a, ha⟩ := hq y.snd
  refine ⟨⟨y.fst, a⟩, Unitization.ext ?_ ?_⟩
  · exact (unitizedHom_coordinates q _).1
  · exact (unitizedHom_coordinates q _).2.trans ha

theorem nonunital_exists_contraction (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (b : B) (hb : ‖b‖ ≤ 1) : ∃ a : A, q a = b ∧ ‖a‖ ≤ 1 := by
  let : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
  obtain ⟨x, hx, hxn⟩ := CStarLift.exists_contraction (unitizedHom q)
    (unitizedHom_surjective q hq) (b := (b : Unitization ℂ B))
    (by simpa only [Unitization.norm_inr] using hb)
  have hf : x.fst = 0 := (unitizedHom_coordinates q x).1.symm.trans
    (congrArg (fun y : Unitization ℂ B => y.fst) hx)
  have he : (x.snd : Unitization ℂ A) = x := Unitization.ext hf.symm rfl
  refine ⟨x.snd, ?_, ?_⟩
  · exact (unitizedHom_coordinates q x).2.symm.trans
      (congrArg (fun y : Unitization ℂ B => y.snd) hx)
  · rw [← Unitization.norm_inr (𝕜 := ℂ), he]
    exact hxn

end WeakPureInfiniteness

end

end OAI
