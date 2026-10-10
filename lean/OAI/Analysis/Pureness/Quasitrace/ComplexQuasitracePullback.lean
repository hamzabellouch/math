import OAI.Analysis.Pureness.Quasitrace.QuasitraceFamily

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder IsMulCommutative
variable {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]

def ComplexQuasitrace.comap (T : ComplexQuasitrace E) (φ : D →⋆ₙₐ[ℂ] E) :
    ComplexQuasitrace D where
  toFun x := T (φ x)
  polar x := by simpa only [map_mul, map_star] using T.polar (φ x)
  square_nonneg x := by simpa only [map_mul, map_star] using T.square_nonneg (φ x)
  real_add_I a b := by
    simpa only [map_add, map_smul] using
      T.real_add_I ⟨φ a.1, a.2.map φ⟩ ⟨φ b.1, b.2.map φ⟩
  abelian_linear S _ := by
    let R := S.map φ
    let : IsMulCommutative R := IsMulCommutative.of_setLike_mul_comm (fun x hx y hy => by
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have he : a*b=b*a := congrArg Subtype.val (mul_comm (⟨a,ha⟩ : S) ⟨b,hb⟩)
      change φ a * φ b = φ b * φ a
      rw [← map_mul, ← map_mul, he])
    let L : S →ₗ[ℂ] R :=
      { toFun x := ⟨φ x.1, ⟨x.1, x.2, rfl⟩⟩
        map_add' x y := Subtype.ext (map_add φ x.1 y.1)
        map_smul' c x := Subtype.ext (map_smul φ c x.1) }
    obtain ⟨f, hf⟩ := T.abelian_linear R
    exact ⟨f.comp L, fun x => hf (L x)⟩

@[simp] lemma ComplexQuasitrace.comap_apply (T : ComplexQuasitrace E)
    (φ : D →⋆ₙₐ[ℂ] E) (x : D) : T.comap φ x = T (φ x) := rfl

lemma ComplexQuasitrace.comap_faithful (T : ComplexQuasitrace E)
    (φ : D →⋆ₙₐ[ℂ] E) (hφ : Function.Injective φ)
    (hT : ∀ x, T (star x*x)=0 ↔ x=0) (x : D) :
    T.comap φ (star x*x)=0 ↔ x=0 := by
  change T (φ (star x*x))=0 ↔ x=0
  rw [map_mul, map_star, hT, map_eq_zero_iff φ hφ]
end CuntzPureness

end

end OAI
