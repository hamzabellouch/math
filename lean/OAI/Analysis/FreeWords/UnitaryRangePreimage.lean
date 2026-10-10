import Mathlib

namespace OAI

noncomputable section

namespace KKVariableUltra

noncomputable section

variable {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ A] [StarModule ℂ B]

omit [StarModule ℂ A] in
theorem unitary_range_preimage (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ)
    (u : unitary B) (hu : u.val∈φ.range) :
    ∃ v : unitary A, φ v.val=u.val := by
  obtain ⟨a,ha⟩ := hu
  change φ a=u.val at ha
  have hsa : star a*a=1 := by
    apply hi
    simp only [map_mul,map_star,map_one]
    rw [ha]
    exact u.property.1
  have has : a*star a=1 := by
    apply hi
    simp only [map_mul,map_star,map_one]
    rw [ha]
    exact u.property.2
  exact ⟨⟨a,⟨hsa,has⟩⟩,ha⟩

omit [StarModule ℂ A] [StarModule ℂ B] in
theorem unitary_preimage_zpow (φ : A →⋆ₐ[ℂ] B) (u : unitary A) (v : unitary B)
    (h : φ u.val=v.val) (k : ℤ) : φ ((u^k).val)=(v^k).val := by
  have hv : Unitary.map (StarMonoidHom.ofClass φ) u=v := Subtype.ext h
  have hh := congrArg Subtype.val (map_zpow (Unitary.map (StarMonoidHom.ofClass φ)) u k)
  change φ ((u^k).val)=_ at hh
  rwa [hv] at hh

end

end KKVariableUltra
end

end OAI
