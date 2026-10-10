import OAI.Analysis.KadisonSimilarity.FreeProduct.ConcreteDihedralSpectralArc

namespace OAI

/-! Faithful-coordinate transport of the spectral arc. Only the actual
generated subalgebra must have a von Neumann range. -/

noncomputable section
namespace KadisonSimilarity

section Transport
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem starAlgHom_unit_zpow (ρ : A →⋆ₐ[ℂ] B) (u : Aˣ) (l : ℤ) :
    ρ (↑(u ^ l) : A) = (↑((Units.map ρ.toAlgHom.toMonoidHom u) ^ l) : B) :=
  congrArg (fun v : Bˣ => (v : B)) (map_zpow (Units.map ρ.toAlgHom.toMonoidHom) u l)

/-- An arc in a faithful represented subalgebra is an arc in the source,
with exactly the same trace moments. -/
theorem dihedralSpectralArcInput_of_injective
    (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ) (ρ : A →⋆ₐ[ℂ] B)
    (hρ : Function.Injective ρ) (hτ : ∀ a, τB (ρ a) = τA a)
    (C : StarSubalgebra ℂ A) (w d : Aˣ)
    (hinput : DihedralSpectralArcInput τB (C.map ρ)
      (Units.map ρ.toAlgHom.toMonoidHom w) (Units.map ρ.toAlgHom.toMonoidHom d)) :
    DihedralSpectralArcInput τA C w d := by
  intro θ hθ hθπ
  obtain ⟨F⟩ := hinput θ hθ hθπ
  obtain ⟨a, ha, heq⟩ := F.mem
  change a ∈ C at ha
  change ρ a = F.element at heq
  have hwp (l : ℤ) := starAlgHom_unit_zpow ρ w l
  refine ⟨{
    element := a
    mem := ha
    selfAdjoint := ?_
    norm_le := ?_
    commute_rotation := ?_
    commute_reflection := ?_
    rotation_moment := ?_
    reflection_moment := ?_
    square_moment := ?_
    square_reflection_moment := ?_
  }⟩
  · apply hρ
    rw [map_star ρ, heq, F.selfAdjoint]
  · rw [← NonUnitalStarAlgHom.norm_map ρ hρ a, heq]
    exact F.norm_le
  · apply hρ
    simp only [map_mul ρ, heq]
    exact F.commute_rotation.eq
  · apply hρ
    simp only [map_mul ρ, heq]
    exact F.commute_reflection.eq
  · intro l
    rw [← hτ, map_mul ρ, heq, hwp]
    exact F.rotation_moment l
  · intro l
    simp only [← hτ, map_mul ρ, heq, hwp]
    exact F.reflection_moment l
  · rw [← hτ, map_mul ρ, heq]
    exact F.square_moment
  · simp only [← hτ, map_mul ρ, heq]
    exact F.square_reflection_moment

end Transport
end KadisonSimilarity

end

end OAI
