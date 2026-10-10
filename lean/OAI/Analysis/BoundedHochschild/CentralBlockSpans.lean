import OAI.Analysis.BoundedHochschild.CentralBlockUnitaries

namespace OAI

/-! Matrix coefficients in the span of finite block unitary groups. -/

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

variable {M I G : Type*} [CStarAlgebra M] [Fintype I] [Group G]
  (p : I → M) (hp : ∀ i, IsStarProjection (p i))
  (hc : ∀ i a, p i * a = a * p i)
  (ho : ∀ i j, i ≠ j → p i * p j = 0)
  (hs : ∑ i, p i = 1) (ρ : G →* unitary M)

def centralBlockSpan : Submodule ℂ M := Submodule.span ℂ
  (Set.range (fun a : I → G => (centralBlockHom p hp hc ho hs ρ a : M)))

lemma centralBlock_unitary_mem_span (a : I → G) :
    centralBlock p (fun i => (ρ (a i) : M)) ∈ centralBlockSpan p hp hc ho hs ρ :=
  Submodule.subset_span ⟨a, rfl⟩

lemma centralBlock_component_mem_span (j : I) (g z : G) (hz : (ρ z : M) = -1) :
    p j * (ρ g : M) ∈ centralBlockSpan p hp hc ho hs ρ := by
  classical
  let a : I → G := fun _ => g
  let b : I → G := Function.update a j (z * g)
  have hdiff : centralBlock p (fun i => (ρ (a i) : M)) -
      centralBlock p (fun i => (ρ (b i) : M)) = (2 : ℂ) • (p j * (ρ g : M)) := by
    rw [centralBlock, centralBlock, ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp only [a, b, Function.update_self, map_mul, Submonoid.coe_mul, hz,
        neg_one_mul, mul_neg, sub_neg_eq_add, two_smul]
    · intro k _ hkj
      simp only [b, Function.update_of_ne hkj, sub_self]
    · simp
  have h := (centralBlockSpan p hp hc ho hs ρ).sub_mem
    (centralBlock_unitary_mem_span p hp hc ho hs ρ a)
    (centralBlock_unitary_mem_span p hp hc ho hs ρ b)
  rw [hdiff] at h
  have h' := (centralBlockSpan p hp hc ho hs ρ).smul_mem (2⁻¹ : ℂ) h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using h'

lemma centralBlock_mul_mem_span (j : I) (z : G) (hz : (ρ z : M) = -1)
    {a : M} (ha : a ∈ Submodule.span ℂ (Set.range (fun g : G => (ρ g : M)))) :
    p j * a ∈ centralBlockSpan p hp hc ho hs ρ := by
  let S := (centralBlockSpan p hp hc ho hs ρ).comap
    (ContinuousLinearMap.mul ℂ M (p j)).toLinearMap
  have hle : Submodule.span ℂ (Set.range (fun g : G => (ρ g : M))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact centralBlock_component_mem_span p hp hc ho hs ρ j g z hz
  exact hle ha

end KadisonRingrose
end BoundedHochschild

end

end OAI
