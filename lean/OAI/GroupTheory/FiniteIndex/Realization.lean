import OAI.GroupTheory.FiniteIndex.Extension

namespace OAI

/-! Realization of finite-index subgroups in extensions with free abelian quotient. -/

namespace FiniteIndexRealization

lemma normal_map_of_characteristic {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (K : Subgroup N) [K.Characteristic] : (K.map N.subtype).Normal := by
  classical
  constructor
  intro x hx g
  obtain ⟨x, hx, rfl⟩ := hx
  let e : N ≃* N :=
    { toFun := fun a => ⟨g * a * g⁻¹, (inferInstance : N.Normal).conj_mem a a.property g⟩
      invFun := fun a => ⟨g⁻¹ * a * (g⁻¹)⁻¹, (inferInstance : N.Normal).conj_mem a a.property g⁻¹⟩
      left_inv := by intro a; apply Subtype.ext; simp [mul_assoc]
      right_inv := by intro a; apply Subtype.ext; simp [mul_assoc]
      map_mul' := by intro a b; apply Subtype.ext; simp [mul_assoc] }
  exact ⟨e x, Subgroup.characteristic_iff_le_comap.mp inferInstance e hx, rfl⟩

theorem realize_finite_index (G : Type*) [Group G] (N : Subgroup G)
    [N.Normal] [Group.FG N] (r : Nat)
    (e : G ⧸ N ≃* (Fin r → Multiplicative Int))
    (N0 : Subgroup N) [N0.FiniteIndex] :
    ∃ G0 : Subgroup G, G0.FiniteIndex ∧ G0.comap N.subtype ≤ N0 := by
  classical
  obtain ⟨K, hKchar, hKfin, hKle⟩ := characteristic_finiteIndex_refinement N N0
  let := hKchar
  let := hKfin
  let L : Subgroup G := K.map N.subtype
  let : L.Normal := normal_map_of_characteristic N K
  have hLN : L ≤ N := by
    rintro x ⟨a, ha, rfl⟩
    exact a.property
  let π : G →* (Fin r → Multiplicative Int) := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπker : π.ker = N := by
    ext x
    change e (QuotientGroup.mk' N x) = 1 ↔ x ∈ N
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hπFG : Group.FG π.ker := by rw [hπker]; infer_instance
  let := hπFG
  let : Group.FG G := fg_of_surjective_with_fg_kernel π hπsurj
  have hLπ : L ≤ π.ker := by rw [hπker]; exact hLN
  let f : G ⧸ L →* (Fin r → Multiplicative Int) := QuotientGroup.lift L π hLπ
  let t : N →* G ⧸ L := (QuotientGroup.mk' L).comp N.subtype
  have htker : t.ker = K := by
    ext x
    change QuotientGroup.mk' L (x : G) = 1 ↔ x ∈ K
    refine (QuotientGroup.eq_one_iff (N := L) (x : G)).trans ?_
    constructor
    · rintro ⟨y, hy, heq⟩
      have : y = x := Subtype.ext heq
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have htrange : t.range = f.ker := by
    rw [show f.ker = π.ker.map (QuotientGroup.mk' L) from QuotientGroup.ker_lift L π hLπ]
    rw [hπker]
    change ((QuotientGroup.mk' L).comp N.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have htfin : Finite (N ⧸ t.ker) := by rw [htker]; infer_instance
  let := htfin
  let : Finite t.range := Finite.of_surjective (QuotientGroup.quotientKerEquivRange t)
    (QuotientGroup.quotientKerEquivRange t).surjective
  have hffin : Finite f.ker := by rw [← htrange]; infer_instance
  let := hffin
  obtain ⟨J, hJ, hdisjoint⟩ := finite_kernel_free_abelian_disjoint r f
  let := hJ
  have hJcomap : (J.comap (QuotientGroup.mk' L)).FiniteIndex := by
    constructor
    rw [J.index_comap_of_surjective (QuotientGroup.mk'_surjective L)]
    exact hJ.index_ne_zero
  refine ⟨J.comap (QuotientGroup.mk' L), hJcomap, ?_⟩
  intro x hx
  have hfx : f (QuotientGroup.mk' L (x : G)) = 1 := by
    change π (x : G) = 1
    rw [← MonoidHom.mem_ker, hπker]
    exact x.property
  have hxJ : QuotientGroup.mk' L (x : G) ∈ J := hx
  have hone : QuotientGroup.mk' L (x : G) = 1 := by
    have hmem : QuotientGroup.mk' L (x : G) ∈ J ⊓ f.ker := ⟨hxJ, hfx⟩
    rw [hdisjoint] at hmem
    exact hmem
  have hxK : x ∈ K := by
    rw [← htker]
    exact hone
  exact hKle hxK
end FiniteIndexRealization

end OAI
