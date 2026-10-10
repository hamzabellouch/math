import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.TetrahedronChainInjection

namespace OAI

noncomputable section

namespace Problem340.SimplicialSphere

theorem radial_surjective : Function.Surjective radial := by
  intro x
  let v : Fin 4 → ℝ := ![x.val 0, x.val 1, x.val 2, 0]
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty v
  have hm (i : Fin 4) : m ≤ v i := Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty v
  let D : ℝ := ∑ i : Fin 4, (v i - m)
  have hDn : 0 ≤ D := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hm i))
  have hDp : 0 < D := by
    by_contra! h
    have hDz : D = 0 := le_antisymm h hDn
    have hv : ∀ i : Fin 4, v i = m := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) =>
          sub_nonneg.mpr (hm k))).mp hDz i (Finset.mem_univ i)
      exact sub_eq_zero.mp hz
    have hm0 : m = 0 := by simpa [v] using (hv 3).symm
    have hx0 : x.val = 0 := by
      ext i
      fin_cases i
      · simpa [v, hm0] using hv 0
      · simpa [v, hm0] using hv 1
      · simpa [v, hm0] using hv 2
    have hx := x.property
    simp [hx0] at hx
  let coordinates : RealSimplex.coordinateSet (Fin 4) := ⟨fun i => (v i - m) / D, by
    constructor
    · intro i
      exact div_nonneg (sub_nonneg.mpr (hm i)) hDp.le
    · rw [← Finset.sum_div]
      exact div_self hDp.ne'⟩
  let p : Convexity.StdSimplex ℝ (Fin 4) := RealSimplex.coordinateHomeomorph.symm coordinates
  have hp (index : Fin 4) : p index = (v index - m) / D :=
    RealSimplex.coordinateHomeomorph_symm_apply_at coordinates index
  have hboundary : ∃ i : Fin 4, p i = 0 := by
    refine ⟨j, ?_⟩
    rw [hp]
    rw [← hjm, sub_self, zero_div]
  let b : TopologicalBoundary := ⟨p, hboundary⟩
  have hb : tetraVector b = D⁻¹ • x.val := by
    ext i
    fin_cases i
    · change p 0 - p 3 = D⁻¹ * x.val 0
      rw [hp, hp]
      dsimp [v]
      ring
    · change p 1 - p 3 = D⁻¹ * x.val 1
      rw [hp, hp]
      dsimp [v]
      ring
    · change p 2 - p 3 = D⁻¹ * x.val 2
      rw [hp, hp]
      dsimp [v]
      ring
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change ‖tetraVector b‖⁻¹ • tetraVector b = x.val
  have hxnorm : ‖x.val‖ = 1 := by simp
  rw [hb, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hDp),
    hxnorm, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hDp.ne', one_smul]

instance compactSpace_topologicalBoundary : CompactSpace TopologicalBoundary := by
  have hi (j : Fin 4) : IsClosed {p : Convexity.StdSimplex ℝ (Fin 4) | p j = 0} :=
    isClosed_eq (Convexity.StdSimplex.continuous_weights_apply ℝ j) continuous_const
  have hu := isClosed_iUnion_of_finite hi
  have hc : IsCompact {p : Convexity.StdSimplex ℝ (Fin 4) | ∃ j : Fin 4, p j = 0} := by
    simpa only [Set.iUnion_ofPred] using hu.isCompact
  exact isCompact_iff_compactSpace.mp hc

def radialHomeomorph : TopologicalBoundary ≃ₜ StandardSphere2 :=
  IsHomeomorph.homeomorph radial
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_radial, radial_injective, radial_surjective⟩)

@[simp] theorem radialHomeomorph_apply (p : TopologicalBoundary) :
    radialHomeomorph p = radial p := rfl

end Problem340.SimplicialSphere

end

end OAI
