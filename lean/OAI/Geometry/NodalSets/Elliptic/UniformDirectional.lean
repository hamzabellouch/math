import OAI.Geometry.NodalSets.Elliptic.ContinuousPolynomialFamily

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def directionalPrimitive (v : Fin 4 → ℂ) (i : Fin 4) (p : CPoly) : CPoly :=
  aeval (transverse v i) (Yau.primitive i (aeval (original v i) p))

theorem directionalPrimitive_right_inverse (v : Fin 4 → ℂ) (i : Fin 4)
    (hi : v i ≠ 0) (p : CPoly) : direction v (directionalPrimitive v i p) = p := by
  rw [directionalPrimitive, directional_substitution v i hi, Yau.pderiv_primitive]
  exact substitution_inverse v i hi p

lemma directionalPrimitive_homogeneous (v : Fin 4 → ℂ) (i : Fin 4)
    {p : CPoly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (directionalPrimitive v i p).IsHomogeneous (n + 1) := by
  have hq : (aeval (original v i) p).IsHomogeneous n := by
    simpa using hp.aeval (original v i) (original_homogeneous v i)
  simpa [directionalPrimitive] using (Yau.primitive_homogeneous i hq).aeval (transverse v i)
    (transverse_homogeneous v i)

variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.primitive {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (i : Fin 4) : ContinuousPolyFamily (fun t ↦ Yau.primitive i (P t)) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ Yau.primitive i (P t)) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • monomial (d + Finsupp.single i 1)
        (((d i : ℂ) + 1)⁻¹) := by
    funext t
    simp only [Yau.primitive, smul_monomial, smul_eq_mul, div_eq_mul_inv]
    exact Finset.sum_subset (hs t) (fun d _ hd ↦ by
      simp [notMem_support_iff.mp hd])
  rw [he]
  exact continuousPolyFamily_of_representation s _ _ (fun d _ ↦ hp.1 d)

lemma continuousPolyFamily_original (v : T → Fin 4 → ℂ)
    (hv : ∀ j, Continuous (fun t ↦ v t j)) (i j : Fin 4) :
    ContinuousPolyFamily (fun t ↦ original (v t) i j) := by
  unfold original
  split_ifs
  · exact (ContinuousPolyFamily.C (hv i)).mul (ContinuousPolyFamily.const _)
  · exact (ContinuousPolyFamily.const _).add ((ContinuousPolyFamily.C (hv j)).mul (ContinuousPolyFamily.const _))

lemma continuousPolyFamily_transverse (v : T → Fin 4 → ℂ)
    (hv : ∀ j, Continuous (fun t ↦ v t j)) (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (j : Fin 4) : ContinuousPolyFamily (fun t ↦ transverse (v t) i j) := by
  unfold transverse
  split_ifs
  · exact (ContinuousPolyFamily.C ((hv i).inv₀ hi)).mul (ContinuousPolyFamily.const _)
  · exact (ContinuousPolyFamily.const _).add ((ContinuousPolyFamily.C (((hv j).div (hv i) hi).neg)).mul (ContinuousPolyFamily.const _))

theorem ContinuousPolyFamily.directionalPrimitive {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (v : T → Fin 4 → ℂ)
    (hv : ∀ j, Continuous (fun t ↦ v t j)) (i : Fin 4) (hi : ∀ t, v t i ≠ 0) :
    ContinuousPolyFamily (fun t ↦ directionalPrimitive (v t) i (P t)) := by
  exact ((hp.aeval (fun j t ↦ original (v t) i j)
    (continuousPolyFamily_original v hv i)).primitive i).aeval
      (fun j t ↦ transverse (v t) i j) (continuousPolyFamily_transverse v hv i hi)

theorem directionalPrimitive_uniform_bound {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hi : ∀ t, v t i ≠ 0) (s : Set T) (hs : IsCompact s) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (reval (directionalPrimitive (v t) i (P t))) x‖ ≤ C :=
  (hp.directionalPrimitive v hv i hi).uniform_derivative_bound s hs R k

end
end Yau.Jets

end OAI
