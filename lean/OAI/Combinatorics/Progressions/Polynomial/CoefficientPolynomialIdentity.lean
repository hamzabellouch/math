import OAI.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical

noncomputable def identityPhysicalCube (q : ℕ) : Fin q → (Unit ⊕ Fin q) → ℤ :=
  fun x => Sum.elim (fun _ => 0) (fun i => if i = x then 1 else 0)

theorem identityPhysicalCube_frame (q : ℕ) :
    (fun k x => (standardPhysicalCubeFrame (identityPhysicalCube q) (k,x) : ℝ)) =
      identityCoefficientFrame (Fin q) := by
  funext k x
  cases k <;> simp [standardPhysicalCubeFrame, identityPhysicalCube, identityCoefficientFrame]

theorem coefficient_polynomial_identity_transfer
    {m q : ℕ} {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (rows : ∀ j, O j → Finset (Fin q))
    (d D : ℕ) (hD : 0 < D) (hd : d ∣ D)
    {T : Type*} [Fintype T] (period : T → ℕ) (hperiod : ∀ t, period t ∣ D)
    (c : T → ℂ) (f : T → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ)
    (M : EuclideanJetLayers U O → ℂ)
    (hidentity : ∀ (p : ∀ j, VectorPolynomial (Fin q) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : Fin q → ℕ) (j.val + 1) (p j))
      (hm : ∀ j e, coefficients (p j) e ∈ U j)
      (v : Fin q → (Unit ⊕ Fin q) → ℤ),
      M (physicalCubeRowSample U d rows p hm v) =
        ∑ t, c t * f t (coefficientAmbientTorus U
          (affineCoefficientCoverSample U p hm (period t)
            (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ)))))
    (z : CoefficientTorus (K := Fin q) U) :
    M (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
      (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z)) =
      ∑ t, c t * f t ((D / period t) • coefficientAmbientTorus U z) := by
  obtain ⟨p, hm, hp, hz⟩ := exists_coefficient_sample_realization U D hD z
  have hsample (a : ℕ) (ha : a ∣ D) :
      affineCoefficientCoverSample U p hm a
        (fun k x => (standardPhysicalCubeFrame (identityPhysicalCube q) (k,x) : ℝ)) =
      quotientIntegerCover (coefficientIntegerLattice U) (D / a) z := by
    rw [identityPhysicalCube_frame, ← hz]
    exact (affineCoefficientCoverSample_divisor_projection U p hm D a hD ha _).symm
  have hj := coefficientCoverSample_physicalRows U d p hp hm rows (identityPhysicalCube q)
  rw [hsample d hd] at hj
  rw [hj, hidentity p hp hm (identityPhysicalCube q)]
  apply Finset.sum_congr rfl
  intro t _
  rw [hsample (period t) (hperiod t), coefficientAmbientTorus_cover]

end Erdos3.BooleanCubeKernel

end

end OAI
