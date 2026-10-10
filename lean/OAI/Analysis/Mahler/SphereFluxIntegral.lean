import OAI.Analysis.Mahler.OrientedSphereDensity
import OAI.Analysis.Mahler.ReferenceSphere

namespace OAI

open MeasureTheory Metric
open scoped BigOperators

namespace Mahler

/-- The order is recursive and interleaved, not an arbitrary finite equivalence. -/
def powerFinEquiv : (k : ℕ) → WedgePowerSlots k ≃ Fin (2*k)
  | 0 => Equiv.refl _
  | k+1 => (Equiv.sumCongr (Equiv.refl (Fin 2)) (powerFinEquiv k)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))

def boundaryFinEquiv (k : ℕ) : (Fin 1 ⊕ WedgePowerSlots k) ≃ Fin (2*k+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (powerFinEquiv k)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

def ambientFinEquiv (k : ℕ) : WedgePowerSlots (k+1) ≃ Fin ((2*k+1)+1) :=
  (powerFinEquiv (k+1)).trans (finCongr (by omega))

noncomputable def sphereVolume (k : ℕ) :
    ComplexEuclidean (k+1) [⋀^Fin ((2*k+1)+1)]→ₗ[ℝ] ℂ :=
  (interleavedVolume (k+1)).domDomCongr (ambientFinEquiv k)

noncomputable def sphereFrame (k : ℕ) :
    OrthonormalBasis (Fin ((2*k+1)+1)) ℝ (ComplexEuclidean (k+1)) :=
  (Pi.orthonormalBasis (fun _ : Fin (k+1) => Complex.orthonormalBasisOneI)).reindex
    ((Equiv.sigmaEquivProd (Fin (k+1)) (Fin 2)).trans
      ((pairSlotEquiv (k+1)).symm.trans (ambientFinEquiv k)))

lemma topForm_basis_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {d : ℕ} (b : Module.Basis (Fin d) ℝ E)
    {Ω : E [⋀^Fin d]→ₗ[ℝ] ℂ} (hΩ : Ω ≠ 0) : Ω b ≠ 0 := by
  classical
  intro hz
  apply hΩ
  apply b.ext_alternating
  intro v hv
  let e : Equiv.Perm (Fin d) := Equiv.ofBijective v ⟨hv, Finite.surjective_of_injective hv⟩
  change Ω (b ∘ e) = 0
  rw [Ω.map_perm, hz, smul_zero]

lemma sphereVolume_frame_ne_zero (k : ℕ) : sphereVolume k (sphereFrame k) ≠ 0 := by
  apply topForm_basis_ne_zero (sphereFrame k).toBasis
  intro hz
  have h := congrArg (fun a => a (interleavedBasis ∘ (ambientFinEquiv k).symm)) hz
  have he : ((interleavedBasis ∘ (ambientFinEquiv k).symm) ∘ ambientFinEquiv k) =
      (interleavedBasis : WedgePowerSlots (k+1) → ComplexEuclidean (k+1)) := by
    funext i; simp
  simp only [sphereVolume, AlternatingMap.domDomCongr_apply, he,
    interleavedVolume_basis, AlternatingMap.zero_apply] at h
  exact one_ne_zero h

/-- Actual boundary form, in its standard ordered slots. -/
noncomputable def boundaryFormFin {k : ℕ}
    (a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+1)) :
    ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ :=
  (wedge (oneForm a x).toAlternatingMap
    (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k)).domDomCongr (boundaryFinEquiv k)

/-- The integral uses Euclidean area and the cofactor surface density with
outward normal x on the unit sphere. -/
noncomputable def sphereFlux (k : ℕ)
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ) : ℝ :=
  ∫ x : sphere (0 : ComplexEuclidean (k+1)) 1,
    (orientedDensity (sphereFrame k) (sphereVolume k) (B x) x).re ∂sphereArea (k+1)

/-- The coefficient for contraction of the normalized top
volume. Equality with the Liouville boundary
form is not assumed. -/
theorem sphereFlux_normalized_contraction (k : ℕ) :
    sphereFlux k (fun x => ((k.factorial : ℂ) / 2) • (sphereVolume k).curryLeft x) =
      Real.pi^(k+1) := by
  unfold sphereFlux
  convert reference_sphere_density_integral (k+1) (by omega) using 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : ‖(x : ComplexEuclidean (k+1))‖ = 1 := by
    simpa only [mem_sphere_iff_norm, sub_zero] using x.property
  rw [orientedDensity_smul, orientedDensity_contraction _ _ (sphereVolume_frame_ne_zero k)]
  simp [hx]

end Mahler

end OAI
