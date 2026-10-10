import OAI.Geometry.NodalSets.Spectral.SphereSmoothFrameRayleigh

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set
open scoped ContDiff
noncomputable section
local instance sphereIndexedRayleighMeasurable : MeasurableSpace Base := borel Base
local instance sphereIndexedRayleighBorel : BorelSpace Base := ⟨rfl⟩

def sphereRayleighUpperLevels (d : SphereEnergyData) (N : ℕ) : Set ℝ :=
  {a | ∃ V : Submodule ℝ sphereSmoothFunctions,
    FiniteDimensional ℝ V ∧ Module.finrank ℝ V = N+1 ∧
    ∀ x ∈ V, x ≠ 0 → sphereRayleighQuotient d.tensor d.density x ≤ a}

def sphereIndexedEigenvalue (d : SphereEnergyData) (N : ℕ) : ℝ :=
  sInf (sphereRayleighUpperLevels d N)

theorem sphere_rayleigh_levels_nonneg (d : SphereEnergyData) (N : ℕ)
    (a : ℝ) (ha : a ∈ sphereRayleighUpperLevels d N) : 0 ≤ a := by
  obtain ⟨V,hV,hdim,hbound⟩ := ha
  let := hV
  have hV0 : V ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  apply le_trans _ (hbound x hx hx0)
  apply div_nonneg (sphereDirichletForm_nonneg d.tensor d.pos x)
  exact (sphereWeightedPairing_self_pos d.density x d.continuous d.positive x.property.continuous
    (fun h ↦ hx0 (Subtype.ext h))).le

theorem sphereIndexedEigenvalue_eq_of_minmax (d : SphereEnergyData) (N : ℕ) (a : ℝ)
    (hupper : a ∈ sphereRayleighUpperLevels d N)
    (hlower : ∀ V : Submodule ℝ sphereSmoothFunctions,
      FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : sphereSmoothFunctions, x ∈ V ∧ x ≠ 0 ∧ a ≤ sphereRayleighQuotient d.tensor d.density x) :
    sphereIndexedEigenvalue d N = a := by
  have hbelow : ∀ b ∈ sphereRayleighUpperLevels d N, a ≤ b := by
    rintro b ⟨V,hV,hdim,hb⟩
    obtain ⟨x,hx,hx0,hlo⟩ := hlower V hV hdim
    exact hlo.trans (hb x hx hx0)
  exact le_antisymm (csInf_le ⟨a,hbelow⟩ hupper) (le_csInf ⟨a,hupper⟩ hbelow)

theorem sphereIndexedEigenvalue_eq_frame (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) :
    sphereIndexedEigenvalue d N = (mu (Fin.last N))⁻¹-1 := by
  obtain ⟨hup,hlo⟩ := sphere_smooth_frame_rayleigh_minmax d u mu ho hmu he hanti hmax
  exact sphereIndexedEigenvalue_eq_of_minmax d N _ hup hlo

theorem sphereIndexedEigenvalue_minmax (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    sphereIndexedEigenvalue d N ∈ sphereRayleighUpperLevels d N ∧
    (∀ V : Submodule ℝ sphereSmoothFunctions, FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : sphereSmoothFunctions, x ∈ V ∧ x ≠ 0 ∧
        sphereIndexedEigenvalue d N ≤ sphereRayleighQuotient d.tensor d.density x) ∧
    0 ≤ sphereIndexedEigenvalue d N := by
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  obtain ⟨hup,hlo⟩ := sphere_smooth_frame_rayleigh_minmax d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  have hupp : sphereIndexedEigenvalue d N ∈ sphereRayleighUpperLevels d N := heq.symm ▸ hup
  exact ⟨hupp,heq.symm ▸ hlo,sphere_rayleigh_levels_nonneg d N _ hupp⟩

theorem sphereIndexedEigenvalue_smooth_realization (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    ∃ u : SphereEnergySmooth d, u ≠ 0 ∧ ‖sphereEnergyL2Linear d u‖=1 ∧
      sphereL2Resolvent d (sphereEnergyL2Linear d u) =
        (sphereIndexedEigenvalue d N+1)⁻¹ • sphereEnergyL2Linear d u ∧
      ∀ v : SphereEnergyHilbert d,
        sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
          sphereIndexedEigenvalue d N * inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Map d v) := by
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  let i := Fin.last N
  refine ⟨u i,?_,ho.norm_eq_one i,?_,?_⟩
  · intro hz
    have hn := ho.ne_zero i
    exact hn (by rw [hz,map_zero])
  · rw [heq,sub_add_cancel,inv_inv]
    exact (he i).2.2
  · intro v
    rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe,
      sphere_resolvent_smooth_variational d (mu i) (he i).1.ne' (u i) (he i).2.2 v,heq]
    ring

end
end Yau.Target

end OAI
