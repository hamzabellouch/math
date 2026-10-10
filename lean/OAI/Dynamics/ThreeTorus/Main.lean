import OAI.Dynamics.ThreeTorus.SpectralTransport

namespace OAI

/-! Unconditional smooth simple Lebesgue spectrum theorem with real L2 cyclic generator. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- The unconditional main theorem. The generator and its
entire basis are produced by the physical smooth diagonal, then transported by
the fixed measure-preserving coordinate equivalence. -/
theorem simple_lebesgue_spectrum : MainConclusion := by
  obtain ⟨D,f,hf,hfr,ho,hd⟩ := exists_physical_basis
  let f₀ : physicalMeanZero := ⟨f,hf⟩
  let v₀ (k : ℤ) : physicalMeanZero := ⟨D.orbit f k,D.orbit_centered hf k⟩
  have hov : Orthonormal ℂ v₀ := by
    rw [orthonormal_iff_ite]
    intro k j
    exact orthonormal_iff_ite.mp ho k j
  have hdv : Dense (Submodule.span ℂ (Set.range v₀) : Set physicalMeanZero) :=
    physical_subtype_dense v₀ hd
  let g := physicalZeroEquiv f₀
  let v (k : ℤ) := physicalZeroEquiv (v₀ k)
  have hgr : IsReal g := by
    filter_upwards [physicalToTorus_ae f,
      measurePreserving_torusTriple.quasiMeasurePreserving.ae hfr] with x hx hy
    change (physicalToTorus f x).im=0
    rw [hx]
    exact hy
  have hvg (k : ℤ) : ∀ᵐ x ∂μ, (v k).1 x=g.1 (((D.torusMap 1)^k) x) := by
    change ∀ᵐ x ∂μ, physicalToTorus (D.orbit f k) x=physicalToTorus f (((D.torusMap 1)^k) x)
    rw [D.torusMap_zpow]
    filter_upwards [physicalToTorus_ae (D.orbit f k),
      measurePreserving_torusTriple.quasiMeasurePreserving.ae (D.orbit_ae f k),
      (D.torusMap_mp k).quasiMeasurePreserving.ae (physicalToTorus_ae f)] with x hx hy hz
    simp only [D.torusMap_apply,torusTriple.apply_symm_apply] at hz
    exact hx.trans (hy.trans hz.symm)
  exact mainConclusion_of_basis (D.torusMap 1) (D.torusMap_smooth 1)
    (by rw [D.torusMap_symm]; exact D.torusMap_smooth (-1)) (D.torusMap_mp 1)
    g hgr v hvg (hov.comp_linearIsometryEquiv physicalZeroEquiv)
    (physicalZeroEquiv_dense_span v₀ hdv)

end ThreeTorus
end
end

end OAI
