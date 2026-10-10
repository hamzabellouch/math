import OAI.Analysis.KadisonSimilarity.Representation.GeneratedNormalRange
import OAI.Analysis.KadisonSimilarity.FreeProduct.NormalSpectralArc
import OAI.Analysis.KadisonSimilarity.FreeProduct.GeneratedDihedralAlgebras
import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralPositiveDensity

namespace OAI

/-! The generated free dihedral algebra inherits its normal realization
from the ambient tracial geometry. Its spectral input is therefore a
consequence of the two free centered symmetries. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem generated_dihedral_spectralInput
    (h1 : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (D B : StarSubalgebra ℂ A) (hfree : ScalarFree G.trace D B)
    (d s : Aˣ) (hd : (d : A) ∈ D) (hs : (s : A) ∈ B)
    (hd0 : G.trace (d : A) = 0) (hs0 : G.trace (s : A) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s)
    (hds : star d = d) (hss : star s = s) :
    DihedralSpectralArcInput G.trace
      (G.generatedDihedralAlgebra (d : A) (s : A)) (d * s) d := by
  obtain ⟨N, hN⟩ := G.exists_l2Generated_normal_range h1 hfaithful M hrange
    (StarAlgebra.adjoin ℂ ({(d : A), (s : A)} : Set A))
  have hw : star (↑(d * s) : A) = (↑(d * s)⁻¹ : A) := by
    exact congrArg (fun u : Aˣ => (u : A))
      (free_symmetry_product_star d s hds hss hdi hsi)
  apply dihedralSpectralArcInput_of_normal_range G.trace G.left
    (G.left_injective hfaithful) (G.vector 1) G.trace_eq_vectorTrace
    (G.generatedDihedralAlgebra (d : A) (s : A)) N hN (d * s) d
  · exact (G.generatedDihedralAlgebra (d : A) (s : A)).mul_mem
      (G.first_mem_generatedDihedralAlgebra (d : A) (s : A))
      (G.second_mem_generatedDihedralAlgebra (d : A) (s : A))
  · exact hw
  · nontriviality A
    have hn : ‖(↑(d * s) : A)‖ * ‖(↑(d * s) : A)‖ = 1 := by
      rw [← CStarRing.norm_star_mul_self, hw, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, norm_one]
    nlinarith [norm_nonneg (↑(d * s) : A)]
  · simpa only [hdi, Units.val_mul, Units.val_one] using
      congrArg (fun u : Aˣ => (u : A)) (inv_mul_cancel d)
  · exact congrArg (fun u : Aˣ => (u : A)) hds
  · rw [hw]
    exact congrArg (fun u : Aˣ => (u : A)) (free_symmetry_rotation_conjugation d s hdi hsi)
  · exact free_symmetry_haar_moments G.trace h1 D B hfree d s hd hs hd0 hs0 hdi hsi
  · exact G.free_symmetry_first_coset_moments D B hfree d s hd hs hd0 hs0 hdi hsi

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
