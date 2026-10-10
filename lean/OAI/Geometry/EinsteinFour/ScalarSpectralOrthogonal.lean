import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace OAI

/-! The orthonormal family obtained by combining orthonormal bases of the
eigenspaces of a symmetric scalar operator. -/

namespace PositiveEinsteinFour.Geometry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem scalar_spectral_family_orthonormal (T : V →L[ℝ] V) (hT : T.IsSymmetric)
    [∀ μ : Module.End.Eigenvalues T.toLinearMap,
      FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ.val)] :
    Orthonormal ℝ (fun i : (Σ μ : Module.End.Eigenvalues T.toLinearMap,
        Fin (Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ.val))) =>
      (stdOrthonormalBasis ℝ (Module.End.eigenspace T.toLinearMap i.1.val) i.2).val) :=
  hT.orthogonalFamily_eigenspaces'.orthonormal_sigma_orthonormal
    (fun μ => (stdOrthonormalBasis ℝ (Module.End.eigenspace T.toLinearMap μ.val)).orthonormal)

end
end PositiveEinsteinFour.Geometry

end OAI
