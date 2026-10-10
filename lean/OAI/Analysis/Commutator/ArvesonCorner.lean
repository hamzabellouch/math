import Mathlib
import OAI.Analysis.Commutator.ArvesonFinite
import OAI.Analysis.Commutator.CpMapOperations

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.CpOperations

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma compression_norm_le (V : K →L[ℂ] H) (hV : ‖V‖≤1) (T : H →L[ℂ] H) :
    ‖compression V T‖≤‖T‖ := by
  calc
    _ ≤ ‖V.adjoint‖*(‖T‖*‖V‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(‖T‖*1) := by
      simp only [LinearIsometryEquiv.norm_map]
      gcongr
    _ = ‖T‖ := by ring

end Kadison.CpOperations

namespace Kadison.OperatorSystem

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_corner_extension (S : Submodule ℂ A) (h1 : (1 : A)∈S)
    (hs : ∀ a∈S,star a∈S) (f : S →ₗ[ℂ] (H →L[ℂ] H))
    (hf : IsCompletelyPositive S f) (E : Submodule ℂ H) [FiniteDimensional ℂ E] :
    ∃ Φ : A →CP (H →L[ℂ] H), (∀ a,‖Φ a‖≤‖f ⟨1,h1⟩‖*‖a‖) ∧
      ∀ a : S,∀ x∈E,∀ y∈E,⟪Φ a x,y⟫_ℂ=⟪f a x,y⟫_ℂ := by
  let e := (stdOrthonormalBasis ℂ E).repr
  let W : CoordinateSpace (Fin (Module.finrank ℂ E)) →ₗᵢ[ℂ] H :=
    E.subtypeₗᵢ.comp e.symm.toLinearIsometry
  let J := W.toContinuousLinearMap
  have hJ : ‖J‖≤1 := W.norm_toContinuousLinearMap_le
  have hJ' : ‖J.adjoint‖≤1 := by simpa only [LinearIsometryEquiv.norm_map] using hJ
  let g := (CpOperations.compression J).toLinearMap.comp f
  have hg : IsCompletelyPositive S g := CpOperations.isCompletelyPositive_comp S f hf _
  obtain ⟨η,hη⟩ := exists_finite_extension_all S h1 hs g hg
  let Φ := CpOperations.comp (CpOperations.compression J.adjoint) η
  have hnorm : ‖Φ 1‖≤‖f ⟨1,h1⟩‖ := by
    have he : η 1=g ⟨1,h1⟩ := hη ⟨1,h1⟩
    change ‖CpOperations.compression J.adjoint (η 1)‖≤_
    exact (CpOperations.compression_norm_le _ hJ' _).trans
      (by rw [he]; exact CpOperations.compression_norm_le _ hJ _)
  have hproj (x : H) (hx : x∈E) : J (J.adjoint x)=x := by
    let v := e ⟨x,hx⟩
    have hv : J v=x := by simp [J,W,v]
    rw [←hv]
    have he := congrArg (fun T => T v) W.adjoint_comp_self
    change J.adjoint (J v)=v at he
    rw [he]
  refine ⟨Φ,fun a => (CpOperations.norm_apply_le Φ a).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg a)),?_⟩
  intro a x hx y hy
  change ⟪J.adjoint.adjoint (η a (J.adjoint x)),y⟫_ℂ=_
  rw [ContinuousLinearMap.adjoint_adjoint,hη a]
  change ⟪J (J.adjoint (f a (J (J.adjoint x)))),y⟫_ℂ=_
  rw [hproj x hx,←ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left,hproj y hy]

end Kadison.OperatorSystem

end

end
end

end OAI
