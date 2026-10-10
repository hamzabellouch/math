import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportStrictInterior
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters

namespace OAI

/-! # Switching heights for every actual compact probe template -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem exists_probe_switching_height
    (b : Basis (Fin (finrank ℝ H)) ℝ H)
    {E V : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hV : IsOpen V) (hEV : E ⊆ V) (i : Fin M.letterCount) :
    ∃ z : Fin (finrank ℝ H) → ℝ,
      eW (heightProjection T.character (b.equivFun.symm z : L)) ∈ V ∧
      (M.supportIn T hunimod eW).weightSupport E i < M.weight i (b.equivFun.symm z) := by
  have hnz : (M.supportIn T hunimod eW).weight i ≠ 0 := by
    intro hz
    apply M.weight_nonzero i
    funext h
    have he := congrArg (fun f : W →ₗ[ℝ] ℝ =>
      f (eW (heightProjection T.character (h : L)))) hz
    simpa [supportIn, SupportDatum.transport, supportDatum_weight,
      cartanHeightWeight_projection] using he
  obtain ⟨w, hw, hs⟩ := (M.supportIn T hunimod eW).exists_weightSupport_lt_on_open
    hE hne hV hEV i hnz
  obtain ⟨v, hv⟩ := (eW.surjective.comp (cartan_height_surjective T H)) w
  change eW (heightProjection T.character (v : L)) = w at hv
  refine ⟨b.equivFun v, ?_, ?_⟩
  · simpa only [LinearEquiv.symm_apply_apply, hv] using hw
  · simp only [LinearEquiv.symm_apply_apply]
    have he : (M.supportIn T hunimod eW).weight i w = M.weight i v := by
      rw [← hv]
      simp [supportIn, SupportDatum.transport, supportDatum_weight,
        cartanHeightWeight_projection]
    exact hs.trans_eq he

end PolycyclicRecognition.CartanWordModel

end

end OAI
