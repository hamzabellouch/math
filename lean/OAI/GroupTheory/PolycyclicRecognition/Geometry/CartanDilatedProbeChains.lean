import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeChainDilation

namespace OAI

/-! # Transporting actual probe chains to the contact pivot -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Exact dilation transports all measurable prefixes, generator amplitudes
and endpoints. The chain length and prefix radius are unchanged. -/
def BoxProbeChains.dilate
    (hbij : Function.Bijective F.ExpN)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E B : Set W) (hE : IsCompact E) (hne : E.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (w : W)
    (γ : M.Bases) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ
      ((M.supportIn T hunimod eW).weightSupport B) scale probe) :
    M.BoxProbeChains T F hunimod eW b₀ ((fun x => x + w) '' E) γ
      ((M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' B)) scale
      (fun n q => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
        M.bound_zero
        (cartanIdealWeightDilation T H (scale n • cartanHeightSection T H (eW.symm w)))
        (probe n q)) := by
  let h := fun n => scale n • cartanHeightSection T H (eW.symm w)
  let D := fun n => cartanIdealWeightDilation T H (h n)
  let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
    M.bound_zero (D n)
  have hS (n) (v : cartanRootIdeal H) :
      S n (F.ExpN (F.N.equiv v)) = F.ExpN (F.N.equiv (D n v)) :=
    integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbij dynkinN F.isExpN
      M.bound_zero (D n) v
  refine {
    length := P.length
    amplitude := P.amplitude
    prefixRadius := P.prefixRadius
    amplitude_ge_one := P.amplitude_ge_one
    prefixRadius_nonneg := P.prefixRadius_nonneg
    mode := P.mode
    coefficient := fun n q j => P.coefficient n q j *
      Real.exp (scale n * M.weight (P.mode n j) (cartanHeightSection T H (eW.symm w)))
    vertex := fun n q j => D n (P.vertex n q j)
    coefficient_measurable := fun n j => (P.coefficient_measurable n j).mul_const _
    vertex_measurable := ?_
    coefficient_bound := ?_
    vertex_zero := ?_
    vertex_last := ?_
    vertex_bound := ?_
    vertex_step := ?_ }
  · intro n j
    let A := b₀.equivFun.toLinearMap.comp ((D n).toLinearMap.comp b₀.equivFun.symm.toLinearMap)
    have hm := A.continuous_of_finiteDimensional.measurable.comp (P.vertex_measurable n j)
    have he : (fun q => A (b₀.equivFun (P.vertex n q j))) =
        (fun q => b₀.equivFun (D n (P.vertex n q j))) := by
      funext q
      change b₀.equivFun (D n (b₀.equivFun.symm (b₀.equivFun (P.vertex n q j)))) = _
      rw [LinearEquiv.symm_apply_apply]
    exact he ▸ hm
  · intro n q j
    exact M.probe_dilation_coefficient_bound T hunimod eW hE hne w (scale n)
      (P.coefficient n q j) P.amplitude (P.mode n j) (P.coefficient_bound n q j)
  · intro n q
    rw [P.vertex_zero, map_zero]
  · intro n q
    rw [← hS, P.vertex_last]
  · intro n q j
    change ‖(M.boxBasis T hunimod eW ((fun x => x + w) '' B) γ (scale n)).equivFun
      (D n (P.vertex n q j))‖ ≤ _
    rw [M.probe_dilation_coordinate_norm T hunimod eW hB hBne w γ (scale n)]
    exact P.vertex_bound n q j
  · intro n q j
    have hs := M.probe_dilation_generator_step T F.N.equiv F.ExpN F.isExpN hbij dynkinN
      (h n) (P.vertex n q j.castSucc) (P.vertex n q j.succ) (P.mode n j)
      (P.coefficient n q j) (P.vertex_step n q j)
    simpa only [h, map_smul, smul_eq_mul] using hs

end PolycyclicRecognition.CartanWordModel

end

end OAI
