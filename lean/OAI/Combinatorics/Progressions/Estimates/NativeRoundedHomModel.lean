import OAI.Combinatorics.Progressions.Fourier.NativeRoundedBohrModel

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem rounded_graph_progression_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε : ℝ}
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let C := (2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)
    let z := roundedModelLogBudget P (Fintype.card I)
    let v := fun h => roundedCoefficient M l (a h)
    ∃ J ⊆ H, J.Nonempty ∧
      (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J.card : ℝ) ∧
      ∃ (Q : ℕ+) (B : Finset (ZMod (Q : ℕ)))
        (f : (ZMod N × (I → ZMod M)) → ZMod (Q : ℕ))
        (L : ZMod (Q : ℕ) → (ZMod N × (I → ZMod M)))
        (T : BohrProgression.CyclicCenteredGAP (Q : ℕ)),
        B.Nonempty ∧ B = (additiveGraph J v).image f ∧ B.card = J.card ∧
        IsAddFreimanIso 8 (additiveGraph J v : Set _) (B : Set _) f ∧
        (Q : ℝ) ≤ 2 * C ^ 16 * H.card ∧
        (T.rank : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        T.Proper ∧ T.carrier ⊆ 2 • B - 2 • B ∧
        Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8)) * (Q : ℝ) ≤
          (T.carrier.card : ℝ) ∧
        Set.MapsTo L (T.carrier : Set _)
          (2 • additiveGraph J v - 2 • additiveGraph J v : Finset _) ∧
        Set.InjOn L (T.carrier : Set _) ∧ L 0 = 0 ∧
        ∀ x ∈ T.carrier, ∀ y ∈ T.carrier, ∀ w ∈ T.carrier, ∀ t ∈ T.carrier,
          L x + L y = L w + L t ↔ x + y = w + t := by
  intro K C z v
  obtain ⟨J, hJH, hJ, hsize, Q, B, f, L, S, hB, hBimage, hBcard, hf,
      hQsize, _hSreg, hSpos, hSupper, hSrank, hSwidth, _hSvolume, hSsub,
      hmap, hinj, hzero, hadd⟩ := D.rounded_graph_bohr_model a c M l hsmall hnear
  obtain ⟨T, hTdim, hT, hTS, hTsize⟩ := BohrProgression.exists_proper_progression_of_quartic_bounds
    S quarticBogolyubovConstant_pos.le (roundedModelLogBudget_nonneg P _)
    hSpos hSupper hSrank hSwidth
  refine ⟨J, hJH, hJ, hsize, Q, B, f, L, T, hB, hBimage, hBcard, hf,
    hQsize, hTdim, hT, hTS.trans hSsub, hTsize,
    (fun x hx => hmap (hTS hx)), hinj.mono hTS, hzero, ?_⟩
  intro x hx y hy w hw t ht
  exact hadd x (hTS hx) y (hTS hy) w (hTS hw) t (hTS ht)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem rounded_graph_coordinate_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε : ℝ}
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let C := (2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)
    let z := roundedModelLogBudget P (Fintype.card I)
    let v := fun h => roundedCoefficient M l (a h)
    ∃ J ⊆ H, J.Nonempty ∧
      (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J.card : ℝ) ∧
      ∃ (Q : ℕ+) (B : Finset (ZMod (Q : ℕ)))
        (f : (ZMod N × (I → ZMod M)) → ZMod (Q : ℕ))
        (T : BohrProgression.CyclicCenteredGAP (Q : ℕ))
        (Φ : (Fin T.rank → ℤ) →+ (ZMod N × (I → ZMod M))),
        B.Nonempty ∧ B = (additiveGraph J v).image f ∧ B.card = J.card ∧
        IsAddFreimanIso 8 (additiveGraph J v : Set _) (B : Set _) f ∧
        (Q : ℝ) ≤ 2 * C ^ 16 * H.card ∧
        (T.rank : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        T.Proper ∧ T.carrier ⊆ 2 • B - 2 • B ∧
        Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8)) * (Q : ℝ) ≤
          (T.carrier.card : ℝ) ∧
        Set.MapsTo Φ (T.coefficientBox : Set _)
          (2 • additiveGraph J v - 2 • additiveGraph J v : Finset _) ∧
        Set.InjOn Φ (T.coefficientBox : Set _) ∧
        (T.coefficientBox.image Φ).card = T.carrier.card := by
  intro K C z v
  classical
  obtain ⟨J, hJH, hJ, hsize, Q, B, f, L, T, hB, hBimage, hBcard, hf,
      hQsize, hTdim, hT, hTsub, hTsize, hmap, hinj, hzero, hadd⟩ :=
    D.rounded_graph_progression_model a c M l hsmall hnear
  have hpair (x y z t : T.Param)
      (h : T.eval x + T.eval y = T.eval z + T.eval t) :
      L (T.eval x) + L (T.eval y) = L (T.eval z) + L (T.eval t) :=
    (hadd _ (T.eval_mem_carrier x) _ (T.eval_mem_carrier y)
      _ (T.eval_mem_carrier z) _ (T.eval_mem_carrier t)).mpr h
  let Φ := T.freimanHom L
  refine ⟨J, hJH, hJ, hsize, Q, B, f, T, Φ, hB, hBimage, hBcard, hf,
    hQsize, hTdim, hT, hTsub, hTsize, ?_, T.freimanHom_injOn hT L hinj hzero hpair, ?_⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := T.mem_coefficientBox.mp hz
    change T.freimanHom L (T.coeff x) ∈ _
    rw [T.freimanHom_coeff L hzero hpair]
    exact hmap (T.eval_mem_carrier x)
  · rw [T.image_freimanHom L hzero hpair]
    exact Finset.card_image_of_injOn hinj

end Erdos3.NativeRankRelation.CommonData

end

end OAI
