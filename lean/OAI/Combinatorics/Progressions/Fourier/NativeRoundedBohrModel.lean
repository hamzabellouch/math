import OAI.Combinatorics.Progressions.Estimates.NativeRoundedCyclicModel

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

theorem rounded_graph_bohr_model {I : Type*} [Fintype I]
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
        (L : ZMod (Q : ℕ) → (ZMod N × (I → ZMod M))) (S : CyclicBohr.Set (Q : ℕ)),
        B.Nonempty ∧ B = (additiveGraph J v).image f ∧ B.card = J.card ∧
        IsAddFreimanIso 8 (additiveGraph J v : Set _) (B : Set _) f ∧
        (Q : ℝ) ≤ 2 * C ^ 16 * H.card ∧
        S.IsRankRegular ∧ 0 < S.radius ∧ S.radius ≤ 1 ∧
        (S.rank : ℝ) ≤ 1 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        Real.exp (-(quarticBogolyubovConstant * (z + 1))) ≤ S.radius ∧
        Real.exp (-(quarticBogolyubovVolumeConstant * (z + 1) ^ 5)) * (Q : ℝ) ≤
          (S.carrier.card : ℝ) ∧ S.carrier ⊆ 2 • B - 2 • B ∧
        Set.MapsTo L (S.carrier : Set _)
          (2 • additiveGraph J v - 2 • additiveGraph J v : Finset _) ∧
        Set.InjOn L (S.carrier : Set _) ∧ L 0 = 0 ∧
        ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, ∀ w ∈ S.carrier, ∀ t ∈ S.carrier,
          L x + L y = L w + L t ↔ x + y = w + t := by
  intro K C z v
  classical
  obtain ⟨J, hJH, hJ, hsize, Q, B, f, L, hQ, hB, hBimage, hBcard, hf,
      hQsize, hdensity, hmap, hinj, hzero, hadd⟩ := D.rounded_graph_cyclic_model a c M l hsmall hnear
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density P (Fintype.card I)).trans hdensity
  obtain ⟨S, hSreg, hSpos, hSupper, hSrank, hSwidth, hSvolume, hSsub⟩ :=
    exists_quartic_bogolyubov_with_volume B (roundedModelLogBudget_nonneg P _) hdensity'
  refine ⟨J, hJH, hJ, hsize, ⟨Q, hQ⟩, B, f, L, S, hB, hBimage, hBcard, hf,
    hQsize, hSreg, hSpos, hSupper, hSrank, hSwidth, hSvolume, hSsub,
    (fun x hx => hmap (hSsub hx)), hinj.mono hSsub, hzero, ?_⟩
  intro x hx y hy w hw t ht
  exact hadd x (hSsub hx) y (hSsub hy) w (hSsub hw) t (hSsub ht)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
