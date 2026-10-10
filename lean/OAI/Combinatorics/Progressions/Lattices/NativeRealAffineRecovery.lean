import OAI.Combinatorics.Progressions.Estimates.NativeRoundedHomModel

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

theorem rounded_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε : ℝ}
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => roundedCoefficient M l (a h)
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ)
        (Φ : (Fin r → ℤ) →+ (ZMod N × (I → ZMod M)))
        (base : ZMod N × (I → ZMod M)),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧ (h, v h) = base + Φ x := by
  intro K z δ v
  classical
  obtain ⟨J, hJH, hJ, hsize, Q, B, f, T, Φ, hB, hBimage, hBcard, hf,
      hQsize, hTdim, hT, hTsub, hTsize, hmap, hinj, hcard⟩ :=
    D.rounded_graph_coordinate_model a c M l hsmall hnear
  let A := additiveGraph J v
  let S := T.coefficientBox.image Φ
  have hS : S ⊆ 2 • A - 2 • A := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hmap hx
  have hbound : ((A - S).card : ℝ) ≤ (Q : ℝ) := by
    have hb := FreimanModel.card_sub_le_of_fourfold_subset A S f
      (hf.mono (hmn := by decide)) hS
    have hb' : (A - S).card ≤ (Q : ℕ) := by simpa only [ZMod.card] using hb
    exact_mod_cast hb'
  have hSsize : δ * (Q : ℝ) ≤ (S.card : ℝ) := by
    change δ * (Q : ℝ) ≤ ((T.coefficientBox.image Φ).card : ℝ)
    rw [hcard]
    exact hTsize
  obtain ⟨base, _hbase, F, hFA, hF, hFsize, hFsub⟩ := exists_dense_translate A S
    (hJ.image _) (Real.exp_pos _) (by exact_mod_cast Q.pos) hbound hSsize
  let J' := F.image Prod.fst
  have hgraph : additiveGraph J' v = F := additiveGraph_image_fst J v F hFA
  have hFcard : F.card = J'.card := by rw [← hgraph, additiveGraph_card]
  have hJ' : J' ⊆ H := by
    intro h hh
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hh
    exact hJH ((mem_additiveGraph_iff J v y).mp (hFA hy)).1
  have hretain : δ * (J.card : ℝ) ≤ (J'.card : ℝ) := by
    simpa only [A, additiveGraph_card, hFcard] using hFsize
  refine ⟨J', hJ', hF.image _, ?_, T.rank, T.radius, Φ, base, hTdim, ?_, ?_⟩
  · calc
      _ ≤ δ * (16 ^ (Fintype.card I + 2) * (J.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
      _ = 16 ^ (Fintype.card I + 2) * (δ * J.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro x hx y hy hxy
    exact hinj (T.mem_coefficientBox_iff_abs_le.mpr hx)
      (T.mem_coefficientBox_iff_abs_le.mpr hy) hxy
  · intro h hh
    have hhF : (h, v h) ∈ F := by
      rw [← hgraph, mem_additiveGraph_iff]
      exact ⟨hh, rfl⟩
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp (hFsub (h, v h) hhF)
    refine ⟨x, T.mem_coefficientBox_iff_abs_le.mp hx, ?_⟩
    rw [heq]
    abel

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
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

theorem unrounded_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] (hl : 0 < l) {ε : ℝ}
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (ξ : (Fin r → ℤ) →+ ZMod N)
        (h₀ : ZMod N) (α : I → ℝ) (β : Fin r → I → ℝ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l)) ∧
        (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l)) ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + ξ x ∧
          ∃ q ∈ realDenominatorGrid l,
            ‖a h - (α + ∑ j, (x j : ℝ) • β j) - q‖ ≤ 1 / ((M : ℝ) * l) := by
  intro K z δ
  obtain ⟨J', hJH, hJ, hsize, r, R, Φ, base, hrank, _hinj, hrepr⟩ :=
    D.rounded_graph_affine_model a c M l hsmall hnear
  let ξ := (AddMonoidHom.fst (ZMod N) (I → ZMod M)).comp Φ
  let ψ := (AddMonoidHom.snd (ZMod N) (I → ZMod M)).comp Φ
  refine ⟨J', hJH, hJ, hsize, r, R, ξ, base.1, finiteCoefficientLift l base.2,
    (fun j => finiteCoefficientLift l (ψ (Pi.single j 1))), hrank, ?_, ?_, ?_⟩
  · exact finiteCoefficientLift_mem_Ico l hl base.2
  · intro j
    exact finiteCoefficientLift_mem_Ico l hl (ψ (Pi.single j 1))
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    refine ⟨x, hx, ?_, ?_⟩
    · exact congrArg Prod.fst heq
    · exact exists_unrounded_affine l hl base.2 ψ x (a h) (congrArg Prod.snd heq)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
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

theorem real_affine_recovery {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : ℕ) (hl : 0 < l) {ε : ℝ} (hε : 0 < ε)
    (hsmall : 2 * (l : ℝ) * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (ξ : (Fin r → ℤ) →+ ZMod N)
        (h₀ : ZMod N) (α : I → ℝ) (β : Fin r → I → ℝ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l)) ∧
        (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l)) ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + ξ x ∧
          ∃ q ∈ realDenominatorGrid l,
            ‖a h - (α + ∑ j, (x j : ℝ) • β j) - q‖ ≤ 2 * ε := by
  intro K z δ
  obtain ⟨M, hM, hMsmall, hMerror⟩ := exists_rounding_modulus_with_recovery l hl hε hsmall
  let _ : NeZero M := ⟨hM.ne'⟩
  obtain ⟨J', hJH, hJ, hsize, r, R, ξ, h₀, α, β, hrank, hα, hβ, hrepr⟩ :=
    D.unrounded_affine_model a c M l hl hMsmall hnear
  refine ⟨J', hJH, hJ, hsize, r, R, ξ, h₀, α, β, hrank, hα, hβ, ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, q, hq, herr⟩ := hrepr h hh
  exact ⟨x, hx, hspace, q, hq, herr.trans hMerror⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
