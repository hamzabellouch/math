import OAI.Combinatorics.Progressions.Estimates.FastHorizontalFactorization

namespace OAI

section

namespace Erdos3

variable {σ G E H R : Type*} [Group G] [Field R]
  [AddCommGroup E] [Module R E] [AddCommGroup H] [Module R H]

theorem cocycle_kernel_reabsorption
    (ρ : G →* (E ≃ₗ[R] E)) (Y : G → σ → E)
    (hY : ∀ g h i, Y (g * h) i = Y g i + ρ g (Y h i))
    (P : E →ₗ[R] H) (hρ : ∀ g x, P (ρ g x) = P x)
    (U K : Submodule R H) (B a c : G) (S T : K →ₗ[R] E)
    (hST : S = (ρ B).toLinearMap.comp T)
    (hS : P.comp S = K.subtype) (hT : P.comp T = K.subtype)
    (small rational : σ → E) (k A C : σ → K)
    (hsystem : ∀ i, Y B i = small i + ρ B (rational i) + S (k i))
    (hsmall : ∀ i, P (small i) = 0) (hrational : ∀ i, P (rational i) = 0)
    (ha : ∀ i, P (Y a i) = (A i).val) (hc : ∀ i, P (Y c i) = (C i).val)
    (hkU : ∀ i, (k i).val ∈ U) (hAU : ∀ i, (A i).val ∈ U) (hCU : ∀ i, (C i).val ∈ U) :
    let B' := a⁻¹ * B * c⁻¹
    let S' := (ρ a).symm.toLinearMap.comp S
    let T' := (ρ c).toLinearMap.comp T
    let small' := fun i => (ρ a).symm (small i - Y a i) + S' (A i)
    let rational' := fun i => ρ c (rational i) - Y c i + T' (C i)
    let k' := fun i => k i - A i - C i
    a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp T' ∧
      P.comp S' = K.subtype ∧ P.comp T' = K.subtype ∧
      ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k' i) ∧
        P (small' i) = 0 ∧ P (rational' i) = 0 ∧ P (Y B' i) = (k' i).val ∧
        P (Y B' i) ∈ U ⊓ K := by
  intro B' S' T' small' rational' k'
  have hprod : a * B' * c = B := by dsimp [B']; group
  have haction (x : E) : ρ B x = ρ a (ρ B' (ρ c x)) := by
    rw [← hprod]
    exact linear_action_triple ρ a B' c x
  have hfac : S' = (ρ B').toLinearMap.comp T' :=
    linear_lift_remove (ρ a) (ρ c) (ρ B) (ρ B') haction S T hST
  have hhor := horizontal_lift_remove P (ρ a) (ρ c) (hρ a) (hρ c) S T K.subtype hS hT
  refine ⟨hprod, hfac, hhor.1, hhor.2, fun i => ?_⟩
  let rawSmall := (ρ a).symm (small i - Y a i)
  let rawRational := ρ c (rational i) - Y c i
  have htriple := linear_cocycle_triple ρ (fun g => Y g i)
    (fun g h => hY g h i) a B' c
  rw [hprod] at htriple
  have hraw : Y B' i = rawSmall + ρ B' rawRational + S' (k i) :=
    linear_derivative_remove (ρ a) (ρ c) (ρ B) (ρ B') haction
      (Y B i) (Y a i) (Y B' i) (Y c i) (small i) (rational i) (S (k i))
      htriple (hsystem i)
  have hnew : Y B' i = small' i + ρ B' (rational' i) + S' (k' i) := by
    have h := linear_derivative_absorb (ρ B').toLinearMap S' T' hfac
      (Y B' i) rawSmall rawRational (k i) (-A i) (-C i) hraw
    simp only [map_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
    exact h
  have hrawSmall : P rawSmall = -(A i).val := by
    have h := hρ a rawSmall
    change P (ρ a ((ρ a).symm (small i - Y a i))) = P rawSmall at h
    rw [LinearEquiv.apply_symm_apply, map_sub, hsmall, ha, zero_sub] at h
    exact h.symm
  have hrawRational : P rawRational = -(C i).val := by
    change P (ρ c (rational i) - Y c i) = _
    rw [map_sub, hρ, hrational, hc, zero_sub]
  have hs0 : P (small' i) = 0 := by
    change P (rawSmall + S' (A i)) = 0
    rw [map_add, hrawSmall, show P (S' (A i)) = (A i).val from DFunLike.congr_fun hhor.1 (A i)]
    exact neg_add_cancel _
  have hr0 : P (rational' i) = 0 := by
    change P (rawRational + T' (C i)) = 0
    rw [map_add, hrawRational, show P (T' (C i)) = (C i).val from DFunLike.congr_fun hhor.2 (C i)]
    exact neg_add_cancel _
  have hPB : P.comp (ρ B').toLinearMap = P := by
    apply LinearMap.ext
    intro x
    exact hρ B' x
  have hk : (k' i).val ∈ U := U.sub_mem (U.sub_mem (hkU i) (hAU i)) (hCU i)
  have hfinal := horizontal_derivative_of_zero_parts U K P (ρ B').toLinearMap hPB S'
    hhor.1 (Y B' i) (small' i) (rational' i) (k' i) hnew hs0 hr0 hk
  exact ⟨hnew, hs0, hr0, hfinal.1, hfinal.2⟩

theorem linear_absorption_preserves_projection {K Z : Type*}
    [AddCommGroup K] [Module R K] [AddCommGroup Z] [Module R Z]
    (Q : E →ₗ[R] Z) (S T : K →ₗ[R] E)
    (hS : Q.comp S = 0) (hT : Q.comp T = 0) (small rational : E) (ks kr : K) :
    Q (small + S ks) = Q small ∧ Q (rational + T kr) = Q rational := by
  have hs : Q (S ks) = 0 := DFunLike.congr_fun hS ks
  have ht : Q (T kr) = 0 := DFunLike.congr_fun hT kr
  simp only [map_add, hs, ht, add_zero, and_self]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
    (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF U)
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W (Subtype.val g) (Pi.single i 1))

include hU in
theorem realFast_kernel_reabsorption [DecidableEq σ]
    (B : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔)
    (hSR : S = (ρ B).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k A C : σ → K)
    (hsystem : ∀ i, Y B i = small i + ρ B (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) = 0) (hrational : ∀ i, 𝓟 (rational i) = 0)
    (hk : ∀ i, (k i).val ∈ 𝓤) (hA : ∀ i, (A i).val ∈ 𝓤) (hC : ∀ i, (C i).val ∈ 𝓤) :
    ∃ a B' c : 𝓖,
      a.val = F.realLayerOneCorrection e ω hF (fun i => (A i).val) ∧
      c.val = F.realLayerOneCorrection e ω hF (fun i => (C i).val) ∧
      (B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
        B'.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U) ∧
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) 0 = 0 ∧
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) (Finsupp.single i 1)) =
          (k i - A i - C i).val) ∧
      let S' := (ρ a).symm.toLinearMap.comp S
      let R' := (ρ c).toLinearMap.comp R
      let small' := fun i => (ρ a).symm (small i - Y a i) + S' (A i)
      let rational' := fun i => ρ c (rational i) - Y c i + R' (C i)
      a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp R' ∧
        (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
        ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k i - A i - C i) ∧
          𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧
          𝓟 (Y B' i) = (k i - A i - C i).val ∧ 𝓟 (Y B' i) ∈ 𝓤 ⊓ K := by
  let a := F.realFastLayerOneCorrection e ω hF U W hU (fun i => (A i).val) hA
  let c := F.realFastLayerOneCorrection e ω hF U W hU (fun i => (C i).val) hC
  have hdata := cocycle_kernel_reabsorption ρ Y
    (fun g h i => F.realFastCoefficientDirectionMap_mul W e ω hF g h (Pi.single i 1))
    𝓟 (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) W e ω hF)
    𝓤 K B a c S R hSR hS hR small rational k A C hsystem hsmall hrational
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hA i)
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hC i) hk hA hC
  have hpointwise : B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
      (a⁻¹ * B * c⁻¹).val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U := by
    intro hB
    let G := F.realPointwisePolynomialSubgroup e ω hF (fun _ : σ => 1) U
    exact G.mul_mem (G.mul_mem (G.inv_mem
      (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hA)) hB)
        (G.inv_mem (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hC))
  have hzeroa : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) a.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hzeroc : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) c.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hconst := F.realAdapted_factor_middle_constant (fun _ => 1) B.val a.val
    (a⁻¹ * B * c⁻¹).val c.val (congrArg Subtype.val hdata.1) hzeroa hzeroc
  have hzero' := hconst.trans hzero
  have hlinear (i : σ) : (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
        (Finsupp.single i 1)) = (k i - A i - C i).val := by
    have hd := F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i
      (a⁻¹ * B * c⁻¹).val.coord hzero'
    have he : 𝓟 (Y (a⁻¹ * B * c⁻¹) i) = (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
          (Finsupp.single i 1)) := hd
    exact he.symm.trans (hdata.2.2.2.2 i).2.2.2.1
  exact ⟨a, a⁻¹ * B * c⁻¹, c, rfl, rfl, hpointwise, hzero', hlinear, hdata⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
