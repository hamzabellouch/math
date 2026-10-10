import OAI.Analysis.KadisonKastler.ModularPhaseFunctionalCalculus
import OAI.Analysis.KadisonKastler.StrongContractionLimits

namespace OAI

/-! # The strong limit of the regularized modular groups

The weighted estimates make the approximants Cauchy on a dense range.
Their contraction bounds extend convergence to every vector. Group laws
and inverse operators then pass to the strong limit.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def modularRegularizationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem modularRegularizationScale_pos (n : ℕ) : 0 < modularRegularizationScale n := by
  unfold modularRegularizationScale
  positivity

theorem modularRegularizationScale_tendsto :
    Tendsto modularRegularizationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def modularApproximation (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (n : ℕ) (t : ℝ) : H →L[ℂ] H :=
  regularizedModularGroup M J Ω (modularRegularizationScale n) (Multiplicative.ofAdd t)

theorem modularApproximation_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (n : ℕ) (t : ℝ) :
    ‖modularApproximation M J Ω n t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [modularApproximation, Unitary.norm_map, one_mul, le_refl]

theorem modularApproximation_cutoff_cauchy (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (t : ℝ) (x : H) :
    CauchySeq (fun n => modularApproximation M J Ω n t (graphResolventCutoff M J Ω x)) := by
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  let C := |t| * ‖x‖
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp modularRegularizationScale_tendsto.cauchySeq
    (η / (C + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hd := hN m hm n hn
  have hb := regularizedModularGroup_cutoff_apply_bound (M := M) J Ω t
    (modularRegularizationScale_pos m) (modularRegularizationScale_pos n) x
  have hh : C * dist (modularRegularizationScale m) (modularRegularizationScale n) ≤
      (C + 1) * dist (modularRegularizationScale m) (modularRegularizationScale n) := by
    gcongr
    linarith
  have hl : (C + 1) * dist (modularRegularizationScale m) (modularRegularizationScale n) < η := by
    have := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hd
    linarith
  rw [dist_eq_norm]
  calc
    _ ≤ C * dist (modularRegularizationScale m) (modularRegularizationScale n) := by
      simpa only [modularApproximation, C, Real.dist_eq, mul_assoc, mul_left_comm,
        mul_comm] using hb
    _ ≤ _ := hh
    _ < _ := hl

variable [SeparableSpace H]

theorem exists_modularStrongLimit (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ 1 ∧
      ∀ x, Tendsto (fun n => modularApproximation M J Ω n t x) atTop (𝓝 (T x)) := by
  obtain ⟨ξ, hξ⟩ := exists_dense_seq H
  have hd := (graphResolventCutoff_dense J Ω hsep hcyc).comp hξ
    (graphResolventCutoff M J Ω).continuous
  exact exists_strong_limit_of_dense_contractions _ hd
    (fun n => modularApproximation M J Ω n t)
    (fun n => modularApproximation_contracts J Ω n t)
    (fun j => modularApproximation_cutoff_cauchy J Ω t (ξ j))

def modularStrongLimit (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) : H →L[ℂ] H :=
  (exists_modularStrongLimit J Ω hsep hcyc t).choose

theorem modularStrongLimit_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    ‖modularStrongLimit J Ω hsep hcyc t‖ ≤ 1 :=
  (exists_modularStrongLimit J Ω hsep hcyc t).choose_spec.1

theorem modularApproximation_tendsto (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (x : H) :
    Tendsto (fun n => modularApproximation M J Ω n t x) atTop
      (𝓝 (modularStrongLimit J Ω hsep hcyc t x)) :=
  (exists_modularStrongLimit J Ω hsep hcyc t).choose_spec.2 x

theorem modularStrongLimit_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    modularStrongLimit J Ω hsep hcyc 0 = 1 := by
  ext x
  have ht := modularApproximation_tendsto J Ω hsep hcyc 0 x
  have he (n : ℕ) : modularApproximation M J Ω n 0 x = x := by
    change (regularizedModularGroup M J Ω (modularRegularizationScale n) 1 : H →L[ℂ] H) x = x
    rw [map_one]
    rfl
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem modularStrongLimit_add (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (s t : ℝ) :
    modularStrongLimit J Ω hsep hcyc (s + t) =
      modularStrongLimit J Ω hsep hcyc s * modularStrongLimit J Ω hsep hcyc t := by
  ext x
  have ht := tendsto_mul_contractions (fun n => modularApproximation M J Ω n s)
    (fun n => modularApproximation M J Ω n t) _ _
    (fun n => modularApproximation_contracts J Ω n s)
    (modularApproximation_tendsto J Ω hsep hcyc s)
    (modularApproximation_tendsto J Ω hsep hcyc t) x
  have he (n : ℕ) : modularApproximation M J Ω n s * modularApproximation M J Ω n t =
      modularApproximation M J Ω n (s + t) := by
    exact (congrArg (fun u : unitary (H →L[ℂ] H) => u.val)
      ((regularizedModularGroup M J Ω (modularRegularizationScale n)).map_mul
        (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))).symm
  simp only [he] at ht
  exact tendsto_nhds_unique (modularApproximation_tendsto J Ω hsep hcyc (s + t) x) ht

theorem modularStrongLimit_norm_map (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (x : H) :
    ‖modularStrongLimit J Ω hsep hcyc t x‖ = ‖x‖ := by
  have ht := (modularApproximation_tendsto J Ω hsep hcyc t x).norm
  have he (n : ℕ) : ‖modularApproximation M J Ω n t x‖ = ‖x‖ :=
    Unitary.norm_map _ x
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- The limiting group consists of actual unitaries, with inverse at negative time. -/
def modularStrongUnitary (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) : unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm
    { (modularStrongLimit J Ω hsep hcyc t).toLinearMap with
      invFun := modularStrongLimit J Ω hsep hcyc (-t)
      left_inv := fun x => by
        change (modularStrongLimit J Ω hsep hcyc (-t) *
          modularStrongLimit J Ω hsep hcyc t) x = x
        rw [← modularStrongLimit_add, neg_add_cancel, modularStrongLimit_zero]
        rfl
      right_inv := fun x => by
        change (modularStrongLimit J Ω hsep hcyc t *
          modularStrongLimit J Ω hsep hcyc (-t)) x = x
        rw [← modularStrongLimit_add, add_neg_cancel, modularStrongLimit_zero]
        rfl
      norm_map' := modularStrongLimit_norm_map J Ω hsep hcyc t }

theorem modularStrongUnitary_coe (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    (modularStrongUnitary J Ω hsep hcyc t : H →L[ℂ] H) =
      modularStrongLimit J Ω hsep hcyc t := rfl

def modularStrongGroup (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) : Multiplicative ℝ →* unitary (H →L[ℂ] H) where
  toFun t := modularStrongUnitary J Ω hsep hcyc t.toAdd
  map_one' := by
    apply Subtype.ext
    exact modularStrongLimit_zero J Ω hsep hcyc
  map_mul' s t := by
    apply Subtype.ext
    exact modularStrongLimit_add J Ω hsep hcyc s.toAdd t.toAdd

end

end KadisonKastler

end OAI
