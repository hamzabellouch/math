import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter

namespace Kadison

namespace HilbertTensor

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

noncomputable def slicePre (ℓ : E →L[𝕜] 𝕜) : E ⊗[𝕜] F →L[𝕜] F :=
  (TensorProduct.lidIsometry 𝕜 F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (TensorProduct.mapL ℓ (ContinuousLinearMap.id 𝕜 F))

@[simp] lemma slicePre_tmul (ℓ : E →L[𝕜] 𝕜) (x : E) (y : F) :
    slicePre ℓ (x ⊗ₜ[𝕜] y) = ℓ x • y := by simp [slicePre]

lemma norm_slicePre_le (ℓ : E →L[𝕜] 𝕜) : ‖slicePre (F := F) ℓ‖ ≤ ‖ℓ‖ := by
  apply (slicePre (F := F) ℓ).opNorm_le_bound (norm_nonneg ℓ)
  intro x
  change ‖TensorProduct.lidIsometry 𝕜 F (TensorProduct.mapL ℓ (.id 𝕜 F) x)‖ ≤ _
  rw [(TensorProduct.lidIsometry 𝕜 F).norm_map]
  calc
    _ ≤ ‖TensorProduct.mapL ℓ (.id 𝕜 F)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖ℓ‖ * ‖ContinuousLinearMap.id 𝕜 F‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le _ _) (norm_nonneg _)
    _ ≤ ‖ℓ‖ * ‖x‖ := by
      simpa using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := F)) (norm_nonneg ℓ))
        (norm_nonneg x)

noncomputable def slice (ℓ : E →L[𝕜] 𝕜) :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion F := (slicePre (F := F) ℓ).completion

@[simp] lemma slice_coe (ℓ : E →L[𝕜] 𝕜) (x : E ⊗[𝕜] F) :
    slice ℓ (x : Completion (E ⊗[𝕜] F)) = ((slicePre (F := F) ℓ x : F) : Completion F) := by
  simp [slice]

lemma norm_slice_le (ℓ : E →L[𝕜] 𝕜) : ‖slice (F := F) ℓ‖ ≤ ‖ℓ‖ := by
  apply (slice (F := F) ℓ).opNorm_le_bound (norm_nonneg ℓ)
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x =>
    simpa using (ContinuousLinearMap.le_opNorm (slicePre (F := F) ℓ) x).trans
      (mul_le_mul_of_nonneg_right (norm_slicePre_le ℓ) (norm_nonneg x))

lemma tendsto_slice_zero {ι : Type*} {l : Filter ι} (ℓ : ι → E →L[𝕜] 𝕜)
    {C : NNReal} (hC : ∀ i, ‖ℓ i‖ ≤ C)
    (hℓ : ∀ x : E, Tendsto (fun i => ℓ i x) l (𝓝 0))
    (y : Completion (E ⊗[𝕜] F)) :
    Tendsto (fun i => slice (F := F) (ℓ i) y) l (𝓝 0) := by
  induction y using Completion.induction_on with
  | hp =>
    apply Equicontinuous.isClosed_setOfPred_tendsto _ continuous_const
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ C
    intro i
    apply (slice (F := F) (ℓ i)).lipschitzWith.weaken
    exact (norm_slice_le (F := F) (ℓ i)).trans (hC i)
  | ih y =>
    induction y using TensorProduct.inductionOn with
    | tmul x y =>
      simpa only [slice_coe, slicePre_tmul, Completion.coe_smul, zero_smul] using
        (hℓ x).smul (tendsto_const_nhds (x := (y : Completion F)))
    | add x y hx hy =>
      simpa only [Completion.coe_add, map_add, add_zero] using hx.add hy

lemma tendsto_orthonormal_inner_zero {v : ℕ → E} (hv : Orthonormal 𝕜 v) (x : E) :
    Tendsto (fun n => inner 𝕜 (v n) x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (hv.inner_products_summable x).tendsto_atTop_zero
  have hs := (Real.continuous_sqrt.tendsto 0).comp h
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

lemma norm_completion (f : E →L[𝕜] F) : ‖f.completion‖ = ‖f‖ := by
  apply le_antisymm
  · apply f.completion.opNorm_le_bound (norm_nonneg f)
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa using f.le_opNorm x
  · apply f.opNorm_le_bound (norm_nonneg f.completion)
    intro x
    simpa using f.completion.le_opNorm (x : Completion E)

variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

lemma norm_mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    ‖TensorProduct.mapL f g‖ = ‖f‖ * ‖g‖ := by
  apply le_antisymm (TensorProduct.norm_mapL_le f g)
  have hxy (x : E) (y : G) :
      ‖f x‖ * ‖g y‖ ≤ ‖TensorProduct.mapL f g‖ * (‖x‖ * ‖y‖) := by
    simpa only [TensorProduct.mapL_tmul, TensorProduct.norm_tmul] using
      (TensorProduct.mapL f g).le_opNorm (x ⊗ₜ[𝕜] y)
  have hy (y : G) : ‖f‖ * ‖g y‖ ≤ ‖TensorProduct.mapL f g‖ * ‖y‖ := by
    have h := ((‖g y‖ : 𝕜) • f).opNorm_le_bound
      (mul_nonneg (norm_nonneg (TensorProduct.mapL f g)) (norm_nonneg y)) (fun x => ?_)
    · simpa only [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
        mul_comm ‖g y‖ ‖f‖] using h
    · simpa only [FunLike.coe_smul, Pi.smul_apply, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg _), mul_comm ‖g y‖ ‖f x‖,
        mul_assoc, mul_comm ‖y‖ ‖x‖] using hxy x y
  have h := ((‖f‖ : 𝕜) • g).opNorm_le_bound
    (norm_nonneg (TensorProduct.mapL f g)) (fun y => ?_)
  · simpa only [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] using h
  · simpa only [FunLike.coe_smul, Pi.smul_apply, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)] using hy y

noncomputable def map (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] H) :=
  (TensorProduct.mapL f g).completion

lemma norm_map (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    ‖map f g‖ = ‖f‖ * ‖g‖ := by rw [map, norm_completion, norm_mapL]

@[simp] lemma map_coe_tmul (f : E →L[𝕜] F) (g : G →L[𝕜] H) (x : E) (y : G) :
    map f g ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) : Completion (E ⊗[𝕜] G)) =
      ((f x ⊗ₜ[𝕜] g y : F ⊗[𝕜] H) : Completion (F ⊗[𝕜] H)) := by
  simp [map]

lemma completion_ext {f g : Completion (E ⊗[𝕜] G) →L[𝕜] H}
    (h : ∀ (x : E) (y : G), f ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) : Completion _) =
      g ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) : Completion _)) : f = g := by
  ext z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simp only [Completion.coe_add, map_add, hx, hy]

lemma map_add_left (f₁ f₂ : E →L[𝕜] F) (g : G →L[𝕜] H) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  apply completion_ext
  intro x y
  simp [TensorProduct.add_tmul, Completion.coe_add]

lemma map_add_right (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  apply completion_ext
  intro x y
  simp [TensorProduct.tmul_add, Completion.coe_add]

lemma map_sub_right (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    map f (g₁ - g₂) = map f g₁ - map f g₂ := by
  apply completion_ext
  intro x y
  simp [TensorProduct.tmul_sub, Completion.coe_sub]

lemma map_smul_left (c : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    map (c • f) g = c • map f g := by
  apply completion_ext
  intro x y
  simp [← TensorProduct.smul_tmul', Completion.coe_smul]

lemma map_smul_right (c : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    map f (c • g) = c • map f g := by
  apply completion_ext
  intro x y
  simp [TensorProduct.tmul_smul, Completion.coe_smul]

lemma map_mul (f₁ f₂ : E →L[𝕜] E) (g₁ g₂ : F →L[𝕜] F) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ := by
  apply completion_ext
  intro x y
  simp

@[simp] lemma map_one_one : map (1 : E →L[𝕜] E) (1 : F →L[𝕜] F) = 1 := by
  apply completion_ext
  intro x y
  simp

lemma hankel_commutator_norm (T H : E →L[𝕜] E) (B S : F →L[𝕜] F) (u : 𝕜) :
    ‖map (1 : E →L[𝕜] E) B * (u • (map T (1 : F →L[𝕜] F) + map H S)) -
      (u • (map T (1 : F →L[𝕜] F) + map H S)) * map (1 : E →L[𝕜] E) B‖ =
      ‖u‖ * ‖H‖ * ‖B * S - S * B‖ := by
  have h : map (1 : E →L[𝕜] E) B * (map T (1 : F →L[𝕜] F) + map H S) -
      (map T (1 : F →L[𝕜] F) + map H S) * map (1 : E →L[𝕜] E) B =
      map H (B * S - S * B) := by
    rw [mul_add, add_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    simp only [one_mul, mul_one, map_sub_right]
    abel
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, h, norm_smul, norm_map, mul_assoc]

lemma tendsto_orthonormal_slice_zero {v : ℕ → E} (hv : Orthonormal 𝕜 v)
    (y : Completion (E ⊗[𝕜] F)) :
    Tendsto (fun n => slice (F := F) (innerSL 𝕜 (v n)) y) atTop (𝓝 0) := by
  apply tendsto_slice_zero (C := 1)
  · intro n
    simp only [innerSL_apply_norm, hv.norm_eq_one, NNReal.coe_one, le_refl]
  · exact tendsto_orthonormal_inner_zero hv

end HilbertTensor

end Kadison
end

end OAI
