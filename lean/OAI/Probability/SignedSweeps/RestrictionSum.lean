import OAI.Probability.SignedSweeps.TraceDecomposition

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
variable {G E F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

def mixedConjugationSum (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F := ∑ g, (σ g).comp (T.comp (ρ g⁻¹))

lemma mixedConjugationSum_intertwines {G E F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E)
    (σ : Representation ℂ G F) (T : E →ₗ[ℂ] F) (h : G) (x : E) :
    mixedConjugationSum ρ σ T (ρ h x) = σ h (mixedConjugationSum ρ σ T x) := by
  have he := Equiv.sum_comp (Equiv.mulLeft h)
    (fun g : G => σ g (T (ρ g⁻¹ (ρ h x))))
  change (∑ g, σ (h * g) (T (ρ (h * g)⁻¹ (ρ h x)))) = _ at he
  have hi : ρ h⁻¹ (ρ h x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hi]

lemma matrixCoefficient_inner_eq_zero (ρ : Representation ℂ G E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ σ, f = 0) (v x : E) (w y : F) :
    inner ℂ (matrixCoefficient σ w y) (matrixCoefficient ρ v x) = 0 := by
  let T : E →ₗ[ℂ] F := (InnerProductSpace.rankOne ℂ w v).toLinearMap
  let A : Representation.IntertwiningMap ρ σ :=
    (mixedConjugationSum ρ σ T).intertwiningMap_of_isIntertwiningMap ρ σ
      (mixedConjugationSum_intertwines ρ σ T)
  have hz : mixedConjugationSum ρ σ T x = 0 :=
    congrArg (fun f : Representation.IntertwiningMap ρ σ => f x) (hn A)
  calc
    _ = inner ℂ y (mixedConjugationSum ρ σ T x) := by
      rw [PiLp.inner_apply, mixedConjugationSum, LinearMap.sum_apply, inner_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [matrixCoefficient_apply, RCLike.inner_apply, LinearMap.comp_apply,
        T, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
      rw [map_smul, inner_smul_right, inner_conj_symm]
      congr 1
      simpa only [inv_inv] using representation_inner_inverse σ hσ g⁻¹ y w
    _ = 0 := by rw [hz, inner_zero_right]

lemma bilateral_matrixCoefficient {G F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (σ : Representation ℂ G F)
    (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (a b : G) (w y : F) :
    bilateralRepresentation (a, b) (matrixCoefficient σ w y) =
      matrixCoefficient σ (σ b w) (σ a y) := by
  ext g
  rw [bilateralRepresentation_apply, matrixCoefficient_apply, matrixCoefficient_apply,
    representation_inner_inverse σ hσ]
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, inv_inv]

lemma subgroup_coefficient_orthogonal (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ (σ.comp H.subtype), f = 0)
    (v x : E) (w y : F) :
    inner ℂ (subgroupExtension H (normalizedCoefficient ρ v x))
      (matrixCoefficient σ w y) = 0 := by
  rw [subgroupExtension_inner]
  change inner ℂ (normalizedCoefficient ρ v x) (matrixCoefficient (σ.comp H.subtype) w y) = 0
  rw [normalizedCoefficient, LinearMap.smul_apply, inner_smul_left]
  have he := matrixCoefficient_inner_eq_zero ρ (σ.comp H.subtype)
    (fun h => hσ h) hn v x w y
  have hh : inner ℂ (matrixCoefficient ρ v x) (matrixCoefficient (σ.comp H.subtype) w y) = 0 := by
    rw [← inner_conj_symm, he, map_zero]
  rw [hh, mul_zero]

lemma subgroupCoefficientProjection_kills (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ (σ.comp H.subtype), f = 0)
    (w y : F) :
    subgroupCoefficientProjection H ρ (matrixCoefficient σ w y) = 0 := by
  apply ((subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_apply_eq_zero_iff).mpr
  rw [Submodule.mem_orthogonal]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨⟨a, b⟩, v, x⟩, rfl⟩ := hz
    change inner ℂ (bilateralRepresentation (a, b)
      (subgroupExtension H (normalizedCoefficient ρ v x))) (matrixCoefficient σ w y) = 0
    rw [representation_inner_inverse (bilateralRepresentation (G := G))
      (bilateralRepresentation_norm (G := G)) (a,b),
      show (a,b)⁻¹ = (a⁻¹,b⁻¹) by rfl, bilateral_matrixCoefficient σ hσ]
    exact subgroup_coefficient_orthogonal H ρ σ hσ hn v x _ _
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul c x _ hx => simp [inner_smul_left, hx]

lemma supportedCoefficients_kills (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ (σ.comp H.subtype), f = 0)
    (f : G → ℂ) : coefficientAction σ (supportedCoefficients H ρ f) = 0 := by
  ext y
  apply ext_inner_left ℂ
  intro w
  have he := matrixCoefficient_action σ w (supportedCoefficients H ρ f) y
  rw [supportedCoefficients_action, subgroupCoefficientProjection_commutes,
    Module.End.mul_apply, subgroupCoefficientProjection_kills H ρ σ hσ hn w y, map_zero] at he
  have ht := congrArg (fun v : EuclideanSpace ℂ G => v 1) he
  simpa only [matrixCoefficient_apply, inv_one, map_one, Module.End.one_apply,
    PiLp.zero_apply, LinearMap.zero_apply, inner_zero_right] using ht

lemma coefficientAction_sub {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (f h : G → ℂ) :
    coefficientAction ρ (f - h) = coefficientAction ρ f - coefficientAction ρ h := by
  simp only [coefficientAction, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma supportedCoefficients_difference_positive {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : Subgroup G) (ρ : Representation ℂ H E)
    (f : G → ℂ) (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction finiteRegularRepresentation (f - supportedCoefficients H ρ f)).IsPositive := by
  let P := subgroupCoefficientProjection H ρ
  let X := coefficientAction finiteRegularRepresentation f
  have hP : P.IsSymmetric := subgroupCoefficientProjection_symmetric H ρ
  have hPP : P * P = P := subgroupCoefficientProjection_idempotent H ρ
  have hPX : P * X = X * P := subgroupCoefficientProjection_commutes H ρ f
  have hPXp : P * X * P = P * X := by
    rw [mul_assoc, ← hPX, ← mul_assoc, hPP]
  have he : (1 - P) * X * (1 - P) = X - P * X := by
    simp only [sub_mul, one_mul, mul_sub, mul_one, ← hPX, hPXp, sub_self, sub_zero]
  have hp := hf.conj_adjoint (1 - P)
  rw [(LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one hP).adjoint_eq] at hp
  change ((1 - P) * X * (1 - P)).IsPositive at hp
  rw [he] at hp
  rw [coefficientAction_sub, supportedCoefficients_action]
  exact hp

lemma supportedCoefficients_trace_le (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) [σ.IsIrreducible] [Nontrivial F]
    (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (LinearMap.trace ℂ F (coefficientAction σ (supportedCoefficients H ρ f))).re ≤
      (LinearMap.trace ℂ F (coefficientAction σ f)).re := by
  have hp := coefficientAction_positive σ hσ _ (supportedCoefficients_difference_positive H ρ f hf)
  rw [coefficientAction_sub] at hp
  have ht := Complex.re_le_re hp.trace_nonneg
  simpa only [map_sub, Complex.sub_re, Complex.zero_re, sub_nonneg] using ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

def RestrictionEligible {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H : Subgroup (SymmetricGroup n)) (ρ : Representation ℂ H E) (lam : Partition n) : Prop :=
  ∃ f : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp H.subtype), f ≠ 0

theorem specht_positive_restriction {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : Subgroup (SymmetricGroup n)) (ρ : Representation ℂ H E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ∧
    (finrank ℂ E : ℝ) * (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ≤
      ((Fintype.card H : ℝ) / (Fintype.card (SymmetricGroup n) : ℝ)) *
        ∑ lam : Partition n, if RestrictionEligible H ρ lam then
          (spechtDimension lam : ℝ) *
            (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re
        else 0 := by
  have hb := subgroup_supported_trace_bound H ρ hρ f hf
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← supportedCoefficients_action, regular_trace_specht_expansion, Complex.re_sum]
  apply Finset.sum_le_sum
  intro lam _
  let := specht_irreducible lam
  by_cases he : RestrictionEligible H ρ lam
  · simp only [ite_eq_left he, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left
      (supportedCoefficients_trace_le H ρ (spechtRepresentation lam) (spechtRepresentation_norm lam) f hf)
      (Nat.cast_nonneg _)
  · have hn : ∀ f : Representation.IntertwiningMap ρ
        ((spechtRepresentation lam).comp H.subtype), f = 0 := by
      intro f
      by_contra hn
      exact he ⟨f, hn⟩
    rw [supportedCoefficients_kills H ρ (spechtRepresentation lam)
      (spechtRepresentation_norm lam) hn f]
    simp [he]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

def outerTensorRepresentation {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) :
    Representation ℂ (G × H) (E ⊗[ℂ] F) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

@[simp]
lemma outerTensorRepresentation_apply {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (g : G) (h : H) :
    outerTensorRepresentation ρ σ (g, h) = TensorProduct.map (ρ g) (σ h) := rfl

lemma outerTensorRepresentation_norm {G H E F : Type*} [Monoid G] [Monoid H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ h y, ‖σ h y‖ = ‖y‖)
    (gh : G × H) (x : E ⊗[ℂ] F) : ‖outerTensorRepresentation ρ σ gh x‖ = ‖x‖ := by
  exact (TensorProduct.mapIsometry
    (⟨ρ gh.1, hρ gh.1⟩ : E →ₗᵢ[ℂ] E) (⟨σ gh.2, hσ gh.2⟩ : F →ₗᵢ[ℂ] F)).norm_map x

@[simp]
lemma outerTensorRepresentation_character {G H E F : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (g : G) (h : H) :
    (outerTensorRepresentation ρ σ).character (g, h) = ρ.character g * σ.character h := by
  rw [outerTensorRepresentation, Representation.char_tensor]
  rfl

lemma outerTensorRepresentation_end_finrank {G H E F : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    finrank ℂ (Representation.IntertwiningMap (outerTensorRepresentation ρ σ)
      (outerTensorRepresentation ρ σ)) = 1 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  let : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := H)).ne')
  let : Invertible (Nat.card (G × H) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G × H)).ne')
  apply Nat.cast_injective (R := ℂ)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [Fintype.sum_prod_type, Prod.inv_mk, outerTensorRepresentation_character,
    Nat.card_prod, Nat.cast_mul, mul_inv_rev, Nat.cast_one]
  calc
    _ = ((Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * ρ.character g⁻¹) *
        ((Nat.card H : ℂ)⁻¹ * ∑ h, σ.character h * σ.character h⁻¹) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = 1 := by simp only [Representation.char_orthonormal,
      ite_eq_left (show Nonempty (Representation.Equiv ρ ρ) from ⟨.refl ρ⟩),
      ite_eq_left (show Nonempty (Representation.Equiv σ σ) from ⟨.refl σ⟩), mul_one]

theorem outerTensorRepresentation_irreducible {G H E F : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ h y, ‖σ h y‖ = ‖y‖)
    [ρ.IsIrreducible] [σ.IsIrreducible] : (outerTensorRepresentation ρ σ).IsIrreducible := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) σ.asModule
  let : Nontrivial E := ρ.asModuleEquiv.toEquiv.symm.nontrivial
  let : Nontrivial F := σ.asModuleEquiv.toEquiv.symm.nontrivial
  apply irreducible_of_scalar_commutant _ (outerTensorRepresentation_norm ρ σ hρ hσ)
  intro f
  let τ := outerTensorRepresentation ρ σ
  have h1 : (1 : Representation.IntertwiningMap τ τ) ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : E ⊗[ℂ] F)
    exact hx (congrArg (fun f : Representation.IntertwiningMap τ τ => f x) hz)
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' _ h1).mp
    (outerTensorRepresentation_end_finrank ρ σ) f
  exact ⟨z, hz.symm⟩

theorem exists_specht_intertwiner {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (τ : Representation ℂ (SymmetricGroup n) E) :
    ∃ γ : Partition n, ∃ f : Representation.IntertwiningMap (spechtRepresentation γ) τ,
      f ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz (γ : Partition n) :
      finrank ℂ (Representation.IntertwiningMap (spechtRepresentation γ) τ) = 0 :=
    finrank_zero_iff_forall_zero.mpr (hn γ)
  have he := character_specht_expansion τ 1
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero, Representation.char_one] at he
  have hc : finrank ℂ E = 0 := Nat.cast_eq_zero.mp he
  exact (Module.finrank_pos (R := ℂ) (M := E)).ne' hc

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical
variable {G H E F L : Type*} [Monoid G] [Monoid H]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup L] [Module ℂ L]

def multiplicityAction (ρ : Representation ℂ G E) (τ : Representation ℂ (G × H) L)
    (h : H) (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) :
    Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H)) :=
  (τ (1, h) ∘ₗ f.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change τ (1, h) (f (ρ g x)) = τ (g, 1) (τ (1, h) (f x))
    rw [f.isIntertwining]
    change (τ (1, h) * τ (g, 1)) (f x) = (τ (g, 1) * τ (1, h)) (f x)
    rw [← map_mul, ← map_mul]
    simp)

@[simp] lemma multiplicityAction_apply (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) (h : H)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) (x : E) :
    multiplicityAction ρ τ h f x = τ (1, h) (f x) := rfl

def multiplicityRepresentation (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) :
    Representation ℂ H (Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) where
  toFun h := {
    toFun := multiplicityAction ρ τ h
    map_add' := by intro f k; ext x; simp
    map_smul' := by intro c f; ext x; simp }
  map_one' := by
    ext f x
    change τ (1, 1) (f x) = f x
    change τ 1 (f x) = f x
    simp
  map_mul' h k := by
    ext f x
    change τ (1, h * k) (f x) = (τ (1, h) * τ (1, k)) (f x)
    rw [← map_mul]
    simp

@[simp] lemma multiplicityRepresentation_apply (ρ : Representation ℂ G E)
    (τ : Representation ℂ (G × H) L) (h : H)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G H))) (x : E) :
    multiplicityRepresentation ρ τ h f x = τ (1, h) (f x) := rfl

def tensorMultiplicityEvaluation (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) :
    E ⊗[ℂ] F →ₗ[ℂ] L :=
  TensorProduct.lift {
    toFun x := {
      toFun y := f y x
      map_add' := by intro y z; simp
      map_smul' := by intro c y; simp }
    map_add' := by intro x z; ext y; simp
    map_smul' := by intro c x; ext y; simp }

@[simp] lemma tensorMultiplicityEvaluation_tmul
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F) (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) (x : E) (y : F) :
    tensorMultiplicityEvaluation ρ σ τ f (x ⊗ₜ[ℂ] y) = f y x := rfl

def tensorMultiplicityIntertwiner (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) :
    Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ :=
  (tensorMultiplicityEvaluation ρ σ τ f).intertwiningMap_of_isIntertwiningMap _ _ (by
    rintro ⟨g, h⟩ v
    induction v using TensorProduct.inductionOn with
    | tmul x y =>
      change tensorMultiplicityEvaluation ρ σ τ f
        (TensorProduct.map (ρ g) (σ h) (x ⊗ₜ[ℂ] y)) = _
      rw [TensorProduct.map_tmul, tensorMultiplicityEvaluation_tmul,
        f.isIntertwining, multiplicityRepresentation_apply, (f y).isIntertwining]
      change (τ (1, h) * τ (g, 1)) (f y x) = τ (g, h) (f y x)
      rw [← map_mul]
      simp
    | add x y hx hy => simp only [map_add, hx, hy])

lemma tensorMultiplicityIntertwiner_ne_zero (ρ : Representation ℂ G E)
    (σ : Representation ℂ H F) (τ : Representation ℂ (G × H) L)
    (f : Representation.IntertwiningMap σ (multiplicityRepresentation ρ τ)) (hf : f ≠ 0) :
    tensorMultiplicityIntertwiner ρ σ τ f ≠ 0 := by
  intro hz
  apply hf
  ext y x
  exact congrArg (fun k : Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ =>
    k (x ⊗ₜ[ℂ] y)) hz

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

theorem exists_external_specht_extension {G E L : Type*} {h : ℕ}
    [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L]
    (ρ : Representation ℂ G E) (τ : Representation ℂ (G × SymmetricGroup h) L)
    [ρ.IsIrreducible] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (f : Representation.IntertwiningMap ρ (τ.comp (MonoidHom.inl G (SymmetricGroup h))))
    (hf : f ≠ 0) :
    ∃ γ : Partition h, ∃ k : Representation.IntertwiningMap
      (outerTensorRepresentation ρ (spechtRepresentation γ)) τ, Function.Injective k := by
  let : Nontrivial (Representation.IntertwiningMap ρ
      (τ.comp (MonoidHom.inl G (SymmetricGroup h)))) := ⟨⟨f, 0, hf⟩⟩
  obtain ⟨γ, k, hk⟩ := exists_specht_intertwiner (multiplicityRepresentation ρ τ)
  let : (spechtRepresentation γ).IsIrreducible := specht_irreducible γ
  let : (outerTensorRepresentation ρ (spechtRepresentation γ)).IsIrreducible :=
    outerTensorRepresentation_irreducible _ _ hρ (spechtRepresentation_norm γ)
  exact ⟨γ, tensorMultiplicityIntertwiner ρ (spechtRepresentation γ) τ k,
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
      (tensorMultiplicityIntertwiner_ne_zero _ _ _ k hk)⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

lemma complexSign_norm {n : ℕ} (g : SymmetricGroup n) : ‖complexSign n g‖ = 1 := by
  have he := congrArg norm (complexSign_mul_self g)
  rw [norm_mul, norm_one] at he
  nlinarith [norm_nonneg (complexSign n g)]

def signTwist {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) : Representation ℂ (SymmetricGroup n) E where
  toFun g := complexSign n g • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

lemma signTwist_norm {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (g : SymmetricGroup n) (x : E) : ‖signTwist ρ g x‖ = ‖x‖ := by
  change ‖complexSign n g • ρ g x‖ = ‖x‖
  rw [norm_smul, complexSign_norm, hρ, one_mul]

def orbitEvaluation {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) : RegularSpace n →ₗ[ℂ] E where
  toFun f := ∑ g, f g • ρ g x
  map_add' := by intro f k; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c f; simp [smul_smul, Finset.smul_sum]

lemma orbitEvaluation_intertwines {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (g : SymmetricGroup n)
    (f : RegularSpace n) :
    orbitEvaluation ρ x (regularRepresentation n g f) = ρ g (orbitEvaluation ρ x f) := by
  change (∑ h, f (g⁻¹ * h) • ρ h x) = ρ g (∑ h, f h • ρ h x)
  simp only [map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
  have he := (Equiv.sum_comp (Equiv.mulLeft g) (fun h => f (g⁻¹ * h) • ρ h x)).symm
  change (∑ h, f (g⁻¹ * h) • ρ h x) = ∑ h, f (g⁻¹ * (g * h)) • ρ (g * h) x at he
  simpa only [inv_mul_cancel_left] using he

lemma orbitEvaluation_single {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (g : SymmetricGroup n) :
    orbitEvaluation ρ x (EuclideanSpace.single g 1) = ρ g x := by
  simp [orbitEvaluation, PiLp.single_apply, ite_smul]

lemma orbitEvaluation_polytabloid {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) (μ : Partition n) :
    orbitEvaluation ρ x (polytabloid μ) =
      ((Fintype.card (colSubgroup μ) : ℂ) * (Fintype.card (rowSubgroup μ) : ℂ)) •
        groupAverage ((signTwist ρ).comp (colSubgroup μ).subtype)
          (groupAverage (ρ.comp (rowSubgroup μ).subtype) x) := by
  have hr : (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card (colSubgroup μ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [polytabloid, map_sum, map_smul, orbitEvaluation_single]
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    MonoidHom.comp_apply, Subgroup.subtype_apply, signTwist, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [map_smul, map_sum, smul_smul, Finset.smul_sum, map_mul, Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  change complexSign n c.1 • ρ c.1 (ρ a.1 x) = _
  congr 1
  field_simp

lemma projection_product_nonzero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Q : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetric)
    (x : E) (hQx : Q x = x) (hPx : P x ≠ 0) : Q (P x) ≠ 0 := by
  intro hz
  have he := hQ x (P x)
  rw [hQx, hz, inner_zero_right] at he
  have hp := hP.isSymmetric x (P x)
  have hi : P (P x) = P x := congrArg (fun f : E →ₗ[ℂ] E => f x) hP.isIdempotentElem
  rw [hi, he] at hp
  exact hPx (inner_self_eq_zero.mp hp)

def spechtOrbitIntertwiner {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (μ : Partition n) (ρ : Representation ℂ (SymmetricGroup n) E) (x : E) :
    Representation.IntertwiningMap (spechtRepresentation μ) ρ :=
  ((orbitEvaluation ρ x).comp (spechtInclusion μ)).intertwiningMap_of_isIntertwiningMap _ _
    (by intro g v; exact orbitEvaluation_intertwines ρ x g (spechtInclusion μ v))

theorem specht_occurs_of_row_average {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (μ : Partition n) (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (x : E)
    (hcol : ∀ c : colSubgroup μ, ρ c.1 x = complexSign n c.1 • x)
    (hrow : groupAverage (ρ.comp (rowSubgroup μ).subtype) x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ) ρ,
      Function.Injective f := by
  let P := groupAverage (ρ.comp (rowSubgroup μ).subtype)
  let Q := groupAverage ((signTwist ρ).comp (colSubgroup μ).subtype)
  have hP : P.IsSymmetricProjection := ⟨groupAverage_idempotent _,
    groupAverage_symmetric _ (fun g => hρ g.1)⟩
  have hQ : Q.IsSymmetric := groupAverage_symmetric _ (fun g => signTwist_norm ρ hρ g.1)
  have hQx : Q x = x := by
    apply groupAverage_fixed
    intro c
    change complexSign n c.1 • ρ c.1 x = x
    rw [hcol, smul_smul, complexSign_mul_self, one_smul]
  have hv : Q (P x) ≠ 0 := projection_product_nonzero P Q hP hQ x hQx hrow
  have hf : spechtOrbitIntertwiner μ ρ x ≠ 0 := by
    intro hz
    have he := congrArg (fun f : Representation.IntertwiningMap (spechtRepresentation μ) ρ =>
      f (spechtGenerator μ)) hz
    change orbitEvaluation ρ x (polytabloid μ) = 0 at he
    rw [orbitEvaluation_polytabloid] at he
    have hn : (Fintype.card (colSubgroup μ) : ℂ) * (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero) (by exact_mod_cast Fintype.card_ne_zero)
    exact hv ((smul_eq_zero.mp he).resolve_left hn)
  let : (spechtRepresentation μ).IsIrreducible := specht_irreducible μ
  exact ⟨spechtOrbitIntertwiner μ ρ x, (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right hf⟩

end SignedSweeps
end

end OAI
