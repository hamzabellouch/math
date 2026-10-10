import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas

namespace OAI

section

/-!
An affine map family presented by a surjective input map and an injective
output map is precisely the quotient-parameter family with vanishing subspace
the input kernel and target subspace the output range. Both its uniform law
and its dimension budget agree exactly with the intrinsic restriction data.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionPresentation

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F D C : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]

/-- Change from surjective/injective presentation coordinates to the actual
quotient-domain and subspace-target parameter. -/
def parameterEquiv (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) :
    (D →ₗ[F2] C) ≃ₗ[F2] Parameter L.ker J.range :=
  LinearEquiv.arrowCongr (L.quotKerEquivOfSurjective hL).symm
    (LinearEquiv.ofInjective J hJ)

@[simp] theorem parameterEquiv_apply_mk (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) (x : E) :
    ((parameterEquiv L hL J hJ X) (L.ker.mkQ x) : F) = J (X (L x)) := rfl

/-- The embedded quotient parameter is the original two-sided composition. -/
@[simp] theorem embed_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) :
    embed L.ker J.range (parameterEquiv L hL J hJ X) = J.comp (X.comp L) := by
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem translate_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (T : E →ₗ[F2] F) (X : D →ₗ[F2] C) :
    translate L.ker J.range T (parameterEquiv L hL J hJ X) =
      T + J.comp (X.comp L) := by
  rw [Fourier.MatrixRestrictions.translate, embed_parameterEquiv]

/-- Exact uniform expectation in any presentation of the actual restriction. -/
theorem expect_presentation [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L))) =
      𝔼 A : Parameter L.ker J.range, restrict f L.ker J.range T A := by
  apply Fintype.expect_equiv (parameterEquiv L hL J hJ).toEquiv
  intro X
  exact congrArg f (translate_parameterEquiv L hL J hJ T X).symm

/-- In particular, the normalized squared restriction norms coincide. -/
theorem expect_presentation_sq [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) =
      𝔼 A : Parameter L.ker J.range, (restrict f L.ker J.range T A) ^ 2 :=
  expect_presentation L hL J hJ T (fun X => f X ^ 2)

/-- The intrinsic restriction order is exactly the dimensions lost by the
surjective input and injective output presentations. -/
theorem order_add_dimensions [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) :
    order L.ker J.range + Module.finrank F2 D + Module.finrank F2 C =
      Module.finrank F2 E + Module.finrank F2 F := by
  have hD := L.ker.finrank_quotient_add_finrank
  have hD' := (L.quotKerEquivOfSurjective hL).finrank_eq
  have hF := J.range.finrank_quotient_add_finrank
  have hC := (LinearEquiv.ofInjective J hJ).finrank_eq
  unfold order
  omega

/-- The sum-of-dimensions budget used in the fourth-moment statement implies
the actual quotient/subspace restriction budget, without truncated subtraction. -/
theorem order_le_of_dimensions [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) (r : ℕ)
    (h : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r) :
    order L.ker J.range ≤ r := by
  have hdim := order_add_dimensions L hL J hJ
  omega

end
end UniqueGamesTheorem.Inverse.KMSAffineRestrictionPresentation

end

section

/-!
The actual parameter space of an affine matrix restriction splits along a
complementary domain decomposition. The constrained coordinate is a map out of
`U / D`, while the complementary coordinate is an unrestricted map into `W`.
The equivalence transports the full uniform law to independent uniform factors.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The original vanishing subspace viewed inside the chosen large summand. -/
abbrev localVanishing (D U : Submodule F2 E) : Submodule F2 U :=
  D.comap U.subtype

/-- The constrained component of an actual quotient parameter. -/
def splitLeft (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : Parameter (localVanishing D U) W :=
  (localVanishing D U).liftQ (A.comp (D.mkQ.comp U.subtype)) (by
    intro x hx
    change A (D.mkQ (x : E)) = 0
    have hz : D.mkQ (x : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero D).mpr hx
    rw [hz, map_zero])

@[simp] theorem splitLeft_apply (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : U) :
    splitLeft D U W A ((localVanishing D U).mkQ x) =
      A (D.mkQ (x : E)) := rfl

/-- The free component of an actual quotient parameter. -/
def splitRight (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : E₀ →ₗ[F2] W :=
  A.comp (D.mkQ.comp E₀.subtype)

@[simp] theorem splitRight_apply (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : E₀) :
    splitRight D E₀ W A x = A (D.mkQ (x : E)) := rfl

/-- Assemble the two components before quotienting by `D`. -/
def joinMap (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hc : IsCompl U E₀) (B : Parameter (localVanishing D U) W)
    (C : E₀ →ₗ[F2] W) : E →ₗ[F2] W :=
  B.comp ((localVanishing D U).mkQ.comp (U.projectionOnto E₀ hc)) +
    C.comp (E₀.projectionOnto U hc.symm)

@[simp] theorem joinMap_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    joinMap D U E₀ W hc B C (x : E) = B ((localVanishing D U).mkQ x) := by
  simp [joinMap]

@[simp] theorem joinMap_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    joinMap D U E₀ W hc B C (x : E) = C x := by
  simp [joinMap]

theorem joinMap_vanishes (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    D ≤ (joinMap D U E₀ W hc B C).ker := by
  intro x hx
  let u : U := ⟨x, hDU hx⟩
  change joinMap D U E₀ W hc B C (u : E) = 0
  rw [joinMap_apply_left]
  have hz : (localVanishing D U).mkQ u = 0 :=
    (Submodule.Quotient.mk_eq_zero (localVanishing D U)).mpr hx
  rw [hz, map_zero]

/-- The actual quotient parameter reconstructed from both independent pieces. -/
def join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) : Parameter D W :=
  D.liftQ (joinMap D U E₀ W hc B C) (joinMap_vanishes D U E₀ W hDU hc B C)

@[simp] theorem join_apply (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E) :
    join D U E₀ W hDU hc B C (D.mkQ x) = joinMap D U E₀ W hc B C x := rfl

@[simp] theorem join_embed_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) =
      (B ((localVanishing D U).mkQ x) : F) := by
  rw [embed_apply, join_apply, joinMap_apply_left]

@[simp] theorem join_embed_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) = (C x : F) := by
  rw [embed_apply, join_apply, joinMap_apply_right]

theorem splitLeft_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitLeft D U W (join D U E₀ W hDU hc B C) = B := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
  rw [splitLeft_apply, join_apply, joinMap_apply_left]

theorem splitRight_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitRight D E₀ W (join D U E₀ W hDU hc B C) = C := by
  apply LinearMap.ext
  intro x
  rw [splitRight_apply, join_apply, joinMap_apply_right]

theorem join_split (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (A : Parameter D W) :
    join D U E₀ W hDU hc (splitLeft D U W A) (splitRight D E₀ W A) = A := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := D.mkQ_surjective q
  obtain ⟨⟨u, v⟩, hx⟩ := (Submodule.prodEquivOfIsCompl U E₀ hc).surjective x
  change (u : E) + (v : E) = x at hx
  rw [← hx]
  simp only [map_add, join_apply, joinMap_apply_left, joinMap_apply_right,
    splitLeft_apply, splitRight_apply]

/-- Linear equivalence of the full restriction domain with the constrained
component and the free complementary component. -/
def splitEquiv (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) :
    Parameter D W ≃ₗ[F2]
      (Parameter (localVanishing D U) W × (E₀ →ₗ[F2] W)) where
  toFun A := (splitLeft D U W A, splitRight D E₀ W A)
  invFun P := join D U E₀ W hDU hc P.1 P.2
  left_inv := join_split D U E₀ W hDU hc
  right_inv P := Prod.ext (splitLeft_join D U E₀ W hDU hc P.1 P.2)
    (splitRight_join D U E₀ W hDU hc P.1 P.2)
  map_add' A B := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl
  map_smul' a A := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl

@[simp] theorem splitEquiv_symm_apply (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    (splitEquiv D U E₀ W hDU hc).symm (B, C) = join D U E₀ W hDU hc B C := rfl

instance freeFintype [Finite E] [Finite F] (E₀ : Submodule F2 E)
    (W : Submodule F2 F) : Fintype (E₀ →ₗ[F2] W) := by
  classical
  letI : Fintype E₀ := Fintype.ofFinite E₀
  letI : Fintype W := Fintype.ofFinite W
  exact Fintype.ofInjective (fun C : E₀ →ₗ[F2] W => (C : E₀ → W))
    DFunLike.coe_injective

/-- Exact product uniform sampling on the original quotient-map parameters. -/
theorem expect_join [Finite E] [Finite F]
    (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (f : Parameter D W → ℝ) :
    (𝔼 A : Parameter D W, f A) =
      𝔼 B : Parameter (localVanishing D U) W,
        𝔼 C : E₀ →ₗ[F2] W, f (join D U E₀ W hDU hc B C) := by
  calc
    _ = 𝔼 P : Parameter (localVanishing D U) W × (E₀ →ₗ[F2] W),
        f (join D U E₀ W hDU hc P.1 P.2) :=
      Fintype.expect_equiv (splitEquiv D U E₀ W hDU hc).toEquiv _ _
        (fun A => congrArg f (join_split D U E₀ W hDU hc A).symm)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]

/-- The same exact split for the observable on the actual affine restriction. -/
theorem expect_restrict [Finite E] [Finite F]
    (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (T : E →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 A : Parameter D W, restrict f D W T A) =
      𝔼 B : Parameter (localVanishing D U) W,
        𝔼 C : E₀ →ₗ[F2] W, f (translate D W T (join D U E₀ W hDU hc B C)) :=
  expect_join D U E₀ W hDU hc (restrict f D W T)

end
end UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit

end

section

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier infrastructure, not the legacy rank-level inequality.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier synthesis in the actual trace-character orthonormal basis. -/
def synthesis (a : (F →ₗ[F2] E) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  ∑ S, a S • (fun X => (linearTraceCharacter S X).re)

@[simp] theorem coeff_synthesis (a : (F →ₗ[F2] E) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (synthesis a) T = a T := by
  unfold synthesis
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem synthesis_coeff (f : (E →ₗ[F2] F) → ℝ) : synthesis (linearCoeff f) = f := by
  funext X
  simpa only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    linear_fourier_inversion f X

theorem eq_of_coeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ T, linearCoeff f T = linearCoeff g T) : f = g := by
  rw [← synthesis_coeff f, ← synthesis_coeff g]
  exact congrArg synthesis (funext h)

/-- Exact inner product of arbitrary synthesized coefficient arrays. -/
theorem synthesis_inner (a b : (F →ₗ[F2] E) → ℝ) :
    (𝔼 X, synthesis a X * synthesis b X) = ∑ T, a T * b T := by
  rw [← linear_parseval_inner]
  simp

/-- Exact squared norm, used for every restricted KMS component. -/
theorem synthesis_energy (a : (F →ₗ[F2] E) → ℝ) :
    (𝔼 X, synthesis a X ^ 2) = ∑ T, a T ^ 2 := by
  rw [← linear_parseval]
  simp

/-- The component formed by retaining precisely the actual frequencies in P. -/
def component (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  synthesis fun T => if P T then linearCoeff f T else 0

@[simp] theorem coeff_component (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (component P f) T = if P T then linearCoeff f T else 0 := by
  exact coeff_synthesis _ _

theorem component_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) = ∑ T with P T, linearCoeff f T ^ 2 := by
  rw [component, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem component_energy_le (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  rw [component_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun T _ _ => sq_nonneg _)

theorem component_inner_self (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X * f X) = 𝔼 X, component P f X ^ 2 := by
  rw [← linear_parseval_inner, component_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_component]
  split_ifs <;> simp [pow_two]

theorem component_comp (P Q : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    component P (component Q f) = component (fun T => P T ∧ Q T) f := by
  apply eq_of_coeff_eq
  intro T
  simp only [coeff_component]
  by_cases hP : P T <;> by_cases hQ : Q T <;> simp [hP, hQ]

/-- Components of disjoint frequency classes are genuinely orthogonal. -/
theorem component_orthogonal (P Q : (F →ₗ[F2] E) → Prop)
    (hPQ : ∀ T, ¬ (P T ∧ Q T)) (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X * component Q g X) = 0 := by
  rw [← linear_parseval_inner]
  apply Finset.sum_eq_zero
  intro T _
  simp only [coeff_component]
  by_cases hP : P T
  · have hQ : ¬ Q T := fun hQ => hPQ T ⟨hP, hQ⟩
    simp [hP, hQ]
  · simp [hP]

/-- The rank-level component uses actual image dimension. -/
def rankComponent (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  component (fun T => Module.finrank F2 T.range = i) f

theorem rankComponent_energy (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankComponent i f X ^ 2) =
      ∑ T with Module.finrank F2 T.range = i, linearCoeff f T ^ 2 := by
  unfold rankComponent
  rw [component_energy]
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro T _
    rfl

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Exact orbit grouping for KMS Fourier norms

The frequency fibers are finite sets with their real cardinality as the
multiplicity. No probability normalization or orbit-size estimate is assumed
by the grouping identity. The later kernel-orbit count supplies these sizes
for the actual binary linear maps.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical

section FiniteFibers

variable {A B J : Type*} [Fintype A] [Fintype B] [Fintype J]

/-- Exact sum of a function constant on the fibers of a finite map. -/
theorem sum_comp_eq_fiber_card (p : A → J) (b : J → ℝ) :
    (∑ x, b (p x)) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j := by
  calc
    (∑ x, b (p x)) = ∑ x, ∑ j, if p x = j then b j else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = ∑ j, ∑ x, if p x = j then b j else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

theorem sum_sq_eq_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) :
    (∑ x, a x ^ 2) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j ^ 2 := by
  simpa only [hab] using sum_comp_eq_fiber_card p (fun j => b j ^ 2)

/-- If every orbit has the same size, its multiplicity factors out exactly. -/
theorem sum_sq_eq_uniform_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) (n : ℕ)
    (hn : ∀ j, (Finset.univ.filter fun x => p x = j).card = n) :
    (∑ x, a x ^ 2) = (n : ℝ) * ∑ j, b j ^ 2 := by
  rw [sum_sq_eq_fiber_card p a b hab, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hn]

/-- Two coefficient arrays with the same orbit values have exactly the ratio
of their orbit multiplicities. Cross multiplication includes zero-energy
functions without dividing by their norm. -/
theorem fiber_constant_energy_cross_mul (p : A → J) (q : B → J)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (a : A → ℝ) (b : B → ℝ)
    (hab : ∀ x y, p x = q y → a x = b y)
    (nA nB : ℕ)
    (hA : ∀ j, (Finset.univ.filter fun x => p x = j).card = nA)
    (hB : ∀ j, (Finset.univ.filter fun y => q y = j).card = nB) :
    (nB : ℝ) * (∑ x, a x ^ 2) = (nA : ℝ) * ∑ y, b y ^ 2 := by
  let c : J → ℝ := fun j => b (Classical.choose (hq j))
  have ha : ∀ x, a x = c (p x) := by
    intro x
    exact hab x (Classical.choose (hq (p x)))
      (Classical.choose_spec (hq (p x))).symm
  have hb : ∀ y, b y = c (q y) := by
    intro y
    obtain ⟨x, hx⟩ := hp (q y)
    exact (hab x y hx).symm.trans (by simpa only [hx] using ha x)
  rw [sum_sq_eq_uniform_fiber_card p a c ha nA hA,
    sum_sq_eq_uniform_fiber_card q b c hb nB hB]
  ring

end FiniteFibers

section FourierFibers

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype J]

/-- Parseval grouped by any genuine finite classification of frequencies. -/
theorem synthesis_energy_grouped (p : (F →ₗ[F2] E) → J)
    (a : (F →ₗ[F2] E) → ℝ) (b : J → ℝ) (hab : ∀ S, a S = b (p S)) :
    (𝔼 X, synthesis a X ^ 2) =
      ∑ j, ((Finset.univ.filter fun S => p S = j).card : ℝ) * b j ^ 2 := by
  rw [synthesis_energy]
  exact sum_sq_eq_fiber_card p a b hab

/-- In particular, basis-invariant coefficients may be grouped by their
actual kernels. The invariance premise is supplied separately by the proved
change-of-basis theorem, not by any inverse or hypercontractive hypothesis. -/
theorem synthesis_energy_by_kernel [Fintype (Submodule F2 F)]
    (a : (F →ₗ[F2] E) → ℝ) (b : Submodule F2 F → ℝ)
    (hab : ∀ S, a S = b S.ker) :
    (𝔼 X, synthesis a X ^ 2) =
      ∑ K : Submodule F2 F,
        ((Finset.univ.filter fun S : F →ₗ[F2] E => S.ker = K).card : ℝ) * b K ^ 2 :=
  synthesis_energy_grouped (fun S => S.ker) a b hab

end FourierFibers
end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
Exact trace-character identities for the adapted Hybrid coordinates. The
three coordinate blocks contribute multiplicatively to the actual character,
and assembling through the last-block embedding preserves the small phase.
These identities require neither rank assumptions nor analytic estimates.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergyPhase

noncomputable section
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

section Product

variable {H U V : Type*}
  [AddCommGroup H] [Module F2 H]
  [AddCommGroup U] [Module F2 U]
  [AddCommGroup V] [Module F2 V]

/-- Each frequency block pairs with the corresponding restriction of the
primal map. The trace is taken on the common codomain `H`. -/
theorem tracePair_prod (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    linearTracePair X (S.prod T) =
      linearTracePair (X.comp (LinearMap.inl F2 U V)) S +
      linearTracePair (X.comp (LinearMap.inr F2 U V)) T := by
  have hc : X.comp (S.prod T) =
      (X.comp (LinearMap.inl F2 U V)).comp S +
        (X.comp (LinearMap.inr F2 U V)).comp T := by
    apply LinearMap.ext
    intro h
    change X (S h, T h) = X (S h, 0) + X (0, T h)
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      X.map_add (S h, 0) (0, T h)
  simp only [linearTracePair, hc, map_add]

/-- Exact complex-valued phase splitting into two frequency blocks. -/
theorem character_prod (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    linearTraceCharacter (S.prod T) X =
      linearTraceCharacter S (X.comp (LinearMap.inl F2 U V)) *
      linearTraceCharacter T (X.comp (LinearMap.inr F2 U V)) := by
  simp only [linearTraceCharacter_apply, tracePair_prod, binarySign_add]

/-- The real phases multiply because every binary trace character is real. -/
theorem character_prod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) X).re =
      (linearTraceCharacter S (X.comp (LinearMap.inl F2 U V))).re *
      (linearTraceCharacter T (X.comp (LinearMap.inr F2 U V))).re := by
  rw [character_prod, Complex.mul_re]
  simp [linearTraceCharacter_apply]

/-- Splitting a primal map and its dual frequency introduces no cardinal
factor: both traces remain on the common space `H`. -/
theorem character_prod_coprod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (a : U →ₗ[F2] H) (X : V →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) (a.coprod X)).re =
      (linearTraceCharacter S a).re * (linearTraceCharacter T X).re := by
  simpa only [LinearMap.coprod_inl, LinearMap.coprod_inr] using
    character_prod_re S T (a.coprod X)

end Product

section AdaptedCoordinates

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

/-- The three actual block phases of the assembled Hybrid frequency. -/
theorem character_assemble {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    linearTraceCharacter (assemble p) X =
      linearTraceCharacter p.alpha (X.comp (LinearMap.inl F2 A (W × D))) *
        (linearTraceCharacter p.psi
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D)) *
        linearTraceCharacter (p.v.comp (LinearMap.snd F2 B C))
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D))) := by
  simp only [assemble, character_prod]

/-- The real phase factorization used in the coefficient fiber sum. -/
theorem character_assemble_re {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    (linearTraceCharacter (assemble p) X).re =
      (linearTraceCharacter p.alpha (X.comp (LinearMap.inl F2 A (W × D)))).re *
        ((linearTraceCharacter p.psi
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D))).re *
        (linearTraceCharacter (p.v.comp (LinearMap.snd F2 B C))
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D))).re) := by
  simp only [assemble, character_prod_re]

/-- The ambient character is exactly the small character after restricting
the primal map along the last-block embedding. -/
theorem character_assemble_eq_fullCoordinates {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    linearTraceCharacter (assemble p) X =
      linearTraceCharacter (fullCoordinates p) (X.comp (embedLast p.v)) := by
  simp only [assemble_eq_embedLast_comp, linearTraceCharacter_apply,
    linearTracePair, LinearMap.comp_assoc]

/-- Real-valued form of the exact small-character transport. -/
theorem character_assemble_eq_fullCoordinates_re {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    (linearTraceCharacter (assemble p) X).re =
      (linearTraceCharacter (fullCoordinates p) (X.comp (embedLast p.v))).re :=
  congrArg Complex.re (character_assemble_eq_fullCoordinates p X)

end AdaptedCoordinates
end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergyPhase

end

section

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives

section General

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The coefficient of an actual Hybrid derivative is the translated sum over
the actual Hybrid selector and quotient-compression fiber. -/
theorem linearCoeff_hybridDerivative
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ)
    (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (hybridDerivative A B T f) Z =
      ∑ S : F →ₗ[F2] E,
        if LinearIdentities.Hybrid S A B ∧ Restriction.compressFrequency A B S = Z
        then linearCoeff f S * (linearTraceCharacter S T).re else 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro S _
  simp only [hybridProjector, linearCoeff_spectralProjector]
  by_cases hH : LinearIdentities.Hybrid S A B <;>
    by_cases hC : Restriction.compressFrequency A B S = Z <;> simp [hH, hC]

/-- Exact normalized derivative energy, with counting measure on frequencies. -/
theorem hybridDerivative_energy_eq_coefficients
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, hybridDerivative A B T f N ^ 2) =
      ∑ Z : B →ₗ[F2] (E ⧸ A),
        (∑ S : F →ₗ[F2] E,
          if LinearIdentities.Hybrid S A B ∧ Restriction.compressFrequency A B S = Z
          then linearCoeff f S * (linearTraceCharacter S T).re else 0) ^ 2 := by
  rw [← linear_parseval]
  simp_rw [linearCoeff_hybridDerivative]

end General

section ProductEquivalences

variable {R A U B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup U] [Module R U]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-- The first factor, regarded as its actual coordinate subspace. -/
def leftRangeEquiv : B ≃ₗ[R] LinearMap.range (LinearMap.inl R B C) where
  toFun b := ⟨(b, 0), ⟨b, rfl⟩⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := hx
    rfl
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

@[simp] theorem leftRangeEquiv_coe (b : B) :
    (leftRangeEquiv (R := R) (C := C) b : B × C) = (b, 0) := rfl

/-- The second projection descends through the first-factor quotient. -/
def quotientRightMap :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) →ₗ[R] U :=
  (LinearMap.range (LinearMap.inl R A U)).liftQ (LinearMap.snd R A U) (by
    rintro x ⟨a, rfl⟩
    rfl)

@[simp] theorem quotientRightMap_mkQ (x : A × U) :
    quotientRightMap (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

/-- The quotient by the first coordinate has the second coordinate as a
canonical linear presentation. -/
def quotientRightEquiv :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) ≃ₗ[R] U where
  toLinearMap := quotientRightMap
  invFun u := (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u)
  left_inv := by
    intro q
    obtain ⟨⟨a, u⟩, rfl⟩ := (LinearMap.range (LinearMap.inl R A U)).mkQ_surjective q
    change (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) =
      (LinearMap.range (LinearMap.inl R A U)).mkQ (a, u)
    have hz : (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    calc
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) +
          (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) := by rw [hz, zero_add]
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ ((a, 0) + (0, u)) :=
        (map_add _ _ _).symm
      _ = _ := by simp
  right_inv _ := rfl

@[simp] theorem quotientRightEquiv_mkQ (x : A × U) :
    quotientRightEquiv (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

/-- The exact change of frequency coordinates for a product restriction. -/
def productFrequencyEquiv :
    ((LinearMap.range (LinearMap.inl R B C)) →ₗ[R]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U))) ≃ (B →ₗ[R] U) where
  toFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).toLinearMap)
  invFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).symm.toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).symm.toLinearMap)
  left_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end ProductEquivalences

section ProductEnergy

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- Actual quotient compression becomes the block compression. -/
@[simp] theorem productFrequencyEquiv_compressFrequency
    (S : (B × C) →ₗ[F2] (A × U)) :
    productFrequencyEquiv (Restriction.compressFrequency
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S) =
      (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) := by
  apply LinearMap.ext
  intro b
  rfl

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- Equality of actual compressed frequencies is exactly equality of blocks. -/
theorem compressFrequency_eq_iff_product
    (S : (B × C) →ₗ[F2] (A × U))
    (Z : (LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :
    Restriction.compressFrequency (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S = Z ↔
    (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) =
      productFrequencyEquiv Z := by
  constructor
  · intro h
    rw [← productFrequencyEquiv_compressFrequency S, h]
  · intro h
    apply productFrequencyEquiv.injective
    rw [productFrequencyEquiv_compressFrequency, h]

variable [Finite A] [Finite U] [Finite B] [Finite C]
  [Fintype ((A × U) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × U))] [Fintype (B →ₗ[F2] U)]

/-- The actual Hybrid derivative energy in product coordinates. The sum is
over ordinary block frequencies, with no quotient or basis multiplicity. -/
theorem hybridDerivative_product_energy_eq_coefficients
    (T : (A × U) →ₗ[F2] (B × C))
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T f N ^ 2) =
      ∑ Z : B →ₗ[F2] U,
        (∑ S : (B × C) →ₗ[F2] (A × U),
          if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
              (LinearMap.range (LinearMap.inl F2 B C)) ∧
              (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
          then linearCoeff f S * (linearTraceCharacter S T).re else 0) ^ 2 := by
  let : Fintype ((LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :=
    Fintype.ofEquiv (B →ₗ[F2] U) productFrequencyEquiv.symm
  rw [hybridDerivative_energy_eq_coefficients]
  apply Fintype.sum_equiv productFrequencyEquiv
  intro Z
  simp_rw [compressFrequency_eq_iff_product]

end ProductEnergy
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
