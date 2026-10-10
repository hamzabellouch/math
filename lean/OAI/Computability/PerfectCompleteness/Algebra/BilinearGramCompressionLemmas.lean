import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Projective
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

namespace PerfectCompleteness.BilinearGramCompression

open scoped BigOperators

noncomputable section

variable {K H R I J : Type*} [Field K] [AddCommGroup H] [Module K H]
  [Fintype R] [Fintype I] [Fintype J]

def combinations (rows : R → H) (T : Matrix I R K) : I → H :=
  fun i => ∑ r, T i r • rows r

def crossGram (F : H →ₗ[K] Module.Dual K H) (left : I → H) (right : J → H) :
    Matrix I J K :=
  fun i j => F (left i) (right j)

def gram (F : H →ₗ[K] Module.Dual K H) (rows : R → H) : Matrix R R K :=
  crossGram F rows rows

omit [Fintype I] [Fintype J] in
theorem crossGram_combinations (F : H →ₗ[K] Module.Dual K H) (rows : R → H)
    (T : Matrix I R K) (S : Matrix J R K) :
    crossGram F (combinations rows T) (combinations rows S) =
      T * gram F rows * S.transpose := by
  classical
  ext i j
  simp only [crossGram, combinations, gram, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  ac_rfl

omit [Fintype I] in
theorem gram_combinations (F : H →ₗ[K] Module.Dual K H) (rows : R → H)
    (T : Matrix I R K) :
    gram F (combinations rows T) = T * gram F rows * T.transpose :=
  crossGram_combinations F rows T T

omit [Fintype I] in
theorem cross_rank_le (F : H →ₗ[K] Module.Dual K H) (rows : R → H)
    (T : Matrix I R K) (S : Matrix J R K) :
    (crossGram F (combinations rows T) (combinations rows S)).rank ≤
      (gram F rows).rank := by
  rw [crossGram_combinations]
  exact (Matrix.rank_mul_le_left (T * gram F rows) S.transpose).trans
    (Matrix.rank_mul_le_right T (gram F rows))

theorem gram_rank_le (F : H →ₗ[K] Module.Dual K H) (rows : R → H)
    (T : Matrix I R K) :
    (gram F (combinations rows T)).rank ≤ (gram F rows).rank :=
  cross_rank_le F rows T T

omit [Fintype I] in
theorem cross_rank_le_one (F : H →ₗ[K] Module.Dual K H) (rows : R → H)
    (T : Matrix I R K) (S : Matrix J R K) (tested : (gram F rows).rank ≤ 1) :
    (crossGram F (combinations rows T) (combinations rows S)).rank ≤ 1 :=
  (cross_rank_le F rows T S).trans tested

end
end PerfectCompleteness.BilinearGramCompression

end

section

namespace PerfectCompleteness.BilinearRestrictionRank

noncomputable section

open Module

variable {𝕜 H V U : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup U] [Module 𝕜 U]

def restrictForm (F : H →ₗ[𝕜] Module.Dual 𝕜 H) (N : Submodule 𝕜 H) :
    N →ₗ[𝕜] Module.Dual 𝕜 N :=
  N.dualRestrict.comp (F.domRestrict N)

@[simp]
theorem restrictForm_apply (F : H →ₗ[𝕜] Module.Dual 𝕜 H)
    (N : Submodule 𝕜 H) (x y : N) :
    restrictForm F N x y = F (x : H) (y : H) := rfl

theorem ker_domRestrict_finrank_le [FiniteDimensional 𝕜 H]
    (f : H →ₗ[𝕜] V) (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.ker (f.domRestrict N)) ≤ finrank 𝕜 (LinearMap.ker f) := by
  let inclusion : LinearMap.ker (f.domRestrict N) →ₗ[𝕜] LinearMap.ker f :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply LinearMap.finrank_le_finrank_of_injective (f := inclusion)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.ker f => (z : H)) h

theorem rank_domRestrict_add_codim [FiniteDimensional 𝕜 H]
    (f : H →ₗ[𝕜] V) (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.range f) ≤
      finrank 𝕜 (LinearMap.range (f.domRestrict N)) + finrank 𝕜 (H ⧸ N) := by
  have hwhole := f.finrank_range_add_finrank_ker
  have hrestricted := (f.domRestrict N).finrank_range_add_finrank_ker
  have hquotient := N.finrank_quotient_add_finrank
  have hkernel := ker_domRestrict_finrank_le f N
  omega

theorem rank_le_rank_comp_add_ker [FiniteDimensional 𝕜 V]
    (g : H →ₗ[𝕜] V) (f : V →ₗ[𝕜] U) :
    finrank 𝕜 (LinearMap.range g) ≤
      finrank 𝕜 (LinearMap.range (f.comp g)) + finrank 𝕜 (LinearMap.ker f) := by
  have hrange : LinearMap.range (f.domRestrict (LinearMap.range g)) =
      LinearMap.range (f.comp g) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  have hrank := (f.domRestrict (LinearMap.range g)).finrank_range_add_finrank_ker
  rw [hrange] at hrank
  have hkernel := ker_domRestrict_finrank_le f (LinearMap.range g)
  omega

theorem dualRestrict_ker_finrank [FiniteDimensional 𝕜 H] (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.ker N.dualRestrict) = finrank 𝕜 (H ⧸ N) := by
  rw [N.dualRestrict_ker_eq_dualAnnihilator]
  exact (Subspace.quotEquivAnnihilator N).finrank_eq.symm

theorem rank_restrict_add_codim [FiniteDimensional 𝕜 H]
    (F : H →ₗ[𝕜] Module.Dual 𝕜 H) (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.range F) ≤
      finrank 𝕜 (LinearMap.range (restrictForm F N)) + 2 * finrank 𝕜 (H ⧸ N) := by
  have hdomain := rank_domRestrict_add_codim F N
  have hcodomain := rank_le_rank_comp_add_ker (F.domRestrict N) N.dualRestrict
  rw [dualRestrict_ker_finrank] at hcodomain
  change finrank 𝕜 (LinearMap.range (F.domRestrict N)) ≤
    finrank 𝕜 (LinearMap.range (restrictForm F N)) + finrank 𝕜 (H ⧸ N) at hcodomain
  omega

theorem rank_sub_two_codim_le [FiniteDimensional 𝕜 H]
    (F : H →ₗ[𝕜] Module.Dual 𝕜 H) (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.range F) - 2 * finrank 𝕜 (H ⧸ N) ≤
      finrank 𝕜 (LinearMap.range (restrictForm F N)) := by
  have h := rank_restrict_add_codim F N
  omega

end
end PerfectCompleteness.BilinearRestrictionRank

end

section

namespace PerfectCompleteness.MatrixRowQuotient

noncomputable section

variable {𝕜 H K : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]

theorem exists_section (W : Submodule 𝕜 H) :
    ∃ s : (H ⧸ W) →ₗ[𝕜] H, W.mkQ.comp s = LinearMap.id :=
  W.mkQ.exists_rightInverse_of_surjective W.range_mkQ

def projectMatrix (W : Submodule 𝕜 H) (X : Module.Dual 𝕜 H →ₗ[𝕜] K) :
    Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K :=
  X.comp W.mkQ.dualMap

def liftMatrix (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) : Module.Dual 𝕜 H →ₗ[𝕜] K :=
  X.comp s.dualMap

@[simp] theorem projectMatrix_apply (W : Submodule 𝕜 H)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (q : Module.Dual 𝕜 (H ⧸ W)) :
    projectMatrix W X q = X (q.comp W.mkQ) := rfl

@[simp] theorem liftMatrix_apply (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) (q : Module.Dual 𝕜 H) :
    liftMatrix W s X q = X (q.comp s) := rfl

theorem project_lift (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (hs : W.mkQ.comp s = LinearMap.id)
    (X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) :
    projectMatrix W (liftMatrix W s X) = X := by
  apply LinearMap.ext
  intro q
  change X (s.dualMap (W.mkQ.dualMap q)) = X q
  apply congrArg X
  apply LinearMap.ext
  intro h
  change q (W.mkQ (s h)) = q h
  have hh := LinearMap.congr_fun hs h
  change W.mkQ (s h) = h at hh
  rw [hh]

theorem projectMatrix_surjective (W : Submodule 𝕜 H) :
    Function.Surjective (projectMatrix (K := K) W) := by
  obtain ⟨s, hs⟩ := exists_section W
  intro X
  exact ⟨liftMatrix W s X, project_lift W s hs X⟩

theorem liftMatrix_injective (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (hs : W.mkQ.comp s = LinearMap.id) :
    Function.Injective (liftMatrix (K := K) W s) := by
  intro X Y h
  have h' := congrArg (projectMatrix W) h
  simpa only [project_lift W s hs] using h'

def residualVector (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (hs : W.mkQ.comp s = LinearMap.id) : H →ₗ[𝕜] W :=
  (LinearMap.id - s.comp W.mkQ).codRestrict W (by
    intro h
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change W.mkQ (h - s (W.mkQ h)) = 0
    rw [map_sub]
    have hh := LinearMap.congr_fun hs (W.mkQ h)
    change W.mkQ (s (W.mkQ h)) = W.mkQ h at hh
    rw [hh, sub_self])

@[simp] theorem residualVector_val (W : Submodule 𝕜 H)
    (s : (H ⧸ W) →ₗ[𝕜] H) (hs : W.mkQ.comp s = LinearMap.id) (h : H) :
    (residualVector W s hs h : H) = h - s (W.mkQ h) := rfl

theorem subtype_comp_residualVector (W : Submodule 𝕜 H)
    (s : (H ⧸ W) →ₗ[𝕜] H) (hs : W.mkQ.comp s = LinearMap.id) :
    W.subtype.comp (residualVector W s hs) = LinearMap.id - s.comp W.mkQ := rfl

theorem residual_factorization (W : Submodule 𝕜 H)
    (s : (H ⧸ W) →ₗ[𝕜] H) (hs : W.mkQ.comp s = LinearMap.id)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) :
    X - liftMatrix W s (projectMatrix W X) =
      (X.comp (residualVector W s hs).dualMap).comp W.subtype.dualMap := by
  apply LinearMap.ext
  intro q
  change X q - X (W.mkQ.dualMap (s.dualMap q)) =
    X ((residualVector W s hs).dualMap (W.subtype.dualMap q))
  rw [← map_sub]
  apply congrArg X
  apply LinearMap.ext
  intro h
  change q h - q (s (W.mkQ h)) = q (h - s (W.mkQ h))
  rw [map_sub]

theorem project_rankOne (W : Submodule 𝕜 H) (X : Module.Dual 𝕜 H →ₗ[𝕜] K)
    (a : K) (h : H) :
    projectMatrix W (X + (Module.Dual.eval 𝕜 H h).smulRight a) =
      projectMatrix W X + (Module.Dual.eval 𝕜 (H ⧸ W) (W.mkQ h)).smulRight a := by
  apply LinearMap.ext
  intro q
  rfl

theorem lift_rankOne (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) (a : K) (h : H ⧸ W) :
    liftMatrix W s (X + (Module.Dual.eval 𝕜 (H ⧸ W) h).smulRight a) =
      liftMatrix W s X + (Module.Dual.eval 𝕜 H (s h)).smulRight a := by
  apply LinearMap.ext
  intro q
  rfl

theorem project_rankOne_of_mem (W : Submodule 𝕜 H)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (a : K) (h : H) (hh : h ∈ W) :
    projectMatrix W (X + (Module.Dual.eval 𝕜 H h).smulRight a) = projectMatrix W X := by
  apply LinearMap.ext
  intro q
  change X (W.mkQ.dualMap q) + q (W.mkQ h) • a = X (W.mkQ.dualMap q)
  have hzero : W.mkQ h = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hh
  rw [hzero, map_zero, zero_smul, add_zero]

end
end PerfectCompleteness.MatrixRowQuotient

end

section

namespace PerfectCompleteness.MatrixSlice

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

def Slice (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C) :=
  {X : E →ₗ[F2] C //
    X.domRestrict W = T.domRestrict W ∧ C'.mkQ.comp X = C'.mkQ.comp T}

theorem domRestrict_translate (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) (A : Parameter W C') :
    (translate W C' T A).domRestrict W = T.domRestrict W := by
  apply LinearMap.ext
  intro w
  change T w + embed W C' A w = T w
  have hw : embed W C' A w = 0 := embed_vanishes W C' A w.property
  rw [hw, add_zero]

theorem exists_translate_iff (W : Submodule F2 E) (C' : Submodule F2 C)
    (T X : E →ₗ[F2] C) :
    (∃ A : Parameter W C', translate W C' T A = X) ↔
      X.domRestrict W = T.domRestrict W ∧ C'.mkQ.comp X = C'.mkQ.comp T := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨domRestrict_translate W C' T A, quotient_translate W C' T A⟩
  · rintro ⟨hW, hC⟩
    have hker : W ≤ LinearMap.ker (X - T) := by
      intro w hw
      change X w - T w = 0
      exact sub_eq_zero.mpr (LinearMap.congr_fun hW ⟨w, hw⟩)
    have hrange : LinearMap.range (X - T) ≤ C' := by
      rintro y ⟨x, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero C').mp
      change C'.mkQ (X x - T x) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hC x)
    obtain ⟨A, hA⟩ := (exists_embed_iff W C' (X - T)).mpr ⟨hker, hrange⟩
    refine ⟨A, ?_⟩
    change T + embed W C' A = X
    rw [hA, add_comm T, sub_add_cancel]

def parameterEquivSlice (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) : Parameter W C' ≃ Slice W C' T :=
  Equiv.ofBijective
    (fun A => ⟨translate W C' T A,
      domRestrict_translate W C' T A, quotient_translate W C' T A⟩)
    ⟨by
      intro A B h
      exact translate_injective W C' T (congrArg Subtype.val h), by
      intro X
      obtain ⟨A, hA⟩ := (exists_translate_iff W C' T X.val).mpr X.property
      exact ⟨A, Subtype.ext hA⟩⟩

@[simp] theorem parameterEquivSlice_val (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) (A : Parameter W C') :
    (parameterEquivSlice W C' T A).val = translate W C' T A := rfl

instance sliceFintype [Finite E] [Finite C] (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) : Fintype (Slice W C' T) :=
  Fintype.ofEquiv (Parameter W C') (parameterEquivSlice W C' T)

instance sliceNonempty (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) : Nonempty (Slice W C' T) := ⟨⟨T, rfl, rfl⟩⟩

theorem expect_translate_eq_slice [Finite E] [Finite C]
    (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C)
    (f : (E →ₗ[F2] C) → ℝ) :
    (𝔼 A : Parameter W C', f (translate W C' T A)) =
      𝔼 X : Slice W C' T, f X.val :=
  Fintype.expect_equiv (parameterEquivSlice W C' T) _ _ (fun _ => rfl)

theorem expect_restrict_eq_slice [Finite E] [Finite C]
    (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C)
    (f : (E →ₗ[F2] C) → ℝ) :
    (𝔼 A : Parameter W C', restrict f W C' T A) =
      𝔼 X : Slice W C' T, f X.val :=
  expect_translate_eq_slice W C' T f

theorem domRestrict_eq_iff_basis [FiniteDimensional F2 E]
    (W : Submodule F2 E) (X T : E →ₗ[F2] C) :
    X.domRestrict W = T.domRestrict W ↔
      ∀ i : Fin (Module.finrank F2 W),
        X (Module.finBasis F2 W i) = T (Module.finBasis F2 W i) := by
  constructor
  · intro h i
    exact LinearMap.congr_fun h (Module.finBasis F2 W i)
  · intro h
    exact (Module.finBasis F2 W).ext h

def rowMap [FiniteDimensional F2 C] (C' : Submodule F2 C) :
    C →ₗ[F2] (Fin (Module.finrank F2 (C ⧸ C')) → F2) :=
  (Module.finBasis F2 (C ⧸ C')).equivFun.toLinearMap.comp C'.mkQ

theorem rowMap_comp_eq_iff [FiniteDimensional F2 C]
    (C' : Submodule F2 C) (X T : E →ₗ[F2] C) :
    (rowMap C').comp X = (rowMap C').comp T ↔
      C'.mkQ.comp X = C'.mkQ.comp T := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply (Module.finBasis F2 (C ⧸ C')).equivFun.injective
    exact LinearMap.congr_fun h x
  · intro h
    apply LinearMap.ext
    intro x
    exact congrArg (Module.finBasis F2 (C ⧸ C')).equivFun
      (LinearMap.congr_fun h x)

theorem rowMap_surjective [FiniteDimensional F2 C] (C' : Submodule F2 C) :
    Function.Surjective (rowMap C') :=
  (Module.finBasis F2 (C ⧸ C')).equivFun.surjective.comp C'.mkQ_surjective

theorem exists_translate_iff_equations [FiniteDimensional F2 E]
    [FiniteDimensional F2 C] (W : Submodule F2 E) (C' : Submodule F2 C)
    (T X : E →ₗ[F2] C) :
    (∃ A : Parameter W C', translate W C' T A = X) ↔
      (∀ i : Fin (Module.finrank F2 W),
        X (Module.finBasis F2 W i) = T (Module.finBasis F2 W i)) ∧
      (rowMap C').comp X = (rowMap C').comp T := by
  rw [exists_translate_iff, domRestrict_eq_iff_basis, rowMap_comp_eq_iff]

theorem equation_count_eq_order (W : Submodule F2 E) (C' : Submodule F2 C) :
    Fintype.card (Fin (Module.finrank F2 W)) +
      Fintype.card (Fin (Module.finrank F2 (C ⧸ C'))) = order W C' := by
  simp only [Fintype.card_fin, order]

theorem column_count_le_order (W : Submodule F2 E) (C' : Submodule F2 C) :
    Module.finrank F2 W ≤ order W C' := Nat.le_add_right _ _

theorem row_count_le_order (W : Submodule F2 E) (C' : Submodule F2 C) :
    Module.finrank F2 (C ⧸ C') ≤ order W C' := Nat.le_add_left _ _

end
end PerfectCompleteness.MatrixSlice

end

section

namespace PerfectCompleteness.TensorCosetEvaluation

noncomputable section

open scoped TensorProduct

section GeneralField

variable {𝕜 U H : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup H] [Module 𝕜 H]

def pureFrequency (a : Module.Dual 𝕜 U) (q : Module.Dual 𝕜 H) :
    Module.Dual 𝕜 (U ⊗[𝕜] H) :=
  TensorProduct.lift (a.smulRight q)

@[simp] theorem pureFrequency_tmul (a : Module.Dual 𝕜 U)
    (q : Module.Dual 𝕜 H) (u : U) (h : H) :
    pureFrequency a q (u ⊗ₜ[𝕜] h) = a u * q h := by
  simp only [pureFrequency, TensorProduct.lift.tmul, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul]

def scalarRestriction (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H)) (u : U) :
    Module.Dual 𝕜 H :=
  Φ.comp (TensorProduct.mk 𝕜 U H u)

@[simp] theorem scalarRestriction_apply (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) (h : H) : scalarRestriction Φ u h = Φ (u ⊗ₜ[𝕜] h) := rfl

@[simp] theorem scalarRestriction_zero (u : U) :
    scalarRestriction (0 : Module.Dual 𝕜 (U ⊗[𝕜] H)) u = 0 := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_add (Φ Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) : scalarRestriction (Φ + Ψ) u = scalarRestriction Φ u + scalarRestriction Ψ u := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_sub (Φ Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) : scalarRestriction (Φ - Ψ) u = scalarRestriction Φ u - scalarRestriction Ψ u := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_smul (c : 𝕜) (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) : scalarRestriction (c • Φ) u = c • scalarRestriction Φ u := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_pure (a : Module.Dual 𝕜 U)
    (q : Module.Dual 𝕜 H) (u : U) :
    scalarRestriction (pureFrequency a q) u = a u • q := by
  apply LinearMap.ext
  intro h
  simp only [scalarRestriction_apply, pureFrequency_tmul,
    LinearMap.smul_apply, smul_eq_mul]

def equationSpace (Q : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Submodule 𝕜 (Module.Dual 𝕜 (U ⊗[𝕜] H)) :=
  Submodule.span 𝕜
    (Set.range (fun p : Module.Dual 𝕜 U × Q => pureFrequency p.1 p.2))

theorem scalarRestriction_mem (Q : Submodule 𝕜 (Module.Dual 𝕜 H))
    (Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H)) (hΨ : Ψ ∈ equationSpace (U := U) Q) (u : U) :
    scalarRestriction Ψ u ∈ Q := by
  unfold equationSpace at hΨ
  refine Submodule.span_induction
    (p := fun Ψ _ => scalarRestriction Ψ u ∈ Q) ?_ ?_ ?_ ?_ hΨ
  · rintro Ψ ⟨⟨a, q⟩, rfl⟩
    rw [scalarRestriction_pure]
    exact Q.smul_mem (a u) q.property
  · rw [scalarRestriction_zero]
    exact Q.zero_mem
  · intro Ψ₁ Ψ₂ _ _ h₁ h₂
    rw [scalarRestriction_add]
    exact Q.add_mem h₁ h₂
  · intro c Ψ _ h
    rw [scalarRestriction_smul]
    exact Q.smul_mem c h

theorem scalarRestriction_sub_base_mem (Q : Submodule 𝕜 (Module.Dual 𝕜 H))
    (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H)) (a : Module.Dual 𝕜 U)
    (z : Module.Dual 𝕜 H) (u : U) (hu : a u = 1)
    (hΦ : Φ - pureFrequency a z ∈ equationSpace (U := U) Q) :
    scalarRestriction Φ u - z ∈ Q := by
  have h := scalarRestriction_mem Q _ hΦ u
  simpa only [scalarRestriction_sub, scalarRestriction_pure, hu, one_smul] using h

theorem scalarRestriction_mem_coset_of_eq (Q : Submodule 𝕜 (Module.Dual 𝕜 H))
    (Φ Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H)) (a : Module.Dual 𝕜 U)
    (z : Module.Dual 𝕜 H) (u : U) (hu : a u = 1)
    (hΨ : Ψ ∈ equationSpace (U := U) Q) (hΦ : Φ = pureFrequency a z + Ψ) :
    scalarRestriction Φ u - z ∈ Q := by
  apply scalarRestriction_sub_base_mem Q Φ a z u hu
  rw [hΦ, add_sub_cancel_left]
  exact hΨ

theorem scalarRestriction_mem_of_vanishes
    (Q : Submodule 𝕜 (Module.Dual 𝕜 H)) [FiniteDimensional 𝕜 Q]
    (Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (hΨ : ∀ u h, h ∈ Q.dualCoannihilator → Ψ (u ⊗ₜ[𝕜] h) = 0) (u : U) :
    scalarRestriction Ψ u ∈ Q := by
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Q)]
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro h hh
  exact hΨ u h hh

theorem scalarRestriction_factor_mem
    {L : Type*} [AddCommGroup L] [Module 𝕜 L]
    (Q : Submodule 𝕜 (Module.Dual 𝕜 H)) [FiniteDimensional 𝕜 Q]
    (R : (U ⊗[𝕜] H) →ₗ[𝕜] L)
    (hR : ∀ u h, h ∈ Q.dualCoannihilator → R (u ⊗ₜ[𝕜] h) = 0)
    (ψ : Module.Dual 𝕜 L) (u : U) : scalarRestriction (ψ.comp R) u ∈ Q := by
  refine scalarRestriction_mem_of_vanishes Q (ψ.comp R) ?_ u
  intro v h hh
  change ψ (R (v ⊗ₜ[𝕜] h)) = 0
  rw [hR v h hh, map_zero]

theorem scalarRestriction_mem_coset_of_factor
    {L : Type*} [AddCommGroup L] [Module 𝕜 L]
    (Q : Submodule 𝕜 (Module.Dual 𝕜 H)) [FiniteDimensional 𝕜 Q]
    (R : (U ⊗[𝕜] H) →ₗ[𝕜] L)
    (hR : ∀ u h, h ∈ Q.dualCoannihilator → R (u ⊗ₜ[𝕜] h) = 0)
    (ψ : Module.Dual 𝕜 L) (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (a : Module.Dual 𝕜 U) (z : Module.Dual 𝕜 H) (u : U) (hu : a u = 1)
    (hΦ : Φ = pureFrequency a z + ψ.comp R) : scalarRestriction Φ u - z ∈ Q := by
  rw [hΦ, scalarRestriction_add, scalarRestriction_pure, hu, one_smul,
    add_sub_cancel_left]
  exact scalarRestriction_factor_mem Q R hR ψ u

end GeneralField

section Binary

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K H : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H]

theorem exists_value_one (a : Module.Dual F2 K) (ha : a ≠ 0) :
    ∃ w : K, a w = 1 := by
  by_contra hnone
  apply ha
  apply LinearMap.ext
  intro w
  change a w = 0
  rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (a w) with hw | hw
  · exact hw
  · exact (hnone ⟨w, hw⟩).elim

theorem exists_candidate_restriction (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 H)) (σ : Module.Dual F2 K)
    (hσ : σ.comp W.subtype ≠ 0) (z : Module.Dual F2 H)
    (Φ : Module.Dual F2 (W ⊗[F2] H))
    (hΦ : Φ - pureFrequency (σ.comp W.subtype) z ∈ equationSpace (U := W) Q) :
    ∃ w : W, σ w = 1 ∧ scalarRestriction Φ w - z ∈ Q := by
  obtain ⟨w, hw⟩ := exists_value_one (σ.comp W.subtype) hσ
  exact ⟨w, hw, scalarRestriction_sub_base_mem Q Φ (σ.comp W.subtype) z w hw hΦ⟩

theorem annihilator_iff_restriction_zero (W : Submodule F2 K) (σ : Module.Dual F2 K) :
    σ ∈ W.dualAnnihilator ↔ σ.comp W.subtype = 0 := Iff.rfl

theorem card_annihilatingCharacters [FiniteDimensional F2 K] (W : Submodule F2 K) :
    Nat.card W.dualAnnihilator =
      2 ^ (Module.finrank F2 K - Module.finrank F2 W) := by
  have hdim : Module.finrank F2 W.dualAnnihilator =
      Module.finrank F2 K - Module.finrank F2 W :=
    Nat.eq_sub_of_add_eq' (Subspace.finrank_add_finrank_dualAnnihilator_eq W)
  rw [Module.natCard_eq_pow_finrank (K := F2), hdim]
  rw [show Nat.card F2 = 2 from Nat.card_zmod 2]

end Binary
end
end PerfectCompleteness.TensorCosetEvaluation

end

section

namespace PerfectCompleteness.TensorRestriction

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {W H : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup H] [Module F2 H] [FiniteDimensional F2 H]

def tensorEquivHom : (W ⊗[F2] H) ≃ₗ[F2] (Module.Dual F2 H →ₗ[F2] W) :=
  (TensorProduct.comm F2 W H).trans
    ((TensorProduct.congr (Module.evalEquiv F2 H) (LinearEquiv.refl F2 W)).trans
      (dualTensorHomEquiv F2 (Module.Dual F2 H) W))

@[simp] theorem tensorEquivHom_tmul (w : W) (h : H) (q : Module.Dual F2 H) :
    tensorEquivHom (w ⊗ₜ[F2] h) q = q h • w := rfl

def restrictionMap (Q : Submodule F2 (Module.Dual F2 H)) :
    (W ⊗[F2] H) →ₗ[F2] (Q →ₗ[F2] W) :=
  (LinearMap.domRestrict' Q).comp tensorEquivHom.toLinearMap

@[simp] theorem restrictionMap_apply (Q : Submodule F2 (Module.Dual F2 H))
    (X : W ⊗[F2] H) (q : Q) :
    restrictionMap Q X q = tensorEquivHom X q.val := rfl

@[simp] theorem restrictionMap_tmul (Q : Submodule F2 (Module.Dual F2 H))
    (w : W) (h : H) (q : Q) :
    restrictionMap Q (w ⊗ₜ[F2] h) q = q.val h • w := rfl

theorem restrictionMap_surjective (Q : Submodule F2 (Module.Dual F2 H)) :
    Function.Surjective (restrictionMap (W := W) Q) := by
  intro f
  obtain ⟨g, hg⟩ := f.exists_extend
  refine ⟨tensorEquivHom.symm g, ?_⟩
  change (tensorEquivHom (tensorEquivHom.symm g)).comp Q.subtype = f
  rw [LinearEquiv.apply_symm_apply]
  exact hg

theorem fiber_nonempty (Q : Submodule F2 (Module.Dual F2 H)) (t : Q →ₗ[F2] W) :
    Nonempty {X : W ⊗[F2] H // restrictionMap Q X = t} := by
  obtain ⟨X, hX⟩ := restrictionMap_surjective Q t
  exact ⟨⟨X, hX⟩⟩

theorem dualMap_injective (Q : Submodule F2 (Module.Dual F2 H)) :
    Function.Injective (restrictionMap (W := W) Q).dualMap :=
  LinearMap.dualMap_injective_of_surjective (restrictionMap_surjective Q)

theorem dualMap_ne_zero (Q : Submodule F2 (Module.Dual F2 H))
    (f : Module.Dual F2 (Q →ₗ[F2] W)) (hf : f ≠ 0) :
    (restrictionMap Q).dualMap f ≠ 0 := by
  intro h
  apply hf
  apply dualMap_injective Q
  simpa only [map_zero] using h

def dualImage (Q : Submodule F2 (Module.Dual F2 H)) :
    Submodule F2 (Module.Dual F2 (W ⊗[F2] H)) :=
  LinearMap.range (restrictionMap (W := W) Q).dualMap

theorem restrictionMap_tmul_eq_zero (Q : Submodule F2 (Module.Dual F2 H))
    (w : W) (h : H) (hh : h ∈ Q.dualCoannihilator) :
    restrictionMap Q (w ⊗ₜ[F2] h) = 0 := by
  apply LinearMap.ext
  intro q
  rw [restrictionMap_tmul]
  have hq : q.val h = 0 := (Submodule.mem_dualCoannihilator h).mp hh q.val q.property
  rw [hq, zero_smul, LinearMap.zero_apply]

theorem dualImage_vanishes (Q : Submodule F2 (Module.Dual F2 H))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ∈ dualImage (W := W) Q)
    (w : W) (h : H) (hh : h ∈ Q.dualCoannihilator) :
    Φ (w ⊗ₜ[F2] h) = 0 := by
  obtain ⟨f, rfl⟩ := hΦ
  change f (restrictionMap Q (w ⊗ₜ[F2] h)) = 0
  rw [restrictionMap_tmul_eq_zero Q w h hh, map_zero]

variable [FiniteDimensional F2 W]

theorem finrank_range (Q : Submodule F2 (Module.Dual F2 H)) :
    Module.finrank F2 (LinearMap.range (restrictionMap (W := W) Q)) =
      Module.finrank F2 W * Module.finrank F2 Q := by
  let : Module.Free F2 Q := Module.Free.of_divisionRing F2 Q
  rw [LinearMap.range_eq_top.mpr (restrictionMap_surjective Q), finrank_top,
    Module.finrank_linearMap F2 F2 Q W, Nat.mul_comm]

theorem finrank_dualImage (Q : Submodule F2 (Module.Dual F2 H)) :
    Module.finrank F2 (dualImage (W := W) Q) =
      Module.finrank F2 W * Module.finrank F2 Q := by
  let : Module.Free F2 Q := Module.Free.of_divisionRing F2 Q
  rw [dualImage, LinearMap.finrank_range_of_inj (dualMap_injective Q),
    Subspace.dual_finrank_eq, Module.finrank_linearMap F2 F2 Q W, Nat.mul_comm]

theorem finrank_range_le (Q : Submodule F2 (Module.Dual F2 H)) {ℓ r : Nat}
    (hW : Module.finrank F2 W ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r) :
    Module.finrank F2 (LinearMap.range (restrictionMap (W := W) Q)) ≤ ℓ * r := by
  rw [finrank_range]
  exact Nat.mul_le_mul hW hQ

end
end PerfectCompleteness.TensorRestriction

end

section

namespace PerfectCompleteness.TensorEquationSpace

noncomputable section

open scoped BigOperators TensorProduct
open TensorCosetEvaluation

section GeneralField

variable {𝕜 U H : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup H] [Module 𝕜 H]

theorem basis_expansion {I : Type*} [Fintype I] (b : Module.Basis I 𝕜 U)
    (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H)) :
    Φ = ∑ i, pureFrequency (b.coord i) (scalarRestriction Φ (b i)) := by
  apply TensorProduct.ext'
  intro u h
  simp only [LinearMap.sum_apply, pureFrequency_tmul, scalarRestriction_apply,
    Module.Basis.coord_apply]
  have hb := congrArg (fun v : U => Φ (v ⊗ₜ[𝕜] h)) (b.sum_repr u)
  simpa only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul',
    map_sum, map_smul, smul_eq_mul] using hb.symm

variable [FiniteDimensional 𝕜 U]

theorem mem_equationSpace_of_scalarRestriction_mem
    (Q : Submodule 𝕜 (Module.Dual 𝕜 H))
    (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (hΦ : ∀ u, scalarRestriction Φ u ∈ Q) :
    Φ ∈ equationSpace (U := U) Q := by
  rw [basis_expansion (Module.finBasis 𝕜 U) Φ]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.subset_span
  exact ⟨⟨(Module.finBasis 𝕜 U).coord i,
    ⟨scalarRestriction Φ ((Module.finBasis 𝕜 U) i), hΦ _⟩⟩, rfl⟩

theorem mem_equationSpace_iff (Q : Submodule 𝕜 (Module.Dual 𝕜 H))
    (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H)) :
    Φ ∈ equationSpace (U := U) Q ↔ ∀ u, scalarRestriction Φ u ∈ Q :=
  ⟨fun hΦ u => scalarRestriction_mem Q Φ hΦ u,
    mem_equationSpace_of_scalarRestriction_mem Q Φ⟩

end GeneralField

section Binary

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {W H : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup H] [Module F2 H] [FiniteDimensional F2 H]

def pureFactor (Q : Submodule F2 (Module.Dual F2 H))
    (a : Module.Dual F2 W) (q : Q) : Module.Dual F2 (Q →ₗ[F2] W) where
  toFun T := a (T q)
  map_add' T S := by simp only [LinearMap.add_apply, map_add]
  map_smul' c T := by simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply]

omit [FiniteDimensional F2 H] in
@[simp] theorem pureFactor_apply (Q : Submodule F2 (Module.Dual F2 H))
    (a : Module.Dual F2 W) (q : Q) (T : Q →ₗ[F2] W) :
    pureFactor Q a q T = a (T q) := rfl

theorem dualMap_pureFactor (Q : Submodule F2 (Module.Dual F2 H))
    (a : Module.Dual F2 W) (q : Q) :
    (TensorRestriction.restrictionMap Q).dualMap (pureFactor Q a q) =
      pureFrequency a q.val := by
  apply TensorProduct.ext'
  intro w h
  change a (TensorRestriction.restrictionMap Q (w ⊗ₜ[F2] h) q) =
    pureFrequency a q.val (w ⊗ₜ[F2] h)
  simp only [TensorRestriction.restrictionMap_tmul, pureFrequency_tmul,
    map_smul, smul_eq_mul, mul_comm]

theorem pureFrequency_mem_dualImage (Q : Submodule F2 (Module.Dual F2 H))
    (a : Module.Dual F2 W) (q : Q) :
    pureFrequency a q.val ∈ TensorRestriction.dualImage (W := W) Q :=
  ⟨pureFactor Q a q, dualMap_pureFactor Q a q⟩

theorem equationSpace_le_dualImage (Q : Submodule F2 (Module.Dual F2 H)) :
    equationSpace (U := W) Q ≤ TensorRestriction.dualImage (W := W) Q := by
  apply Submodule.span_le.mpr
  rintro Φ ⟨⟨a, q⟩, rfl⟩
  exact pureFrequency_mem_dualImage Q a q

variable [FiniteDimensional F2 W]

theorem dualImage_le_equationSpace (Q : Submodule F2 (Module.Dual F2 H)) :
    TensorRestriction.dualImage (W := W) Q ≤ equationSpace (U := W) Q := by
  intro Φ hΦ
  apply mem_equationSpace_of_scalarRestriction_mem Q Φ
  intro w
  exact scalarRestriction_mem_of_vanishes Q Φ
    (TensorRestriction.dualImage_vanishes Q Φ hΦ) w

theorem dualImage_eq_equationSpace (Q : Submodule F2 (Module.Dual F2 H)) :
    TensorRestriction.dualImage (W := W) Q = equationSpace (U := W) Q :=
  le_antisymm (dualImage_le_equationSpace Q) (equationSpace_le_dualImage Q)

theorem finrank_equationSpace (Q : Submodule F2 (Module.Dual F2 H)) :
    Module.finrank F2 (equationSpace (U := W) Q) =
      Module.finrank F2 W * Module.finrank F2 Q := by
  rw [← dualImage_eq_equationSpace, TensorRestriction.finrank_dualImage]

end Binary
end
end PerfectCompleteness.TensorEquationSpace

end

end OAI
