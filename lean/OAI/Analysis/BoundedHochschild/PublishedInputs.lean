import OAI.Analysis.BoundedHochschild.CentralPrimitives
import OAI.Analysis.BoundedHochschild.Corners

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace CentralCorner

open HochschildCorners

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)

/-- The inclusion of a corner into its ambient algebra. -/
def includeMap : Corner p hp →L[ℂ] M :=
  (corner p hp).toNonUnitalSubalgebra.toSubmodule.subtypeL

/-- Compression to a central corner, which is an algebra homomorphism. -/
def compressMap : M →L[ℂ] Corner p hp :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨p * a, by
        constructor
        · rw [← mul_assoc, hp.isIdempotentElem.eq]
        · calc
            (p * a) * p = p * (a * p) := mul_assoc _ _ _
            _ = p * (p * a) := by rw [← hc a]
            _ = p * a := by rw [← mul_assoc, hp.isIdempotentElem.eq]⟩
      map_add' := fun a b => Subtype.ext (mul_add p a b)
      map_smul' := fun c a => Subtype.ext (by
        change p * (c • a) = c • (p * a)
        rw [mul_smul_comm]) }
    1 (fun a => by
      change ‖p * a‖ ≤ 1 * ‖a‖
      exact (norm_mul_le p a).trans (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma includeMap_apply (a : Corner p hp) : includeMap p hp a = (a : M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_coe (a : M) :
    (compressMap p hp hc a : M) = p * a := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_includeMap (a : Corner p hp) :
    compressMap p hp hc (includeMap p hp a) = a := Subtype.ext a.property.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_mul (a b : M) :
    compressMap p hp hc (a * b) = compressMap p hp hc a * compressMap p hp hc b := by
  apply Subtype.ext
  exact (central_idempotent_mul p hp.isIdempotentElem.eq hc a b).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_left_module (a : Corner p hp) (b : M) :
    compressMap p hp hc ((a : M) * b) = a * compressMap p hp hc b := by
  apply Subtype.ext
  change p * ((a : M) * b) = (a : M) * (p * b)
  rw [← mul_assoc, a.property.1, ← mul_assoc, a.property.2]

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_right_module (a : M) (b : Corner p hp) :
    compressMap p hp hc (a * (b : M)) = compressMap p hp hc a * b := by
  apply Subtype.ext
  exact (mul_assoc p a (b : M)).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_norm (a : M) : ‖compressMap p hp hc a‖ ≤ ‖a‖ := by
  exact (norm_mul_le p a).trans
    ((mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)).trans_eq (one_mul _))

/-- Restrict inputs to a central corner and compress the output. -/
def restrict {n : ℕ} (f : Cochain M n) : Cochain (Corner p hp) n :=
  (compressMap p hp hc).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun _ => includeMap p hp))

/-- Pull a corner cochain back along central compression. -/
def extend {n : ℕ} (g : Cochain (Corner p hp) n) : Cochain M n :=
  (includeMap p hp).compContinuousMultilinearMap
    (g.compContinuousLinearMap (fun _ => compressMap p hp hc))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma restrict_apply {n : ℕ} (f : Cochain M n) (x : Fin n → Corner p hp) :
    restrict p hp hc f x = compressMap p hp hc (f (fun i => (x i : M))) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma extend_apply {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    extend p hp hc g x = (g (fun i => compressMap p hp hc (x i)) : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma restrict_norm {n : ℕ} (f : Cochain M n) : ‖restrict p hp hc f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (compressMap_norm p hp hc _).trans (f.le_opNorm (fun i => (x i : M)))

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_norm {n : ℕ} (g : Cochain (Corner p hp) n) :
    ‖extend p hp hc g‖ ≤ ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => compressMap_norm p hp hc (x i)))
    (norm_nonneg _))

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_supported {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    p * extend p hp hc g x = extend p hp hc g x :=
  (g (fun i => compressMap p hp hc (x i))).property.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma merge_include {n : ℕ} (x : Fin (n + 1) → Corner p hp) (j : Fin n) :
    mergeInputs (fun i => (x i : M)) j = fun i => (mergeInputs (M := Corner p hp) x j i : M) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma merge_compress {n : ℕ} (x : Fin (n + 1) → M) (j : Fin n) :
    mergeInputs (fun i => compressMap p hp hc (x i)) j =
      fun i => compressMap p hp hc (mergeInputs x j i) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> first | rfl | exact (compressMap_mul p hp hc _ _).symm

omit [PartialOrder M] [StarOrderedRing M] in
/-- Restriction to a central corner commutes with the Hochschild differential. -/
lemma differential_restrict {n : ℕ} (f : Cochain M n)
    (x : Fin (n + 1) → Corner p hp) :
    differentialValue (restrict p hp hc f) x =
      compressMap p hp hc (differentialValue f (fun i => (x i : M))) := by
  simp only [differentialValue, restrict_apply, map_add, map_sum, map_smul,
    merge_include, compressMap_left_module, compressMap_right_module]

omit [PartialOrder M] [StarOrderedRing M] in
lemma restrict_cocycle {n : ℕ} (f : Cochain M n)
    (hf : ∀ x, differentialValue f x = 0) :
    ∀ x, differentialValue (restrict p hp hc f) x = 0 := by
  intro x
  rw [differential_restrict, hf, map_zero]

omit [PartialOrder M] [StarOrderedRing M] in
/-- A primitive on a central corner pulls back to a primitive of the central cut. -/
lemma differential_extend {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin (n + 1) → M) :
    differentialValue (extend p hp hc g) x =
      (differentialValue (M := Corner p hp) g (fun i => compressMap p hp hc (x i)) : M) := by
  change differentialValue (extend p hp hc g) x =
    includeMap p hp (differentialValue (M := Corner p hp) g (fun i => compressMap p hp hc (x i)))
  simp only [differentialValue, map_add, map_sum, map_smul, extend_apply,
    includeMap_apply, merge_compress]
  congr 2
  · change x 0 * (g _ : M) = (p * x 0) * (g _ : M)
    rw [hc (x 0), mul_assoc, (g _).property.1]
  · change (g _ : M) * x (Fin.last n) = (g _ : M) * (p * x (Fin.last n))
    rw [← mul_assoc, (g _).property.2]

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_primitive {n : ℕ} (f : Cochain M (n + 1))
    (g : Cochain (Corner p hp) n)
    (hg : ∀ x, differentialValue g x = restrict p hp hc f x)
    (x : Fin (n + 1) → M) :
    differentialValue (extend p hp hc g) x =
      centralCut p (centralOutput p f) x := by
  rw [differential_extend, hg]
  rfl

section Normality
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
/-- A central corner carries the quotient predual of its ambient algebra. -/
theorem wstar : WStarAlgebra (Corner p hp) :=
  ⟨⟨CornerPredual p hp e, inferInstance, inferInstance, inferInstance,
    ⟨cornerPredualEquiv p hp e⟩⟩⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma restrict_curryRight {n : ℕ} (f : Cochain M (n + 1))
    (a : Fin n → Corner p hp) (b : Corner p hp) :
    (restrict p hp hc f).curryRight a b =
      compressMap p hp hc (f.curryRight (fun i => (a i : M)) (b : M)) := by
  simp only [ContinuousMultilinearMap.curryRight_apply, restrict_apply]
  congr 2
  funext i
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]
  | cast i => simp only [Fin.snoc_castSucc]

/-- Restriction to a central summand preserves normality in the last input. -/
lemma restrict_last_normal {n : ℕ} (f : Cochain M (n + 1))
    (hn : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∀ a : Fin n → Corner p hp,
      HasPreadjoint (cornerPredualEquiv p hp e) ((restrict p hp hc f).curryRight a) := by
  intro a z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨z', hz'⟩ := HochschildSakai.mul_hasPreadjoint e p z
    obtain ⟨w, hw⟩ := hn (fun i => (a i : M)) z'
    refine ⟨Submodule.Quotient.mk w, fun b => ?_⟩
    calc
      _ = e.symm (p * f.curryRight (fun i => (a i : M)) (b : M)) z := by
        rw [restrict_curryRight, cornerPredualEquiv_symm_mk, compressMap_coe]
      _ = e.symm (f.curryRight (fun i => (a i : M)) (b : M)) z' := hz' _
      _ = e.symm (b : M) w := hw _
      _ = _ := (cornerPredualEquiv_symm_mk p hp e b w).symm

end Normality

end CentralCorner
end BoundedHochschild

end

end OAI
