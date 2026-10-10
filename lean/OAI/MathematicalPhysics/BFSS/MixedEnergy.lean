import Mathlib
import OAI.MathematicalPhysics.BFSS.Kinetic
import OAI.MathematicalPhysics.BFSS.PotentialSquares

namespace OAI

/-! Mixed first-order differential and potential energy identities. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def kineticComplexSymbol (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
    Fermion N →L[ℂ] Fermion N :=
  M.principalSymbol (Pi.single α 1) (EuclideanSpace.single p 1)

lemma kineticComplexSymbol_apply (α : SpinIndex) (p : SpaceIndex × ColorIndex N) (z : Fermion N) :
    M.kineticComplexSymbol α p z = M.kineticSymbol α p z := rfl

lemma kineticComplexSymbol_selfAdjoint (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
    IsSelfAdjoint (M.kineticComplexSymbol α p) := M.cliffordLinear_selfAdjoint _

lemma principalCoefficients_coordinate (α : SpinIndex) (i : SpaceIndex)
    (A : ColorIndex N) (β : SpinIndex) (B : ColorIndex N) :
    M.principalCoefficients (Pi.single α 1) (EuclideanSpace.single (i,A) 1) (β,B) =
      if A = B then M.gamma i α β else 0 := by
  rw [M.principalCoefficients_basis]
  simp [PiLp.single_apply, Prod.mk.injEq, ite_and, eq_comm]

lemma deformed_mixed_anticommutator (h m : ℝ) (x : Boson N)
    (p : SpaceIndex × ColorIndex N) :
    (∑ α : SpinIndex, (M.kineticComplexSymbol α p * M.deformedPotentialMultiplier h m x α +
      M.deformedPotentialMultiplier h m x α * M.kineticComplexSymbol α p)) = 0 := by
  simp only [kineticComplexSymbol, principalSymbol, deformedPotentialMultiplier,
    M.cliffordLinear_mixed]
  rw [← Finset.sum_smul]
  suffices hs : (∑ α : SpinIndex, ∑ r : FermionIndex N,
      M.principalCoefficients (Pi.single α 1) (EuclideanSpace.single p 1) r *
        M.deformedPotentialCoefficients h m x α r) = 0 by
    simp only [← Complex.ofReal_sum, hs, Complex.ofReal_zero, zero_smul]
  rcases p with ⟨i,A⟩
  simp only [Fintype.sum_prod_type, M.principalCoefficients_coordinate,
    deformedPotentialCoefficients, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have ht := BFSSGamma.gamma_bracketMass_trace_zero M.gamma M.gamma_clifford
    M.gamma_symmetric h m (fun p => M.coordinateBracket x p A) (fun i => x (i,A)) i
  rw [(M.gamma_symmetric i).eq] at ht
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, deformedPotentialMatrix] using ht

lemma deformedPotentialCoefficients_contDiff (h m : ℝ) (α : SpinIndex) (r : FermionIndex N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Boson N => M.deformedPotentialCoefficients h m x α r) := by
  unfold deformedPotentialCoefficients deformedPotentialMatrix BFSSGamma.bracketMassMatrix
    coordinateBracket
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  fun_prop

lemma deformedPotentialMultiplier_contDiff (h m : ℝ) (α : SpinIndex) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Boson N => M.deformedPotentialMultiplier h m x α) := by
  unfold deformedPotentialMultiplier cliffordLinear
  exact ContDiff.sum fun r _ =>
    (Complex.ofRealCLM.contDiff.comp (M.deformedPotentialCoefficients_contDiff h m α r)).smul
      contDiff_const

end
end BFSSQuantum.AlgebraData

namespace MixedEnergy
noncomputable section
open MeasureTheory Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
abbrev E := EuclideanSpace ℝ ι
abbrev Core := TestFunction (⊤ : TopologicalSpace.Opens (E (ι := ι))) F ⊤

def toL2 : Core (ι := ι) (F := F) →ₗ[ℝ] Lp F 2 (volume : Measure (E (ι := ι))) where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _f _g := MemLp.toLp_add _ _
  map_smul' c _f := MemLp.toLp_const_smul c _

omit [DecidableEq ι] [CompleteSpace F] in
lemma toL2_ae (f : Core (ι := ι) (F := F)) :
    (toL2 f : E (ι := ι) → F) =ᵐ[volume] f :=
  MemLp.coeFn_toLp (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

omit [DecidableEq ι] [CompleteSpace F] in
lemma toL2_inner (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 f) (toL2 g) = ∫ x, inner ℝ (f x) (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toL2_ae f, toL2_ae g] with x hf hg
  rw [hf,hg]

omit [DecidableEq ι] [CompleteSpace F] in
lemma inner_integrable (f g : Core (ι := ι) (F := F)) :
    Integrable (fun x => inner ℝ (f x) (g x)) (volume : Measure (E (ι := ι))) :=
  (f.continuous.inner g.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp₂_left g.hasCompactSupport (by simp))

def delta (p : ι) : Core (ι := ι) (F := F) →ₗ[ℝ] Core (ι := ι) (F := F) :=
  (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single p 1)).toLinearMap

omit [CompleteSpace F] in
lemma delta_apply (p : ι) (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    delta p f x = fderiv ℝ (f : E (ι := ι) → F) x (EuclideanSpace.single p 1) := by
  rw [delta, ContinuousLinearMap.coe_coe, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (f.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv

omit [CompleteSpace F] in
lemma delta_skew (p : ι) (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 f) (toL2 (delta p g)) = -inner ℝ (toL2 (delta p f)) (toL2 g) := by
  rw [toL2_inner, toL2_inner]
  have h1 := inner_integrable (delta p f) g
  have h2 := inner_integrable f (delta p g)
  simp only [delta_apply] at h1 h2 ⊢
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerSL ℝ) h1 h2 (inner_integrable f g)
    (fun x _hx => (f.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _hx => (g.contDiff.differentiable (by simp)).differentiableAt)

def field (V : E (ι := ι) → F →L[ℝ] F)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    Core (ι := ι) (F := F) →ₗ[ℝ] Core (ι := ι) (F := F) where
  toFun f := {
    toFun := fun x => V x (f x)
    contDiff' := hV.clm_apply f.contDiff
    hasCompactSupport' := f.hasCompactSupport.mono (by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      contrapose! hx
      simp [hx])
    tsupport_subset' := by intro x hx; trivial }
  map_add' f g := by ext x; exact map_add (V x) _ _
  map_smul' c f := by ext x; exact map_smul (V x) _ _

omit [DecidableEq ι] [CompleteSpace F] in
lemma field_apply (V : E (ι := ι) → F →L[ℝ] F)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    field V hV f x = V x (f x) := rfl

omit [CompleteSpace F] in
lemma delta_field (V : E (ι := ι) → F →L[ℝ] F)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (p : ι) (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    delta p (field V hV f) x = V x (delta p f x) +
      (fderiv ℝ V x (EuclideanSpace.single p 1)) (f x) := by
  rw [delta_apply, delta_apply]
  change fderiv ℝ (fun y => V y (f y)) x _ = _
  rw [fderiv_clm_apply (hV.differentiable (by simp)).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt]
  rfl

def post (B : F →L[ℝ] F) : Core (ι := ι) (F := F) →ₗ[ℝ] Core (ι := ι) (F := F) :=
  (TestFunction.postcompCLM B).toLinearMap

omit [DecidableEq ι] [CompleteSpace F] in
lemma post_apply (B : F →L[ℝ] F) (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    post B f x = B (f x) := rfl

omit [CompleteSpace F] in
lemma delta_post (B : F →L[ℝ] F) (p : ι) (f : Core (ι := ι) (F := F)) :
    delta p (post B f) = post B (delta p f) := by
  ext x
  have h := delta_field (fun _ : E (ι := ι) => B) contDiff_const p f x
  have he : field (fun _ : E (ι := ι) => B) contDiff_const = post B := by
    ext g y
    rfl
  rw [he] at h
  simpa only [fderiv_const_apply, zero_apply, zero_add, add_zero,
    post_apply] using h

omit [DecidableEq ι] [CompleteSpace F] in
lemma post_skew (B : F →L[ℝ] F)
    (hB : ∀ u v, inner ℝ (B u) v = -inner ℝ u (B v))
    (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 (post B f)) (toL2 g) = -inner ℝ (toL2 f) (toL2 (post B g)) := by
  rw [toL2_inner, toL2_inner, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  exact hB _ _

def firstOrder (B : ι → F →L[ℝ] F) : Core (ι := ι) (F := F) →ₗ[ℝ] Core (ι := ι) (F := F) :=
  ∑ p, (post (B p)).comp (delta p)

omit [CompleteSpace F] in
lemma firstOrder_apply (B : ι → F →L[ℝ] F) (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    firstOrder B f x = ∑ p, B p (delta p f x) := by
  simp only [firstOrder, LinearMap.sum_apply, LinearMap.comp_apply, _root_.sum_apply, post_apply]

omit [CompleteSpace F] in
lemma firstOrder_symmetric (B : ι → F →L[ℝ] F)
    (hB : ∀ p u v, inner ℝ (B p u) v = -inner ℝ u (B p v))
    (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 (firstOrder B f)) (toL2 g) =
      inner ℝ (toL2 f) (toL2 (firstOrder B g)) := by
  simp only [firstOrder, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, sum_inner, inner_sum]
  apply sum_congr rfl
  intro p hp
  rw [post_skew _ (hB p)]
  have hd := delta_skew p f (post (B p) g)
  rw [delta_post] at hd
  exact hd.symm

omit [DecidableEq ι] in
lemma field_symmetric (V : E (ι := ι) → F →L[ℝ] F)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hs : ∀ x, IsSelfAdjoint (V x)) (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 (field V hV f)) (toL2 g) =
      inner ℝ (toL2 f) (toL2 (field V hV g)) := by
  rw [toL2_inner, toL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (hs x).isSymmetric (f x) (g x)

lemma mixed_core_identity (B : ι → F →L[ℝ] F)
    (hB : ∀ p u v, inner ℝ (B p u) v = -inner ℝ u (B p v))
    (V : E (ι := ι) → F →L[ℝ] F)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hs : ∀ x, IsSelfAdjoint (V x)) (f : Core (ι := ι) (F := F)) :
    ‖toL2 (firstOrder B f + field V hV f)‖^2 =
      ‖toL2 (firstOrder B f)‖^2 + ‖toL2 (field V hV f)‖^2 +
      inner ℝ (toL2 f) (toL2 (firstOrder B (field V hV f) + field V hV (firstOrder B f))) := by
  rw [map_add, norm_add_sq_real]
  simp only [map_add, inner_add_right]
  rw [← firstOrder_symmetric B hB, ← field_symmetric V hV hs, real_inner_comm]
  ring

variable {κ : Type*} [Fintype κ]

def remainderField (B : κ → ι → F →L[ℝ] F) (V : κ → E (ι := ι) → F →L[ℝ] F)
    (x : E (ι := ι)) : F →L[ℝ] F :=
  ∑ α, ∑ p, B α p * fderiv ℝ (V α) x (EuclideanSpace.single p 1)

def remainderCore (B : κ → ι → F →L[ℝ] F) (V : κ → E (ι := ι) → F →L[ℝ] F)
    (hV : ∀ α, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V α))
    (f : Core (ι := ι) (F := F)) : Core (ι := ι) (F := F) :=
  ∑ α, (firstOrder (B α) (field (V α) (hV α) f) + field (V α) (hV α) (firstOrder (B α) f))

omit [CompleteSpace F] in
lemma remainderCore_apply (B : κ → ι → F →L[ℝ] F) (V : κ → E (ι := ι) → F →L[ℝ] F)
    (hV : ∀ α, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V α))
    (hanti : ∀ x p, ∑ α, (B α p * V α x + V α x * B α p) = 0)
    (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    remainderCore B V hV f x = remainderField B V x (f x) := by
  simp only [remainderCore, _root_.sum_apply, IsAddApply.add_apply, firstOrder_apply, field_apply,
    delta_field, map_add, map_sum, Finset.sum_add_distrib, remainderField,
    mul_apply_eq_comp]
  have hz : (∑ α, ∑ p, B α p (V α x (delta p f x))) +
      (∑ α, ∑ p, V α x (B α p (delta p f x))) = 0 := by
    rw [← sum_add_distrib]
    simp_rw [← sum_add_distrib]
    rw [sum_comm]
    apply sum_eq_zero
    intro p hp
    have ht := congrArg (fun L : F →L[ℝ] F => L (delta p f x)) (hanti x p)
    simpa only [_root_.sum_apply, add_apply,
      mul_apply_eq_comp, zero_apply] using ht
  have hh : (∑ α, ∑ p, B α p (V α x (delta p f x))) +
      (∑ α, ∑ p, B α p ((fderiv ℝ (V α) x (EuclideanSpace.single p 1)) (f x))) +
      (∑ α, ∑ p, V α x (B α p (delta p f x))) =
      (∑ α, ∑ p, B α p ((fderiv ℝ (V α) x (EuclideanSpace.single p 1)) (f x))) := by
    calc
      _ = ((∑ α, ∑ p, B α p (V α x (delta p f x))) +
          (∑ α, ∑ p, V α x (B α p (delta p f x)))) +
          (∑ α, ∑ p, B α p ((fderiv ℝ (V α) x (EuclideanSpace.single p 1)) (f x))) := by abel
      _ = _ := by rw [hz, zero_add]
  exact hh

lemma averaged_energy_identity (B : κ → ι → F →L[ℝ] F)
    (hB : ∀ α p u v, inner ℝ (B α p u) v = -inner ℝ u (B α p v))
    (V : κ → E (ι := ι) → F →L[ℝ] F)
    (hV : ∀ α, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V α))
    (hs : ∀ α x, IsSelfAdjoint (V α x)) (f : Core (ι := ι) (F := F)) :
    (∑ α, ‖toL2 (firstOrder (B α) f + field (V α) (hV α) f)‖^2) =
      (∑ α, ‖toL2 (firstOrder (B α) f)‖^2) +
      (∑ α, ‖toL2 (field (V α) (hV α) f)‖^2) +
      inner ℝ (toL2 f) (toL2 (remainderCore B V hV f)) := by
  calc
    _ = ∑ α, (‖toL2 (firstOrder (B α) f)‖^2 + ‖toL2 (field (V α) (hV α) f)‖^2 +
        inner ℝ (toL2 f) (toL2 (firstOrder (B α) (field (V α) (hV α) f) +
          field (V α) (hV α) (firstOrder (B α) f)))) := by
      apply sum_congr rfl
      intro α hα
      exact mixed_core_identity (B α) (hB α) (V α) (hV α) (hs α) f
    _ = _ := by
      simp only [sum_add_distrib, remainderCore, map_add, map_sum, inner_add_right, inner_sum]

end
end MixedEnergy

end OAI
