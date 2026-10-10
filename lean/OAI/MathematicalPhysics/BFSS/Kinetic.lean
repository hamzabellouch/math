import Mathlib
import OAI.MathematicalPhysics.BFSS.CliffordSymbols

namespace OAI

/-! Constant-coefficient kinetic identities and local gradient bounds. -/

namespace BFSSKinetic
noncomputable section
open MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
abbrev E := EuclideanSpace ℝ ι
abbrev Core := TestFunction (⊤ : TopologicalSpace.Opens (E (ι := ι))) F ⊤

def delta (p : ι) : Core (ι := ι) (F := F) →ₗ[ℝ] Core (ι := ι) (F := F) :=
  (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single p 1)).toLinearMap

def post (A : F →L[ℝ] F) : Core (ι := ι) (F := F) →ₗ[ℝ] Core (ι := ι) (F := F) :=
  (TestFunction.postcompCLM A).toLinearMap

omit [DecidableEq ι] [CompleteSpace F] in
lemma post_apply (A : F →L[ℝ] F) (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    post A f x = A (f x) := rfl

omit [CompleteSpace F] in
lemma delta_apply (p : ι) (f : Core (ι := ι) (F := F)) (x : E (ι := ι)) :
    delta p f x = fderiv ℝ (f : E (ι := ι) → F) x (EuclideanSpace.single p 1) := by
  change (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single p 1) f) x = _
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (f.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv

omit [CompleteSpace F] in
lemma delta_post (p : ι) (A : F →L[ℝ] F) (f : Core (ι := ι) (F := F)) :
    delta p (post A f) = post A (delta p f) := by
  ext x
  rw [delta_apply, post_apply, delta_apply]
  change fderiv ℝ (A ∘ (f : E (ι := ι) → F)) x _ = _
  rw [fderiv_comp x A.differentiableAt
    ((f.contDiff.differentiable (by simp)).differentiableAt)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]

omit [CompleteSpace F] in
lemma delta_delta (p q : ι) (f : Core (ι := ι) (F := F)) :
    delta p (delta q f) = delta q (delta p f) := by
  ext x
  rw [delta_apply, delta_apply]
  have he (r : ι) : (delta r f : E (ι := ι) → F) =
      fun x => fderiv ℝ (f : E (ι := ι) → F) x (EuclideanSpace.single r 1) := by
    funext x
    exact delta_apply r f x
  rw [he p, he q]
  have hd : DifferentiableAt ℝ (fderiv ℝ (f : E (ι := ι) → F)) x :=
    (f.contDiff.fderiv_right (m := 1) (by norm_cast)).differentiable (by simp) |>.differentiableAt
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, zero_apply, map_zero, zero_add,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact (f.contDiff.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)).eq _ _

def toL2 : Core (ι := ι) (F := F) →ₗ[ℝ] Lp F 2 (volume : Measure (E (ι := ι))) where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

omit [DecidableEq ι] [CompleteSpace F] in
lemma toL2_ae (f : Core (ι := ι) (F := F)) :
    (toL2 f : E (ι := ι) → F) =ᵐ[volume] f :=
  MemLp.coeFn_toLp (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

omit [DecidableEq ι] [CompleteSpace F] in
lemma inner_integrable (f g : Core (ι := ι) (F := F)) :
    Integrable (fun x => inner ℝ (f x) (g x)) (volume : Measure (E (ι := ι))) :=
  (f.continuous.inner g.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp₂_left g.hasCompactSupport (by simp))

omit [DecidableEq ι] [CompleteSpace F] in
lemma toL2_inner (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 f) (toL2 g) = ∫ x, inner ℝ (f x) (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toL2_ae f, toL2_ae g] with x hf hg
  rw [hf, hg]

omit [CompleteSpace F] in
lemma delta_skew (p : ι) (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 f) (toL2 (delta p g)) =
      -inner ℝ (toL2 (delta p f)) (toL2 g) := by
  rw [toL2_inner, toL2_inner]
  have h1 := inner_integrable (delta p f) g
  have h2 := inner_integrable f (delta p g)
  simp only [delta_apply] at h1 h2 ⊢
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerSL ℝ) h1 h2 (inner_integrable f g)
    (fun x hx => (f.contDiff.differentiable (by simp)).differentiableAt)
    (fun x hx => (g.contDiff.differentiable (by simp)).differentiableAt)

omit [DecidableEq ι] in
lemma post_symmetric (A : F →L[ℝ] F) (hA : IsSelfAdjoint A)
    (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 (post A f)) (toL2 g) = inner ℝ (toL2 f) (toL2 (post A g)) := by
  rw [toL2_inner, toL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact hA.isSymmetric (f x) (g x)

variable (A : ι → F →L[ℝ] F)

def kineticDerivative : Core (ι := ι) (F := F) →ₗ[ℝ] Core (ι := ι) (F := F) :=
  ∑p, (post (A p)).comp (delta p)

omit [CompleteSpace F] in
lemma kineticDerivative_apply (f : Core (ι := ι) (F := F)) :
    kineticDerivative A f = ∑p, post (A p) (delta p f) := by
  simp only [kineticDerivative, LinearMap.sum_apply, LinearMap.comp_apply]

lemma kineticDerivative_skew (hA : ∀p, IsSelfAdjoint (A p))
    (f g : Core (ι := ι) (F := F)) :
    inner ℝ (toL2 f) (toL2 (kineticDerivative A g)) =
      -inner ℝ (toL2 (kineticDerivative A f)) (toL2 g) := by
  simp only [kineticDerivative_apply, map_sum, inner_sum, sum_inner, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← post_symmetric (A p) (hA p), delta_skew, delta_post]

omit [DecidableEq ι] [CompleteSpace F] in
lemma post_mul (B C : F →L[ℝ] F) (f : Core (ι := ι) (F := F)) :
    post B (post C f) = post (B * C) f := by
  ext x
  rfl

omit [DecidableEq ι] [CompleteSpace F] in
lemma post_add (B C : F →L[ℝ] F) (f : Core (ι := ι) (F := F)) :
    post (B + C) f = post B f + post C f := by
  ext x
  rfl

omit [CompleteSpace F] in
lemma kineticDerivative_twice_expand (f : Core (ι := ι) (F := F)) :
    kineticDerivative A (kineticDerivative A f) =
      ∑p, ∑q, post (A p * A q) (delta p (delta q f)) := by
  simp only [kineticDerivative_apply, map_sum, delta_post, post_mul]
  exact Finset.sum_comm

omit [CompleteSpace F] in
lemma kineticDerivative_twice (hCAR : ∀p q, A p * A q + A q * A p =
    (if p = q then 1 else 0))
    (f : Core (ι := ι) (F := F)) :
    kineticDerivative A (kineticDerivative A f) +
      kineticDerivative A (kineticDerivative A f) = ∑p, delta p (delta p f) := by
  rw [kineticDerivative_twice_expand]
  conv_lhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  have hp (p q : ι) :
      post (A p * A q) (delta p (delta q f)) +
        post (A q * A p) (delta q (delta p f)) =
      if p = q then delta p (delta p f) else 0 := by
    rw [delta_delta q p, ← post_add, hCAR]
    split_ifs with h
    · subst q
      ext x
      rfl
    · ext x
      rfl
  simp_rw [← Finset.sum_add_distrib, hp]
  simp

lemma kinetic_norm_sq (hA : ∀p, IsSelfAdjoint (A p))
    (hCAR : ∀p q, A p * A q + A q * A p = (if p = q then 1 else 0))
    (f : Core (ι := ι) (F := F)) :
    ‖toL2 (kineticDerivative A f)‖ ^ 2 =
      (1 / 2 : ℝ) * ∑p, ‖toL2 (delta p f)‖ ^ 2 := by
  have he := congrArg (fun g => inner ℝ (toL2 f) (toL2 g))
    (kineticDerivative_twice A hCAR f)
  simp only [map_add, inner_add_right, map_sum, inner_sum] at he
  have hs : inner ℝ (toL2 f) (toL2 (kineticDerivative A (kineticDerivative A f))) =
      - ‖toL2 (kineticDerivative A f)‖ ^ 2 := by
    rw [kineticDerivative_skew A hA, real_inner_self_eq_norm_sq]
  have hp (p : ι) : inner ℝ (toL2 f) (toL2 (delta p (delta p f))) =
      - ‖toL2 (delta p f)‖ ^ 2 := by
    rw [delta_skew, real_inner_self_eq_norm_sq]
  simp only [hs, hp, Finset.sum_neg_distrib] at he
  linarith

end
end BFSSKinetic

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory
variable {N : ℕ} (M : AlgebraData N)

lemma principalSymbol_basis_mixed (α : SpinIndex) (ξ η : Boson N) :
    M.principalSymbol (Pi.single α 1) ξ * M.principalSymbol (Pi.single α 1) η +
      M.principalSymbol (Pi.single α 1) η * M.principalSymbol (Pi.single α 1) ξ =
    ((inner ℝ ξ η : ℝ) : ℂ) • (1 : Fermion N →L[ℂ] Fermion N) := by
  let K := M.principalSymbolLinear α
  have hs (v : Boson N) : K v * K v =
      (((1 / 2 : ℝ) * ‖v‖ ^ 2 : ℝ) : ℂ) • (1 : Fermion N →L[ℂ] Fermion N) := by
    change M.principalSymbol (Pi.single α 1) v * M.principalSymbol (Pi.single α 1) v = _
    rw [M.principalSymbol_sq, basisSpinor_unit, mul_one]
  change K ξ * K η + K η * K ξ = _
  calc
    K ξ * K η + K η * K ξ = K (ξ + η) * K (ξ + η) - K ξ * K ξ - K η * K η := by
      rw [map_add]
      noncomm_ring
    _ = (((1 / 2 : ℝ) * ‖ξ + η‖ ^ 2 - (1 / 2 : ℝ) * ‖ξ‖ ^ 2 -
        (1 / 2 : ℝ) * ‖η‖ ^ 2 : ℝ) : ℂ) • (1 : Fermion N →L[ℂ] Fermion N) := by
      rw [hs, hs, hs]
      simp only [Complex.ofReal_sub]
      module
    _ = _ := by
      congr 2
      rw [norm_add_sq_real]
      ring

def kineticSymbol (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
    Fermion N →L[ℝ] Fermion N :=
  (M.principalSymbol (Pi.single α 1) (EuclideanSpace.single p 1)).restrictScalars ℝ

lemma kineticSymbol_selfAdjoint (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
    IsSelfAdjoint (M.kineticSymbol α p) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have h := (M.cliffordLinear_selfAdjoint
    (M.principalCoefficients (Pi.single α 1) (EuclideanSpace.single p 1))).isSymmetric x y
  simpa [kineticSymbol, principalSymbol, PiLp.inner_apply, real_inner_eq_re_inner, map_sum]
    using congrArg Complex.re h

lemma kineticSymbol_CAR (α : SpinIndex) (p q : SpaceIndex × ColorIndex N) :
    M.kineticSymbol α p * M.kineticSymbol α q +
      M.kineticSymbol α q * M.kineticSymbol α p = (if p = q then 1 else 0) := by
  have h := M.principalSymbol_basis_mixed α (EuclideanSpace.single p 1)
    (EuclideanSpace.single q 1)
  simp only [EuclideanSpace.inner_single_left, PiLp.single_apply] at h
  ext z : 1
  have hz := congrArg (fun A : Fermion N →L[ℂ] Fermion N => A z) h
  by_cases hpq : p = q
  · subst q
    simpa [kineticSymbol] using hz
  · simpa [kineticSymbol, hpq, Ne.symm hpq] using hz

lemma literal_kinetic_norm (α : SpinIndex) (f : SmoothCore N) :
    ‖BFSSKinetic.toL2 (BFSSKinetic.kineticDerivative (M.kineticSymbol α) f)‖ ^ 2 =
      (1 / 2 : ℝ) * ∑p : SpaceIndex × ColorIndex N,
        ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖ ^ 2 := by
  rw [BFSSKinetic.kinetic_norm_sq _ (M.kineticSymbol_selfAdjoint α) (M.kineticSymbol_CAR α)]
  congr 1

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory
variable {N : ℕ} (M : AlgebraData N)

def bracketMultiplier (α : SpinIndex) (x : Boson N) : Fermion N →L[ℂ] Fermion N :=
  ∑i : SpaceIndex, ∑j : SpaceIndex, ∑A : ColorIndex N,
    ∑B : ColorIndex N, ∑C : ColorIndex N, ∑β : SpinIndex,
      ((((1 / 2 : ℝ) * M.structureConstant A B C * M.gammaTwo i j α β : ℝ) : ℂ) *
        (x (i, B) : ℂ) * (x (j, C) : ℂ)) • M.theta β A

lemma bracketMultiplier_continuous (α : SpinIndex) : Continuous (M.bracketMultiplier α) := by
  unfold bracketMultiplier
  fun_prop

lemma kineticSymbol_apply (α : SpinIndex) (i : SpaceIndex) (A : ColorIndex N) (z : Fermion N) :
    M.kineticSymbol α (i, A) z = ∑β : SpinIndex,
      (M.gamma i α β : ℂ) • M.theta β A z := by
  change M.principalSymbol (Pi.single α 1) (EuclideanSpace.single (i, A) 1) z = _
  rw [M.principalSymbol_basis_apply]
  simp [PiLp.single_apply, Prod.mk.injEq, ite_and]

lemma kineticDerivative_pointwise (α : SpinIndex) (f : SmoothCore N) (x : Boson N) :
    BFSSKinetic.kineticDerivative (M.kineticSymbol α) f x =
      ∑ i : SpaceIndex, ∑ A : ColorIndex N, ∑ β : SpinIndex,
        (M.gamma i α β : ℂ) • M.theta β A (coordinateDerivative i A f x) := by
  rw [BFSSKinetic.kineticDerivative_apply]
  simp only [sum_apply, BFSSKinetic.post_apply, Fintype.sum_prod_type,
    M.kineticSymbol_apply]
  rfl

lemma charge_kinetic_plus_bracket (α : SpinIndex) (f : SmoothCore N) (x : Boson N) :
    M.charge α f x = (-Complex.I) • BFSSKinetic.kineticDerivative (M.kineticSymbol α) f x +
      M.bracketMultiplier α x (f x) := by
  rw [M.charge_apply, M.kineticDerivative_pointwise]
  simp only [bracketMultiplier, sum_apply,
    smul_apply, Finset.smul_sum, smul_smul]

def bracketPart (α : SpinIndex) (f : SmoothCore N) : SmoothCore N :=
  M.charge α f - (-Complex.I) • BFSSKinetic.kineticDerivative (M.kineticSymbol α) f

lemma bracketPart_apply (α : SpinIndex) (f : SmoothCore N) (x : Boson N) :
    M.bracketPart α f x = M.bracketMultiplier α x (f x) := by
  change M.charge α f x - (-Complex.I) • _ = _
  rw [M.charge_kinetic_plus_bracket]
  abel

lemma bracketPart_bound {α : SpinIndex} {K : Set (Boson N)} {C : ℝ}
    (hC : ∀ x ∈ K, ‖M.bracketMultiplier α x‖ ≤ C)
    (f : SmoothCore N) (hf : Function.support f ⊆ K) :
    ‖coreToL2 (M.bracketPart α f)‖ ≤ C * ‖coreToL2 f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coreToL2_ae (M.bracketPart α f), coreToL2_ae f] with x hp hx
  rw [hp, hx, M.bracketPart_apply]
  by_cases hfx : f x = 0
  · simp [hfx]
  · exact (M.bracketMultiplier α x).le_opNorm (f x) |>.trans
      (mul_le_mul_of_nonneg_right (hC x (hf hfx)) (norm_nonneg _))

lemma kinetic_norm_le_charge_add_bracket (α : SpinIndex) (f : SmoothCore N) :
    ‖coreToL2 (BFSSKinetic.kineticDerivative (M.kineticSymbol α) f)‖ ≤
      ‖coreToL2 (M.charge α f)‖ + ‖coreToL2 (M.bracketPart α f)‖ := by
  have he : (-Complex.I) • BFSSKinetic.kineticDerivative (M.kineticSymbol α) f =
      M.charge α f - M.bracketPart α f := by
    unfold bracketPart
    abel
  have h := congrArg (fun g : SmoothCore N => coreToL2 g) he
  simp only [map_smul, map_sub] at h
  have ht := norm_sub_le (coreToL2 (M.charge α f)) (coreToL2 (M.bracketPart α f))
  calc
    ‖coreToL2 (BFSSKinetic.kineticDerivative (M.kineticSymbol α) f)‖ =
        ‖(-Complex.I) • coreToL2 (BFSSKinetic.kineticDerivative (M.kineticSymbol α) f)‖ := by
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    _ ≤ _ := h.symm ▸ ht

lemma gradient_bound_of_kinetic_bound (α : SpinIndex) (f : SmoothCore N) {B : ℝ}
    (hB : ‖coreToL2 (BFSSKinetic.kineticDerivative (M.kineticSymbol α) f)‖ ≤ B) :
    ∑p : SpaceIndex × ColorIndex N, ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖ ^ 2 ≤
      2 * B ^ 2 := by
  have he := M.literal_kinetic_norm α f
  change ‖coreToL2 (BFSSKinetic.kineticDerivative (M.kineticSymbol α) f)‖ ^ 2 = _ at he
  have hs := pow_le_pow_left₀ (norm_nonneg _) hB 2
  nlinarith only [he, hs]

lemma compact_bracket_bound {K : Set (Boson N)} (hK : IsCompact K) (α : SpinIndex) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖M.bracketMultiplier α x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (M.bracketMultiplier_continuous α).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left C 0)⟩

attribute [local irreducible] coreToL2 charge bracketPart BFSSKinetic.kineticDerivative

theorem local_gradient_bound {K : Set (Boson N)} (hK : IsCompact K) (α : SpinIndex) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothCore N, Function.support f ⊆ K →
      ∑p : SpaceIndex × ColorIndex N, ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖ ^ 2 ≤
        2 * (‖coreToL2 (M.charge α f)‖ + C * ‖coreToL2 f‖) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := M.compact_bracket_bound hK α
  refine ⟨C, hC, ?_⟩
  intro f hf
  have hr := M.bracketPart_bound (α := α) (K := K) (C := C) hb f hf
  apply M.gradient_bound_of_kinetic_bound α f
  calc
    ‖coreToL2 (BFSSKinetic.kineticDerivative (M.kineticSymbol α) f)‖ ≤
        ‖coreToL2 (M.charge α f)‖ + ‖coreToL2 (M.bracketPart α f)‖ :=
      M.kinetic_norm_le_charge_add_bracket α f
    _ ≤ ‖coreToL2 (M.charge α f)‖ + C * ‖coreToL2 f‖ := add_le_add (le_refl _) hr

end
end BFSSQuantum.AlgebraData

end OAI
