import Mathlib

namespace OAI

/-! Compression. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Compression

section Multiplication

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def fieldAction (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) :
    Lp E 2 μ →L[ℂ] Lp E 2 μ := by
  let mem : ∀ u : Lp E 2 μ, MemLp (fun t => L t (u t)) 2 μ := fun u =>
    ((Lp.memLp u).norm.const_mul C).mono
      ((show Continuous (fun z : (E →L[ℂ] E) × E => z.1 z.2) by fun_prop).comp_aestronglyMeasurable (hL.prodMk (Lp.aestronglyMeasurable u)))
      (hLn.mono fun t ht => by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, abs_norm]
        exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _)))
  let M : Lp E 2 μ →ₗ[ℂ] Lp E 2 μ := {
    toFun u := (mem u).toLp _
    map_add' u v := by
      apply Lp.ext
      filter_upwards [(mem (u + v)).coeFn_toLp, (mem u).coeFn_toLp,
        (mem v).coeFn_toLp, Lp.coeFn_add u v,
        Lp.coeFn_add ((mem u).toLp _) ((mem v).toLp _)] with t huv hu hv ha hb
      simp only [huv, hb, hu, hv, ha, map_add, Pi.add_apply]
    map_smul' c u := by
      apply Lp.ext
      filter_upwards [(mem (c • u)).coeFn_toLp, (mem u).coeFn_toLp,
        Lp.coeFn_smul c u, Lp.coeFn_smul c ((mem u).toLp _)] with t hcu hu ha hb
      simp only [hcu, hb, hu, ha, map_smul, Pi.smul_apply, RingHom.id_apply] }
  apply M.mkContinuous C
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(mem u).coeFn_toLp, hLn] with t ht hn
  change ‖((mem u).toLp _) t‖ ≤ C * ‖u t‖
  rw [ht]
  exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem fieldAction_apply_ae (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) (u : Lp E 2 μ) :
    fieldAction L hL C hC hLn u =ᵐ[μ] fun t => L t (u t) := by
  unfold fieldAction
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

theorem norm_fieldAction_le (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) :
    ‖fieldAction L hL C hC hLn‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldAction_apply_ae L hL C hC hLn u, hLn] with t ht hn
  rw [ht]
  exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

variable [CompleteSpace E]

theorem adjoint_fieldAction (L M : α → E →L[ℂ] E)
    (hL : AEStronglyMeasurable L μ) (hM : AEStronglyMeasurable M μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) (hMn : ∀ᵐ t ∂μ, ‖M t‖ ≤ C)
    (ha : ∀ᵐ t ∂μ, ContinuousLinearMap.adjoint (L t) = M t) :
    ContinuousLinearMap.adjoint (fieldAction L hL C hC hLn) =
      fieldAction M hM C hC hMn := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldAction_apply_ae M hM C hC hMn u,
    fieldAction_apply_ae L hL C hC hLn v, ha] with t hu hv ht
  rw [hu, hv, ← ht, ContinuousLinearMap.adjoint_inner_left]

end Multiplication

section Isometry

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def orbit (R : C(α, E →L[ℂ] E)) : E →ₗ[ℂ] C(α, E) where
  toFun x := ⟨fun t => R t x, R.continuous.clm_apply continuous_const⟩
  map_add' x y := by ext t; exact (R t).map_add x y
  map_smul' c x := by ext t; exact (R t).map_smul c x

def lift (R : C(α, E →L[ℂ] E)) : E →ₗ[ℂ] Lp E 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).toLinearMap.comp (orbit R)

omit [CompleteSpace E] in
theorem lift_apply_ae (R : C(α, E →L[ℂ] E)) (x : E) :
    lift (μ := μ) R x =ᵐ[μ] fun t => R t x :=
  ContinuousMap.coeFn_toLp μ (orbit R x)

theorem inner_lift (R : C(α, E →L[ℂ] E)) (x y : E) :
    ⟪lift (μ := μ) R x, lift (μ := μ) R y⟫_ℂ =
      ⟪x, (∫ t, star (R t) * R t ∂μ) y⟫_ℂ := by
  have hi : Integrable (fun t => star (R t) * R t) μ :=
    (R.continuous.star.mul R.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [L2.inner_def, ContinuousLinearMap.integral_apply hi,
    ← integral_inner (𝕜 := ℂ) (f := fun t => (star (R t) * R t) y)
      ((ContinuousLinearMap.apply ℂ E y).integrable_comp hi) x]
  apply integral_congr_ae
  filter_upwards [lift_apply_ae R x, lift_apply_ae R y] with t hx hy
  rw [hx, hy]
  exact (ContinuousLinearMap.adjoint_inner_right (R t) x (R t y)).symm

def isometry (R : C(α, E →L[ℂ] E)) (hmass : ∫ t, star (R t) * R t ∂μ = 1) :
    E →ₗᵢ[ℂ] Lp E 2 μ :=
  (lift R).isometryOfInner fun x y => by rw [inner_lift, hmass]; rfl

@[simp] theorem isometry_apply (R : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1) (x : E) :
    isometry R hmass x = lift R x := rfl

theorem integral_eq_compression (R L : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hLn : ∀ t, ‖L t‖ ≤ C) :
    (∫ t, star (R t) * L t * R t ∂μ) =
      (isometry R hmass).toContinuousLinearMap.adjoint.comp
        ((fieldAction L L.continuous.aestronglyMeasurable C hC
          (Filter.Eventually.of_forall hLn)).comp (isometry R hmass).toContinuousLinearMap) := by
  have hi : Integrable (fun t => star (R t) * L t * R t) μ :=
    ((R.continuous.star.mul L.continuous).mul R.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.integral_apply hi,
    ← integral_inner (𝕜 := ℂ) (f := fun t => (star (R t) * L t * R t) y)
      ((ContinuousLinearMap.apply ℂ E y).integrable_comp hi) x]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, isometry_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lift_apply_ae R x,
    fieldAction_apply_ae L L.continuous.aestronglyMeasurable C hC
      (Filter.Eventually.of_forall hLn) (lift R y), lift_apply_ae R y] with t hx hL hy
  rw [hx, hL, hy]
  exact ContinuousLinearMap.adjoint_inner_right (R t) x (L t (R t y))

theorem norm_integral_le (R L : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hLn : ∀ t, ‖L t‖ ≤ C) :
    ‖∫ t, star (R t) * L t * R t ∂μ‖ ≤ C := by
  rw [integral_eq_compression R L hmass C hC hLn]
  let V := (isometry R hmass).toContinuousLinearMap
  have hn : ‖V‖ ≤ 1 := (isometry R hmass).norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖V.adjoint‖ * (‖fieldAction L L.continuous.aestronglyMeasurable C hC
        (Filter.Eventually.of_forall hLn)‖ * ‖V‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (C * 1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul hn (mul_le_mul (norm_fieldAction_le _ _ _ _ _) hn
        (norm_nonneg V) hC) (mul_nonneg (norm_nonneg _) (norm_nonneg V)) (by norm_num)
    _ = C := by ring

def densityRoot (Λ : C(α, E →L[ℂ] E)) (hΛ : ∀ t, 0 ≤ Λ t) : C(α, E →L[ℂ] E) :=
  ⟨fun t => CFC.sqrt (Λ t),
    CFC.continuousOn_sqrt.comp_continuous Λ.continuous (fun t => hΛ t)⟩

omit [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α] in
@[simp] theorem densityRoot_star_mul (Λ : C(α, E →L[ℂ] E)) (hΛ : ∀ t, 0 ≤ Λ t)
    (t : α) : star (densityRoot Λ hΛ t) * densityRoot Λ hΛ t = Λ t := by
  change star (CFC.sqrt (Λ t)) * CFC.sqrt (Λ t) = _
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq, CFC.sqrt_mul_sqrt_self _ (hΛ t)]

def densityIsometry (Λ : C(α, E →L[ℂ] E)) (hΛ : ∀ t, 0 ≤ Λ t)
    (hmass : ∫ t, Λ t ∂μ = 1) : E →ₗᵢ[ℂ] Lp E 2 μ :=
  isometry (densityRoot Λ hΛ) (by simpa only [densityRoot_star_mul] using hmass)

theorem densityIsometry_apply_ae (Λ : C(α, E →L[ℂ] E)) (hΛ : ∀ t, 0 ≤ Λ t)
    (hmass : ∫ t, Λ t ∂μ = 1) (x : E) :
    densityIsometry Λ hΛ hmass x =ᵐ[μ] fun t => CFC.sqrt (Λ t) x :=
  lift_apply_ae (densityRoot Λ hΛ) x

end Isometry

end CrouzeixHilbert.Compression

end

end OAI
