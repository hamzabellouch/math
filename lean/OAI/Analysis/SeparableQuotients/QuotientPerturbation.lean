import OAI.Analysis.SeparableQuotients.Model

namespace OAI

namespace SeparableQuotient

open MeasureTheory Cardinal

universe u

section Perturbation

variable {𝕜 : Type} [RCLike 𝕜]
variable {M : Type u} [NormedAddCommGroup M] [NormedSpace 𝕜 M]

/-- A quotient lift with norm bounded by 11/10 times the quotient norm. -/
theorem quotient_lift (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)] (w : M ⧸ Y) :
    ∃ y : M, Y.mkQL y = w ∧ ‖y‖ ≤ (11 / 10 : ℝ) * ‖w‖ := by
  by_cases hw : w = 0
  · subst w
    exact ⟨0, map_zero _, by simp⟩
  · have hp : 0 < ‖w‖ / 10 := div_pos (norm_pos_iff.mpr hw) (by norm_num)
    obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt w hp
    refine ⟨y, hy, ?_⟩
    linarith

noncomputable def quotientRightInverse (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)] :
    Y.mkQL.NonlinearRightInverse where
  toFun w := (quotient_lift Y w).choose
  nnnorm := 11 / 10
  bound' w := by
    simpa using (quotient_lift Y w).choose_spec.2
  right_inv' w := (quotient_lift Y w).choose_spec.1

/-- Quantitative lift constant for a perturbed quotient map. -/
noncomputable def liftConstant (b : ℝ) : ℝ := (11 / 10) / (1 - (11 / 10) * b)

theorem liftConstant_properties {b : ℝ} (_hb0 : 0 ≤ b) (hb : b ≤ 1 / 10) :
    0 < liftConstant b ∧ liftConstant b * b < 1 ∧
      ((11 / 10 : ℝ)⁻¹ - b) * liftConstant b = 1 := by
  have hd : 0 < 1 - (11 / 10 : ℝ) * b := by linarith
  dsimp [liftConstant]
  refine ⟨div_pos (by norm_num) hd, ?_, ?_⟩
  · apply (div_mul_eq_mul_div _ _ _).trans_lt
    apply (div_lt_one hd).mpr
    linarith
  · have hh : 10 - b * 11 ≠ 0 := by linarith
    have he : ((11 / 10 : ℝ)⁻¹ - b) * (11 / 10) = 1 - (11 / 10) * b := by
      norm_num
      ring
    rw [← mul_div_assoc, he, div_self hd.ne']

/-- A 1/10 perturbation of a quotient map is onto, with a quantitative nonlinear lift bound. -/
theorem perturbed_quotient_lift [CompleteSpace M]
    (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)]
    (B : M →L[𝕜] M ⧸ Y) (hB : ‖B‖ ≤ 1 / 10) (w : M ⧸ Y) :
    ∃ y : M, (Y.mkQL - B) y = w ∧ ‖y‖ ≤ liftConstant ‖B‖ * ‖w‖ := by
  have hc := liftConstant_properties (norm_nonneg B) hB
  have ha : ApproximatesLinearOn (Y.mkQL - B) Y.mkQL Set.univ ‖B‖₊ := by
    intro x _ y _
    have he : (Y.mkQL - B) x - (Y.mkQL - B) y - Y.mkQL (x - y) = -(B (x - y)) := by
      simp only [sub_apply, map_sub]
      abel
    rw [he, norm_neg]
    exact B.le_opNorm (x - y)
  have hs := ha.surjOn_closedBall_of_nonlinearRightInverse (quotientRightInverse Y)
    (b := 0) (ε := liftConstant ‖B‖ * ‖w‖)
    (mul_nonneg hc.1.le (norm_nonneg w)) (Set.subset_univ _)
  have hw : w ∈ Metric.closedBall ((Y.mkQL - B) 0)
      ((((quotientRightInverse Y).nnnorm : ℝ)⁻¹ - (‖B‖₊ : ℝ)) *
        (liftConstant ‖B‖ * ‖w‖)) := by
    simp only [map_zero, Metric.mem_closedBall, dist_zero_right]
    change ‖w‖ ≤ ((11 / 10 : ℝ)⁻¹ - ‖B‖) * (liftConstant ‖B‖ * ‖w‖)
    rw [← mul_assoc, hc.2.2, one_mul]
  obtain ⟨y, hy, he⟩ := hs hw
  exact ⟨y, he, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy⟩

/-- The image of the perturbed kernel is dense in the closure of the image of the original kernel. -/
theorem perturbed_quotient_dense [CompleteSpace M]
    (Y : Submodule 𝕜 M) [IsClosed (Y : Set M)]
    (B : M →L[𝕜] M ⧸ Y) (hB : ‖B‖ ≤ 1 / 10)
    (hBV : ∀ y : M, B y ∈ (Y.map B.toLinearMap).topologicalClosure) :
    ((Y.mkQL - B).ker.map B.toLinearMap).topologicalClosure =
      (Y.map B.toLinearMap).topologicalClosure := by
  let V := (Y.map B.toLinearMap).topologicalClosure
  let G := ((Y.mkQL - B).ker.map B.toLinearMap).topologicalClosure
  have hGV : G ≤ V := by
    apply closure_minimal _ (Submodule.isClosed_topologicalClosure _)
    rintro w ⟨x, hx, rfl⟩
    exact hBV x
  have hG : IsClosed (G : Set (M ⧸ Y)) := Submodule.isClosed_topologicalClosure _
  let := hG
  have hsmall : (‖B‖ * liftConstant ‖B‖) * (11 / 10) < 1 := by
    have hd : 0 < 1 - (11/10:ℝ)*‖B‖ := by linarith
    dsimp [liftConstant]
    calc
      ‖B‖ * (11 / 10 / (1 - 11 / 10 * ‖B‖)) * (11 / 10) =
          (‖B‖ * (11 / 10) * (11 / 10)) / (1 - 11 / 10 * ‖B‖) := by ring
      _ < 1 := (div_lt_one hd).mpr (by nlinarith [norm_nonneg B])
  have hVbound : ∀ v ∈ V, ‖G.mkQL v‖ ≤ (‖B‖ * liftConstant ‖B‖) * ‖v‖ := by
    apply closure_minimal ?_ (isClosed_le (G.mkQL.continuous.norm)
      (continuous_const.mul continuous_norm))
    rintro v ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hnx⟩ := perturbed_quotient_lift Y B hB (B y)
    have hQy : Y.mkQL y = 0 := (Submodule.Quotient.mk_eq_zero Y).mpr hy
    have hyx : y + x ∈ (Y.mkQL - B).ker := by
      change (Y.mkQL - B) (y + x) = 0
      rw [map_add, hx]
      simp [hQy]
    have hg : B (y + x) ∈ G :=
      Submodule.le_topologicalClosure _ ⟨y + x, hyx, rfl⟩
    have hzero : G.mkQL (B (y + x)) = 0 :=
      (Submodule.Quotient.mk_eq_zero G).mpr hg
    have he : G.mkQL (B y) = -G.mkQL (B x) := by
      simpa only [map_add, eq_neg_iff_add_eq_zero] using hzero
    change ‖G.mkQL (B y)‖ ≤ (‖B‖ * liftConstant ‖B‖) * ‖B y‖
    rw [he, norm_neg]
    calc
      ‖G.mkQL (B x)‖ ≤ ‖B x‖ := Submodule.Quotient.norm_mk_le G (B x)
      _ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
      _ ≤ ‖B‖ * (liftConstant ‖B‖ * ‖B y‖) :=
        mul_le_mul_of_nonneg_left hnx (norm_nonneg B)
      _ = (‖B‖ * liftConstant ‖B‖) * ‖B y‖ := (mul_assoc _ _ _).symm
  apply le_antisymm hGV
  intro v hv
  obtain ⟨z, hz, hnz⟩ := quotient_lift G (G.mkQL v)
  have hvz : v - z ∈ G := (Submodule.Quotient.eq G).mp hz.symm
  have hzV : z ∈ V := by
    have := V.sub_mem hv (hGV hvz)
    simpa using this
  have hn := hVbound z hzV
  rw [hz] at hn
  have hg0 := (liftConstant_properties (norm_nonneg B) hB).1.le
  have hnn : ‖G.mkQL v‖ ≤ (‖B‖ * liftConstant ‖B‖ * (11 / 10)) * ‖G.mkQL v‖ := by
    calc
      ‖G.mkQL v‖ ≤ (‖B‖ * liftConstant ‖B‖) * ‖z‖ := hn
      _ ≤ (‖B‖ * liftConstant ‖B‖) * ((11 / 10) * ‖G.mkQL v‖) :=
        mul_le_mul_of_nonneg_left hnz (mul_nonneg (norm_nonneg B) hg0)
      _ = _ := (mul_assoc _ _ _).symm
  have hzq : G.mkQL v = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (G.mkQL v)]
  exact (Submodule.Quotient.mk_eq_zero G).mp hzq

end Perturbation

noncomputable def equivOfBijective {𝕜 : Type} [RCLike 𝕜]
    {M N : Type u} [NormedAddCommGroup M] [NormedSpace 𝕜 M] [CompleteSpace M]
    [NormedAddCommGroup N] [NormedSpace 𝕜 N] [CompleteSpace N]
    (f : M →L[𝕜] N) (hf : Function.Bijective f) : M ≃L[𝕜] N :=
  (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquivOfContinuous f.continuous

section Predual

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

@[reducible] noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 E) := inferInstance
@[reducible] noncomputable local instance dualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 E) := inferInstance

/-- Restriction of the canonical evaluation embedding to a subspace of the dual. -/
noncomputable def evalOn (Y : Submodule 𝕜 (StrongDual 𝕜 E)) :
    E →L[𝕜] StrongDual 𝕜 Y :=
  (ContinuousLinearMap.precomp 𝕜 Y.subtypeL).comp (NormedSpace.inclusionInDoubleDual 𝕜 E)

@[simp] theorem evalOn_apply (Y : Submodule 𝕜 (StrongDual 𝕜 E)) (e : E) (y : Y) :
    evalOn Y e y = (y : StrongDual 𝕜 E) e := rfl

/-- Surjectivity from the adjoint-range hypothesis and Hahn–Banach,
using a quotient lift of the graph map. -/
theorem twisted_eval_surjective
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hY : Function.Surjective (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y)
    (hBadj : ∀ w : StrongDual 𝕜 ((StrongDual 𝕜 E) ⧸ Y),
      ∃ e : E, w.comp B = NormedSpace.inclusionInDoubleDual 𝕜 E e) :
    Function.Surjective (evalOn (Y.mkQL - B).ker) := by
  intro f
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (Y.mkQL - B).ker f
  obtain ⟨e₀, he₀⟩ := hY (g.comp Y.subtypeL)
  let z := g - NormedSpace.inclusionInDoubleDual 𝕜 E e₀
  have hz : Y ≤ z.ker := by
    intro y hy
    change g y - y e₀ = 0
    have he := DFunLike.congr_fun he₀ (⟨y, hy⟩ : Y)
    exact sub_eq_zero.mpr he.symm
  let w := Y.liftQL z hz
  obtain ⟨e₁, he₁⟩ := hBadj w
  refine ⟨e₀ + e₁, ?_⟩
  ext x
  have hx : Y.mkQL (x : StrongDual 𝕜 E) = B x := by
    have := x.property
    change Y.mkQL (x : StrongDual 𝕜 E) - B x = 0 at this
    exact sub_eq_zero.mp this
  have hw : w (Y.mkQL (x : StrongDual 𝕜 E)) = g x - (x : StrongDual 𝕜 E) e₀ := rfl
  have he := DFunLike.congr_fun he₁ (x : StrongDual 𝕜 E)
  change w (B x) = (x : StrongDual 𝕜 E) e₁ at he
  rw [hx, he] at hw
  change (x : StrongDual 𝕜 E) (e₀ + e₁) = f x
  rw [map_add, hw, ← hg x]
  abel

/-- The small quotient perturbation preserves injectivity of evaluation. -/
theorem twisted_eval_injective
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hY : Isometry (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y) (hB : ‖B‖ ≤ 1 / 10) :
    Function.Injective (evalOn (Y.mkQL - B).ker) := by
  apply (injective_iff_map_eq_zero (evalOn (Y.mkQL - B).ker)).mpr
  intro e he
  have hc := liftConstant_properties (norm_nonneg B) hB
  have hbnd : ‖evalOn Y e‖ ≤ (liftConstant ‖B‖ * ‖B‖) * ‖e‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hc.1.le (norm_nonneg B)) (norm_nonneg e))
    intro y
    obtain ⟨t, ht, hnt⟩ := perturbed_quotient_lift Y B hB (B y)
    have hQy : Y.mkQL (y : StrongDual 𝕜 E) = 0 :=
      (Submodule.Quotient.mk_eq_zero Y).mpr y.property
    have hyt : (y : StrongDual 𝕜 E) + t ∈ (Y.mkQL - B).ker := by
      change (Y.mkQL - B) ((y : StrongDual 𝕜 E) + t) = 0
      rw [map_add, ht]
      simp [hQy]
    have heyt := DFunLike.congr_fun he
      (⟨(y : StrongDual 𝕜 E) + t, hyt⟩ : (Y.mkQL - B).ker)
    change (y : StrongDual 𝕜 E) e + t e = 0 at heyt
    have hye : (y : StrongDual 𝕜 E) e = -t e := eq_neg_of_add_eq_zero_left heyt
    rw [evalOn_apply, hye, norm_neg]
    calc
      ‖t e‖ ≤ ‖t‖ * ‖e‖ := t.le_opNorm e
      _ ≤ (liftConstant ‖B‖ * ‖B y‖) * ‖e‖ :=
        mul_le_mul_of_nonneg_right hnt (norm_nonneg e)
      _ ≤ (liftConstant ‖B‖ * (‖B‖ * ‖y‖)) * ‖e‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (B.le_opNorm y) hc.1.le) (norm_nonneg e)
      _ = ((liftConstant ‖B‖ * ‖B‖) * ‖e‖) * ‖y‖ := by ring
  have hn : ‖evalOn Y e‖ = ‖e‖ :=
    Isometry.norm_map_of_map_zero (f := fun x => evalOn Y x) hY (map_zero (evalOn Y)) e
  rw [hn] at hbnd
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg e]

noncomputable def twisted_eval_equiv [CompleteSpace E]
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hYiso : Isometry (evalOn Y)) (hYsurj : Function.Surjective (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y) (hB : ‖B‖ ≤ 1 / 10)
    (hBadj : ∀ w : StrongDual 𝕜 ((StrongDual 𝕜 E) ⧸ Y),
      ∃ e : E, w.comp B = NormedSpace.inclusionInDoubleDual 𝕜 E e) :
    E ≃L[𝕜] StrongDual 𝕜 (Y.mkQL - B).ker := by
  have hi : Function.Injective (evalOn (Y.mkQL - B).ker) :=
    twisted_eval_injective Y hYiso B hB
  have hs : Function.Surjective (evalOn (Y.mkQL - B).ker) :=
    twisted_eval_surjective Y hYsurj B hBadj
  exact equivOfBijective (𝕜 := 𝕜) (M := E) (N := StrongDual 𝕜 (Y.mkQL - B).ker)
    (evalOn (Y.mkQL - B).ker) ⟨hi, hs⟩

/-- A small perturbation of a quotient map produces an isomorphic dual of the perturbed kernel. -/
theorem twist [CompleteSpace E]
    (Y : Submodule 𝕜 (StrongDual 𝕜 E)) [IsClosed (Y : Set (StrongDual 𝕜 E))]
    (hYiso : Isometry (evalOn Y)) (hYsurj : Function.Surjective (evalOn Y))
    (B : StrongDual 𝕜 E →L[𝕜] (StrongDual 𝕜 E) ⧸ Y) (hB : ‖B‖ ≤ 1 / 10)
    (hBadj : ∀ w : StrongDual 𝕜 ((StrongDual 𝕜 E) ⧸ Y),
      ∃ e : E, w.comp B = NormedSpace.inclusionInDoubleDual 𝕜 E e)
    (hBrange : B.range ≤ (Y.map B.toLinearMap).topologicalClosure) :
    CompleteSpace (Y.mkQL - B).ker ∧
      (∃ T : E ≃L[𝕜] StrongDual 𝕜 (Y.mkQL - B).ker,
        ∀ (e : E) (x : (Y.mkQL - B).ker), T e x = (x : StrongDual 𝕜 E) e) ∧
      (((Y.mkQL - B).ker).map B.toLinearMap).topologicalClosure =
        (Y.map B.toLinearMap).topologicalClosure := by
  have : IsClosed ((Y.mkQL - B).ker : Set (StrongDual 𝕜 E)) :=
    (Y.mkQL - B).isClosed_ker
  refine ⟨inferInstance, ?_, perturbed_quotient_dense Y B hB (fun y => hBrange ⟨y, rfl⟩)⟩
  let T := twisted_eval_equiv Y hYiso hYsurj B hB hBadj
  exact ⟨T, fun _ _ => rfl⟩

end Predual

end SeparableQuotient

end OAI
