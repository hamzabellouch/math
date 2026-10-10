import OAI.Geometry.SurfaceImmersion.Correction.SmoothSpanSolve
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCalculus
import OAI.Geometry.SurfaceImmersion.Geometry.IntegratedCovariance
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicVanishing

namespace OAI

/-! The periodic corrector constructed smoothly over finite-dimensional
families of geometric data. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.PeriodicCorrector

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def correctorFamily (V : A → C(Period, E)) (r : A → C(Period, ℝ)) (q : A → ℝ) :
    A → C(Period, E) := fun p =>
  ⟨parameterCorrector V r q p, by
    unfold parameterCorrector correctedVector correctedScalar
    exact continuous_const.smul ((((r p).continuous.add
      ((((V p).continuous.sub continuous_const).inner continuous_const).div_const _)).smul
        (V p).continuous).sub continuous_const)⟩

/-- A smooth family of solutions of the angular equations, with zero mean.
The varying subspace is used only for orthogonality and membership; the
actual covariance solve takes place in the fixed ambient Euclidean space. -/
theorem solve_smooth_family (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiff ℝ ∞ Y) (hC : ContDiff ℝ ∞ C) (hX₀ : ContDiff ℝ ∞ X₀)
    (hdet : ∀ p, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p t, V p t ∈ S p)
    (hV : ContDiff ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)))
    (q : A → ℝ) (hq : ContDiff ℝ ∞ q) (hqpos : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p)
    (h K e : A → C(Period, ℝ))
    (hhs : ContDiff ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)))
    (hKs : ContDiff ℝ ∞ (fun z : A × ℝ => K z.1 (z.2 : Period)))
    (hes : ContDiff ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)))
    (hmh : ∀ p, average (h p) = 0) (hmK : ∀ p, average (K p) = 0)
    (hme : ∀ p, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiff ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) ∧
      ContDiff ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) ∧
      (∀ p, average (U p) = 0) ∧
      (∀ (p : A) (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period)) (D p (t : Period)) t) ∧
      (∀ p t, inner ℝ (C p) (U p t) = K p t ∧ inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ p (t : ℝ), inner ℝ (Y p) (U p (t : Period)) =
        PeriodicPrimitive.primitive (fun s : ℝ => h p (s : Period)) t) ∧
      (∀ p, h p = 0 → K p = 0 → e p = 0 → U p = 0) := by
  let H : A → C(Period, ℝ) := primitiveFamily h hhs hmh
  let K' : A → C(Period, ℝ) := derivativeFamily K hKs
  have hHs : ContDiff ℝ ∞ (fun z : A × ℝ => H z.1 (z.2 : Period)) :=
    primitiveFamily_smooth h hhs hmh
  have hK's : ContDiff ℝ ∞ (fun z : A × ℝ => K' z.1 (z.2 : Period)) :=
    derivativeFamily_smooth K hKs
  let T : A → C(Period, E) := fun p =>
    ⟨fun t => spanSolve (Y p) (C p) (H p t, K p t),
      (spanSolve (Y p) (C p)).continuous.comp ((H p).continuous.prodMk (K p).continuous)⟩
  let T' : A → C(Period, E) := fun p =>
    ⟨fun t => spanSolve (Y p) (C p) (h p t, K' p t),
      (spanSolve (Y p) (C p)).continuous.comp ((h p).continuous.prodMk (K' p).continuous)⟩
  have hTs : ContDiff ℝ ∞ (fun z : A × ℝ => T z.1 (z.2 : Period)) :=
    contDiff_spanSolve (hY.comp contDiff_fst) (hC.comp contDiff_fst)
      (hHs.prodMk hKs) (fun z => hdet z.1)
  have hT's : ContDiff ℝ ∞ (fun z : A × ℝ => T' z.1 (z.2 : Period)) :=
    contDiff_spanSolve (hY.comp contDiff_fst) (hC.comp contDiff_fst)
      (hhs.prodMk hK's) (fun z => hdet z.1)
  have hTd (p : A) (t : ℝ) : HasDerivAt (fun s : ℝ => T p (s : Period)) (T' p (t : Period)) t :=
    (spanSolve (Y p) (C p)).hasFDerivAt.comp_hasDerivAt t
      ((primitiveFamily_hasDerivAt h hhs hmh p t).prodMk (derivativeFamily_hasDerivAt K hKs p t))
  let X : A → C(Period, E) := fun p => ContinuousMap.const Period (X₀ p) + V p
  have hXs : ContDiff ℝ ∞ (fun z : A × ℝ => X z.1 (z.2 : Period)) :=
    (hX₀.comp contDiff_fst).add hV
  let a : A → C(Period, ℝ) := fun p =>
    ⟨fun t => inner ℝ (X p t) (T' p t), (X p).continuous.inner (T' p).continuous⟩
  have has : ContDiff ℝ ∞ (fun z : A × ℝ => a z.1 (z.2 : Period)) := hXs.inner ℝ hT's
  let r : A → C(Period, ℝ) := fun p => e p - (a p - ContinuousMap.const Period (average (a p)))
  have hrs : ContDiff ℝ ∞ (fun z : A × ℝ => r z.1 (z.2 : Period)) :=
    hes.sub (has.sub ((contDiff_average_joint has).comp contDiff_fst))
  have hr0 (p : A) : average (r p) = 0 := by
    change average (fun t => e p t - fluctuation (a p) t) = 0
    rw [average_sub (f := e p) (g := fluctuation (a p)) (e p).continuous
      ((a p).continuous.sub continuous_const), hme p, average_fluctuation (a p).continuous, sub_self]
  let W : A → C(Period, E) := correctorFamily V r q
  have hWs : ContDiff ℝ ∞ (fun z : A × ℝ => W z.1 (z.2 : Period)) :=
    contDiff_parameterCorrector_joint hV hrs hq hqpos hcircle
  have hW0 (p : A) : average (W p) = 0 := parameterCorrector_average hqpos hcircle p
  let Z : A → C(Period, E) := primitiveFamily W hWs hW0
  have hZs : ContDiff ℝ ∞ (fun z : A × ℝ => Z z.1 (z.2 : Period)) :=
    primitiveFamily_smooth W hWs hW0
  have hWmem (p : A) (t : Period) : W p t ∈ S p :=
    parameterCorrector_mem_submodule S V r q hVmem hqpos hcircle p t
  have hZmem (p : A) (t : Period) : Z p t ∈ S p := by
    refine Quotient.inductionOn' t ?_
    intro x
    exact PeriodicPrimitive.primitive_mem_submodule (S p)
      ((W p).continuous.comp (AddCircle.continuous_mk' 1)) (fun s => hWmem p (s : Period)) x
  let U : A → C(Period, E) := fun p => T p + Z p
  let D : A → C(Period, E) := fun p => T' p + W p
  have hU0 (p : A) : average (U p) = 0 := by
    change average (fun t => T p t + Z p t) = 0
    rw [average_add (f := T p) (g := Z p) (T p).continuous (Z p).continuous]
    have ht0 := average_spanSolve (Y p) (C p) (H p).continuous (K p).continuous
      (primitiveFamily_mean_zero h hhs hmh p) (hmK p)
    change average (T p) = 0 at ht0
    rw [ht0, zero_add]
    exact primitiveFamily_mean_zero W hWs hW0 p
  refine ⟨U, D, hTs.add hZs, hT's.add hWs, hU0, ?_, ?_, ?_, ?_, ?_⟩
  · intro p t
    exact (hTd p t).add (primitiveFamily_hasDerivAt W hWs hW0 p t)
  · intro p t
    have hy := hPY p (W p t) (hWmem p t)
    have hc := hPC p (Z p t) (hZmem p t)
    change inner ℝ (C p) (T p t + Z p t) = _ ∧ inner ℝ (Y p) (T' p t + W p t) = _
    rw [inner_add_right, hc, add_zero, inner_add_right, hy, add_zero]
    exact ⟨(spanSolve_pairings (Y p) (C p) (hdet p) _).2,
      (spanSolve_pairings (Y p) (C p) (hdet p) _).1⟩
  · intro p
    have hs := parameterCorrector_projection hr0 hqpos hcircle p
    have heq : (fun t => inner ℝ (X₀ p + V p t) (D p t)) =
        (fun t => a p t + inner ℝ (V p t) (W p t)) := by
      funext t
      change inner ℝ (X₀ p + V p t) (T' p t + W p t) =
        inner ℝ (X₀ p + V p t) (T' p t) + inner ℝ (V p t) (W p t)
      simp only [inner_add_right, inner_add_left, hPX p _ (hWmem p t), zero_add]
    rw [heq]
    change (fun t => a p t + inner ℝ (V p t) (W p t) -
      average (fun s => a p s + inner ℝ (V p s) (W p s))) = e p
    rw [average_add (a p).continuous ((V p).continuous.inner (W p).continuous)]
    funext t
    have ht := congrFun hs t
    change inner ℝ (V p t) (W p t) - average (fun s => inner ℝ (V p s) (W p s)) =
      e p t - (a p t - average (a p)) at ht
    linarith
  · intro p t
    change inner ℝ (Y p) (T p (t : Period) + Z p (t : Period)) = _
    rw [inner_add_right, hPY p _ (hZmem p (t : Period)), add_zero]
    exact (spanSolve_pairings (Y p) (C p) (hdet p) _).1
  · intro p hh hK he
    have hHp : H p = 0 := primitiveFamily_zero_at h hhs hmh hh
    have hK'p : K' p = 0 := derivativeFamily_zero_at K hKs hK
    have hTp : T p = 0 := by
      ext t
      change spanSolve (Y p) (C p) (H p t, K p t) = 0
      rw [hHp, hK]
      exact (spanSolve (Y p) (C p)).map_zero
    have hT'p : T' p = 0 := by
      ext t
      change spanSolve (Y p) (C p) (h p t, K' p t) = 0
      rw [hh, hK'p]
      exact (spanSolve (Y p) (C p)).map_zero
    have hap : a p = 0 := by
      ext t
      change inner ℝ (X p t) (T' p t) = 0
      rw [hT'p]
      exact inner_zero_right _
    have hrp : r p = 0 := by
      ext t
      change e p t - (a p t - average (a p)) = 0
      rw [he, hap]
      change (0 : ℝ) - (0 - average (fun _ => (0 : ℝ))) = 0
      rw [average_const, sub_self, sub_self]
    have hWp : W p = 0 := by
      ext t
      exact parameterCorrector_zero (fun s => congrArg (fun f : C(Period, ℝ) => f s) hrp) t
    have hZp : Z p = 0 := primitiveFamily_zero_at W hWs hW0 hWp
    change T p + Z p = 0
    rw [hTp, hZp, add_zero]

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
