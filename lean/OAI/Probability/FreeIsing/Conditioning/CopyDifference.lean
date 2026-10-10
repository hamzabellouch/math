import Mathlib

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

def pullback {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ p hp).toContinuousLinearMap

theorem pullback_ae {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) (f : Lp ℝ 2 μ) :
    pullback hp f =ᵐ[ν] fun z => f (p z) :=
  Lp.coeFn_compMeasurePreserving f hp

@[simp] theorem norm_pullback {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) (f : Lp ℝ 2 μ) :
    ‖pullback hp f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f hp

theorem pullback_comp {μ : Measure A} {ν : Measure B} {ρ : Measure C}
    {p : B → A} {q : C → B}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ρ ν) :
    pullback (hp.comp hq) = (pullback hq).comp (pullback hp) := by
  ext1 f
  exact Lp.compMeasurePreserving_comp_apply f hp hq

def operator {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν := pullback hp - pullback hq

theorem operator_ae {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) :
    operator hp hq f =ᵐ[ν] fun z => f (p z) - f (q z) := by
  have hd := Lp.coeFn_sub (pullback hp f) (pullback hq f)
  exact hd.trans ((pullback_ae hp f).sub (pullback_ae hq f))

theorem norm_operator_apply_le {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) : ‖operator hp hq f‖ ≤ 2 * ‖f‖ := by
  calc
    ‖operator hp hq f‖ ≤ ‖pullback hp f‖ + ‖pullback hq f‖ := norm_sub_le _ _
    _ = 2 * ‖f‖ := by rw [norm_pullback, norm_pullback]; ring

theorem norm_operator_le {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ) :
    ‖operator hp hq‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (norm_operator_apply_le hp hq)

theorem operator_eq_zero_of_ae_const
    {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) (c : ℝ) (hf : f =ᵐ[μ] fun _ => c) :
    operator hp hq f = 0 := by
  apply Lp.ext
  filter_upwards [operator_ae hp hq f, hp.quasiMeasurePreserving.ae hf,
    hq.quasiMeasurePreserving.ae hf, Lp.coeFn_zero ℝ 2 ν] with z hz hpz hqz hzero
  simpa only [hz, hpz, hqz, sub_self, Pi.zero_apply] using hzero.symm

theorem operator_eq_zero_iff
    {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) :
    operator hp hq f = 0 ↔ (fun z => f (p z)) =ᵐ[ν] (fun z => f (q z)) := by
  constructor
  · intro h
    have hzero := Lp.coeFn_zero ℝ 2 ν
    have hae := operator_ae hp hq f
    rw [h] at hae
    filter_upwards [hae, hzero] with z hz hz0
    exact sub_eq_zero.mp (hz.symm.trans hz0)
  · intro h
    apply Lp.ext
    filter_upwards [operator_ae hp hq f, h, Lp.coeFn_zero ℝ 2 ν] with z hz he hz0
    simpa only [hz, he, sub_self, Pi.zero_apply] using hz0.symm

theorem intertwines
    {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    {T : A → A} {S : B → B}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (hpT : p ∘ S = T ∘ p) (hqT : q ∘ S = T ∘ q) :
    (pullback hS).comp (operator hp hq) =
      (operator hp hq).comp (pullback hT) := by
  unfold operator
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ← pullback_comp hp hS, ← pullback_comp hq hS,
    ← pullback_comp hT hp, ← pullback_comp hT hq]
  have congr_pullback {r s : B → A} (hr : MeasurePreserving r ν μ)
      (hs : MeasurePreserving s ν μ) (h : r = s) : pullback hr = pullback hs := by
    subst s
    rfl
  rw [congr_pullback (hp.comp hS) (hT.comp hp) hpT,
    congr_pullback (hq.comp hS) (hT.comp hq) hqT]

section ClosedRange

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rangeClosure (D : E →L[ℝ] F) : Submodule ℝ F :=
  D.toLinearMap.range.topologicalClosure

instance rangeClosure_completeSpace [CompleteSpace F] (D : E →L[ℝ] F) :
    CompleteSpace (rangeClosure D) := by
  unfold rangeClosure
  infer_instance

def toRangeClosure (D : E →L[ℝ] F) : E →L[ℝ] rangeClosure D :=
  D.codRestrict (rangeClosure D) fun x =>
    D.toLinearMap.range.le_topologicalClosure ⟨x, rfl⟩

@[simp] theorem coe_toRangeClosure (D : E →L[ℝ] F) (x : E) :
    (toRangeClosure D x : F) = D x := rfl

theorem denseRange_toRangeClosure (D : E →L[ℝ] F) :
    DenseRange (toRangeClosure D) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  intro y
  rw [← Set.range_comp]
  exact y.property

theorem mapsTo_rangeClosure (D : E →L[ℝ] F) (A : E →L[ℝ] E) (T : F →L[ℝ] F)
    (h : ∀ x, T (D x) = D (A x)) :
    Set.MapsTo T (rangeClosure D) (rangeClosure D) := by
  have hr : Set.MapsTo T (Set.range D) (Set.range D) := by
    rintro y ⟨x, rfl⟩
    exact ⟨A x, (h x).symm⟩
  exact hr.closure T.continuous

def restrictToRangeClosure (D : E →L[ℝ] F) (A : E →L[ℝ] E) (T : F →L[ℝ] F)
    (h : ∀ x, T (D x) = D (A x)) : rangeClosure D →L[ℝ] rangeClosure D :=
  T.restrict (mapsTo_rangeClosure D A T h)

theorem intertwines_toRangeClosure (D : E →L[ℝ] F)
    (A : E →L[ℝ] E) (T : F →L[ℝ] F) (h : ∀ x, T (D x) = D (A x)) :
    (restrictToRangeClosure D A T h).comp (toRangeClosure D) =
      (toRangeClosure D).comp A := by
  ext1 x
  apply Subtype.ext
  exact h x

end ClosedRange

section HilbertRange

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem isSelfAdjoint_restrictToRangeClosure (D : E →L[ℝ] F)
    (A : E →L[ℝ] E) (T : F →L[ℝ] F) (h : ∀ x, T (D x) = D (A x))
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (restrictToRangeClosure D A T h) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact hT.isSymmetric x.val y.val

end HilbertRange

end Problem367.CopyDifference

end

end OAI
