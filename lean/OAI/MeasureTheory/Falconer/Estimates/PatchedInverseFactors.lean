import OAI.MeasureTheory.Falconer.Estimates.FiniteClassFactors

namespace OAI

/-! # Globally supported factors for the exact local inverse

A fixed smooth patch cutoff is inserted in both endpoint factors. It is
one on the support of the original inverse, so the finite sum stays exact.
Each individual factor retains its original support on the whole sphere.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def inverseFactorPatch (m : ℕ) (x : Space (m+3)) : ℂ :=
  (capBump (1/2) (by norm_num) (gnomonicChart (0 : Space (m+2))) x : ℝ)

theorem inverseFactorPatch_contDiff (m : ℕ) : ContDiff ℝ ∞ (inverseFactorPatch m) :=
  Complex.ofRealCLM.contDiff.comp (capBump (1/2) (by norm_num)
    (gnomonicChart (0 : Space (m+2)))).contDiff

theorem inverseFactorPatch_one (m : ℕ) (x : Space (m+3))
    (hx : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4) :
    inverseFactorPatch m x = 1 := by
  have hb : capBump (1/2) (by norm_num) (gnomonicChart (0 : Space (m+2))) x = 1 := by
    apply (capBump (1/2) (by norm_num) (gnomonicChart (0 : Space (m+2)))).one_of_mem_closedBall
    change dist x (gnomonicChart (0 : Space (m+2)) : Space (m+3)) ≤ (1/2 : ℝ)/2
    rw [dist_eq_norm]
    convert hx using 1; norm_num
  simp only [inverseFactorPatch,hb,Complex.ofReal_one]

theorem inverseFactorPatch_ne_zero (m : ℕ) (x : Space (m+3))
    (hx : inverseFactorPatch m x ≠ 0) :
    ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 := by
  have hn : capBump (1/2) (by norm_num) (gnomonicChart (0 : Space (m+2))) x ≠ 0 := by
    simpa only [inverseFactorPatch,ne_eq,Complex.ofReal_eq_zero] using hx
  have hs : x ∈ tsupport (capBump (1/2) (by norm_num)
      (gnomonicChart (0 : Space (m+2)))) := subset_closure hn
  rw [(capBump (1/2) (by norm_num) (gnomonicChart (0 : Space (m+2)))).tsupport_eq] at hs
  simpa only [Metric.mem_closedBall,dist_eq_norm,capBump] using hs

namespace SmoothSeparation

noncomputable def bilateralCutoff {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : SmoothSeparation X Y E) (ψ : E → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    SmoothSeparation X Y E where
  index := S.index
  finite := S.finite
  left := fun i x z => ψ z*S.left i x z
  right := fun i y z => ψ z*S.right i y z
  left_smooth := fun i x => hψ.mul (S.left_smooth i x)
  right_smooth := fun i y => hψ.mul (S.right_smooth i y)

theorem bilateralCutoff_value {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : SmoothSeparation X Y E) (ψ : E → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (x : X) (y : Y) (z : E) :
    (S.bilateralCutoff ψ hψ).value x y z = (ψ z)^2*S.value x y z := by
  change (∑ i : S.index, (ψ z*S.left i x z)*(ψ z*S.right i y z)) =
    (ψ z)^2*∑ i : S.index, S.left i x z*S.right i y z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem HasOrder.bilateralCutoff {X Y E V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : SmoothSeparation X Y E} {B : X → V → ℂ} {C : Y → W → ℂ} {N : ℕ}
    (h : S.HasOrder B C N) (ψ : E → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    (S.bilateralCutoff ψ hψ).HasOrder B C N := by
  obtain ⟨p,q,hpq⟩ := h
  exact ⟨p,q,fun i => ⟨(hpq i).1,(hpq i).2.1.mul_fixed ψ hψ,
    (hpq i).2.2.mul_fixed ψ hψ⟩⟩

end SmoothSeparation

theorem patched_finite_class_inverse_factors {I J X Y : Type*}
    [Countable I] [Countable J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (m j : ℕ) (B : I → Space (m+3) → ℂ) (C : J → Space (m+3) → ℂ)
    (hB : ∀ x, ContDiff ℝ ∞ (B x)) (hC : ∀ y, ContDiff ℝ ∞ (C y))
    (a : X → I) (b : Y → J) (ha : Measurable a) (hb : Measurable b) :
    ∃ S : SmoothSeparation X Y (Space (m+3)),
      S.HasOrder (fun x => B (a x)) (fun y => C (b y)) (2*j) ∧
      (∀ k : S.index, Measurable (Function.uncurry (S.left k)) ∧
        Measurable (Function.uncurry (S.right k))) ∧
      (∀ x y e, localInverseAmplitude m (fun w => B (a x) w*C (b y) w) j e = S.value x y e) ∧
      ∀ e : Sphere (m+3), ∀ k : S.index,
        (∀ x, S.left k x e ≠ 0 → (e : Space (m+3)) ∈ tsupport (B (a x))) ∧
        (∀ y, S.right k y e ≠ 0 → (e : Space (m+3)) ∈ tsupport (C (b y))) := by
  obtain ⟨S,horder,hmeas,hvalue,hsupport⟩ := finite_class_inverse_factors m j B C hB hC a b ha hb
  let ψ := inverseFactorPatch m
  have hψ := inverseFactorPatch_contDiff m
  refine ⟨S.bilateralCutoff ψ hψ,horder.bilateralCutoff ψ hψ,?_,?_,?_⟩
  · intro k
    have hleft : Measurable (fun p : X × Space (m+3) => ψ p.2) :=
      hψ.continuous.measurable.comp measurable_snd
    have hright : Measurable (fun p : Y × Space (m+3) => ψ p.2) :=
      hψ.continuous.measurable.comp measurable_snd
    exact ⟨hleft.mul (hmeas k).1,hright.mul (hmeas k).2⟩
  · intro x y e
    rw [SmoothSeparation.bilateralCutoff_value,← hvalue]
    by_cases hz : localInverseAmplitude m (fun w => B (a x) w*C (b y) w) j e = 0
    · simp only [hz,mul_zero]
    · have ht := localInverseAmplitude_tsupport m j (fun w => B (a x) w*C (b y) w)
        (subset_closure hz)
      rw [stationaryPatchMask_support,Metric.mem_closedBall,dist_eq_norm] at ht
      have hp := inverseFactorPatch_one m e ht
      simp only [ψ,hp,one_pow,one_mul]
  · intro e k
    constructor
    · intro x hx
      have hp := (mul_ne_zero_iff.mp hx).1
      have hh := inverseFactorPatch_ne_zero m e hp
      exact (hsupport e hh k).1 x (mul_ne_zero_iff.mp hx).2
    · intro y hy
      have hp := (mul_ne_zero_iff.mp hy).1
      have hh := inverseFactorPatch_ne_zero m e hp
      exact (hsupport e hh k).2 y (mul_ne_zero_iff.mp hy).2

end Falconer

end OAI
