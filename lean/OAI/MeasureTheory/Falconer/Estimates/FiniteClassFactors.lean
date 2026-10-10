import OAI.MeasureTheory.Falconer.Measures.SeparatedSupport
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! # Measurable endpoint factors from finite Borel classifications

The angular derivatives are taken on finite families of smooth symbols.
Pulling the resulting factors back along measurable endpoint classifiers
retains joint measurability, with no measurability assumption on a
parameter-dependent derivative. Countable labels allow all scale-indexed
finite families to be included before choosing the uniform constants.
-/

namespace Falconer
open MeasureTheory
open scoped ContDiff

variable {I J X Y E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

namespace SymbolOrder

theorem reindex {B : I → V → ℂ} {F : I → E → ℂ} {q : ℕ}
    (h : SymbolOrder B F q) (a : X → I) :
    SymbolOrder (fun x => B (a x)) (fun x => F (a x)) q := by
  refine ⟨fun x => h.smooth (a x),?_⟩
  intro K hK r
  obtain ⟨A,hA,hAb⟩ := h.bound K hK r
  exact ⟨A,hA,fun x => hAb (a x)⟩

end SymbolOrder

namespace SmoothSeparation

noncomputable def reindex (S : SmoothSeparation I J E) (a : X → I) (b : Y → J) :
    SmoothSeparation X Y E where
  index := S.index
  finite := S.finite
  left := fun i x => S.left i (a x)
  right := fun i y => S.right i (b y)
  left_smooth := fun i x => S.left_smooth i (a x)
  right_smooth := fun i y => S.right_smooth i (b y)

@[simp] theorem reindex_value (S : SmoothSeparation I J E) (a : X → I) (b : Y → J)
    (x : X) (y : Y) (e : E) :
    (S.reindex a b).value x y e = S.value (a x) (b y) e := rfl

theorem HasOrder.reindex {S : SmoothSeparation I J E} {B : I → V → ℂ}
    {C : J → W → ℂ} {N : ℕ} (h : S.HasOrder B C N) (a : X → I) (b : Y → J) :
    (S.reindex a b).HasOrder (fun x => B (a x)) (fun y => C (b y)) N := by
  obtain ⟨p,q,hpq⟩ := h
  exact ⟨p,q,fun i => ⟨(hpq i).1,(hpq i).2.1.reindex a,(hpq i).2.2.reindex b⟩⟩

end SmoothSeparation

omit [NormedSpace ℝ E] in
theorem finite_class_smooth_measurable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace E] [BorelSpace E]
    (F : I → E → ℂ) (hF : ∀ i, Continuous (F i)) (a : X → I) (ha : Measurable a) :
    Measurable (fun p : X × E => F (a p.1) p.2) := by
  have h : Measurable (Function.uncurry F) :=
    measurable_from_prod_countable_right (fun i => (hF i).measurable)
  exact h.comp ((ha.comp measurable_fst).prodMk measurable_snd)

theorem finite_class_inverse_factors [Countable I] [Countable J]
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
      ∀ e : Sphere (m+3),
        ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 →
        ∀ k : S.index,
          (∀ x, S.left k x e ≠ 0 → (e : Space (m+3)) ∈ tsupport (B (a x))) ∧
          (∀ y, S.right k y e ≠ 0 → (e : Space (m+3)) ∈ tsupport (C (b y))) := by
  obtain ⟨S,horder,hvalue,hsupport⟩ := localInverseAmplitude_product_factors m j B C hB hC
  refine ⟨S.reindex a b,horder.reindex a b,?_,?_,?_⟩
  · intro k
    exact ⟨finite_class_smooth_measurable (S.left k) (fun i => (S.left_smooth k i).continuous) a ha,
      finite_class_smooth_measurable (S.right k) (fun i => (S.right_smooth k i).continuous) b hb⟩
  · intro x y e
    exact hvalue (a x) (b y) e
  · intro e he k
    exact ⟨fun x hx => (hsupport e he k).1 (a x) hx,
      fun y hy => (hsupport e he k).2 (b y) hy⟩

end Falconer

end OAI
