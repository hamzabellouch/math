import OAI.Probability.StrongRayleigh.PathRealization
import OAI.Probability.StrongRayleigh.DecoderUniqueness
import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
open MeasureTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

theorem innovation_injective {I : Type u_1}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D) :
    Function.Injective (innovation b hb C hbound) := by
  intro y z heq
  have hu := Decoder.bounded_drift_decoder_unique
    (fun t x => b (t.toNNReal, x)) L hL
    (fun t _ x i => hunit (t.toNNReal, x) i)
    (fun t _ x y D hD hxy i => hlip t.toNNReal x y D hD hxy i)
    (fun i t => innovation b hb C hbound y i t.toNNReal)
    (fun i t => y i t.toNNReal) (fun i t => z i t.toNNReal)
    (fun i t _ => intervalIntegrable_driftIntegrand hb C hbound y i 0 t)
    (fun i t _ => intervalIntegrable_driftIntegrand hb C hbound z i 0 t)
    (fun i t ht => by
      simpa only [Real.toNNReal_of_nonneg ht, NNReal.coe_mk, driftIntegrand] using
        innovation_reconstruction hb C hbound y i t.toNNReal)
    (fun i t ht => by
      rw [heq]
      simpa only [Real.toNNReal_of_nonneg ht, NNReal.coe_mk, driftIntegrand] using
        innovation_reconstruction hb C hbound z i t.toNNReal)
  funext i
  apply ContinuousMap.ext
  intro t
  simpa using hu i (t : ℝ) t.property

theorem innovation_measurableEmbedding {I : Type u_2} [Countable I]
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D) :
    MeasurableEmbedding (innovation b hb C hbound) :=
  (measurable_innovation hb C hbound).measurableEmbedding
    (innovation_injective hb C hbound hunit L hL hlip)

theorem innovation_leftTranslate {Γ : Type u_3} [Group Γ]
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (g : Γ) (y : Γ → Path) :
    innovation b hb C hbound (leftTranslate g y) =
      leftTranslate g (innovation b hb C hbound y) := by
  funext i
  apply ContinuousMap.ext
  intro t
  change y (g⁻¹ * i) t - (∫ s in (0 : ℝ)..(t : ℝ),
    b (s.toNNReal, leftTranslate g (fun j => y j s.toNNReal)) i) =
      y (g⁻¹ * i) t - (∫ s in (0 : ℝ)..(t : ℝ),
        b (s.toNNReal, fun j => y j s.toNNReal) (g⁻¹ * i))
  simp_rw [hequiv]

def inverseOnImage {I : Type u_4} {f : (I → Path) → (I → Path)}
    (hf : MeasurableEmbedding f) (w : I → Path) : I → Path := by
  classical
  exact if w ∈ Set.range f then hf.invFun w else 0

theorem measurable_inverseOnImage {I : Type u_5} {f : (I → Path) → (I → Path)}
    (hf : MeasurableEmbedding f) : Measurable (inverseOnImage hf) := by
  classical
  exact Measurable.ite hf.measurableSet_range hf.measurable_invFun measurable_const

@[simp] theorem inverseOnImage_apply {I : Type u_6} {f : (I → Path) → (I → Path)}
    (hf : MeasurableEmbedding f) (y : I → Path) :
    inverseOnImage hf (f y) = y := by
  classical
  rw [inverseOnImage, ite_eq_left (Set.mem_range_self y)]
  exact hf.leftInverse_invFun y

theorem inverseOnImage_leftTranslate {Γ : Type u_7} [Group Γ]
    {f : (Γ → Path) → (Γ → Path)} (hf : MeasurableEmbedding f)
    (hequiv : ∀ g y, f (leftTranslate g y) = leftTranslate g (f y))
    (g : Γ) (w : Γ → Path) :
    inverseOnImage hf (leftTranslate g w) = leftTranslate g (inverseOnImage hf w) := by
  classical
  by_cases hw : w ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hw
    rw [← hequiv, inverseOnImage_apply, inverseOnImage_apply]
  · have hgw : leftTranslate g w ∉ Set.range f := by
      rintro ⟨y, hy⟩
      apply hw
      refine ⟨leftTranslate g⁻¹ y, ?_⟩
      rw [hequiv, hy]
      funext i
      simp [leftTranslate]
    simp only [inverseOnImage, ite_eq_right hgw, ite_eq_right hw]
    rfl

theorem exists_equivariant_innovation_leftInverse
    {Γ : Type u_8} [Group Γ] [Countable Γ]
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i)) :
    ∃ Z : (Γ → Path) → (Γ → Path),
      Measurable Z ∧
      (∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w)) ∧
      Function.LeftInverse Z (innovation b hb C hbound) := by
  let hf := innovation_measurableEmbedding hb C hbound hunit L hL hlip
  refine ⟨inverseOnImage hf, measurable_inverseOnImage hf, ?_, ?_⟩
  · exact inverseOnImage_leftTranslate hf
      (fun g y => innovation_leftTranslate hb C hbound hequiv g y)
  · exact inverseOnImage_apply hf

end Problem336AdditiveD139.PathRealization

end

end OAI
