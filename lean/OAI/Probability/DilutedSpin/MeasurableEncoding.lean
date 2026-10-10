import OAI.Probability.DilutedSpin.FiniteEncoding

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction
local instance measurableEncodingMeasurableSpace (X : TopCat) : MeasurableSpace X := borel X
local instance measurableEncodingBorelSpace (X : TopCat) : BorelSpace X := ⟨rfl⟩

lemma labelMoment_continuous_bound (r : ℕ) (S : PrescribedTree (r+1)) :
    Continuous (labelMoment r S) ∧ ∀ x, |labelMoment r S x|≤1 := by
  induction r with
  | zero =>
    cases S with
    | node k C =>
      change Continuous (fun x : ℝ => ∏ _ : Fin k, Real.tanh x) ∧ _
      refine ⟨continuous_finsetProd _ (fun _ _ => ?_),?_⟩
      · change Continuous (fun x : ℝ => Real.tanh x)
        simp_rw [Real.tanh_eq_sinh_div_cosh]
        exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
      · intro x
        change |∏ _ : Fin k, Real.tanh x|≤1
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => (Real.abs_tanh_lt_one x).le)
  | succ r ih =>
    cases S with
    | node k C =>
      let F (j : Fin k) : Hierarchy r →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
        (labelMoment r (C j)) (ih (C j)).1 1 (fun x => by simpa using (ih (C j)).2 x)
      change Continuous (fun η : ProbabilityMeasure (Hierarchy r) => ∏ j, ∫ x, F j x ∂η) ∧ _
      refine ⟨continuous_finsetProd _ (fun j _ =>
        ProbabilityMeasure.continuous_integral_boundedContinuousFunction (F j)),?_⟩
      intro η
      change ProbabilityMeasure (Hierarchy r) at η
      change |∏ j, ∫ x, F j x ∂η.toMeasure|≤1
      rw [Finset.abs_prod]
      apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      intro j _
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const (μ := η.toMeasure) (f := (F j))
          (ae_of_all _ (fun x => by simpa [F] using (ih (C j)).2 x))

lemma q_tanh (x : ℝ) (s : Spin) : q x s=(1+spin s*Real.tanh x)/2 := by
  have hc := (Real.cosh_pos x).ne'
  cases s
  · simp only [q,spin,Bool.false_eq_true,↓reduceIte,mul_neg_one,
      Real.tanh_eq_sinh_div_cosh]
    rw [← Real.cosh_sub_sinh]
    field_simp
    ring
  · simp only [q,spin,↓reduceIte,mul_one,one_mul,Real.tanh_eq_sinh_div_cosh]
    rw [← Real.cosh_add_sinh]
    field_simp

lemma q_artanh (x : ℝ) (hx : x∈Ioo (-1) 1) (s : Spin) :
    q (Real.artanh x) s=(1+spin s*x)/2 := by rw [q_tanh,Real.tanh_artanh hx]

namespace KernelTower
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z]

lemma measurable_encode_tilt (r : ℕ) (T : KernelTower Ω (r+1)) (m : Fin (r+1) → ℝ)
    {f V : Z → FinitePath Ω (r+1) → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hV : ∀ y, Measurable (fun z => V z y)) :
    Measurable (fun z => encode r (tilt (r+1) T m (f z)) (V z)) := by
  induction r with
  | zero =>
    change Measurable (fun z => Real.artanh
      ((T.1.tilt (m 0) (fun a => f z (a,()))).expect (fun a => V z (a,()))))
    have he := FiniteLaw.measurable_tilt_expect T.1 (m 0)
      (fun a => hf (a,())) (fun a => hV (a,()))
    exact ((measurable_const.add he).div (measurable_const.sub he)).sqrt.log
  | succ r ih =>
    let : MeasurableSpace (ProbabilityMeasure (Hierarchy r)) := borel _
    let : BorelSpace (ProbabilityMeasure (Hierarchy r)) := ⟨rfl⟩
    change Measurable (fun z =>
      (T.1.tilt (m 0) (fun a => backwardLog (r+1) (T.2 a) (fun j => m j.succ)
        (fun y => f z (a,y)))).asProbability
      (fun a => encode r (tilt (r+1) (T.2 a) (fun j => m j.succ) (fun y => f z (a,y)))
        (fun y => V z (a,y))))
    apply FiniteLaw.measurable_asProbability
    · intro a
      exact FiniteLaw.measurable_tilt_weight _ _ (fun b => measurable_backwardLog _ _ _
        (fun y => hf (b,y))) a
    · intro a
      exact ih (T.2 a) (fun j => m j.succ) (fun y => hf (a,y)) (fun y => hV (a,y))

end KernelTower
end DilutedSpinGlass

end

end OAI
