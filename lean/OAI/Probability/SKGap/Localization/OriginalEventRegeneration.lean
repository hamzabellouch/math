import Mathlib
import OAI.Probability.SKGap.Matrix.NormalizedRecipeLaw
import OAI.Probability.SKGap.Entropy.RegeneratedNormalizedQuery

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
namespace SKGapCutoff.Regression

local instance reverseMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

lemma original_event_le_regeneration {n r : ℕ} (hn : 0 < n) {H : Type*} [MeasurableSpace H]
    (ρ : Measure H) (U Y : H → Matrix (Fin n) (Fin r) ℝ) (q : H → Fin n → ℝ)
    (hUm : Measurable U) (hYm : Measurable Y) (hqm : Measurable q)
    (G : Set H) (hG : MeasurableSet G)
    (hgood : ∀ h ∈ G, (U h)ᵀ*U h=1 ∧ (U h)ᵀ*Y h=(Y h)ᵀ*U h ∧
      (∑ i, q h i^2)=1 ∧ (U h)ᵀ *ᵥ q h=0)
    (T : Set (H × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ))) (hT : MeasurableSet T) :
    (ρ.prod (standardArrayLaw (Fin n × Fin n)))
      ((fun z => (z.1,(completedMatrix (U z.1) (Y z.1) z.2 *ᵥ q z.1,
        completedMatrix (U z.1) (Y z.1) z.2))) ⁻¹' T) ≤
    (ρ.prod ((standardArrayLaw (Fin n × Fin n)).prod (standardArrayLaw (Fin n ⊕ Unit))))
      ((fun z => (z.1,(regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2,
        completedMatrix (extendFrame (U z.1) (q z.1))
          (extendFrame (Y z.1) (regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2)) z.2.1))) ⁻¹' T)+ρ Gᶜ := by
  let F : H × ((Fin n × Fin n) → ℝ) →
      H × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) := fun z =>
    (z.1,(completedMatrix (U z.1) (Y z.1) z.2 *ᵥ q z.1,
      completedMatrix (U z.1) (Y z.1) z.2))
  let R : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) →
      H × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) := fun z =>
    (z.1,(regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2,
      completedMatrix (extendFrame (U z.1) (q z.1))
        (extendFrame (Y z.1) (regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2)) z.2.1))
  have hA : Measurable (fun z : H × ((Fin n × Fin n) → ℝ) =>
      completedMatrix (U z.1) (Y z.1) z.2) :=
    measurable_completedMatrix_comp _ _ _ (hUm.comp measurable_fst) (hYm.comp measurable_fst) measurable_snd
  have hF : Measurable F := measurable_fst.prodMk
    ((measurable_matrix_mulVec_comp _ _ hA (hqm.comp measurable_fst)).prodMk hA)
  have hb : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2) :=
    measurable_regeneratedAnswer_comp _ _ _ _ (hUm.comp measurable_fst)
      (hYm.comp measurable_fst) (hqm.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have hUn : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      extendFrame (U z.1) (q z.1)) :=
    measurable_extendFrame.comp ((hUm.comp measurable_fst).prodMk (hqm.comp measurable_fst))
  have hYn : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      extendFrame (Y z.1) (regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2)) :=
    measurable_extendFrame.comp ((hYm.comp measurable_fst).prodMk hb)
  have hR : Measurable R := measurable_fst.prodMk (hb.prodMk
    (measurable_completedMatrix_comp _ _ _ hUn hYn (measurable_fst.comp measurable_snd)))
  apply prod_event_le_of_section_law ρ
    (standardArrayLaw (Fin n × Fin n))
    ((standardArrayLaw (Fin n × Fin n)).prod (standardArrayLaw (Fin n ⊕ Unit))) F R hF hR G hG _ T hT
  intro h hh
  have hsec := completedMatrix_section_law hn (U h) (Y h) (q h)
    (hgood h hh).1 (hgood h hh).2.1 (hgood h hh).2.2.1 (hgood h hh).2.2.2
  have hfo : Measurable (fun g => (completedMatrix (U h) (Y h) g *ᵥ q h,
      completedMatrix (U h) (Y h) g)) :=
    measurable_snd.comp (hF.comp measurable_prodMk_left)
  have hro : Measurable (fun z : ((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ) => (regeneratedAnswer (U h) (Y h) (q h) z.2,
      completedMatrix (extendFrame (U h) (q h))
        (extendFrame (Y h) (regeneratedAnswer (U h) (Y h) (q h) z.2)) z.1)) :=
    measurable_snd.comp (hR.comp measurable_prodMk_left)
  have hout : Measurable (fun t : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => (h,t)) :=
    measurable_const.prodMk measurable_id
  have he := congrArg (Measure.map (fun t : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => (h,t))) hsec
  have hmfo := Measure.map_map (μ := standardArrayLaw (Fin n × Fin n)) hout hfo
  have hmro := Measure.map_map (μ := (standardArrayLaw (Fin n × Fin n)).prod
    (standardArrayLaw (Fin n ⊕ Unit))) hout hro
  exact hmfo.symm.trans (he.trans hmro)

theorem original_exponentiallyRare_of_regenerated
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (r : ℕ)
    (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hYm : ∀ n, Measurable (Y n))
    (hqm : ∀ n, Measurable (q n))
    (G : ∀ n, Set (H n)) (hG : ∀ n, MeasurableSet (G n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hgood : ∀ᶠ n in atTop, ∀ h ∈ G n,
      (U n h)ᵀ*U n h=1 ∧ (U n h)ᵀ*Y n h=(Y n h)ᵀ*U n h ∧
        (∑ i, q n h i^2)=1 ∧ (U n h)ᵀ *ᵥ q n h=0)
    (T : ∀ n, Set (H n × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ)))
    (hT : ∀ n, MeasurableSet (T n))
    (hbad : ExponentiallyRare
      (fun n => (ρ n).prod ((standardArrayLaw (Fin n × Fin n)).prod
        (standardArrayLaw (Fin n ⊕ Unit))))
      (fun n => (fun z => (z.1,(regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2.2,
        completedMatrix (extendFrame (U n z.1) (q n z.1))
          (extendFrame (Y n z.1)
            (regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2.2)) z.2.1))) ⁻¹' T n)) :
    ExponentiallyRare (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n => (fun z => (z.1,(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ q n z.1,
        completedMatrix (U n z.1) (Y n z.1) z.2))) ⁻¹' T n) := by
  apply exponentiallyRare_of_measure_le_add _ _ ρ _ _ _ hbad hrare
  filter_upwards [hgood,eventually_gt_atTop 0] with n hn hn0
  exact original_event_le_regeneration hn0 (ρ n) (U n) (Y n) (q n)
    (hUm n) (hYm n) (hqm n) (G n) (hG n) hn (T n) (hT n)

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

namespace SKGapCutoff.Regression

local instance sampledRawMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

noncomputable def sampledRawAnswer {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (v : Fin n → ℝ) (z : (Fin n ⊕ Unit) → ℝ) : Fin n → ℝ :=
  Y *ᵥ (Uᵀ *ᵥ v) + Real.sqrt (∑ i, (residualProjection U *ᵥ v) i^2) •
    regeneratedAnswer U Y (unitVector (residualProjection U *ᵥ v)) z

lemma sampledRawAnswer_scaled {n r : ℕ} (hn : 0 < n)
    (U Y : Matrix (Fin n) (Fin r) ℝ) (v : Fin n → ℝ) (z : (Fin n ⊕ Unit) → ℝ) (i : Fin n) :
    sampledRawAnswer U Y v z i =
      Real.sqrt ((∑ j, (residualProjection U *ᵥ v) j^2)/(n:ℝ))*
        (Real.sqrt n*regeneratedAnswer U Y (unitVector (residualProjection U *ᵥ v)) z i)+
      ∑ a, ((∑ j, Real.sqrt n*U j a*v j)/(n:ℝ))*(Real.sqrt n*Y i a) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hs : (Real.sqrt (n:ℝ))^2=n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp : (Y *ᵥ (Uᵀ *ᵥ v)) i =
      ∑ a, ((∑ j, Real.sqrt n*U j a*v j)/(n:ℝ))*(Real.sqrt n*Y i a) := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_div,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    nlinarith [congrArg (fun t : ℝ => t*(U j a*v j*Y i a)) hs]
  simp only [sampledRawAnswer,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp]
  rw [Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  field_simp
  ring

lemma ExponentialEmpiricalConcentration.congr_eventually
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν) (he : ∀ᶠ n in atTop, X n=Y n) :
    ExponentialEmpiricalConcentration ρ Y ν := by
  intro f K hf B hB ε hε
  have hr : ExponentiallyRare ρ (fun n => {h | ε ≤ |(∑ i, f (X n h i))/(n:ℝ)-∫ x, f x ∂ν|}) :=
    hX f K hf B hB ε hε
  apply hr.mono
  filter_upwards [he] with n hn
  intro h hh
  simpa only [hn] using hh

lemma ExponentialSquareTails.congr_eventually
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X) (he : ∀ᶠ n in atTop, X n=Y n) :
    ExponentialSquareTails ρ Y := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX ε hε
  refine ⟨R,hR,ht.mono ?_⟩
  filter_upwards [he] with n hn
  intro h hh
  simpa only [hn] using hh

theorem ExponentialEmpiricalConcentration.sampled_unnormalized_assembly
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (X : ∀ n, H n → Fin n → E)
    {r : ℕ} (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (u y : Fin r → E → ℝ) (g : E → ℝ) {K : ℝ≥0} (hK : 1 ≤ K)
    (hy : ∀ a, LipschitzWith K (y a))
    (hyT : ∀ a, ExponentialSquareTails ρ (fun n h i => y a (X n h i)))
    (heu : ∀ (n : ℕ) h i a, Real.sqrt n*U n h i a=u a (X n h i))
    (hey : ∀ (n : ℕ) h i a, Real.sqrt n*Y n h i a=y a (X n h i))
    (c : Fin r → ℝ) (s : ℝ)
    (hC : ExponentialConvergence ρ
      (fun n h a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ)) c)
    (hS : ExponentialConvergence ρ
      (fun n h => (∑ i, (residualProjection (U n h) *ᵥ (fun j => g (X n h j))) i^2)/(n:ℝ)) s)
    (ν : Measure ((E × ℝ) × ℝ)) [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => ((X n z.1 i, Real.sqrt n*
        unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j))) i),
        Real.sqrt n*regeneratedAnswer (U n z.1) (Y n z.1) (unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j)))) z.2 i)) ν)
    (hWT : ExponentialSquareTails
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => Real.sqrt n*regeneratedAnswer (U n z.1) (Y n z.1) (unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j)))) z.2 i))
    (hyi : ∀ a, Integrable (fun z => y a z.1.1^2) ν)
    (hWi : Integrable (fun z => z.2^2) ν) :
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => (((X n z.1 i, Real.sqrt n*
        unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j))) i),
        Real.sqrt n*regeneratedAnswer (U n z.1) (Y n z.1) (unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j)))) z.2 i),
          sampledRawAnswer (U n z.1) (Y n z.1) (fun j => g (X n z.1 j)) z.2 i))
      (ν.map (fun z => (z,Real.sqrt s*z.2+∑ a, c a*y a z.1.1))) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => sampledRawAnswer (U n z.1) (Y n z.1) (fun j => g (X n z.1 j)) z.2 i) := by
  let f : Option (Fin r) → ((E × ℝ) × ℝ) → ℝ := fun a =>
    a.elim Prod.snd (fun a z => y a z.1.1)
  let C : ∀ n, H n → Option (Fin r) → ℝ := fun n h a => a.elim
    (Real.sqrt ((∑ i, (residualProjection (U n h) *ᵥ (fun j => g (X n h j))) i^2)/(n:ℝ)))
    (fun a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ))
  let c' : Option (Fin r) → ℝ := fun a => a.elim (Real.sqrt s) c
  have hcoef : ExponentialConvergence ρ C c' := by
    apply ExponentialConvergence.pi_finite
    intro a
    cases a with
    | none => exact hS.continuous_map Real.continuous_sqrt.continuousAt
    | some a => exact hC.continuous_map (continuous_apply a).continuousAt
  have hf : ∀ a, LipschitzWith K (f a) := by
    intro a
    cases a with
    | none => exact LipschitzWith.prod_snd.weaken hK
    | some a =>
      simpa only [f,Option.elim_some,Function.comp_def,mul_one] using
        ((hy a).comp LipschitzWith.prod_fst).comp LipschitzWith.prod_fst
  have ht := hX.append_unbounded_linear f hf
    (fun a => by
      cases a with
      | none => exact hWT
      | some a => exact (hyT a).prod_fst (fun n => standardArrayLaw (Fin n ⊕ Unit)))
    (fun a => by cases a with | none => exact hWi | some a => exact hyi a)
    (fun n z => C n z.1) c' (hcoef.prod_fst (fun n => standardArrayLaw (Fin n ⊕ Unit)))
  simp only [f,C,c',Fintype.sum_option,Option.elim_none,Option.elim_some] at ht
  have he : ∀ᶠ n in atTop, ∀ z : H n × ((Fin n ⊕ Unit) → ℝ), ∀ i : Fin n,
      Real.sqrt ((∑ j, (residualProjection (U n z.1) *ᵥ (fun k => g (X n z.1 k))) j^2)/(n:ℝ))*
        (Real.sqrt n*regeneratedAnswer (U n z.1) (Y n z.1)
          (unitVector (residualProjection (U n z.1) *ᵥ (fun k => g (X n z.1 k)))) z.2 i)+
      ∑ a, ((∑ j, u a (X n z.1 j)*g (X n z.1 j))/(n:ℝ))*y a (X n z.1 i) =
      sampledRawAnswer (U n z.1) (Y n z.1) (fun j => g (X n z.1 j)) z.2 i := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro z i
    have h := sampledRawAnswer_scaled hn (U n z.1) (Y n z.1) (fun j => g (X n z.1 j)) z.2 i
    simpa only [heu,hey] using h.symm
  constructor
  · apply ht.1.congr_eventually
    filter_upwards [he] with n hn
    funext z i
    congr 1
    exact hn z i
  · apply ht.2.congr_eventually
    filter_upwards [he] with n hn
    funext z i
    exact hn z i

theorem ExponentialEmpiricalConcentration.sampled_full_query
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (r : ℕ) (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (hUm : ∀ n, Measurable (U n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1)
    (u y : Fin r → E → ℝ) (g : E → ℝ) {K : ℝ≥0} (hK : 1 ≤ K)
    (hu : ∀ a, LipschitzWith K (u a)) (hy : ∀ a, LipschitzWith K (y a))
    (hg : LipschitzWith K g)
    (huT : ∀ a, ExponentialSquareTails ρ (fun n h i => u a (X n h i)))
    (hyT : ∀ a, ExponentialSquareTails ρ (fun n h i => y a (X n h i)))
    (hgT : ExponentialSquareTails ρ (fun n h i => g (X n h i)))
    (hui : ∀ a, Integrable (fun x => u a x^2) ν)
    (hyi : ∀ a, Integrable (fun x => y a x^2) ν) (hgi : Integrable (fun x => g x^2) ν)
    (heu : ∀ (n : ℕ) h i a, Real.sqrt n*U n h i a=u a (X n h i))
    (hey : ∀ (n : ℕ) h i a, Real.sqrt n*Y n h i a=y a (X n h i))
    (hs : 0 < ∫ x, residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x^2 ∂ν) :

    let R := fun n h => residualProjection (U n h) *ᵥ (fun i => g (X n h i))
    let q := fun n h => unitVector (R n h)
    let c := fun a => ∫ x, u a x*g x ∂ν
    let s := ∫ x, residualRecipe u g c x^2 ∂ν
    let W := fun n (z : H n × ((Fin n ⊕ Unit) → ℝ)) i =>
      Real.sqrt n*regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2 i
    ExponentialConvergence ρ (fun n h => (∑ i, R n h i^2)/(n:ℝ)) s ∧
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => (((X n z.1 i,Real.sqrt n*q n z.1 i),W n z i),
        sampledRawAnswer (U n z.1) (Y n z.1) (fun j => g (X n z.1 j)) z.2 i))
      ((normalizedRecipeLaw ν u y g).map (fun z => (z, Real.sqrt s*z.2+∑ a, c a*y a z.1.1))) ∧
    ExponentialSquareTails ρ (fun n h i => Real.sqrt n*q n h i) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit))) W ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => sampledRawAnswer (U n z.1) (Y n z.1) (fun j => g (X n z.1 j)) z.2 i) := by
  dsimp only
  have h := hX.regenerated_nondegenerate_step ρ ν X hXm r U Y hUm hU
    u y g hK hu hy hg huT hyT hgT hui hyi hgi heu hey hs
  dsimp only at h
  let : IsProbabilityMeasure (normalizedRecipeLaw ν u y g) :=
    normalizedRecipeLaw_probability ν u y g (fun a => (hu a).continuous.measurable) hg.continuous.measurable
  have hm := normalizedRecipeLaw_moments ν u y g
    (fun a => (hu a).continuous.measurable) (fun a => (hy a).continuous.measurable)
    hg.continuous.measurable hui hyi hgi
  have hC : ExponentialConvergence ρ
      (fun n h a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ))
      (fun a => ∫ x, u a x*g x ∂ν) := by
    apply ExponentialConvergence.pi_finite
    intro a
    exact hX.product_average (u a) g (hu a) hg (huT a) hgT (hui a) hgi
  have hh := h.2.1.sampled_unnormalized_assembly ρ X U Y u y g hK hy hyT heu hey (fun a => ∫ x, u a x*g x ∂ν)
    (∫ x, residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x^2 ∂ν)
    hC h.1 (normalizedRecipeLaw ν u y g) h.2.2.2 hm.2.1 hm.2.2.2
  exact ⟨h.1,hh.1,h.2.2.1,h.2.2.2,hh.2⟩

end SKGapCutoff.Regression

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

end

end OAI
