import OAI.Probability.DilutedSpin.CavityRateLimits
import OAI.Probability.DilutedSpin.CompoundRate
import OAI.Probability.DilutedSpin.MarkSiteCoupling
import OAI.Probability.DilutedSpin.PoissonCountThinning

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

open Classical in
/-- The actual finite-volume Poisson cavity split, with only the discarded
multiple-new-index energy as error. The bound is uniform over the rooted
finite power-mean functional, its old disorder and every auxiliary level. -/
lemma cavity_split_lipschitz_bound (α : ℝ≥0) (q N : ℕ) [NeZero N]
    (V : X × (Fin (q+1) → Fin (N+1)) → E) (hV : Measurable V)
    {D : ℝ} (hD : 0≤D) (hbound : ∀ z,‖V z‖≤D)
    {f : E → ℝ} (hf : LipschitzWith 1 f) :
    |(∫ x, f x ∂compoundPoisson (α*(N+1))
        (Measure.map V (μ.prod (finiteUniform (Fin (q+1) → Fin (N+1))))))-
      (∫ x, f x ∂(compoundPoisson (reservoirRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) → Fin N) => V (z.1,fun i => (z.2 i).succ))
          (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
      compoundPoisson (oneNewRate α q N)
        (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
            V (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
          (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))))))| ≤
      D*cavityBadRate α q N := by
  rw [← cavity_compound_split μ α q N V hV]
  apply (finite_poisson_deletion μ (α*(N+1)) CavityGood V hV hD hbound hf).trans_eq
  rw [cavityBadRate_count]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one,
    NNReal.coe_one,one_mul,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast]
  ring

lemma compoundPoisson_rate_limit (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (r : ℕ → ℝ≥0) (s : ℝ≥0)
    (hr : Tendsto (fun n => (r n:ℝ)) atTop (𝓝 (s:ℝ)))
    (f : ℕ → E → ℝ) (hf : ∀ n, LipschitzWith 1 (f n)) :
    Tendsto (fun n => (∫ x, f n x ∂compoundPoisson (r n) μ)-
      (∫ x, f n x ∂compoundPoisson s μ)) atTop (𝓝 0) := by
  have hh := ((hr.sub_const (s:ℝ)).abs).mul_const (∫ y,‖y‖ ∂μ)
  simp only [sub_self,abs_zero,zero_mul] at hh
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun n => ?_)) hh
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul] using
    compoundPoisson_rate_bound (r n) s μ hμ (hf n)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]
lemma integral_expect (P : FiniteLaw Ω) (μ : Measure X) (f : X → Ω → ℝ)
    (hf : ∀ i,Integrable (fun x => f x i) μ) :
    (∫ x,P.expect (f x) ∂μ)=P.expect (fun i => ∫ x,f x i ∂μ) := by
  unfold expect
  rw [integral_finsetSum _ (fun i _ => (hf i).const_mul _)]
  simp only [integral_const_mul]
lemma integral_expect_bounded (P : FiniteLaw Ω) (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Ω → ℝ) (hf : ∀ i,Measurable (fun x => f x i)) {B : ℝ}
    (hb : ∀ x i,|f x i|≤B) :
    (∫ x,P.expect (f x) ∂μ)=P.expect (fun i => ∫ x,f x i ∂μ) :=
  integral_expect P μ f (fun i => Integrable.of_bound (hf i).aestronglyMeasurable B
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x i)))
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory HeterogeneousMarks
variable {Z : Type} [MeasurableSpace Z]
lemma measurable_spinRoot {N p k l r : ℕ} {A : Fin l → Type} [∀ i,Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Z → Fin k → InteractionSample p) (h : Z → Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hθ : ∀ j σ,Measurable (fun z => (theta z j).1 σ))
    (hh : ∀ i,Measurable (fun z => h z i)) :
    Measurable (fun z => spinRoot Q m (theta z) (h z) indices sites ψ) := by
  apply measurable_root
  · intro x
    exact (Finset.measurable_sum _ (fun j _ => hθ j _)).add
      (Finset.measurable_sum _ (fun i _ => (hh i).mul_const _))
  · intro i x a
    exact measurable_const

lemma spinRoot_bound {N p k l r : ℕ} {A : Fin l → Type} [∀ i,Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j,0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ,|(theta j).1 σ|≤C) (hh : ∀ i,|h i|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |spinRoot Q m theta h indices sites ψ|≤H*N+C*k+D*l :=
  root_uniform_bound _ Q m hm _ id _
    (fun x => finite_logWeight_bound theta h indices (KernelTower.terminalState r x) hθ hh)
    (fun i _ a => hψ i _ a)
end DilutedSpinGlass.SizeCoupling

end

end OAI
