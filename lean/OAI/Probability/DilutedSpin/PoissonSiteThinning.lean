import OAI.Probability.DilutedSpin.EnergyInsertionMean
import OAI.Probability.DilutedSpin.PoissonCountThinning

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

/-- Poisson thinning for independent uniform categorical choices. -/
lemma compoundPoisson_uniform_indicator_at (r : ℝ≥0) (p : ℕ) [NeZero p] (s : Fin p) :
    compoundPoisson r (Measure.map (fun a : Fin p => if a=s then (1:ℝ) else 0)
      (finiteUniform (Fin p))) = compoundPoisson (r/p) (Measure.dirac (1:ℝ)) := by
  classical
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson,charFunDual_compoundPoisson]
  congr 1
  rw [charFunDual_apply,integral_map (measurable_of_countable _).aemeasurable (by fun_prop),
    integral_finiteUniform,charFunDual_apply,integral_dirac]
  have hp : (p:ℂ)≠0 := by exact_mod_cast (NeZero.ne p)
  have hs : (∑ a : Fin p,Complex.exp ((L (if a=s then (1:ℝ) else 0):ℂ)*Complex.I)) =
      Complex.exp ((L 1:ℂ)*Complex.I)+(p-1:ℕ) := by
    have he (a : Fin p) : Complex.exp ((L (if a=s then (1:ℝ) else 0):ℂ)*Complex.I)=
        (if a=s then Complex.exp ((L 1:ℂ)*Complex.I)-1 else 0)+1 := by
      split_ifs <;> simp
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hpn : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
    rw [hpn]; ring
  rw [hs]
  simp only [Fintype.card_fin,NNReal.coe_div,NNReal.coe_natCast,Complex.ofReal_div,Complex.ofReal_natCast,Complex.real_smul,Complex.ofReal_inv]
  rw [show ((p-1:ℕ):ℂ)=(p:ℂ)-1 by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]]
  field_simp
  ring

noncomputable def successCountAt {p k : ℕ} [NeZero p] (s : Fin p) (a : Fin k → Fin p) : ℕ :=
  ∑ i,if a i=s then 1 else 0

lemma map_poisson_successCountAt (r : ℝ≥0) (p : ℕ) [NeZero p] (s : Fin p) :
    Measure.map (fun z : (k : ℕ) × (Fin k → Fin p) => successCountAt s z.2)
      (familyLaw (poissonMeasure r) (fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p)))) =
      poissonMeasure (r/p) := by
  classical
  have he : MeasurableEmbedding (fun n : ℕ => (n:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).measurableEmbedding Nat.cast_injective
  apply he.map_injective
  rw [Measure.map_map (measurable_of_countable _) (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCountAt s a))),
    ← compoundPoisson_dirac_one,← compoundPoisson_uniform_indicator_at r p s]
  simp only [Function.comp_def]
  rw [map_familyLaw_sum _ _ (fun k (a : Fin k → Fin p) => (successCountAt s a:ℝ))
    (fun k => measurable_of_countable _)]
  unfold compoundPoisson
  congr 1
  funext k
  rw [poissonMeasure_singleton,← Measure.pi_map_pi (fun _ : Fin k => (measurable_of_countable
    (fun a : Fin p => if a=s then (1:ℝ) else 0)).aemeasurable),
    Measure.map_map (by fun_prop) (measurable_of_countable _)]
  congr 2
  funext a
  simp [successCountAt]

lemma selectedCount_eq_successCountAt {p : ℕ} [NeZero p] (s : Fin p) (k : ℕ)
    (c : RootPath (Fin p) k) :
    selectedCount k (rootMap (fun a => decide (a=s)) k c)=successCountAt s (rootArray k c) := by
  induction k with
  | zero => simp [selectedCount,successCountAt]
  | succ k ih =>
    simp only [rootMap,successCountAt,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ]
    split_ifs with h
    · simp [h,selectedCount,ih,successCountAt,Nat.add_comm]
    · simp [h,selectedCount,ih,successCountAt]

end DilutedSpinGlass

end

end OAI
