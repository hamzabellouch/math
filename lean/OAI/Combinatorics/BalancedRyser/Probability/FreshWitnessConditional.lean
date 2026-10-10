import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessCounting

namespace OAI

namespace Balanced.FreshTupleWitness

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def fiberSuccessProbability (G : MergedPairs F → Prop)
    [Nonempty {M : MergedPairs F // G M}] (g : Direction F) (T : FourTuple F) : ℝ :=
  ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
    {M | (∃ c, ∀ k, OnLine (tuplePoint M.1 T k) (g,c)) ∧
      Function.Injective (tuplePoint M.1 T)}).toReal

def fiberWitnessProbability (G : MergedPairs F → Prop)
    [Nonempty {M : MergedPairs F // G M}] (g : Direction F) (T : FourTuple F)
    (d : Direction F) (i j : Fin 4) (σ : Bool) : ℝ :=
  ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
    {M | ((∃ c, ∀ k, OnLine (tuplePoint M.1 T k) (g,c)) ∧
      Function.Injective (tuplePoint M.1 T)) ∧
      OnLine (tuplePoint M.1 T i) (constituent M.1 d σ) ∧
      OnLine (tuplePoint M.1 T j) (constituent M.1 d (!σ))}).toReal

theorem sum_fiberWitnessProbability_eq (G : MergedPairs F → Prop)
    [Nonempty {M : MergedPairs F // G M}] (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (U : Finset (Direction F))
    (hfresh : ∀ d ∈ U, ∀ k, T.generator k ≠ d)
    (hG : ∀ d ∈ U, ∀ M v, G (Function.update M d v) ↔ G M) :
    (∑ d ∈ U, ∑ σ : Bool, fiberWitnessProbability G g T d i j σ) =
      2 * (U.card : ℝ) * fiberSuccessProbability G g T /
        (Fintype.card F : ℝ)^2 := by
  calc
    _ = ∑ _d ∈ U, ∑ _σ : Bool,
        fiberSuccessProbability G g T / (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro σ _
      exact oriented_pair_probability_on_event T d (hfresh d hd) i j σ G (hG d hd)
        (fun p => (∃ c, ∀ k, OnLine (p k) (g,c)) ∧ Function.Injective p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
      ring

theorem sum_freshWitness_fiber_le (G : MergedPairs F → Prop)
    [Nonempty {M : MergedPairs F // G M}] (g : Direction F) (i j : Fin 4)
    (U : RootPrescription g → Finset (Direction F))
    (hfresh : ∀ a d, d ∈ U a → ∀ k, a.tuple.generator k ≠ d)
    (hG : ∀ a d, d ∈ U a → ∀ M v, G (Function.update M d v) ↔ G M)
    (C : ℝ) (hC : 0 ≤ C)
    (hmean : (∑ a : RootPrescription g, fiberSuccessProbability G g a.tuple) ≤
      C * Fintype.card F) :
    (∑ a : RootPrescription g, ∑ d ∈ U a, ∑ σ : Bool,
      fiberWitnessProbability G g a.tuple d i j σ) ≤ 4 * C := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hp (a : RootPrescription g) : 0 ≤ fiberSuccessProbability G g a.tuple :=
    ENNReal.toReal_nonneg
  have hU (a : RootPrescription g) : (U a).card ≤ Fintype.card F + 1 := by
    simpa only [Direction, Fintype.card_option] using Finset.card_le_univ (U a)
  calc
    _ = ∑ a : RootPrescription g,
        2 * ((U a).card : ℝ) * fiberSuccessProbability G g a.tuple /
          (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_fiberWitnessProbability_eq G g a.tuple i j (U a) (hfresh a) (hG a)
    _ ≤ ∑ a : RootPrescription g,
        (2 * ((Fintype.card F : ℝ) + 1) / (Fintype.card F : ℝ)^2) *
          fiberSuccessProbability G g a.tuple := by
      apply Finset.sum_le_sum
      intro a _
      have hUa : ((U a).card : ℝ) ≤ (Fintype.card F : ℝ) + 1 := by
        exact_mod_cast hU a
      calc
        _ ≤ 2 * ((Fintype.card F : ℝ) + 1) * fiberSuccessProbability G g a.tuple /
            (Fintype.card F : ℝ)^2 := by
              gcongr
              exact hp a
        _ = _ := by ring
    _ = (2 * ((Fintype.card F : ℝ) + 1) / (Fintype.card F : ℝ)^2) *
        ∑ a : RootPrescription g, fiberSuccessProbability G g a.tuple := by
      rw [Finset.mul_sum]
    _ ≤ (2 * ((Fintype.card F : ℝ) + 1) / (Fintype.card F : ℝ)^2) *
        (C * Fintype.card F) := by gcongr
    _ ≤ 4 * C := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < (Fintype.card F : ℝ)^2)).mpr
      nlinarith [mul_nonneg hC (mul_nonneg hq.le (sub_nonneg.mpr hq1))]

end
end Balanced.FreshTupleWitness

end OAI
