import OAI.Probability.FreeIsing.Cavity.MomentTransport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω ι : Type*} {b : ℕ}

def ownChildFinFamily (e : Fin b ≃ ι) (Z : Option ι → Ω → ℝ) :
    Fin (b + 1) → Ω → ℝ :=
  fun i => Z (((finSuccEquiv b).trans e.optionCongr) i)

@[simp] theorem ownChildFinFamily_zero (e : Fin b ≃ ι)
    (Z : Option ι → Ω → ℝ) : ownChildFinFamily e Z 0 = Z none := rfl

@[simp] theorem ownChildFinFamily_succ (e : Fin b ≃ ι)
    (Z : Option ι → Ω → ℝ) (i : Fin b) :
    ownChildFinFamily e Z i.succ = Z (some (e i)) := by
  simp [ownChildFinFamily]

theorem ownChildFinFamily_eq_cases (e : Fin b ≃ ι)
    (Z : Option ι → Ω → ℝ) :
    ownChildFinFamily e Z = Fin.cases (Z none) (fun j => Z (some (e j))) := by
  funext i
  induction i using Fin.cases <;> simp

theorem iIndepFun_ownChildFinFamily [MeasurableSpace Ω] (e : Fin b ≃ ι)
    {Z : Option ι → Ω → ℝ} {μ : Measure Ω} (hZ : iIndepFun Z μ) :
    iIndepFun (ownChildFinFamily e Z) μ := by
  exact iIndepFun.precomp (f := Z) (g := (finSuccEquiv b).trans e.optionCongr)
    ((finSuccEquiv b).trans e.optionCongr).injective hZ

theorem measurable_ownChildFinFamily [MeasurableSpace Ω] (e : Fin b ≃ ι)
    {Z : Option ι → Ω → ℝ} (hm : ∀ i, Measurable (Z i)) (i : Fin (b + 1)) :
    Measurable (ownChildFinFamily e Z i) :=
  hm _

theorem sum_response_ownChildFinFamily [Fintype ι] (e : Fin b ≃ ι)
    (Z : Option ι → Ω → ℝ) (psi : ℝ → ℝ) (ω : Ω) :
    (∑ i : Fin (b + 1), Fin.cases (ownChildFinFamily e Z 0 ω)
      (fun j => psi (ownChildFinFamily e Z j.succ ω)) i) =
      Z none ω + ∑ a : ι, psi (Z (some a) ω) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, ownChildFinFamily_zero,
    ownChildFinFamily_succ]
  exact congrArg (fun x : ℝ => Z none ω + x)
    (e.sum_comp (fun a => psi (Z (some a) ω)))

end Problem367

end

end OAI
