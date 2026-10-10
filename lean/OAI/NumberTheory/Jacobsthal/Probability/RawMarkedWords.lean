import OAI.NumberTheory.Jacobsthal.Paths.RawWordSpaces

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

noncomputable def rawMarkedWordKernel : (a : ℕ) → (w : List Bool) →
    Kernel (RawHistory a) (RawCycleWordTrace a w.length)
  | _a, [] => Kernel.id
  | a, b::w =>
    (sigmaFamilyKernel (fun n : ℕ =>
      (Kernel.id : Kernel (RawHistory (a+2*(n+1))) (RawHistory (a+2*(n+1)))) ×ₖ
        rawMarkedWordKernel (a+2*(n+1)) w)) ∘ₖ rawBranchReturnKernel a b

lemma rawMarkedWord_bound_and_finite (w : List Bool) : ∀ a : ℕ,
    IsFiniteKernel (rawMarkedWordKernel a w) ∧ ∀ h, rawMarkedWordKernel a w h univ ≤ 1 := by
  induction w with
  | nil =>
    intro a
    constructor
    · change IsFiniteKernel (Kernel.id : Kernel (RawHistory a) (RawHistory a)); infer_instance
    · intro h
      change (Measure.dirac h) univ ≤ 1
      simp
  | cons b w ih =>
    intro a
    let (c : ℕ) : IsFiniteKernel (rawMarkedWordKernel c w) := (ih c).1
    let C : (n : ℕ) → Kernel (RawHistory (a+2*(n+1)))
        (RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) w.length) :=
      fun n => Kernel.id ×ₖ rawMarkedWordKernel (a+2*(n+1)) w
    have hC (n : ℕ) (y : RawHistory (a+2*(n+1))) : C n y univ ≤ 1 := by
      dsimp [C]
      rw [Kernel.id_prod_apply' _ _ MeasurableSet.univ,preimage_univ]
      exact (ih (a+2*(n+1))).2 y
    have : IsFiniteKernel (sigmaFamilyKernel C) :=
      sigmaFamilyKernel_isFinite_of_bound C (by simp : (1:ℝ≥0∞) < ∞) hC
    have hS (r : RawReturnTrace a) : sigmaFamilyKernel C r univ ≤ 1 := by
      rcases r with ⟨n,y⟩
      rw [sigmaFamilyKernel_mass]
      exact hC n y
    constructor
    · change IsFiniteKernel ((sigmaFamilyKernel C) ∘ₖ rawBranchReturnKernel a b)
      infer_instance
    · intro h
      change ((sigmaFamilyKernel C) ∘ₖ rawBranchReturnKernel a b) h univ ≤ 1
      rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
      calc
        _ ≤ ∫⁻ _r, (1:ℝ≥0∞) ∂rawBranchReturnKernel a b h := lintegral_mono hS
        _ = rawBranchReturnKernel a b h univ := by simp
        _ ≤ 1 := rawBranchReturn_mass_le_one a b h

instance rawMarkedWordKernel_isFiniteKernel (a : ℕ) (w : List Bool) : IsFiniteKernel (rawMarkedWordKernel a w) :=
  (rawMarkedWord_bound_and_finite w a).1

theorem rawMarkedWord_mass_le_one (a : ℕ) (w : List Bool) (h : RawHistory a) :
    rawMarkedWordKernel a w h univ ≤ 1 := (rawMarkedWord_bound_and_finite w a).2 h

lemma rawMarkedWord_cons_lintegral (a : ℕ) (b : Bool) (w : List Bool) (h : RawHistory a)
    {F : RawCycleWordTrace a (b::w).length → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ t, F t ∂rawMarkedWordKernel a (b::w) h) =
      ∫⁻ r : RawReturnTrace a, ∫⁻ t,
        F (@Sigma.mk ℕ (fun n => RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) w.length)
          r.1 (r.2,t)) ∂rawMarkedWordKernel (a+2*(r.1+1)) w r.2 ∂rawBranchReturnKernel a b h := by
  rw [rawMarkedWordKernel,Kernel.lintegral_comp _ _ _ hF]
  apply lintegral_congr
  rintro ⟨n,y⟩
  calc
    _ = ∫⁻ p : RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) w.length,
        F (@Sigma.mk ℕ (fun j => RawHistory (a+2*(j+1)) × RawCycleWordTrace (a+2*(j+1)) w.length) n p)
          ∂((Kernel.id : Kernel (RawHistory (a+2*(n+1))) (RawHistory (a+2*(n+1)))) ×ₖ
            rawMarkedWordKernel (a+2*(n+1)) w) y :=
      sigmaFamilyKernel_lintegral (fun j : ℕ =>
        (Kernel.id : Kernel (RawHistory (a+2*(j+1))) (RawHistory (a+2*(j+1)))) ×ₖ
          rawMarkedWordKernel (a+2*(j+1)) w) n y hF
    _ = _ := Kernel.lintegral_id_prod (hF.comp (measurableSigmaMk n)) (rawMarkedWordKernel (a+2*(n+1)) w) y

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
