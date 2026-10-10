import Mathlib
import OAI.Analysis.Commutator.DecomposableLimit
import OAI.Analysis.Commutator.DiagonalCommute
import OAI.Analysis.Commutator.ScalarField

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem exists_member_field (P : VonNeumannAlgebra (Lp H 2 μ))
    (Q : Ω → VonNeumannAlgebra H)
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈Set.centralizer
        (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htmem : ∀ n,∀ᵐ a ∂μ,test n a∈Q a)
    (htdense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop (𝓝 (A f)))
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) (hA : A∈P) :
    ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
      (hb : ∀ᵐ a ∂μ,‖T a‖≤‖A‖),A=operator μ T hm hb ∧ ∀ᵐ a ∂μ,T a∈Q a := by
  obtain ⟨T,hm,hb,he⟩ := exists_field_of_commutes_indicator μ A
    (fun s hs => (hdiag s hs) A hA)
  refine ⟨T,hm,hb,he,?_⟩
  let d : ℂ := ((‖A‖+1:ℝ):ℂ)
  have hdR : 0<‖A‖+1 := by positivity
  have hd : d≠0 := by
    dsimp only [d]
    exact_mod_cast (ne_of_gt hdR)
  have hdn : ‖d⁻¹ • A‖≤1 := by
    rw [norm_smul,norm_inv]
    have hnd : ‖d‖=‖A‖+1 := by
      dsimp only [d]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdR]
    rw [hnd]
    have hi : (‖A‖+1)⁻¹*‖A‖=‖A‖/(‖A‖+1) := by ring
    rw [hi]
    exact (div_le_one hdR).mpr (by linarith)
  obtain ⟨k,hk⟩ := htdense (d⁻¹ • A) (P.smul_mem hA d⁻¹) hdn
  have hlim : ∀ f,Tendsto
      (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop
      (𝓝 (operator μ (fun a => d⁻¹ • T a) (smul_measurable μ d⁻¹ T hm)
        (smul_field_bound μ d⁻¹ T hb) f)) := by
    intro f
    rw [operator_smul μ d⁻¹ T hm hb,←he]
    exact hk f
  have hmem := mem_ae_of_bounded_strong_limit μ Q
    (fun a => d⁻¹ • T a) (smul_measurable μ d⁻¹ T hm)
    (smul_field_bound μ d⁻¹ T hb) (fun n => test (k n)) (fun n => ht (k n))
    (by norm_num : (0:ℝ)≤1) (fun n => htb (k n)) (fun n => htmem (k n)) hlim
  filter_upwards [hmem] with a ha
  have h := (Q a).smul_mem (r:=d) ha
  change T a∈(Q a).toStarSubalgebra
  simpa only [smul_smul,mul_inv_cancel₀ hd,one_smul] using h

end Kadison.Decomposable

end

end
end

end OAI
