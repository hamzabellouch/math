import OAI.NumberTheory.Jacobsthal.Paths.NearPrefixOccurrence
import OAI.NumberTheory.Jacobsthal.Probability.CompletedMarkEvents

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceBadCompactOccurrence

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories ActualSuccessfulHistories ActualFlagInvariant ActualProcessCoupling
open FiniteHistoryTransport PriorPrimeWindow CompactPrefixOccurrence CompletedMarkEvents
open RegeneratingInverseBands NearbyParentGeometry

variable {w ell S R b₀ b₁ : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem missing_occurrence_inclusion (hc : Consistent start) (hb₀ : 0 < b₀)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E →
      p.node.gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start p.primes) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      occurs E N h → (last N h).2 = true ∨
        mapHist (fun q => q.1.2) N h ∈ badCompactPath (Real.log start.gap) ((11/10)*R) b₀ b₁ N := by
  filter_upwards [sourceHistory_success_good hw hell hS0 hS hr hs hsS hm N,
    sourceHistory_prior_mark hw hell hS0 hS hr hs hsS hc hm hmesh N herror] with h hg hprior
  intro hocc
  by_cases hf : (last N h).2 = true
  · exact Or.inl hf
  have hfalse : (last N h).2 = false := by cases hval : (last N h).2 <;> simp_all
  obtain ⟨j,hjE⟩ := hocc
  let j' : Finset.Iic N := ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩
  cases hp : (h j').1.1 with
  | none =>
    change selectedNode E (h j').1.1 at hjE
    rw [hp] at hjE
    exact False.elim hjE
  | some p =>
    change selectedNode E (h j').1.1 at hjE
    rw [hp] at hjE
    have hpE := hE p hjE
    have hgj : GoodAt (Real.log start.gap) mesh j'.1 (some p,(h j').1.2) := by
      simpa only [← hp] using hg hfalse j'
    cases hz : (h j').1.2 with
    | inr u => rw [hz] at hgj; exact False.elim hgj
    | inl z =>
      rw [hz] at hgj
      have hn : (j'.1:ℝ) ≤ N := by exact_mod_cast Finset.mem_Iic.mp j'.2
      have herr : 4*(j'.1:ℝ)*mesh ≤ Real.log (11/10) :=
        (by nlinarith : 4*(j'.1:ℝ)*mesh ≤ 4*(N:ℝ)*mesh).trans herror
      have he : Real.exp (4*(j'.1:ℝ)*mesh) ≤ (11/10:ℝ) := by
        rw [← Real.exp_log (by norm_num : 0 < (11/10:ℝ))]
        exact Real.exp_le_exp.mpr herr
      have hpPos := terminal_gap_positive (by linarith : 0 ≤ ell) hr hs p.admissible
      have hrel := log_gap_relative hpPos (Real.exp_pos _) hgj.2.2.2
      have hgap : gapValue (Real.log start.gap) z ≤ (11/10)*R :=
        hrel.2.trans ((mul_le_mul_of_nonneg_right he hpPos.le).trans
          (mul_le_mul_of_nonneg_left hpE.1 (by norm_num)))
      apply Or.inr
      refine ⟨j',?_,?_⟩
      · change compactPoint (Real.log start.gap) ((11/10)*R) (h j').1.2
        rw [hz]
        exact hgap
      · intro i hij hMark
        change markedPoint (Real.log start.gap) b₀ b₁ (h i).1.2 at hMark
        cases hi : (h i).1.2 with
        | inr u => rw [hi] at hMark; exact False.elim hMark
        | inl y =>
          rw [hi] at hMark
          exact hpE.2 (hprior hfalse i j' hij p hp y hi b₀ b₁ hb₀
            hMark.1 hMark.2.1 hMark.2.2.1 hMark.2.2.2.1 hMark.2.2.2.2)

end NumberTheoryLean.SourceBadCompactOccurrence

end

end Erdos970

end OAI
