import OAI.Probability.GammaPassage.EnclosingContour
import OAI.Probability.GammaPassage.ContourEnumeration
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The finite-dependent high-density bound in crossings.tex:cr:oriented-paths.
The tests need not be stationary. -/
namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

def SeparatedGoodIndependent (P : Measure Ω) (G : Vertex → Set Ω) (k : ℕ) : Prop :=
  ∀ T : Finset Vertex,
    Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) →
    iIndepSet (fun q : T => G q.val) P

theorem independent_complement_inter {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hi : iIndepSet A P) :
    P {ω | ∀ i, ω ∉ A i} = ∏ i, P (A i)ᶜ := by
  have hh := (iIndepSet_iff_iIndep A P).mp hi
  have hm (i : ι) : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i)ᶜ :=
    (MeasurableSpace.measurableSet_generateFrom (mem_singleton (A i))).compl
  have he := hh.meas_iInter hm
  have heq : {ω | ∀ i, ω ∉ A i} = ⋂ i, (A i)ᶜ := by ext ω; simp
  rw [heq]
  exact he

/-- Probability of all forced-bad sites on one fixed loop. The exponent
uses an integer threshold, avoiding a rounding loss in m/[8(2k+1)^2]. -/
theorem contour_bad_probability {m : ℕ} (c : SquareLoop m)
    (hc : c.NoRepeatedSides) (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (q : ℝ≥0∞) (hq : q ≤ 1)
    (hbad : ∀ v, P (G v)ᶜ ≤ q^(8*(2*k+1)^2)) :
    P {ω | ∀ v ∈ c.badSites, ω ∉ G v} ≤ q^m := by
  classical
  obtain ⟨T,hT,hpair,hcard⟩ := lattice_separated_selection c.badSites k
  have hlen : m ≤ (8*(2*k+1)^2)*T.card := by
    have hh := c.length_le_eight_badSites hc
    nlinarith
  calc
    _ ≤ P {ω | ∀ v : T, ω ∉ G v.val} := by
      apply measure_mono
      intro ω hω v
      exact hω v.val (hT v.property)
    _ = ∏ v : T, P (G v.val)ᶜ := independent_complement_inter _ (hind T hpair)
    _ ≤ ∏ _v : T, q^(8*(2*k+1)^2) := by
      apply Finset.prod_le_prod
      intro v hv
      exact hbad v.val
    _ = q^((8*(2*k+1)^2)*T.card) := by simp [← pow_mul]
    _ ≤ q^m := pow_le_pow_right_of_le_one' hq hlen

theorem enclosingLoop_card_geometric (n : ℕ) :
    Fintype.card (EnclosingLoop n) ≤ 9*16^(n+1) := by
  have hp (n : ℕ) : n+2 ≤ 2^(n+1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      omega
  have hsq : (n+2)^2 ≤ 4^(n+1) := by
    calc
      _ ≤ (2^(n+1))^2 := Nat.pow_le_pow_left (hp n) 2
      _ = (2^2)^(n+1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm (n+1) 2]
      _ = _ := by norm_num
  calc
    _ ≤ 9*(n+2)^2*4^(n+1) := enclosingLoop_card n
    _ ≤ 9*(4^(n+1))*4^(n+1) := by gcongr
    _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num

end PlanarFPP

end OAI
