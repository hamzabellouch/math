import OAI.Probability.InvariantIsing.Fields.RationalFieldLaw

namespace OAI

/-! Finite transport plans for rational field laws and the magnetic
one-Lipschitz estimate against every such plan. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing.RationalFieldLaw

structure Coupling (p q : RationalFieldLaw) where
  mass : Fin p.size → Fin q.size → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  row : ∀ i, ∑ j, mass i j=p.mass i
  col : ∀ j, ∑ i, mass i j=q.mass j

namespace Coupling

variable {p q : RationalFieldLaw}

def independent (p q : RationalFieldLaw) : Coupling p q where
  mass i j := p.mass i*q.mass j
  nonneg i j := mul_nonneg (p.mass_pos i).le (q.mass_pos j).le
  row i := by rw [← Finset.mul_sum,q.mass_sum,mul_one]
  col j := by rw [← Finset.sum_mul,p.mass_sum,one_mul]

instance : Nonempty (Coupling p q) := ⟨independent p q⟩

def cost (w : Coupling p q) : ℝ := ∑ i, ∑ j, w.mass i j* |p.field i-q.field j|

lemma cost_nonneg (w : Coupling p q) : 0 ≤ w.cost :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (w.nonneg i j) (abs_nonneg _)

def flip (w : Coupling p q) : Coupling q p where
  mass j i := w.mass i j
  nonneg j i := w.nonneg i j
  row j := w.col j
  col i := w.row i

lemma flip_cost (w : Coupling p q) : w.flip.cost=w.cost := by
  unfold cost flip
  rw [Finset.sum_comm]
  simp only [abs_sub_comm]

lemma magneticValue_sub_le_cost (w : Coupling p q)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Set.Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) :
    p.magneticValue (measureR (ν : Measure ℝ) b)-q.magneticValue (measureR (ν : Measure ℝ) b) ≤ w.cost := by
  have hh := measureMagnetic_transport_le ν a b hcompact hbound ha hb w.mass
    p.mass p.field q.mass q.field w.nonneg (fun i => (p.mass_pos i).le) q.mass_pos
    p.mass_sum q.mass_sum w.row w.col
  change p.magneticValue _ ≤ q.magneticValue _+w.cost at hh
  linarith

lemma abs_magneticValue_sub_le_cost (w : Coupling p q)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Set.Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) :
    |p.magneticValue (measureR (ν : Measure ℝ) b)-q.magneticValue (measureR (ν : Measure ℝ) b)| ≤ w.cost := by
  have h1 := w.magneticValue_sub_le_cost ν a b hcompact hbound ha hb
  have h2 := w.flip.magneticValue_sub_le_cost ν a b hcompact hbound ha hb
  rw [flip_cost] at h2
  exact abs_le.mpr ⟨by linarith,h1⟩

end Coupling
end InvariantIsing.RationalFieldLaw

end

end OAI
