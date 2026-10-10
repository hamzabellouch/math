import OAI.Dynamics.StandardMap.EndpointMatching

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma covering_contraction {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (F : Set X)
    (r s : X → ℝ) (R : ℝ) (η : ℝ≥0∞)
    (hr : ∀ x∈F, 0<r x ∧ r x≤R)
    (hlocal : ∀ b∈F,
      μ (⋃ a∈F, ⋃ (_ : (ball a (r a) ∩ ball b (r b)).Nonempty ∧ r a≤2*r b), ball a (s a)) ≤
        η*μ (ball b (r b))) :
    μ (⋃ a∈F, ball a (s a)) ≤ η*μ (⋃ a∈F, ball a (r a)) := by
  obtain ⟨U,hUF,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun x => ball x (r x)) F r 2 (by norm_num)
    (fun x hx => (hr x hx).1.le) R (fun x hx => (hr x hx).2)
    (fun x hx => ⟨x,mem_ball_self (hr x hx).1⟩)
  have hcount : U.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x hx => ⟨x,mem_ball_self (hr x (hUF hx)).1⟩)
  let G := fun b => ⋃ a∈F, ⋃ (_ : (ball a (r a) ∩ ball b (r b)).Nonempty ∧ r a≤2*r b), ball a (s a)
  have hsub : (⋃ a∈F, ball a (s a)) ⊆ ⋃ b∈U, G b := by
    intro x hx
    obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨b,hb,hab,hrab⟩ := hcover a ha
    exact mem_iUnion₂.mpr ⟨b,hb,mem_iUnion₂.mpr ⟨a,ha,mem_iUnion.mpr ⟨⟨hab,hrab⟩,hx⟩⟩⟩
  calc
    _ ≤ μ (⋃ b∈U, G b) := measure_mono hsub
    _ ≤ ∑' b : U, μ (G b) := measure_biUnion_le μ hcount G
    _ ≤ ∑' b : U, η*μ (ball b (r b)) := ENNReal.tsum_le_tsum fun b => hlocal b (hUF b.property)
    _ = η*μ (⋃ b∈U, ball b (r b)) := by
      rw [ENNReal.tsum_mul_left,measure_biUnion hcount hdisj (fun _ _ => measurableSet_ball)]
    _ ≤ _ := by
      gcongr
      exact iUnion_subset fun hb => subset_iUnion_of_subset (hUF hb) Subset.rfl

lemma covering_contraction_of_distance {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (F : Set X)
    (r s : X → ℝ) (R : ℝ) (η : ℝ≥0∞)
    (hr : ∀ x∈F, 0<r x ∧ r x≤R)
    (hlocal : ∀ b∈F,
      μ (⋃ a∈F, ⋃ (_ : dist a b<3*r b ∧ r a≤2*r b), ball a (s a)) ≤
        η*μ (ball b (r b))) :
    μ (⋃ a∈F, ball a (s a)) ≤ η*μ (⋃ a∈F, ball a (r a)) := by
  apply covering_contraction μ F r s R η hr
  intro b hb
  apply le_trans (measure_mono ?_) (hlocal b hb)
  intro x hx
  obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨⟨hab,hrab⟩,hx⟩ := mem_iUnion.mp hx
  have hd := dist_lt_add_of_nonempty_ball_inter_ball hab
  exact mem_iUnion₂.mpr ⟨a,ha,mem_iUnion.mpr ⟨⟨by linarith,hrab⟩,hx⟩⟩
lemma iterate_covering_contraction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (V : ℕ → Set X) (F : Set X) (η B : ℝ≥0∞)
    (hB : μ (V 0)≤B) (hF : ∀ n, F⊆V n) (hstep : ∀ n, μ (V (n+1))≤η*μ (V n)) :
    ∀ n, μ F≤η^n*B := by
  have hbound (n : ℕ) : μ (V n)≤η^n*B := by
    induction n with
    | zero => simpa using hB
    | succ n ih =>
      calc
        _ ≤ η*μ (V n) := hstep n
        _ ≤ η*(η^n*B) := by gcongr
        _ = _ := by rw [pow_succ]; ring
  exact fun n => (measure_mono (hF n)).trans (hbound n)
end StandardMapEntropy

end OAI
