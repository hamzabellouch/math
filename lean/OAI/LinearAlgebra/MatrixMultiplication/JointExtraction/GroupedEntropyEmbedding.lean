import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.GroupedEntropyPartition

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointGroupedEntropyEmbedding

open MatrixMultiplication.Foundation JointCompatibilityIncidence JointNativeGroupedEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {U V K L A : Type*}
  [Fintype U] [Fintype V] [Fintype K] [Fintype L] [Fintype A]

omit [Fintype K] [Fintype L] in
theorem groupMass_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (k : K) :
    groupMass p (j ∘ group) (j k) = groupMass p group k := by
  simp only [groupMass, Function.comp_apply, hj.eq_iff]

omit [Fintype K] [Fintype L] [Fintype A] in
theorem groupLaw_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (q : U → A → ℝ) (k : K) :
    groupLaw p (j ∘ group) q (j k) = groupLaw p group q k := by
  funext a
  simp only [groupLaw, groupMass_label_injective j hj,
    Function.comp_apply, hj.eq_iff]

omit [Fintype K] [Fintype L] in
theorem groupMass_label_not_mem_range (j : K → L) (p : U → ℝ)
    (group : U → K) (l : L) (hl : l ∉ Set.range j) :
    groupMass p (j ∘ group) l = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  exact ite_eq_right (fun equality => hl ⟨group u, equality⟩)

theorem groupedEntropy_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (q : U → A → ℝ) :
    groupedEntropy p (j ∘ group) q = groupedEntropy p group q := by
  unfold groupedEntropy
  symm
  apply Fintype.sum_of_injective j hj
  · intro l hl
    rw [groupMass_label_not_mem_range j p group l hl, zero_mul]
  · intro k
    rw [groupMass_label_injective j hj, groupLaw_label_injective j hj]

def pushforwardWeight (p : U → ℝ) (f : U → V) (v : V) : ℝ :=
  ∑ u, if f u = v then p u else 0

theorem sum_pushforwardWeight_mul (p : U → ℝ) (f : U → V) (test : V → ℝ) :
    (∑ v, pushforwardWeight p f v * test v) = ∑ u, p u * test (f u) := by
  simp only [pushforwardWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [ite_mul, zero_mul]
  simp

omit [Fintype K] in
theorem groupMass_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (k : K) :
    groupMass (pushforwardWeight p f) group k = groupMass p (group ∘ f) k := by
  simpa only [groupMass, mul_ite, mul_one, mul_zero, Function.comp_apply] using
    (sum_pushforwardWeight_mul p f (fun v => if group v = k then 1 else 0))

omit [Fintype K] [Fintype A] in
theorem groupMeasure_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupMeasure (pushforwardWeight p f) group q k =
      groupMeasure p (group ∘ f) (q ∘ f) k := by
  funext a
  simpa only [groupMeasure, mul_ite, mul_zero, Function.comp_apply] using
    (sum_pushforwardWeight_mul p f (fun v => if group v = k then q v a else 0))

omit [Fintype K] [Fintype A] in
theorem groupLaw_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupLaw (pushforwardWeight p f) group q k =
      groupLaw p (group ∘ f) (q ∘ f) k := by
  funext a
  change groupMeasure (pushforwardWeight p f) group q k a /
      groupMass (pushforwardWeight p f) group k =
    groupMeasure p (group ∘ f) (q ∘ f) k a / groupMass p (group ∘ f) k
  rw [groupMeasure_pushforward, groupMass_pushforward]

theorem groupedEntropy_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) :
    groupedEntropy (pushforwardWeight p f) group q =
      groupedEntropy p (group ∘ f) (q ∘ f) := by
  simp only [groupedEntropy, groupMass_pushforward, groupLaw_pushforward]

theorem groupedEntropy_pushforward_of_agree (p : U → ℝ) (f : U → V)
    (group : V → K) (qU : U → A → ℝ) (qV : V → A → ℝ)
    (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (pushforwardWeight p f) group qV =
      groupedEntropy p (group ∘ f) qU := by
  rw [groupedEntropy_pushforward]
  have he : qV ∘ f = qU := funext hq
  rw [he]

theorem groupedEntropy_pushforward_embedding (p : U → ℝ) (f : U → V)
    (groupU : U → K) (groupV : V → L) (j : K → L) (hj : Function.Injective j)
    (hgroup : ∀ u, groupV (f u) = j (groupU u))
    (qU : U → A → ℝ) (qV : V → A → ℝ) (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (pushforwardWeight p f) groupV qV = groupedEntropy p groupU qU := by
  rw [groupedEntropy_pushforward_of_agree p f groupV qU qV hq]
  have hg : groupV ∘ f = j ∘ groupU := funext hgroup
  rw [hg, groupedEntropy_label_injective j hj]

theorem sum_map_mass_mul (p : FiniteLaw U) (f : U → V) (test : V → ℝ) :
    (∑ v, (p.map f).mass v * test v) = ∑ u, p.mass u * test (f u) := by
  simpa only [FiniteLaw.map_mass, pushforwardWeight] using
    (sum_pushforwardWeight_mul p.mass f test)

omit [Fintype K] in
theorem groupMass_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (k : K) :
    groupMass (p.map f).mass group k = groupMass p.mass (group ∘ f) k := by
  simpa only [groupMass, mul_ite, mul_one, mul_zero, Function.comp_apply] using
    (sum_map_mass_mul p f (fun v => if group v = k then 1 else 0))

omit [Fintype K] [Fintype A] in
theorem groupMeasure_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupMeasure (p.map f).mass group q k =
      groupMeasure p.mass (group ∘ f) (q ∘ f) k := by
  funext a
  simpa only [groupMeasure, mul_ite, mul_zero, Function.comp_apply] using
    (sum_map_mass_mul p f (fun v => if group v = k then q v a else 0))

omit [Fintype K] [Fintype A] in
theorem groupLaw_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupLaw (p.map f).mass group q k = groupLaw p.mass (group ∘ f) (q ∘ f) k := by
  funext a
  change groupMeasure (p.map f).mass group q k a / groupMass (p.map f).mass group k =
    groupMeasure p.mass (group ∘ f) (q ∘ f) k a / groupMass p.mass (group ∘ f) k
  rw [groupMeasure_map, groupMass_map]

theorem groupedEntropy_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (q : V → A → ℝ) :
    groupedEntropy (p.map f).mass group q =
      groupedEntropy p.mass (group ∘ f) (q ∘ f) := by
  simp only [groupedEntropy, groupMass_map, groupLaw_map]

theorem groupedEntropy_map_of_agree (p : FiniteLaw U) (f : U → V)
    (group : V → K) (qU : U → A → ℝ) (qV : V → A → ℝ)
    (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (p.map f).mass group qV =
      groupedEntropy p.mass (group ∘ f) qU := by
  rw [groupedEntropy_map]
  have he : qV ∘ f = qU := funext hq
  rw [he]

theorem groupedEntropy_map_embedding (p : FiniteLaw U) (f : U → V)
    (groupU : U → K) (groupV : V → L) (j : K → L) (hj : Function.Injective j)
    (hgroup : ∀ u, groupV (f u) = j (groupU u))
    (qU : U → A → ℝ) (qV : V → A → ℝ) (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (p.map f).mass groupV qV = groupedEntropy p.mass groupU qU := by
  rw [groupedEntropy_map_of_agree p f groupV qU qV hq]
  have hg : groupV ∘ f = j ∘ groupU := funext hgroup
  rw [hg, groupedEntropy_label_injective j hj]

end MatrixMultiplication.JointGroupedEntropyEmbedding

end

end OAI
