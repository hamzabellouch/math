import OAI.Probability.RadialTransition.GrandBounds

namespace OAI

universe uX uY

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma antidiagonal_map {X : Type uX} {Y : Type uY} (f : X → Y) (s : Multiset X) :
    (s.map f).antidiagonal = s.antidiagonal.map (fun p => (p.1.map f, p.2.map f)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.antidiagonal_cons, ih, Multiset.map_add, Multiset.map_map]
    congr 1 <;> apply Multiset.map_congr rfl <;> intro p hp <;> simp

lemma powerset_val_map {X : Type uX} (s : Finset X) :
    (s.powerset.val.map Finset.val) = s.val.powerset := by
  simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]

lemma configurationMultiset_val {X : Type uX} {ι : Type} [Fintype ι] (x : ι → X) :
    configurationMultiset x = (Finset.univ.val.map x) := by
  simp only [configurationMultiset, Finset.sum]
  simpa only [Multiset.map_map, Function.comp_def] using
    Multiset.sum_map_singleton (Finset.univ.val.map x)

lemma configurationMultiset_subtype {X : Type uX} {ι : Type} [Fintype ι]
    (x : ι → X) (T : Finset ι) :
    configurationMultiset (fun i : T => x i) = T.val.map x := by
  unfold configurationMultiset
  calc
    (∑ i : T, {x i}) = ∑ i ∈ T, {x i} := Finset.sum_finset_coe (fun i => {x i}) T
    _ = _ := by
      change (T.val.map (fun i => {x i})).sum = T.val.map x
      simpa only [Multiset.map_map, Function.comp_def] using Multiset.sum_map_singleton (T.val.map x)

def clusterConvolution {X : Type uX} (F G : Multiset X → ℝ≥0∞) (s : Multiset X) : ℝ≥0∞ :=
  (s.antidiagonal.map (fun p => F p.1 * G p.2)).sum

lemma clusterConvolution_add_ge {X : Type uX} (F G : Multiset X → ℝ≥0∞) (s u : Multiset X) :
    F s*G u ≤ clusterConvolution F G (s+u) := by
  apply Multiset.single_le_sum (fun _ _ => bot_le)
  exact Multiset.mem_map.mpr ⟨(s,u), Multiset.mem_antidiagonal.mpr rfl, rfl⟩

lemma clusterConvolution_configuration {X : Type uX} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F G : Multiset X → ℝ≥0∞) (x : ι → X) :
    clusterConvolution F G (configurationMultiset x) =
      ∑ T : Finset ι, F (configurationMultiset (fun i : {i // i ∉ T} => x i)) *
        G (configurationMultiset (fun i : T => x i)) := by
  classical
  rw [clusterConvolution, configurationMultiset_val, antidiagonal_map,
    Multiset.antidiagonal_eq_map_powerset, ← powerset_val_map]
  simp only [Multiset.map_map, Function.comp_def]
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro T _
  congr 1
  · have hval : Finset.univ.val-T.val = Tᶜ.val := by
      change (Finset.univ \ T).val = Tᶜ.val
      rfl
    rw [hval]
    congr 1
    let e : {i // i ∉ T} ≃ {i // i ∈ Tᶜ} := Equiv.subtypeEquivProp (by simp)
    have hh := configurationMultiset_equiv e (fun i : {i // i ∈ Tᶜ} => x i)
    rw [configurationMultiset_subtype] at hh
    exact hh.symm
  · congr 1
    exact (configurationMultiset_subtype x T).symm

end RadialTransition
end

end OAI
