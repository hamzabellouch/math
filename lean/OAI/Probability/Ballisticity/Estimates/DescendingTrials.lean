import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedHeight
import OAI.Probability.Ballisticity.Crossings.HittingIteration

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma signedHeight_step_ge {d : ℕ} (e : Direction d) (x : Lattice d) (f : Direction d) :
    signedHeight e x-1 ≤ signedHeight e (x+step f) := by
  simp only [signedHeight,Pi.add_apply,step]
  split <;> split <;> (try split) <;> omega

lemma integer_first_descent (z : ℕ → ℤ) (k : ℕ) (m : ℕ)
    (h0 : z 0 = (k:ℤ)+1) (hm : z m < 0)
    (hstep : ∀ n, z n-1 ≤ z (n+1)) :
    ∃ n < m, z n = (k:ℤ) ∧ ∀ j < n, (k:ℤ)+1 ≤ z j := by
  have hex : ∃ j, z j < (k:ℤ)+1 := ⟨m,by omega⟩
  let n := Nat.find hex
  have hn : z n < (k:ℤ)+1 := Nat.find_spec hex
  have hnm : n ≤ m := Nat.find_min' hex (by omega)
  have hpre : ∀ j < n, (k:ℤ)+1 ≤ z j := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hn0 : 0 < n := by
    by_contra hh
    have hh0 : n=0 := by omega
    rw [hh0,h0] at hn
    omega
  have hp := hpre (n-1) (by omega)
  have hs := hstep (n-1)
  have hnEq : n-1+1=n := by omega
  rw [hnEq] at hs
  have he : z n = (k:ℤ) := by omega
  have hlt : n < m := by
    by_contra hh
    have hEq : n=m := by omega
    rw [hEq] at he
    omega
  exact ⟨n,hlt,he,hpre⟩

def BoxStrip {d : ℕ} (e : Direction d) (N : ℕ) (B : Set (Lattice d)) : Set (Lattice d) :=
  {y | y ∈ B ∧ 0 ≤ signedHeight e y ∧ signedHeight e y ≤ (N:ℤ)}

lemma down_hit_disjoint_cross {d : ℕ} (e : Direction d) (N : ℕ)
    (S T : Set (Lattice d)) (x : Lattice d)
    (hx : 0 ≤ signedHeight e x)
    (hS : ∀ y ∈ S, signedHeight e y ≤ (N:ℤ))
    (hT : ∀ y ∈ T, signedHeight e y < signedHeight e x) :
    Disjoint (Hit S T) (Cross (realPosition (step e)) x (N+1)) := by
  apply Set.disjoint_left.mpr
  intro X hdown hup
  obtain ⟨n,hnT,hnS⟩ := Set.mem_iUnion.mp hdown
  obtain ⟨m,hmH,hmD⟩ := hup
  simp only [signedHeight_projection] at hmH hmD
  by_cases hmn : m < n
  · have hb := hS (X m) (hnS m hmn)
    have hb' : (signedHeight e (X m):ℝ) ≤ (N:ℝ) := by exact_mod_cast hb
    have hx' : (0:ℝ) ≤ signedHeight e x := by exact_mod_cast hx
    linarith
  · have ht := hT (X n) hnT
    have ht' : (signedHeight e (X n):ℝ) < signedHeight e x := by exact_mod_cast ht
    by_cases hnm : n < m
    · have hl := hmD n hnm
      linarith
    · have heq : n=m := by omega
      rw [heq] at ht'
      have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
      linarith

lemma down_hit_mass_le {d : ℕ} (ω : Environment d) (e : Direction d) (N : ℕ)
    (S T : Set (Lattice d)) (x : Lattice d)
    (hx : 0 ≤ signedHeight e x)
    (hS : ∀ y ∈ S, signedHeight e y ≤ (N:ℤ))
    (hT : ∀ y ∈ T, signedHeight e y < signedHeight e x) (δ : ℝ≥0∞)
    (hδ : δ ≤ crossingQuenched (realPosition (step e)) x (N+1) ω) :
    quenchedKernel (ω,x) (Hit S T) ≤ 1-δ := by
  have hd := down_hit_disjoint_cross e N S T x hx hS hT
  calc
    _ ≤ quenchedKernel (ω,x) (Cross (realPosition (step e)) x (N+1))ᶜ :=
      measure_mono (Set.disjoint_left.mp hd)
    _ = 1-crossingQuenched (realPosition (step e)) x (N+1) ω := by
      rw [measure_compl (measurableSet_cross _ _ _) (measure_ne_top _ _),measure_univ]
      rfl
    _ ≤ _ := tsub_le_tsub_left hδ _

theorem quenched_descending_trials {d : ℕ} (ω : Environment d) (e : Direction d)
    (N : ℕ) (B : Set (Lattice d)) (δ : ℝ≥0∞)
    (hgood : ∀ y ∈ BoxStrip e N B,
      δ ≤ crossingQuenched (realPosition (step e)) y (N+1) ω) :
    ∀ k : ℕ, ∀ x ∈ B, signedHeight e x = (k:ℤ) → k ≤ N →
      quenchedKernel (ω,x) (Hit (BoxStrip e N B) {y | signedHeight e y < 0}) ≤ (1-δ)^(k+1) := by
  let S := BoxStrip e N B
  let T : Set (Lattice d) := {y | signedHeight e y < 0}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => not_lt_of_ge hs.2.1 ht)
  intro k
  induction k with
  | zero =>
    intro x hx hx0 hk
    simpa only [zero_add,pow_one] using down_hit_mass_le ω e N S T x
      (by omega) (fun y hy => hy.2.2) (fun y hy => by change signedHeight e y < 0 at hy; omega) δ
      (hgood x ⟨hx,by omega,by omega⟩)
  | succ k ih =>
    intro x hx hxk hkN
    let U : Set (Lattice d) := {y | y ∈ B ∧ signedHeight e y = (k:ℤ)}
    have hsub : ∀ᵐ X ∂quenchedKernel (ω,x),
        X ∈ Hit S T → X ∈ ⋃ n, HitAt (S \ U) U n ∩ FutureEvent (fun _ => Hit S T) n := by
      filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hNN hX
      obtain ⟨m,hm,hmS⟩ := Set.mem_iUnion.mp hX
      have hstep (n : ℕ) : signedHeight e (X n)-1 ≤ signedHeight e (X (n+1)) := by
        obtain ⟨f,hf⟩ := hNN n
        rw [hf]; exact signedHeight_step_ge e (X n) f
      obtain ⟨n,hnm,hnEq,_⟩ := integer_first_descent (fun n => signedHeight e (X n)) k m
        (by rw [h0,hxk]; simp) hm hstep
      apply hit_split_subset S T U hST X hX
      exact ⟨n,⟨(hmS n hnm).1,hnEq⟩,fun j hj => hmS j (hj.trans hnm)⟩
    calc
      _ ≤ quenchedKernel (ω,x) (⋃ n, HitAt (S \ U) U n ∩ FutureEvent (fun _ => Hit S T) n) :=
        measure_mono_ae hsub
      _ ≤ (1-δ)^(k+1) * quenchedKernel (ω,x) (Hit (S \ U) U) :=
        quenched_hit_future_bound ω x Set.disjoint_sdiff_left (fun _ => Hit S T)
          (fun _ => measurableSet_hit S T) _ (fun y hy => ih y hy.1 hy.2 (by omega))
      _ ≤ (1-δ)^(k+1) * (1-δ) := by
        apply mul_le_mul_right
        exact down_hit_mass_le ω e N (S \ U) U x (by omega)
          (fun y hy => hy.1.2.2) (fun y hy => by change _ = _ at hxk; rw [hy.2,hxk]; omega) δ
          (hgood x ⟨hx,by omega,by omega⟩)
      _ = _ := (pow_succ _ _).symm

end DirectionalTransience

end

end OAI
