import OAI.Probability.FirstPassage.BKForcing
import OAI.Probability.FirstPassage.LocalizedEvents
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic.Positivity

namespace OAI

namespace PlanarFPP
open Finset

structure StrictPathWitness where
  start : Vertex
  steps : List Step
  bound : ℝ

namespace StrictPathWitness

def edges (p : StrictPathWitness) : Finset Edge := pathEdges p.start p.steps

def bits (p : StrictPathWitness) (t : ℕ) : Finset (Edge × Fin t) := p.edges ×ˢ univ

end StrictPathWitness

noncomputable def dyadicSurvival (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : ℝ :=
  ∑ h : Fin t, if (e,h) ∈ x then 1/(2:ℝ)^(h.val+1) else 0

lemma dyadicSurvival_nonneg (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    0 ≤ dyadicSurvival t x e := by
  apply Finset.sum_nonneg
  intro h _
  split_ifs <;> positivity

lemma dyadicSurvival_mono (t : ℕ) {x y : Finset (Edge × Fin t)} (hxy : x ⊆ y) (e : Edge) :
    dyadicSurvival t x e ≤ dyadicSurvival t y e := by
  apply Finset.sum_le_sum
  intro h _
  by_cases hx : (e,h) ∈ x
  · simp [hx,hxy hx]
  · simp only [hx,↓reduceIte]
    split_ifs <;> positivity

lemma dyadicSurvival_eq (t : ℕ) (x y : Finset (Edge × Fin t)) (e : Edge)
    (h : ∀ a : Fin t, (e,a) ∈ x ↔ (e,a) ∈ y) :
    dyadicSurvival t x e = dyadicSurvival t y e := by
  apply Finset.sum_congr rfl
  intro a _
  simp only [h a]

lemma pathCost_le_of_edges {w v : Edge → ℝ} (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e ≤ v e) : pathCost w p ds ≤ pathCost v p ds := by
  induction ds generalizing p with
  | nil => exact le_rfl
  | cons d ds ih =>
    exact add_le_add (h _ (by simp [pathEdges]))
      (ih _ (fun e he => h e (by simp [pathEdges,he])))

def DyadicPathGood (t : ℕ) (x : Finset (Edge × Fin t)) (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < dyadicSurvival t x e) ∧
    pathCost (fun e => -Real.log (dyadicSurvival t x e)) p.start p.steps < p.bound

lemma DyadicPathGood.mono {t : ℕ} {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : DyadicPathGood t x p) (hxy : x ⊆ y) : DyadicPathGood t y p := by
  constructor
  · intro e he
    exact (h.1 e he).trans_le (dyadicSurvival_mono t hxy e)
  · apply lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps ?_) h.2
    intro e he
    exact neg_le_neg (Real.log_le_log (h.1 e he) (dyadicSurvival_mono t hxy e))

lemma DyadicPathGood.of_agree {t : ℕ} {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : DyadicPathGood t x p)
    (hxy : ∀ a ∈ p.bits t, a ∈ y ↔ a ∈ x) : DyadicPathGood t y p := by
  have heq : ∀ e ∈ p.edges, dyadicSurvival t y e = dyadicSurvival t x e := by
    intro e he
    apply dyadicSurvival_eq
    intro a
    exact hxy (e,a) (by simp [StrictPathWitness.bits,he])
  constructor
  · intro e he; rw [heq e he]; exact h.1 e he
  · have hc := pathCost_eq_of_agree
      (fun e => -Real.log (dyadicSurvival t y e))
      (fun e => -Real.log (dyadicSurvival t x e)) p.start p.steps
      (fun e he => congrArg (fun a => -Real.log a) (heq e he))
    rw [hc]; exact h.2

noncomputable def dyadicPathFamily (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S ×ˢ (univ : Finset (Fin t))).powerset.filter
    (fun x => ∃ p ∈ F, p.edges ⊆ S ∧ DyadicPathGood t x p)

lemma mem_dyadicPathFamily (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness)
    (x : Finset (Edge × Fin t)) :
    x ∈ dyadicPathFamily S t F ↔ x ⊆ S ×ˢ univ ∧
      ∃ p ∈ F, p.edges ⊆ S ∧ DyadicPathGood t x p := by
  classical
  simp [dyadicPathFamily]

lemma upward_dyadicPathFamily (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    UpwardFamily (S ×ˢ univ) (dyadicPathFamily S t F) := by
  constructor
  · intro x hx; exact ((mem_dyadicPathFamily ..).mp hx).1
  · intro x hx y hxy hys
    obtain ⟨_,p,hp,he,hgood⟩ := (mem_dyadicPathFamily ..).mp hx
    exact (mem_dyadicPathFamily ..).mpr ⟨hys,p,hp,he,hgood.mono hxy⟩

lemma dyadic_path_forces (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness)
    (x : Finset (Edge × Fin t)) (p : StrictPathWitness)
    (hp : p ∈ F) (he : p.edges ⊆ S) (hgood : DyadicPathGood t x p) :
    ForcesBits (S ×ˢ univ) (dyadicPathFamily S t F) x (p.bits t) := by
  intro y hys hxy
  exact (mem_dyadicPathFamily ..).mpr ⟨hys,p,hp,he,hgood.of_agree hxy⟩

lemma StrictPathWitness.disjoint_bits {p q : StrictPathWitness} (t : ℕ)
    (h : Disjoint p.edges q.edges) : Disjoint (p.bits t) (q.bits t) := by
  apply Finset.disjoint_left.mpr
  intro a hp hq
  exact Finset.disjoint_left.mp h (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1

noncomputable def dyadicDisjointPathFamily (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) : Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S ×ˢ (univ : Finset (Fin t))).powerset.filter (fun x =>
    ∃ ps : List StrictPathWitness,
      List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ DyadicPathGood t x p) ps Fs ∧
      ps.Pairwise (fun p q => Disjoint p.edges q.edges))

theorem dyadic_strict_path_BK (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    fairFamilyMass (S ×ˢ univ) (dyadicDisjointPathFamily S t Fs) ≤
      (Fs.map (fun F => fairFamilyMass (S ×ˢ univ) (dyadicPathFamily S t F))).prod := by
  apply (finite_fair_BK_forcing (S ×ˢ univ) (Fs.map (dyadicPathFamily S t))
    (dyadicDisjointPathFamily S t Fs) ?_ ?_).trans_eq
      (by simp only [List.map_map,Function.comp_def])
  · intro A hA
    obtain ⟨F,_,rfl⟩ := List.mem_map.mp hA
    exact upward_dyadicPathFamily S t F
  · intro x hx
    simp only [dyadicDisjointPathFamily,mem_filter,mem_powerset] at hx
    obtain ⟨hxs,ps,hps,hd⟩ := hx
    refine ⟨hxs,ps.map (fun p => p.bits t),?_,?_⟩
    · clear hd
      induction hps with
      | nil => exact List.Forall₂.nil
      | cons h ht ih =>
        exact List.Forall₂.cons (dyadic_path_forces S t _ x _ h.1 h.2.1 h.2.2) ih
    · rw [List.pairwise_map]
      exact hd.imp (fun h => StrictPathWitness.disjoint_bits t h)

end PlanarFPP

end OAI
