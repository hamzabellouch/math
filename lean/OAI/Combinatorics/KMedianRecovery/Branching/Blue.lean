import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Destination
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelRange

namespace OAI

namespace MetricKMedianRecovery.Completion
namespace Destination
variable {V : Type*} {a : ℕ}
def isBlue : Destination V a → Bool
  | .uncovered _ => true
  | _ => false
end Destination

variable {V : Type*} [DecidableEq V] {a : ℕ}

def designatedRed (R : Finset V) (dest : V → Destination V a) : Finset V :=
  R.filter (fun s => (dest s).isBlue = false)
def designatedBlue (R : Finset V) (dest : V → Destination V a) : Finset V :=
  R.filter (fun s => (dest s).isBlue = true)
def designatedProxies (R : Finset V) (dest : V → Destination V a) : Finset V :=
  R.biUnion (fun s => match dest s with | .proxy v => {v} | _ => ∅)

def requiredColors (R : Finset V) (dest : V → Destination V a) (s : V) : Fin 3 :=
  if s ∈ R then if (dest s).isBlue then 2 else 1 else 0

lemma designated_partition (R : Finset V) (dest : V → Destination V a) :
    Disjoint (designatedRed R dest) (designatedBlue R dest) ∧
      designatedRed R dest ∪ designatedBlue R dest = R := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro s hs ht
    have h₁ := (Finset.mem_filter.mp hs).2
    have h₂ := (Finset.mem_filter.mp ht).2
    simp only [h₁] at h₂
    contradiction
  · ext s
    simp only [designatedBlue,designatedRed,Finset.mem_union,Finset.mem_filter]
    cases (dest s).isBlue <;> simp

lemma designated_count (R : Finset V) (dest : V → Destination V a) :
    (designatedRed R dest).card+(designatedBlue R dest).card = R.card := by
  rw [← Finset.card_union_of_disjoint (designated_partition R dest).1,
    (designated_partition R dest).2]

lemma designatedProxies_mem (R : Finset V) (dest : V → Destination V a) (v : V) :
    v ∈ designatedProxies R dest ↔ ∃ s ∈ R, dest s = .proxy v := by
  simp only [designatedProxies,Finset.mem_biUnion]
  constructor
  · rintro ⟨s,hs,hv⟩
    refine ⟨s,hs,?_⟩
    cases he : dest s with
    | proxy w =>
      simp only [he,Finset.mem_singleton] at hv
      subst w
      rfl
    | covered i => simp only [he,Finset.notMem_empty] at hv
    | uncovered o => simp only [he,Finset.notMem_empty] at hv
  · rintro ⟨s,hs,he⟩
    exact ⟨s,hs,by simp only [he,Finset.mem_singleton]⟩

lemma designatedProxies_card_le (R : Finset V) (dest : V → Destination V a) :
    (designatedProxies R dest).card ≤ R.card := by
  unfold designatedProxies
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _s ∈ R, 1 := Finset.sum_le_sum (fun s _ => by cases dest s <;> simp)
    _ = R.card := by simp

lemma color_requirement_count (R : Finset V) (dest : V → Destination V a) (m : ℕ)
    (hR : R.card ≤ m) : (R ∪ designatedProxies R dest).card ≤ 2*m := by
  have hc := Finset.card_union_le R (designatedProxies R dest)
  have hp := designatedProxies_card_le R dest
  omega

lemma favorable_color_consequences (R : Finset V) (dest : V → Destination V a)
    (hdisj : Disjoint R (designatedProxies R dest)) (colors : V → Fin 3)
    (hcolors : ∀ s ∈ R ∪ designatedProxies R dest, colors s = requiredColors R dest s) :
    (∀ s ∈ designatedRed R dest, colors s = 1) ∧
    (∀ s ∈ designatedBlue R dest, colors s = 2) ∧
    (∀ s ∈ designatedProxies R dest, colors s = 0) := by
  refine ⟨?_,?_,?_⟩
  · intro s hs
    obtain ⟨hsR,hsd⟩ := Finset.mem_filter.mp hs
    simpa only [requiredColors,hsR,↓reduceIte,hsd,Bool.false_eq_true] using
      hcolors s (Finset.mem_union_left _ hsR)
  · intro s hs
    obtain ⟨hsR,hsd⟩ := Finset.mem_filter.mp hs
    simpa only [requiredColors,hsR,↓reduceIte,hsd] using
      hcolors s (Finset.mem_union_left _ hsR)
  · intro s hs
    have hn : s ∉ R := fun hr => Finset.disjoint_left.mp hdisj hr hs
    simpa only [requiredColors,hn,↓reduceIte] using
      hcolors s (Finset.mem_union_right _ hs)

lemma favorable_colors_exist_with_mass [Fintype V]
    (R : Finset V) (dest : V → Destination V a) (m : ℕ) (hR : R.card ≤ m) :
    (1/4 : ℝ)^(2*m) ≤
      ∑ seed : V → Fin 4,
        if ∀ s ∈ R ∪ designatedProxies R dest,
          ColorLabel.color (seed s) = requiredColors R dest s
        then (1/4 : ℝ)^(Fintype.card V) else 0 := by
  exact ColorLabel.favorable_color_probability (R ∪ designatedProxies R dest)
    (requiredColors R dest) m (color_requirement_count R dest m hR)

lemma proxy_requirements_consistent (R Proxies : Finset V)
    (dest : V → Destination V a) (hRP : Disjoint R Proxies)
    (hdest : ∀ s ∈ R, ∀ v, dest s = .proxy v → v ∈ Proxies) :
    Disjoint R (designatedProxies R dest) := by
  refine hRP.mono_right ?_
  intro v hv
  obtain ⟨s,hs,he⟩ := (designatedProxies_mem R dest v).mp hv
  exact hdest s hs v he

end MetricKMedianRecovery.Completion

end OAI
