import OAI.Combinatorics.Crossing.AffinePathHalves
import OAI.Combinatorics.Crossing.AlternatingPaths

namespace OAI

noncomputable section
namespace Zarankiewicz

def OrderedPathPart {a b c d : Plane} (γ : Path a b) (δ : Path c d) : Prop :=
  ∃ f : unitInterval → unitInterval, StrictMono f ∧ ∀ t, γ (f t)=δ t

theorem OrderedPathPart.refl {a b : Plane} (γ : Path a b) : OrderedPathPart γ γ :=
  ⟨id,strictMono_id,fun _ => rfl⟩

theorem OrderedPathPart.trans {a b c d e f : Plane} {γ : Path a b} {δ : Path c d} {η : Path e f}
    (hγ : OrderedPathPart γ δ) (hδ : OrderedPathPart δ η) : OrderedPathPart γ η := by
  obtain ⟨u,hu,he⟩ := hγ
  obtain ⟨v,hv,hf⟩ := hδ
  exact ⟨u ∘ v,hu.comp hv,fun t => (he (v t)).trans (hf t)⟩

theorem OrderedPathPart.left {a b c d e : Plane} {γ : Path a b} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path b c) : OrderedPathPart (γ.trans η) δ :=
  (show OrderedPathPart (γ.trans η) γ from
    ⟨intervalLeft,intervalLeft_strictMono,path_trans_intervalLeft γ η⟩).trans h

theorem OrderedPathPart.right {a b c d e : Plane} {γ : Path b c} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path a b) : OrderedPathPart (η.trans γ) δ :=
  (show OrderedPathPart (η.trans γ) γ from
    ⟨intervalRight,intervalRight_strictMono,path_trans_intervalRight η γ⟩).trans h

theorem OrderedPathPart.congr_right {a b c d e f : Plane} {γ : Path a b}
    {δ : Path c d} {η : Path e f} (h : OrderedPathPart γ δ) (he : ∀ t, δ t=η t) :
    OrderedPathPart γ η := by
  obtain ⟨u,hu,hh⟩ := h
  exact ⟨u,hu,fun t => (hh t).trans (he t)⟩

theorem OrderedPathPart.endpoints_ordered {a b c d : Plane} {γ : Path a b} {δ : Path c d}
    (h : OrderedPathPart γ δ) :
    ∃ u v : unitInterval, u < v ∧ γ u=c ∧ γ v=d := by
  obtain ⟨f,hf,he⟩ := h
  exact ⟨f 0,f 1,hf zero_lt_one,(he 0).trans δ.source,(he 1).trans δ.target⟩

theorem alternatingPath_contains_path (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) :
    (n : ℕ) → ∀ i, i ≤ n → OrderedPathPart (alternatingPath a b p q n) (p i)
  | 0, i, hi => by
    have he : i=0 := by omega
    subst i
    exact OrderedPathPart.refl _
  | n+1, i, hi => by
    by_cases he : i=n+1
    · subst i
      exact (OrderedPathPart.refl (p (n+1))).right _
    · exact ((alternatingPath_contains_path a b p q n i (by omega)).left (q n)).left (p (n+1))

theorem alternatingPath_contains_bridge (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) :
    (n : ℕ) → ∀ i, i < n → OrderedPathPart (alternatingPath a b p q n) (q i)
  | 0, i, hi => by omega
  | n+1, i, hi => by
    by_cases he : i=n
    · subst i
      exact ((OrderedPathPart.refl (q n)).right _).left _
    · exact ((alternatingPath_contains_bridge a b p q n i (by omega)).left (q n)).left (p (n+1))

end Zarankiewicz

end

end OAI
