import OAI.Combinatorics.InfiniteMatroid.Separation

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma sameClass_iff_differences (T X : Set E0) : SameClass T X ↔ Small (X \ T) ∧ Small (T \ X) := by
  constructor
  · intro h
    exact ⟨small_subset h (by intro x hx; exact Or.inl hx),small_subset h (by intro x hx; exact Or.inr hx)⟩
  · rintro ⟨h1,h2⟩
    exact small_union h1 h2

lemma sameClass_of_small_gap {T I Y : Set E0} (hI : SameClass T I) (hIY : I ⊆ Y)
    (hgap : Small (Y \ I)) : SameClass T Y := by
  apply sameClass_trans hI
  apply small_subset hgap
  intro x hx
  rcases hx with hx|hx
  · exact hx
  · exact (hx.2 (hIY hx.1)).elim

lemma small_sdiff_of_class_subset {T S X Y : Set E0} (hX : SameClass T X)
    (hY : SameClass S Y) (hXY : X ⊆ Y) : Small (T \ S) := by
  apply small_subset (small_union hX hY)
  intro x hx
  have hxy := @hXY x
  simp only [Set.mem_sdiff,Set.mem_union,Set.mem_symmDiff] at hx ⊢
  tauto

def Outcome (I Y B : Set E0) : Prop := B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B
lemma outcome_compl {I Y B : Set E0} (h : Outcome I Y B) : Outcome Yᶜ Iᶜ Bᶜ := by
  rcases h with h | ⟨h1,h2⟩ | h
  · exact Or.inr (Or.inr (compl_subset_compl.mpr h))
  · exact Or.inr (Or.inl ⟨compl_subset_compl.mpr h2,compl_subset_compl.mpr h1⟩)
  · exact Or.inl (compl_subset_compl.mpr h)

def Meets (F : Set (Set E0)) (I Y : Set E0) : Prop := ∃ B ∈ F, Outcome I Y B
lemma meets_mono {F G : Set (Set E0)} (hFG : F ⊆ G) {I Y : Set E0} (h : Meets F I Y) : Meets G I Y := by
  obtain ⟨B,hB,hout⟩ := h
  exact ⟨B,hFG hB,hout⟩

lemma localRule_meets_of_small_left (s : Bool) {T I Y : Set E0}
    (hT : ¬ Small T) (hTc : ¬ Small Tᶜ) (hIY : I ⊆ Y) (hTI : Small (T \ I)) :
    Meets (LocalRule s T) I Y := by
  by_cases hI : SameClass T I
  · by_cases hg : Small (Y \ I)
    · exact localRule_interval s hT hTc hIY hI (sameClass_of_small_gap hI hIY hg)
    · obtain ⟨B,hB,hBI | hIBY⟩ := localRule_lower_endpoint s hT hTc hIY hI hg
      · exact ⟨B,hB,Or.inl hBI⟩
      · exact ⟨B,hB,Or.inr (Or.inl hIBY)⟩
  · have hj : SameClass T (T ∩ I) := by
      apply small_subset hTI
      intro x hx
      simp only [Set.mem_symmDiff,Set.mem_inter_iff,Set.mem_sdiff] at hx ⊢
      tauto
    have hg : ¬ Small (I \ (T ∩ I)) := by
      intro h
      apply hI
      apply small_subset (small_union h hTI)
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl ⟨hx.1,fun hi ↦ hx.2 hi.1⟩
      · exact Or.inr hx
    obtain ⟨B,hB,hBJ | ⟨_,hBI⟩⟩ := localRule_lower_endpoint s hT hTc inter_subset_right hj hg
    · exact ⟨B,hB,Or.inl (hBJ.trans inter_subset_right)⟩
    · exact ⟨B,hB,Or.inl hBI⟩

lemma localRule_meets_of_small_right (s : Bool) {T I Y : Set E0}
    (hT : ¬ Small T) (hTc : ¬ Small Tᶜ) (hIY : I ⊆ Y) (hYT : Small (Y \ T)) :
    Meets (LocalRule s T) I Y := by
  have he : Tᶜ \ Yᶜ = Y \ T := by ext x; simp only [Set.mem_sdiff,Set.mem_compl_iff]; tauto
  obtain ⟨B,hB,hout⟩ := localRule_meets_of_small_left (!s) hTc (by simpa using hT)
    (compl_subset_compl.mpr hIY) (by rwa [he])
  refine ⟨Bᶜ,?_,?_⟩
  · simpa only [Bool.not_not,compl_compl] using localRule_compl hB
  · simpa only [compl_compl] using outcome_compl hout

abbrev Prototype := Set E0 × Bool

def flipPrototype (p : Prototype) : Prototype := (p.1ᶜ,!p.2)
@[simp] lemma flipPrototype_flip (p : Prototype) : flipPrototype (flipPrototype p) = p := by
  simp [flipPrototype]

def PrototypeBases (P : Set Prototype) : Set (Set E0) := {B | ∃ p ∈ P, B ∈ LocalRule p.2 p.1}
lemma prototypeBases_mono {P Q : Set Prototype} (hPQ : P ⊆ Q) : PrototypeBases P ⊆ PrototypeBases Q := by
  rintro B ⟨p,hp,hB⟩
  exact ⟨p,hPQ hp,hB⟩
lemma localRule_subset_bases {P : Set Prototype} {p : Prototype} (hp : p ∈ P) :
    LocalRule p.2 p.1 ⊆ PrototypeBases P := fun _ h ↦ ⟨p,hp,h⟩

namespace RankModel
variable (R : RankModel D)

structure GoodPrototypes (P : Set Prototype) : Prop where
  admissible : ∀ p ∈ P, R.Admissible p.1
  flip_closed : ∀ p ∈ P, flipPrototype p ∈ P
  separated : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ¬ Small (p.1 \ q.1)

lemma good_empty : R.GoodPrototypes ∅ := ⟨by simp,by simp,by simp⟩

lemma bases_compl_closed {P : Set Prototype} (hP : R.GoodPrototypes P) :
    ∀ ⦃B⦄, B ∈ PrototypeBases P → Bᶜ ∈ PrototypeBases P := by
  rintro B ⟨p,hp,hB⟩
  exact ⟨flipPrototype p,hP.flip_closed p hp,localRule_compl hB⟩

lemma bases_antichain {P : Set Prototype} (hP : R.GoodPrototypes P) :
    ∀ ⦃B C⦄, B ∈ PrototypeBases P → C ∈ PrototypeBases P → B ⊆ C → B = C := by
  rintro B C ⟨p,hp,hB⟩ ⟨q,hq,hC⟩ hBC
  by_cases he : p = q
  · subst q
    exact localRule_antichain p.2 p.1 hB hC hBC
  · exact (hP.separated p hp q hq he
      (small_sdiff_of_class_subset (localRule_class hB) (localRule_class hC) hBC)).elim

lemma bases_swap {P : Set Prototype} :
    ∀ ⦃B⦄, B ∈ PrototypeBases P → ∀ e ∈ B, ∀ f ∉ B, insert f (B \ {e}) ∈ PrototypeBases P := by
  rintro B ⟨p,hp,hB⟩ e he f hf
  exact ⟨p,hp,localRule_swap hB e he f hf⟩

variable (hK : R.ideal = KIdeal)
include hK
lemma bases_admissible {P : Set Prototype} (hP : R.GoodPrototypes P) :
    ∀ ⦃B⦄, B ∈ PrototypeBases P → R.Admissible B := by
  rintro B ⟨p,hp,hB⟩
  exact R.admissible_sameClass hK (hP.admissible p hp) (localRule_class hB)

lemma unmet_separation {P : Set Prototype} (hP : R.GoodPrototypes P)
    {I Y : Set E0} (hIY : I ⊆ Y) (hnot : ¬ Meets (PrototypeBases P) I Y) :
    ∀ p ∈ P, ¬ Small (p.1 \ I) ∧ ¬ Small (Y \ p.1) := by
  intro p hp
  have ht := R.admissible_positive hK (hP.admissible p hp)
  have htc := R.admissible_positive hK (R.admissible_compl (hP.admissible p hp))
  exact ⟨fun hs ↦ hnot (meets_mono (localRule_subset_bases hp)
    (localRule_meets_of_small_left p.2 ht htc hIY hs)),
    fun hs ↦ hnot (meets_mono (localRule_subset_bases hp)
    (localRule_meets_of_small_right p.2 ht htc hIY hs))⟩

end RankModel
end InfiniteMatroidCounterexample
end

end OAI
