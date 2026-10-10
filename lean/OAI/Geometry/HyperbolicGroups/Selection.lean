import Mathlib
import OAI.Geometry.HyperbolicGroups.Exceptional

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction

universe a b c
/-- A genuine action on an arbitrary chosen space in the specified universe. -/
structure CATActionWitness (G : Type a) [Group G] where
  Space : Type b
  metric : MetricSpace Space
  nonempty : Nonempty Space
  proper : ProperSpace Space
  complete : CompleteSpace Space
  cat : CATZero Space
  action : GeometricAction G Space

attribute [instance] CATActionWitness.metric CATActionWitness.nonempty
  CATActionWitness.proper CATActionWitness.complete

lemma catActionWitness_iff {G : Type a} [Group G] :
    Nonempty (CATActionWitness.{a,b} G) ↔ ¬ NoGeometricCATZeroAction.{b} G := by
  classical
  constructor
  · rintro ⟨W⟩ h
    exact (h W.Space W.metric W.nonempty W.proper W.complete W.cat).false W.action
  · intro h
    simp only [NoGeometricCATZeroAction, not_forall] at h
    obtain ⟨X, m, hn, hp, hc, hcat, ha⟩ := h
    exact ⟨⟨X, m, hn, hp, hc, hcat, Classical.choice (not_isEmpty_iff.mp ha)⟩⟩

namespace SamplingSequence
variable {F : Type*} [DecidableEq F] {Adm : Finset F → Prop}
  {L Ω : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n}

theorem reindex (S : SamplingSequence F Adm L Ω label) (f : ℕ → ℕ)
    (hf : Tendsto f atTop atTop) :
    @SamplingSequence F _ Adm (L ∘ f) (Ω ∘ f)
      (fun n => inferInstanceAs (Fintype (L (f n))))
      (fun n => inferInstanceAs (Nonempty (L (f n))))
      (fun n => inferInstanceAs (DecidableEq (L (f n))))
      (fun n => inferInstanceAs (Fintype (Ω (f n))))
      (fun n => inferInstanceAs (Nonempty (Ω (f n))))
      (fun n => label (f n)) := by
  let : ∀ n, Fintype ((L ∘ f) n) := fun n => inferInstanceAs (Fintype (L (f n)))
  let : ∀ n, Nonempty ((L ∘ f) n) := fun n => inferInstanceAs (Nonempty (L (f n)))
  let : ∀ n, DecidableEq ((L ∘ f) n) := fun n => inferInstanceAs (DecidableEq (L (f n)))
  let : ∀ n, Fintype ((Ω ∘ f) n) := fun n => inferInstanceAs (Fintype (Ω (f n)))
  let : ∀ n, Nonempty ((Ω ∘ f) n) := fun n => inferInstanceAs (Nonempty (Ω (f n)))
  refine ⟨fun e => (S.singleton e).comp hf, ?_⟩
  intro I e he ha k
  obtain ⟨η, hη, hh⟩ := S.star I e he ha k
  exact ⟨η ∘ f, hη.comp hf, hf.eventually hh⟩
end SamplingSequence

namespace MasterGraph
open IncidenceTemplate
variable {L Ω : ℕ → Type a} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → Field → L n}
  {G : ℕ → Type c} [∀ n, Group (G n)] [∀ n, Infinite (G n)]
  (letter : ∀ n, L n → G n) (inv : ∀ n, L n ≃ L n)
  (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)
  (hgen : ∀ n, Subgroup.closure (Set.range (letter n)) = ⊤)
  (g : ∀ n m, Potential (label n m) (letter n))
  (S : SamplingSequence Field Admissible L Ω label)
  (Row : ∀ n, L n → Type a) [∀ n i, Fintype (Row n i)]
  (κ : ∀ n i, FiniteLaw (Row n i)) (row : ∀ n i, Row n i → Fin 5 → L n)
  (hrow : ∀ n i r, (List.ofFn (letter n ∘ row n i r)).prod = (letter n i)⁻¹)
  (hmarg : ∀ n i j l, ((κ n i).map (fun r => row n i r j)).mass l ≤ 2 / Fintype.card (L n))

include hinv hgen g S κ hrow hmarg in
/-- The geometric half of selection: any infinite-group sequence with the
literal sampling assertions and six-letter rows has a no-action member. -/
theorem exists_noAction : ∃ n, NoGeometricCATZeroAction.{b} (G n) := by
  classical
  by_contra! h
  have hw (n : ℕ) : Nonempty (CATActionWitness.{c,b} (G n)) := catActionWitness_iff.mpr (h n)
  let W n := Classical.choice (hw n)
  have hn (n : ℕ) := EnergyOrbit.exists_of_geometric (W n).cat (W n).action
    (letter n) (inv n) (hinv n) (hgen n) (Row n) (κ n) (row n) (hrow n) (hmarg n)
  choose r hr O hO using hn
  let A (n : ℕ) := MetricScale.action (W n).action.act (r := r n) (hr := hr n)
  have hact (n : ℕ) (i : L n) : A n (letter n i) = (O n).isom i := (hO n i).symm
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  exact impossible_sequence O A letter hact g (by norm_num) inv hinv S hU

include hinv hgen g S κ hrow hmarg in
/-- Eventually the groups admit no geometric CAT(0) action. -/
theorem eventually_noAction : ∀ᶠ n in atTop, NoGeometricCATZeroAction.{b} (G n) := by
  classical
  by_contra h
  obtain ⟨f, hf, hn⟩ := exists_seq_forall_of_frequently (show ∃ᶠ n in atTop,
    ¬ NoGeometricCATZeroAction.{b} (G n) from by simpa only [Filter.Frequently, not_not] using h)
  let : ∀ n, Fintype ((L ∘ f) n) := fun n => inferInstanceAs (Fintype (L (f n)))
  let : ∀ n, Nonempty ((L ∘ f) n) := fun n => inferInstanceAs (Nonempty (L (f n)))
  let : ∀ n, DecidableEq ((L ∘ f) n) := fun n => inferInstanceAs (DecidableEq (L (f n)))
  let : ∀ n, Fintype ((Ω ∘ f) n) := fun n => inferInstanceAs (Fintype (Ω (f n)))
  let : ∀ n, Nonempty ((Ω ∘ f) n) := fun n => inferInstanceAs (Nonempty (Ω (f n)))
  let : ∀ n, Group ((G ∘ f) n) := fun n => inferInstanceAs (Group (G (f n)))
  let : ∀ n, Infinite ((G ∘ f) n) := fun n => inferInstanceAs (Infinite (G (f n)))
  let R (n : ℕ) := Row (f n)
  let : ∀ n i, Fintype (R n i) := fun n i => inferInstanceAs (Fintype (Row (f n) i))
  obtain ⟨n, hh⟩ := exists_noAction (L := L ∘ f) (Ω := Ω ∘ f) (G := G ∘ f)
    (fun n => letter (f n)) (fun n => inv (f n)) (fun n => hinv (f n))
    (fun n => hgen (f n)) (fun n => g (f n)) (S.reindex f hf) R
    (fun n => κ (f n)) (fun n => row (f n)) (fun n => hrow (f n)) (fun n => hmarg (f n))
  exact hn n hh

end MasterGraph
end HyperbolicObstruction
end
end

section

end
end

end OAI
