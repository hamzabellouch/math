import OAI.NumberTheory.TotientAsymptotic.ActualBlockCount

namespace OAI

/-! Selecting one actual witness pair for each distinct suffix pair. -/

noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma finite_image_representatives {α β : Type*} [DecidableEq β] (Q : Finset α) (f : α → β) :
    ∃ S : Finset α, S ⊆ Q ∧ Set.InjOn f (↑S : Set α) ∧ S.image f=Q.image f := by
  classical
  let pick : {b // b ∈ Q.image f} → α := fun b => Classical.choose (Finset.mem_image.mp b.2)
  have hp (b : {b // b ∈ Q.image f}) : pick b ∈ Q ∧ f (pick b)=b.val :=
    Classical.choose_spec (Finset.mem_image.mp b.2)
  let S := (Q.image f).attach.image pick
  refine ⟨S,?_,?_,?_⟩
  · intro a ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    exact (hp b).1
  · intro a ha a' ha' he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp ha'
    have hb : b=b' := Subtype.ext ((hp b).2.symm.trans (he.trans (hp b').2))
    rw [hb]
  · ext b
    constructor
    · intro hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
      rw [(hp b).2]
      exact b.2
    · intro hb
      let b' : {b // b ∈ Q.image f} := ⟨b,hb⟩
      exact Finset.mem_image.mpr ⟨pick b',Finset.mem_image.mpr ⟨b',Finset.mem_attach _ _,rfl⟩,(hp b').2⟩

/-- The full exponential saving counts distinct suffix pairs independently
of how many common prefixes or full witnesses represent each suffix. -/
theorem actual_suffix_block_count (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    ((Q.image (fun q => pairSuffix q i)).card : ℝ) ≤
      y/Real.log y*Real.exp (-B y/(8*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨y₀,hy₀,hcount⟩ := actual_block_count hford hmertens
  refine ⟨y₀,hy₀,?_⟩
  filter_upwards [hcount] with H hH
  filter_upwards [hH] with x hx
  intro i hi hL hR t y hy hBy hlo hup Q hQ
  obtain ⟨S,hSQ,hinj,himage⟩ := finite_image_representatives Q (fun q => pairSuffix q i)
  have he := hx i hi hL hR t y hy hBy hlo hup S (fun q hq => hQ q (hSQ hq)) hinj
  rw [← himage,Finset.card_image_of_injOn hinj]
  exact he

end TotientAsymptotic

end

end OAI
