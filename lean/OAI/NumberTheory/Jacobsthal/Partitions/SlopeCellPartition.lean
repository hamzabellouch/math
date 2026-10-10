import OAI.NumberTheory.Jacobsthal.Sieve.AugmentedCRTCell

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def sampledSlopes {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) : Finset ℤ :=
  (Finset.Ico (0 : ℤ) (p : ℤ)).filter
    (fun s => ∀ i,(c i : ZMod (u i))*(s : ZMod (u i))+b i ∈ E (s : ZMod M0) i)

theorem sampledSlopes_partition {ι : Type*} [Fintype ι] (p M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) :
    sampledSlopes p M0 u c b E = Finset.univ.biUnion (fun v : ZMod M0 => slopeCell p M0 u v c b (E v)) := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsp,hE⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_biUnion.mpr ⟨(s : ZMod M0),Finset.mem_univ _,Finset.mem_filter.mpr ⟨hsp,rfl,hE⟩⟩
  · intro hs
    obtain ⟨v,hv,hcell⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨hsp,hsv,hE⟩ := Finset.mem_filter.mp hcell
    apply Finset.mem_filter.mpr
    refine ⟨hsp,?_⟩
    rwa [hsv]

theorem slopeCells_disjoint {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) {v w : ZMod M0} (hne : v ≠ w) :
    Disjoint (slopeCell p M0 u v c b (E v)) (slopeCell p M0 u w c b (E w)) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact hne ((Finset.mem_filter.mp hs).2.1.symm.trans (Finset.mem_filter.mp ht).2.1)

theorem sampledSlopes_card {ι : Type*} [Fintype ι] (p M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) :
    (sampledSlopes p M0 u c b E).card = ∑ v : ZMod M0,(slopeCell p M0 u v c b (E v)).card := by
  rw [sampledSlopes_partition,Finset.card_biUnion]
  intro v hv w hw hne
  exact slopeCells_disjoint p M0 u c b E hne

end ErdosInverseCRT

end

end Erdos970

end OAI
