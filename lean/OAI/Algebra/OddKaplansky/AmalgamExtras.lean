import OAI.Algebra.OddKaplansky.PrescribedInverse

namespace OAI

section
namespace OddKaplansky.StarAmalgam
noncomputable section
open Monoid
open scoped Classical
variable {I G : Type} [Group G] {D S : I → Type}
variable [∀ i, Group (D i)] [∀ i, Group (S i)]
variable (f : ∀ i, S i →* G) (g : ∀ i, S i →* D i)
@[elab_as_elim]
theorem induction_on {P : Amalgam f g → Prop} (x : Amalgam f g)
    (hb : ∀ h, P (ofBase f g h)) (hd : ∀ i h, P (ofFactor f g i h))
    (hmul : ∀ x y, P x → P y → P (x*y)) : P x := by
  change ∀ left right : (con f g).Quotient, P left → P right → P (left * right) at hmul
  change ∀ element : G, P ((con f g).mk' (Coprod.inl element)) at hb
  obtain ⟨w,rfl⟩ := (Con.mk'_surjective (c := con f g)) x
  induction w using Coprod.induction_on with
  | inl h => exact hb h
  | inr w =>
    induction w using CoprodI.induction_on with
    | one => simpa only [map_one] using hb 1
    | of i h => exact hd i h
    | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
lemma base_central (z : G) (hz : ∀ h, Commute z h)
    (a : ∀ i, S i) (ha : ∀ i, f i (a i)=z) (hc : ∀ i h, Commute (g i (a i)) h) :
    ∀ x : Amalgam f g, Commute (ofBase f g z) x := by
  intro x
  induction x using induction_on f g with
  | hb h => exact (hz h).map (ofBase f g)
  | hd i h =>
    rw [← ha i,identify]
    exact (hc i h).map (ofFactor f g i)
  | hmul x y hx hy => exact hx.mul_right hy
instance [Finite I] [∀ i, Finite (D i)] [Group.FG G] : Group.FG (Amalgam f g) := by
  obtain ⟨B,hB,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let C : Set (Amalgam f g) := ofBase f g '' B ∪ Set.range (fun z : (i : I) × D i => ofFactor f g z.1 z.2)
  apply Group.fg_iff.mpr
  refine ⟨C,?_,(hfin.image _).union (Set.finite_range _)⟩
  apply top_unique
  intro x hxTop
  clear hxTop
  induction x using induction_on f g with
  | hb h =>
    have hh : h ∈ Subgroup.closure B := hB ▸ Subgroup.mem_top h
    induction hh using Subgroup.closure_induction with
    | mem h hh => exact Subgroup.subset_closure (Or.inl ⟨h,hh,rfl⟩)
    | one => simp
    | mul h k _ _ hh hk => simpa only [map_mul] using (Subgroup.closure C).mul_mem hh hk
    | inv h _ hh => simpa only [map_inv] using (Subgroup.closure C).inv_mem hh
  | hd i h => exact Subgroup.subset_closure (Or.inr ⟨⟨i,h⟩,rfl⟩)
  | hmul x y hx hy => exact (Subgroup.closure C).mul_mem hx hy
end
end OddKaplansky.StarAmalgam

end

end OAI
