import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcDecay

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumBridge.Corridor
abbrev ArcShape (M : ℕ) := ArchWord.CylinderArch M ⊕ BridgeWord.CylinderBridge M
namespace ArcShape
variable {M : ℕ}
def word : ArcShape M → List Bool
  | .inl A => A.val.word
  | .inr A => A.val.word
noncomputable def mass (A : ArcShape M) : ℝ := criticalActivity^A.word.length

theorem word_injective : Function.Injective (word (M:=M)) := by
  intro A B h
  cases A with
  | inl A =>
    cases B with
    | inl B => exact congrArg Sum.inl (Subtype.ext (ArchWord.ext h))
    | inr B =>
      change A.val.word=B.val.word at h
      have ht:=A.val.terminal.symm.trans (by rw [h,B.val.terminal])
      cases ht
  | inr A =>
    cases B with
    | inl B =>
      change A.val.word=B.val.word at h
      have ht:=A.val.terminal.symm.trans (by rw [h,B.val.terminal])
      cases ht
    | inr B => exact congrArg Sum.inr (Subtype.ext (BridgeWord.ext h))

theorem mass_nonneg (A : ArcShape M) : 0≤A.mass := (pow_pos criticalActivity_pos _).le

theorem mass_summable (M : ℕ) (hM : 0<M) : Summable (mass (M:=M)) := by
  apply Summable.sum
  · exact ArchWord.cylinder_arch_mass_summable M
  · exact BridgeWord.cylinder_bridge_mass_summable M hM
end ArcShape

abbrev ArcChoice (M : ℕ) := Unit ⊕ ArcShape M
namespace ArcChoice
variable {M : ℕ}
noncomputable def mass : ArcChoice M → ℝ
  | .inl _ => 1
  | .inr A => A.mass

theorem mass_nonneg (A : ArcChoice M) : 0 ≤ mass A := by
  cases A with
  | inl _ => exact zero_le_one
  | inr A => exact A.mass_nonneg

theorem mass_summable (M : ℕ) (hM : 0<M) : Summable (mass (M:=M)) := by
  apply Summable.sum
  · exact (hasSum_fintype _).summable
  · exact ArcShape.mass_summable M hM
end ArcChoice

 

theorem summable_fin_product {α : Type*} (f : α → ℝ) (hf : Summable f) (hp : ∀a,0≤f a) (n : ℕ) :
    Summable (fun s : Fin n → α => ∏i,f (s i)) := by
  induction n with
  | zero => exact (hasSum_fintype _).summable
  | succ n ih =>
    apply (Fin.consEquiv (fun _ : Fin (n+1) => α)).summable_iff.mp
    have hh:=hf.mul_of_nonneg ih hp (fun s => Finset.prod_nonneg (fun i _ => hp (s i)))
    simpa [Function.comp_def,Fin.prod_univ_succ] using hh

theorem summable_finite_product {α β : Type*} [Fintype β]
    (f : α → ℝ) (hf : Summable f) (hp : ∀a,0≤f a) :
    Summable (fun s : β → α => ∏i,f (s i)) := by
  let e := Equiv.piCongrLeft (fun _ : β => α) (Fintype.equivFin β).symm
  apply e.summable_iff.mp
  have he (s : Fin (Fintype.card β) → α) : (∏i,f (e s i))=∏i,f (s i) := by
    simpa [e,Equiv.piCongrLeft] using (Fintype.equivFin β).prod_comp (fun i => f (s i))
  simpa only [Function.comp_def,he] using summable_fin_product f hf hp (Fintype.card β)

noncomputable def arcChoiceMajorant {M : ℕ} [NeZero M] (s : Bool × ZMod M → ArcChoice M) : ℝ := ∏i,ArcChoice.mass (s i)

theorem arcChoice_summable (M : ℕ) [NeZero M] : Summable (arcChoiceMajorant (M:=M)) := by
  have hM : 0<M := Nat.pos_of_ne_zero (NeZero.ne M)
  exact summable_finite_product _ (ArcChoice.mass_summable M hM) ArcChoice.mass_nonneg
end PolynomialVacuumCylinder

end OAI
