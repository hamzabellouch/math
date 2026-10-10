import OAI.Algebra.Finitistic.Rectification.TotalExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {S : Type u} [Ring S]
variable {X Y Z : CochainComplex (ModuleCat.{u} S) ℤ}

/-- A specified degreewise splitting proves exactness for its original maps. -/
theorem component_shortExact (i : X ⟶ Y) (q : Y ⟶ Z)
    (r : Y ⟶ X) (s : Z ⟶ Y)
    (hi : i ≫ r = 𝟙 _) (hq : s ≫ q = 𝟙 _)
    (hz : i ≫ q = 0) (hs : r ≫ i + q ≫ s = 𝟙 _) (n : ℤ) :
    Function.Injective (i.f n) ∧ Function.Exact (i.f n) (q.f n) ∧
      Function.Surjective (q.f n) := by
  have hi' (x : X.X n) : r.f n (i.f n x) = x :=
    congrArg (fun a : X ⟶ X => a.f n x) hi
  have hq' (z : Z.X n) : q.f n (s.f n z) = z :=
    congrArg (fun a : Z ⟶ Z => a.f n z) hq
  have hz' (x : X.X n) : q.f n (i.f n x) = 0 :=
    congrArg (fun a : X ⟶ Z => a.f n x) hz
  have hs' (y : Y.X n) : i.f n (r.f n y) + s.f n (q.f n y) = y :=
    congrArg (fun a : Y ⟶ Y => a.f n y) hs
  refine ⟨?_, ?_, ?_⟩
  · intro x y he
    simpa only [hi'] using congrArg (r.f n) he
  · intro y
    constructor
    · intro hy
      exact ⟨r.f n y, by simpa [hy] using hs' y⟩
    · rintro ⟨x, rfl⟩
      exact hz' x
  · intro z
    exact ⟨s.f n z, hq' z⟩

variable (X Y : CochainComplex (ModuleCat.{u} S) ℤ)
theorem inr_fst_shortExact (n : ℤ) :
    Function.Injective ((biprod.inr : Y ⟶ X ⊞ Y).f n) ∧
    Function.Exact ((biprod.inr : Y ⟶ X ⊞ Y).f n)
      ((biprod.fst : X ⊞ Y ⟶ X).f n) ∧
    Function.Surjective ((biprod.fst : X ⊞ Y ⟶ X).f n) := by
  apply component_shortExact _ _ biprod.snd biprod.inl (by simp) (by simp) (by simp)
  simp [add_comm]

theorem zero_id_shortExact (Z : CochainComplex (ModuleCat.{u} S) ℤ)
    (hZ : ∀ n, Subsingleton (Z.X n)) (n : ℤ) :
    Function.Injective ((0 : Z ⟶ X).f n) ∧
    Function.Exact ((0 : Z ⟶ X).f n) ((𝟙 X : X ⟶ X).f n) ∧
      Function.Surjective ((𝟙 X : X ⟶ X).f n) := by
  let := hZ n
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun x => ⟨x, rfl⟩⟩
  intro x
  constructor
  · intro hx
    exact ⟨0, hx.symm⟩
  · rintro ⟨z, rfl⟩
    rfl
end ExternalTensor.Section4.SourceFiltration

end

end OAI
