import Mathlib.Data.Set.Function

namespace OAI

/-! Retain a prescribed real subfamily when choosing local branches. -/

open Function Classical
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def subfamilyOverride {A L Y : Type*} (ι : A → L) (r : A → Y) (u : L → Y) (l : L) : Y :=
  if h : ∃ j, ι j = l then r (Classical.choose h) else u l

theorem subfamilyOverride_at {A L Y : Type*} (ι : A → L) (hι : Injective ι)
    (r : A → Y) (u : L → Y) (j : A) : subfamilyOverride ι r u (ι j) = r j := by
  have h : ∃ k, ι k = ι j := ⟨j, rfl⟩
  have he : Classical.choose h = j := hι (Classical.choose_spec h)
  simp only [subfamilyOverride, dite_eq_left h, he]

theorem subfamilyOverride_of_notMem {A L Y : Type*} (ι : A → L)
    (r : A → Y) (u : L → Y) {l : L} (hl : l ∉ Set.range ι) :
    subfamilyOverride ι r u l = u l := by
  simp only [subfamilyOverride, dite_eq_right (show ¬∃ j, ι j = l from hl)]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
