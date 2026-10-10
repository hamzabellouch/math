import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProduct

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorProduct
open Construction ResidueHaar HistoryCRTIntegration HistorySignedSpectatorDiagramAverage
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def rootUnitExtension {D : ℕ} (F : UnitPair D → ℂ) (z : MixedPair D) : ℂ :=
  if h : IsUnit z.1 then F (h.unit,z.2) else 0

@[simp] theorem rootUnitExtension_unit {D : ℕ} (F : UnitPair D → ℂ) (z : UnitPair D) :
    rootUnitExtension F ((z.1:ZMod D),z.2) = F z := by
  rw [rootUnitExtension, dite_eq_left z.1.isUnit]
  congr 1
  apply Prod.ext
  · apply Units.ext
    exact z.1.isUnit.unit_spec
  · rfl

theorem rootUnitExtension_nonunit {D : ℕ} (F : UnitPair D → ℂ) (z : MixedPair D)
    (hz : ¬IsUnit z.1) : rootUnitExtension F z = 0 := dite_eq_right hz

theorem rootUnitExtension_eq_of_isUnit {D : ℕ} (F : UnitPair D → ℂ) (z : MixedPair D)
    (hz : IsUnit z.1) : rootUnitExtension F z = F (hz.unit,z.2) := dite_eq_left hz

theorem sum_rootUnitExtension {D : ℕ} [NeZero D] (F : UnitPair D → ℂ) :
    (∑ z : MixedPair D, rootUnitExtension F z) = ∑ z : UnitPair D, F z := by
  let e : UnitPair D → MixedPair D := fun z => ((z.1:ZMod D),z.2)
  have he : Function.Injective e := by
    intro a b h
    apply Prod.ext
    · apply Units.ext
      exact congrArg (fun z : MixedPair D => z.1) h
    · exact congrArg (fun z : MixedPair D => z.2) h
  symm
  apply Fintype.sum_of_injective e he
  · intro z hz
    apply rootUnitExtension_nonunit
    intro hu
    apply hz
    exact ⟨(hu.unit,z.2),Prod.ext hu.unit_spec rfl⟩
  · intro z
    exact (rootUnitExtension_unit F z).symm

theorem average_rootUnitExtension {D : ℕ} [NeZero D] (F : UnitPair D → ℂ) :
    average (rootUnitExtension F) = ((Nat.totient D:ℂ)/(D:ℂ))*average F := by
  have hD : (D:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have hφ : (Nat.totient D:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos D)).ne'
  simp only [average, sum_rootUnitExtension, Fintype.card_prod, ZMod.card,
    ZMod.card_units_eq_totient, Nat.cast_mul]
  field_simp

theorem norm_totient_density_le {D : ℕ} [NeZero D] :
    ‖((Nat.totient D:ℂ)/(D:ℂ))‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact (div_le_one (by exact_mod_cast NeZero.pos D : (0:ℝ)<D)).mpr
    (by exact_mod_cast Nat.totient_le D)

theorem norm_average_rootUnitExtension_le {D : ℕ} [NeZero D] (F : UnitPair D → ℂ) :
    ‖average (rootUnitExtension F)‖ ≤ ‖average F‖ := by
  rw [average_rootUnitExtension, norm_mul]
  exact (mul_le_mul_of_nonneg_right norm_totient_density_le (norm_nonneg _)).trans_eq (one_mul _)

def mixedTest {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ)
    (roots : MixedPair outside.prod) (samples : Fin (2^l)×Fin m → (ZMod outside.prod)ˣ) : ℂ :=
  rootUnitExtension (fun z => unitTest h k hs ks hp hV σ g z samples) roots

@[simp] theorem mixedTest_unit {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ)
    (roots : UnitPair outside.prod) (samples : Fin (2^l)×Fin m → (ZMod outside.prod)ˣ) :
    mixedTest h k hs ks hp hV σ g ((roots.1:ZMod outside.prod),roots.2) samples =
      unitTest h k hs ks hp hV σ g roots samples := rootUnitExtension_unit _ _

theorem mixedTest_nonunit {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ)
    (roots : MixedPair outside.prod) (samples : Fin (2^l)×Fin m → (ZMod outside.prod)ˣ)
    (hr : ¬IsUnit roots.1) : mixedTest h k hs ks hp hV σ g roots samples = 0 :=
  rootUnitExtension_nonunit _ _ hr

theorem mixedTest_eq_of_isUnit {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ)
    (roots : MixedPair outside.prod) (samples : Fin (2^l)×Fin m → (ZMod outside.prod)ˣ)
    (hr : IsUnit roots.1) : mixedTest h k hs ks hp hV σ g roots samples =
      unitTest h k hs ks hp hV σ g (hr.unit,roots.2) samples := rootUnitExtension_eq_of_isUnit _ _ hr

end Ostmann.Arithmetic.HistoryBulkSpectatorProduct

end

end OAI
