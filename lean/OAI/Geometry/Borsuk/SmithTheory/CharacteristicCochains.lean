import Mathlib
import OAI.Geometry.Borsuk.SphereGeometry.OddSphereMap

namespace OAI

namespace BorsukNine.SmithTheory

section CharacteristicCochains
variable {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
variable (d N : P →ₗ[ZMod 2] P)

def SmithCocycle : Submodule (ZMod 2) (P →ₗ[ZMod 2] ZMod 2) where
  carrier := {φ | φ.comp N = 0 ∧ φ.comp d = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ; simp [LinearMap.add_comp, hφ.1, hφ.2, hψ.1, hψ.2]
  smul_mem' := by intro a φ hφ; simp [LinearMap.smul_comp, hφ.1, hφ.2]

noncomputable def smithLift (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : P →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)

lemma smithLift_comp_norm (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : (smithLift d N hexact φ).comp N = φ.val :=
  Classical.choose_spec (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)

noncomputable def smithNext (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    SmithCocycle d N :=
  ⟨(smithLift d N hexact φ).comp d, by
    constructor
    · rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc,
        smithLift_comp_norm, φ.property.2]
    · rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]⟩

noncomputable def smithCochain (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    ℕ → SmithCocycle d N
  | 0 => φ
  | n+1 => smithNext d N hd hcomm hexact (smithCochain hd hcomm hexact φ n)

noncomputable def smithDegree (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) :
    P →ₗ[ZMod 2] ZMod 2 :=
  smithLift d N hexact (smithCochain d N hd hcomm hexact φ n)

lemma smithDegree_norm (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    smithDegree d N hd hcomm hexact φ n (N c) =
      (smithCochain d N hd hcomm hexact φ n).val c :=
  LinearMap.congr_fun (smithLift_comp_norm d N hexact _) c

lemma smithCochain_succ (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    (smithCochain d N hd hcomm hexact φ (n+1)).val c =
      smithDegree d N hd hcomm hexact φ n (d c) := rfl

variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]

lemma smithDegree_natural
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N)
    (d' N' : Q →ₗ[ZMod 2] Q) (hd' : d'.comp d' = 0) (hcomm' : d'.comp N' = N'.comp d')
    (hexact' : LinearMap.ker N' ≤ LinearMap.range N') (φ' : SmithCocycle d' N')
    (T : P →ₗ[ZMod 2] Q) (hTd : d'.comp T = T.comp d) (hTN : N'.comp T = T.comp N)
    (hTφ : φ'.val.comp T = φ.val) (n : ℕ) (c : P) (hNc : N c = 0) (hdc : d c = 0) :
    smithDegree d' N' hd' hcomm' hexact' φ' n (T c) =
      smithDegree d N hd hcomm hexact φ n c := by
  induction n generalizing c with
  | zero =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm]
    exact LinearMap.congr_fun hTφ x
  | succ n ih =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm, smithCochain_succ, smithCochain_succ,
      ← LinearMap.comp_apply d' T, hTd, LinearMap.comp_apply]
    apply ih
    · rw [← LinearMap.comp_apply N d, ← hcomm, LinearMap.comp_apply, hx, hdc]
    · exact LinearMap.congr_fun hd x

end CharacteristicCochains
end BorsukNine.SmithTheory

end OAI
