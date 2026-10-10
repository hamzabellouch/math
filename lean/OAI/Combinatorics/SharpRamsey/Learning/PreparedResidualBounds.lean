import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.PreparedRadialBounds

namespace OAI

section
namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]
local instance flat_JoinedPreparedResidualBounds_1 : Finite (Submodule (ZMod q) (Fin 4→ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4→ZMod q) => (W : Set (Fin 4→ZMod q)))
    SetLike.coe_injective
local instance flat_JoinedPreparedResidualBounds_2 : Fintype (Submodule (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _
local instance flat_JoinedPreparedResidualBounds_3 : Fintype (Projectivization (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

theorem residual_radial_pairs (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (c a : ℝ) (hc : 0<c) (ha : 0≤a)
    (Kp : ℕ) (hM2 : 2≤⌈a/c⌉₊) (hMN : ⌈a/c⌉₊≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<⌈a/c⌉₊)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊))<1/2)
    (hKM : 8*Kp≤⌈a/c⌉₊^2) :
    (∑ x,((richRadials (X x) x c a).card:ℝ))*a^2≤
      8718*((q:ℝ)+1)*(c*S.card)*a := by
  let M := ⌈a/c⌉₊
  let P := ((univ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q) ×
        ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card
  have hp : P*M≤8718*(q+1)*S.card :=
    residual_pairs hq S hS X hX M Kp hM2 hMN hcap hsmall hchar hprob hKM
  have hp' : (P:ℝ)*(M:ℝ)≤8718*((q:ℝ)+1)*S.card := by exact_mod_cast hp
  have hsum : (∑ x,((richRadials (X x) x c a).card:ℝ))≤P := by
    exact_mod_cast sum_richRadials_le_pairs X c a M
      (fun x W hw => rich_threshold (X x) x W a c hc hw)
  have haM : a≤c*M := by
    have hh := Nat.le_ceil (a/c)
    exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  have hh1 := mul_le_mul_of_nonneg_right hsum ha
  have hh2 := mul_le_mul_of_nonneg_left haM (Nat.cast_nonneg P)
  have hh3 := mul_le_mul_of_nonneg_left hp' hc.le
  have hh : (∑ x,((richRadials (X x) x c a).card:ℝ))*a≤
      8718*((q:ℝ)+1)*(c*S.card) := by nlinarith
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right hh ha

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
