import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectionCenterTools

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

lemma center_budget (q N Q H s a t u e τ : ℝ)
    (hq : 2≤q) (hN : 0<N) (hH : 0≤H) (hQ : q*N≤Q) (hHQ : q*H≤Q)
    (hs : 0<s) (ha : 0<a) (hu : 0<u) (hτ : 0<τ)
    (hst : s≤N/100000) (htt : 1000000*q≤t) (he : e≤τ*s*t/q) :
    N*t/(t/(100*q))^2+H*u/(100*u/q)+s^2*(q+1)/(s/100)+
      a^2*(q+1)/(100*a^2/N)+H*e/(100*τ*s*t/q^2)<Q := by
  have hq0 : 0<q := by linarith
  have ht : 0<t := lt_of_lt_of_le (by positivity) htt
  have hQ0 : 0<Q := (mul_pos hq0 hN).trans_le hQ
  have hv : N*t/(t/(100*q))^2≤Q/100 := by
    calc
      _ = 10000*N*q^2/t := by field_simp; ring
      _ ≤ 10000*N*q^2/(1000000*q) := div_le_div_of_nonneg_left (by positivity) (by positivity) htt
      _ = q*N/100 := by field_simp; ring
      _ ≤ _ := by linarith only [hQ]
  have hd : H*u/(100*u/q)≤Q/100 := by
    calc
      _ = q*H/100 := by field_simp
      _ ≤ _ := by linarith only [hHQ]
  have hcS : s^2*(q+1)/(s/100)≤Q/500 := by
    calc
      _ = 100*s*(q+1) := by field_simp
      _ ≤ 200*s*q := by nlinarith
      _ ≤ q*N/500 := by nlinarith [mul_le_mul_of_nonneg_right hst hq0.le]
      _ ≤ _ := by linarith only [hQ]
  have hcA : a^2*(q+1)/(100*a^2/N)≤Q/50 := by
    calc
      _ = N*(q+1)/100 := by field_simp
      _ ≤ q*N/50 := by nlinarith
      _ ≤ _ := by linarith only [hQ]
  have hi : H*e/(100*τ*s*t/q^2)≤Q/100 := by
    calc
      _ ≤ H*(τ*s*t/q)/(100*τ*s*t/q^2) := by gcongr
      _ = q*H/100 := by field_simp
      _ ≤ _ := by linarith only [hHQ]
  linarith only [hv,hd,hcS,hcA,hi,hQ0]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance finiteDualV : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedProjectionCenterBounds_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedProjectionCenterBounds_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

theorem good_center {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S A : Finset (Projectivization K V))
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hA : A.Nonempty) (hU : U.Nonempty) (τ : ℝ) (hτ : 0<τ)
    (hsmall : (S.card:ℝ)≤(Nat.card K:ℝ)^(n+1)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ)≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤τ*S.card*T.card/Nat.card K) :
    ∃ z : Projectivization K V,
      |((cut T z).card:ℝ)-(∑ i∈range (n+2),(Nat.card K:ℝ)^i)/
        (∑ i∈range (n+3),(Nat.card K:ℝ)^i)*T.card| < (T.card:ℝ)/(100*Nat.card K) ∧
      ((cut U z).card:ℝ)<100*U.card/Nat.card K ∧
      (orderedCollisions S z:ℝ)<(S.card:ℝ)/100 ∧
      (orderedCollisions A z:ℝ)<100*(A.card:ℝ)^2/(Nat.card K:ℝ)^(n+1) ∧
      (incidenceCount S (cut T z):ℝ)<100*τ*S.card*T.card/(Nat.card K:ℝ)^2 := by
  let q : ℝ := Nat.card K
  let N := q^(n+1)
  let H := ∑ i∈range (n+2),q^i
  let Q := ∑ i∈range (n+3),q^i
  have hq : 2≤q := by
    dsimp only [q]
    exact_mod_cast (show 2≤Nat.card K from Finite.one_lt_card)
  have hq0 : 0<q := by linarith
  have hN : 0<N := by dsimp [N]; positivity
  have hH : 0≤H := by dsimp [H]; positivity
  have hHQ : q*H≤Q := by have hh := geom_sum_succ (x:=q) (n:=n+2); dsimp [H,Q]; linarith
  have hQ : q*N≤Q := by
    have hh : q^(n+2)≤Q := single_le_sum (fun i hi => by positivity) (by simp)
    simpa only [N,show n+2=(n+1)+1 by omega,pow_succ,mul_comm] using hh
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have ha : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hu : (0:ℝ)<U.card := by exact_mod_cast card_pos.mpr hU
  have ht : (0:ℝ)<T.card := lt_of_lt_of_le (by positivity) hlarge
  apply exists_center hdim S A T U ((T.card:ℝ)/(100*q)) (100*U.card/q)
    (S.card/100) (100*(A.card:ℝ)^2/N) (100*τ*S.card*T.card/q^2)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  have hnS : (((S.card*(S.card-1)*(Nat.card K+1):ℕ):ℝ))≤(S.card:ℝ)^2*(q+1) := by
    push_cast
    have hh : ((S.card-1:ℕ):ℝ)≤S.card := by exact_mod_cast Nat.sub_le S.card 1
    dsimp only [q]
    calc
      _ ≤ (S.card:ℝ)*(S.card:ℝ)*(Nat.card K+1) := by gcongr
      _ = _ := by ring
  have hnA : (((A.card*(A.card-1)*(Nat.card K+1):ℕ):ℝ))≤(A.card:ℝ)^2*(q+1) := by
    push_cast
    have hh : ((A.card-1:ℕ):ℝ)≤A.card := by exact_mod_cast Nat.sub_le A.card 1
    dsimp only [q]
    calc
      _ ≤ (A.card:ℝ)*(A.card:ℝ)*(Nat.card K+1) := by gcongr
      _ = _ := by ring
  have hb := center_budget q N Q H S.card A.card T.card U.card (incidenceCount S T) τ
    hq hN hH hQ hHQ hs ha hu hτ hsmall hlarge hsparse
  apply lt_of_le_of_lt _ hb
  dsimp only [N,H,Q,q]
  gcongr

end
end SharpLogRamsey.Projection

end

end OAI
