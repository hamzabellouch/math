import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.QuotientSupports

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

lemma cut_mean_bounds (q : ℝ) (hq : 2≤q) (n : ℕ) :
    1/(2*q) ≤ (∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i) ∧
    (∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i) ≤ 1/q := by
  let H := ∑ i∈range (n+2),q^i
  let Q := ∑ i∈range (n+3),q^i
  have hH : 1≤H := by
    have hh := single_le_sum (s:=range (n+2)) (f:=fun i => q^i)
      (fun i hi => pow_nonneg (by linarith) i) (by simp : 0∈range (n+2))
    simpa only [pow_zero] using hh
  have he : Q=q*H+1 := geom_sum_succ
  have hq0 : 0<q := by linarith
  have hQ : 0<Q := by rw [he]; positivity
  constructor
  · apply (div_le_div_iff₀ (by positivity) hQ).mpr
    rw [he]
    have hh : 1≤q*H := by nlinarith
    nlinarith
  · apply (div_le_div_iff₀ hQ hq0).mpr
    rw [he]
    nlinarith

lemma actual_cut_bounds (q t x μ : ℝ) (hq : 0<q) (ht : 0≤t)
    (hμ : 1/(2*q)≤μ ∧ μ≤1/q) (hx : |x-μ*t|<t/(100*q)) :
    t/(3*q)≤x ∧ x≤2*t/q := by
  have he := abs_lt.mp hx
  have hlo := mul_le_mul_of_nonneg_right hμ.1 ht
  have hhi := mul_le_mul_of_nonneg_right hμ.2 ht
  constructor
  · have hh : t/(3*q)≤t/(2*q)-t/(100*q) := by
      field_simp
      nlinarith
    have hmul : 1/(2*q)*t=t/(2*q) := by ring
    rw [hmul] at hlo
    linarith
  · have hmul : 1/q*t=t/q := by ring
    rw [hmul] at hhi
    have hh : t/q+t/(100*q)≤2*t/q := by
      field_simp
      nlinarith
    linarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedQuotientBounds_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedQuotientBounds_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedQuotientBounds_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

theorem quotient_data {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S A : Finset (Projectivization K V))
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hTU : T⊆U) (τ : ℝ) (hτ : 0<τ)
    (hS : 100≤S.card)
    (hsmall : (S.card:ℝ)≤(Nat.card K:ℝ)^(n+1)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ)≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤τ*S.card*T.card/Nat.card K) :
    ∃ z : Projectivization K V,
      (9/10:ℝ)*S.card≤(projected S z).card ∧
      (T.card:ℝ)/(3*Nat.card K)≤(quotientCut T z).card ∧
      ((quotientCut T z).card:ℝ)≤2*T.card/Nat.card K ∧
      ((quotientCut U z).card:ℝ)≤100*U.card/Nat.card K ∧
      (S.card:ℝ)*T.card/(4*Nat.card K)≤
        (projected S z).card*(quotientCut T z).card ∧
      (incidenceCount (projected S z) (quotientCut T z):ℝ)≤
        400*τ*(projected S z).card*(quotientCut T z).card/Nat.card K ∧
      (orderedCollisions S z:ℝ)<(S.card:ℝ)/100 ∧
      (orderedCollisions A z:ℝ)<100*(A.card:ℝ)^2/(Nat.card K:ℝ)^(n+1) := by
  let q : ℝ := Nat.card K
  have hq : 2≤q := by dsimp [q]; exact_mod_cast (show 2≤Nat.card K from Finite.one_lt_card)
  have hq0 : 0<q := by linarith
  have ht : (0:ℝ)<T.card := lt_of_lt_of_le (by positivity) hlarge
  have hTpos : T.Nonempty := card_pos.mp (by exact_mod_cast ht)
  obtain ⟨z,hcut,hU,hcS,hcA,hi⟩ := good_center hdim S A T U
    (card_pos.mp (by omega)) hA (hTpos.mono hTU) τ hτ hsmall hlarge hsparse
  have hs : (100:ℝ)≤S.card := by exact_mod_cast hS
  have hSn : (9/10:ℝ)*S.card≤(projected S z).card := by
    have hp : (S.card:ℝ)≤(projected S z).card+orderedCollisions S z+1 := by
      exact_mod_cast projection_loss S z
    linarith
  obtain ⟨hlo,hhi⟩ := actual_cut_bounds q T.card (cut T z).card
    ((∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i)) hq0 ht.le
    (cut_mean_bounds q hq n) hcut
  rw [←quotientCut_card] at hlo hhi
  have hp : (S.card:ℝ)*T.card/(4*q)≤(projected S z).card*(quotientCut T z).card := by
    have hh := mul_le_mul hSn hlo (by positivity : 0≤(T.card:ℝ)/(3*q)) (by positivity)
    apply le_trans _ hh
    apply (div_le_iff₀ (by positivity : 0<4*q)).mpr
    field_simp
    nlinarith
  refine ⟨z,hSn,hlo,hhi,by simpa only [quotientCut_card] using hU.le,hp,?_,hcS,hcA⟩
  have hm : (incidenceCount (projected S z) (quotientCut T z):ℝ)≤ incidenceCount S (cut T z) := by
    exact_mod_cast quotient_incidence_le S T z
  apply hm.trans (hi.le.trans _)
  have hh := (div_le_iff₀ (by positivity : 0<4*q)).mp hp
  apply (div_le_div_iff₀ (pow_pos hq0 2) hq0).mpr
  have hh' := mul_le_mul_of_nonneg_left hh (show 0≤100*τ*q by positivity)
  dsimp only [q] at hh' ⊢
  nlinarith only [hh']

end
end SharpLogRamsey.Projection

end

end OAI
