import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.SparsePencilBounds
import OAI.Combinatorics.SharpRamsey.Learning.PreparedSparse

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical GreedyPreparation
open scoped BigOperators Classical NNReal
noncomputable section

lemma geometric_ratio_le (q : ℝ) (hq : 0<q) (j : ℕ) :
    (∑ i∈range j,q^i)/(∑ i∈range (j+1),q^i)≤ 1/q := by
  have he : q*(∑ i∈range j,q^i)+1=∑ i∈range (j+1),q^i := by
    exact geom_sum_succ.symm
  have hp : 0<∑ i∈range (j+1),q^i := by
    have hn : 0≤ ∑ i∈range j,q^i := sum_nonneg (fun i _ => pow_nonneg hq.le i)
    nlinarith
  apply (div_le_div_iff₀ hp hq).mpr
  linarith

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedRegularPreparationBounds_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedRegularPreparationBounds_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedRegularPreparationBounds_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem source_regular_preparation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) (hcsmall : (c:ℝ)≤ 1/100)
    (hcell : ∀ i : Fin bs.length,((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)≤ 1/25)
    (L : ℝ) (hL : 0≤ L) :
    let B := (Nat.card K:ℝ)^(n+2)/(S.card:ℝ)
    let E := badHyperplanes S U bs c
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)≤ (S.card:ℝ)/10000*Real.exp (-L/500) ∧
      (E.card:ℝ)≤ 10400*(Nat.card K:ℝ)*B ∧
      (∑ H∈E,mass S c H)≤ 20804*(Nat.card K:ℝ)*B ∧
      (∀ x,((own S U bs x).card:ℝ)/(S.card:ℝ)≤ 1/25) ∧
      ∀ x,x∉D →
        ((pencil x∩E).card:ℝ)<50000*B*Real.exp (L/1000) ∧
        (∀ H∈pencil x\E,
          3/4≤ outsideMass S (own S U bs x) x c H ∧
          outsideMass S (own S U bs x) x c H≤ 2 ∧
          |outsideMass S (own S U bs x) x c H-
            (1-((own S U bs x).card:ℝ)/(S.card:ℝ))|≤ 13/100) ∧
        (∑ H∈pencil x\E,(outsideMass S (own S U bs x) x c H-
          (1-((own S U bs x).card:ℝ)/(S.card:ℝ)))^2)≤ 400000*B*Real.exp (L/1000) := by
  let q : ℝ := Nat.card K
  let s : ℝ := S.card
  let B : ℝ := q^(n+2)/s
  let e : ℝ := Real.exp (L/1000)
  have hq : 2≤ q := by
    change (2:ℝ)≤ Nat.card K
    have hh : 2≤ Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    exact_mod_cast hh
  have hq0 : 0<q := by linarith
  have hs : 0<s := by
    change (0:ℝ)<S.card
    exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  have he : 1≤ e := Real.one_le_exp (by positivity)
  have he0 : 0<e := by linarith
  have hbpow : q^(n+3)/s=q*B := by dsimp [B]; rw [show n+3=n+2+1 by omega,pow_succ]; ring
  have hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤ (50000*B*e)/2 := by
    change (∑ k∈range (n+2),q^k)/(∑ k∈range (n+3),q^k)*(10408*(q^(n+3)/s))≤ _
    rw [hbpow]
    have hr : (∑ k∈range (n+2),q^k)/(∑ k∈range (n+3),q^k)≤ 1/q := by
      simpa only [show n+2+1=n+3 by omega] using geometric_ratio_le q hq0 (n+2)
    have hh := mul_le_mul_of_nonneg_right hr (show 0≤ 10408*(q*B) by positivity)
    have heq : 1/q*(10408*(q*B))=10408*B := by field_simp
    rw [heq] at hh
    nlinarith [mul_le_mul_of_nonneg_left he hB.le]
  obtain ⟨D,hD,hE,hW,hf,hr⟩ := regular_preparation hdim S hS U bs c hc hcsmall hcell
    (50000*B*e) (by positivity) hmean
  refine ⟨D,?_,?_,?_,hf,?_⟩
  · have heq : q^(2*n+4)/s=B^2*s := by
      dsimp [B]
      field_simp
      ring
    change (D.card:ℝ)*(50000*B*e/2)^2≤ 10408*q^(2*n+4)/s at hD
    have hdRewrite : 10408*q^(2*n+4)/s=10408*(B^2*s) := by rw [mul_div_assoc,heq]
    rw [hdRewrite] at hD
    have hd : (D.card:ℝ)*e^2≤ s/10000 := by
      have hh : (D.card:ℝ)*e^2*(625000000*B^2)≤ (s/10000)*(625000000*B^2) := by
        nlinarith [mul_nonneg (sq_nonneg B) hs.le]
      exact (mul_le_mul_iff_left₀ (by positivity : 0<625000000*B^2)).mp hh
    have hexp : Real.exp (-L/500)*e^2=1 := by
      dsimp [e]
      rw [←Real.exp_nat_mul,←Real.exp_add]
      norm_num only [Nat.cast_ofNat]
      rw [show -L/500+2*(L/1000)=0 by ring,Real.exp_zero]
    have hmul := mul_le_mul_of_nonneg_left hd (Real.exp_pos (-L/500)).le
    change (D.card:ℝ)≤ s/10000*Real.exp (-L/500)
    nlinarith [hexp]
  · change (badHyperplanes S U bs c).card≤ 10400*q*B
    change ((badHyperplanes S U bs c).card:ℝ)≤ 10400*(q^(n+3)/s) at hE
    rw [hbpow] at hE
    nlinarith only [hE]
  · change (∑ H∈badHyperplanes S U bs c,mass S c H)≤ 20804*q*B
    change (∑ H∈badHyperplanes S U bs c,mass S c H)≤ 20804*(q^(n+3)/s) at hW
    rw [hbpow] at hW
    nlinarith only [hW]
  · intro x hx
    obtain ⟨hpc,htyp,hsq⟩ := hr x hx
    refine ⟨hpc,htyp,hsq.trans ?_⟩
    have hc' : (c:ℝ)=q/s := hc
    have hcard : ((pencil x\badHyperplanes S U bs c).card:ℝ)≤ 2*q^(n+1) := by
      have hle : ((pencil x\badHyperplanes S U bs c).card:ℝ)≤ (pencil x).card := by
        exact_mod_cast card_le_card sdiff_subset
      have hpcard : (pencil x).card=∑ i∈range (n+2),Nat.card K^i := by
        have hd : Module.finrank K V=(n+2)+1 := by omega
        have hh := Incidence.card_incident_dual hd x
        rw [Nat.card_eq_fintype_card] at hh
        simpa only [Incidence.incident_iff_submodule,Fintype.card_subtype,pencil] using hh
      rw [hpcard] at hle
      exact hle.trans (by simpa only [Nat.cast_sum,Nat.cast_pow] using
        Incidence.geom_sum_le_twice_pow q hq (n+1))
    have heq : 2*q^(n+1)*(c:ℝ)^2=2*B*(c:ℝ) := by
      rw [hc']
      dsimp [B]
      field_simp
      ring
    have hsmall : ((pencil x\badHyperplanes S U bs c).card:ℝ)*(c:ℝ)^2≤ B/50 := by
      have hh := mul_le_mul_of_nonneg_right hcard (sq_nonneg (c:ℝ))
      rw [heq] at hh
      have hh' := mul_le_mul_of_nonneg_left hcsmall (show 0≤ 2*B by positivity)
      linarith
    change 3*(50000*B*e+50000*B*e+_*(c:ℝ)^2)≤ 400000*B*e
    nlinarith [mul_le_mul_of_nonneg_left he hB.le]

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
