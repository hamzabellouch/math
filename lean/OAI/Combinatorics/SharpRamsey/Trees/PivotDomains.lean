import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotGeometry
import OAI.Combinatorics.SharpRamsey.Trees.TreeDecoder
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalPotential
import OAI.Combinatorics.SharpRamsey.Trees.TreePotential

namespace OAI

section
namespace SharpLogRamsey.PivotDomains
open Finset Real Incidence TreeDecoder
open scoped Classical BigOperators
noncomputable section

lemma cap_product {q s t a b C K : ℝ} (r : ℕ) (hq : 0<q) (hs : 0<s) (ht : 0<t)
    (hC : 0≤ C) (hb : 0≤ b)
    (hp : q^r*exp (-K)≤ s*t) (hca : a≤ C*q^r/t) (hcb : b≤ C*q^r/s) :
    a*b≤ C^2*q^r*exp K := by
  have hx := mul_le_mul hca hcb hb (by positivity : 0≤ C*q^r/t)
  have hp' : q^r≤ s*t*exp K := by
    have hh := mul_le_mul_of_nonneg_right hp (exp_pos K).le
    have he : exp (-K)*exp K=1 := by rw [←exp_add]; simp
    simpa only [mul_assoc,he,mul_one] using hh
  have hden : 0<s*t := mul_pos hs ht
  have he : (C*q^r/t)*(C*q^r/s)=C^2*(q^r)^2/(s*t) := by ring
  rw [he] at hx
  apply hx.trans
  apply (div_le_iff₀ hden).mpr
  have hh := mul_le_mul_of_nonneg_left hp' (show 0≤ C^2*q^r by positivity)
  nlinarith only [hh]

lemma mixing_cap_bound {e p x q C b : ℝ} (n : ℕ) (hq : 0<q)
    (hC : 1≤ C) (hb : 0≤ b) (hx : 0≤ x) (hp : p≤1/q)
    (hprod : x≤ C^2*q^(n+3)*exp b)
    (hmix : (e-p*x)^2≤ q^(n+1)*x) :
    e≤2*C^2*q^(n+2)*exp b := by
  let M := C^2*q^(n+2)*exp b
  have hm : 0≤ M := by dsimp [M]; positivity
  have hmean : p*x≤ M := by
    apply (mul_le_mul_of_nonneg_right hp hx).trans
    apply (mul_le_mul_of_nonneg_left hprod (by positivity : 0≤1/q)).trans_eq
    dsimp [M]
    rw [show n+3=(n+2)+1 by omega,pow_succ]
    field_simp
    ring
  have he : 1≤ exp b := one_le_exp_iff.mpr hb
  have hc : 1≤ C^2 := by nlinarith
  have hcp : 1≤ C^2*exp b := one_le_mul_of_one_le_of_one_le hc he
  have herror : q^(n+1)*x≤ M^2 := by
    apply (mul_le_mul_of_nonneg_left hprod (by positivity : 0≤ q^(n+1))).trans
    have hh := mul_le_mul_of_nonneg_left hcp (show 0≤ C^2*q^(2*n+4)*exp b by positivity)
    have heq : q^(n+1)*(C^2*q^(n+3)*exp b)=C^2*q^(2*n+4)*exp b := by
      rw [show 2*n+4=(n+1)+(n+3) by omega,pow_add]; ring
    rw [heq]
    simp only [mul_one] at hh
    apply hh.trans_eq
    dsimp [M]
    rw [show 2*n+4=(n+2)*2 by omega,pow_mul]
    ring
  have hh : e-p*x≤ M := by nlinarith [hmix.trans herror]
  dsimp [M] at hmean hh
  linarith

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma flagDomain_card (A : Finset (Projectivization K V))
    (B : Finset (Projectivization K (Module.Dual K V))) :
    (flagDomain SharpLogRamsey.Incidence.Incident (A,B)).card=incidenceCount A B := by
  simp only [flagDomain,incidenceCount,card_filter,sum_product]
  exact sum_comm

theorem new_domain {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A : Finset (Projectivization K V))
    (B : Finset (Projectivization K (Module.Dual K V)))
    (s t C b : ℝ) (hs : 0<s) (ht : 0<t) (hC : 1≤ C) (hb : 0≤ b)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤ s*t)
    (hca : (A.card:ℝ)≤ C*(Nat.card K:ℝ)^(n+3)/t)
    (hcb : (B.card:ℝ)≤ C*(Nat.card K:ℝ)^(n+3)/s) :
    ((flagDomain SharpLogRamsey.Incidence.Incident (A,B)).card:ℝ)≤2*C^2*(Nat.card K:ℝ)^(n+2)*exp b := by
  let q : ℝ := Nat.card K
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast (Nat.card_pos : 0<Nat.card K)
  rw [flagDomain_card]
  have hp : (A.card:ℝ)*B.card≤ C^2*q^(n+3)*exp b :=
    cap_product (n+3) hq hs ht (by linarith) (Nat.cast_nonneg _)
      hprod hca hcb
  have hg := PreparedGeometry.geometric_ratio_le q hq (n+2)
  simp only [show n+2+1=n+3 by omega] at hg
  have hm := projective_mixing_sq hdim A B
  simp only [mul_assoc] at hm
  exact mixing_cap_bound n hq hC hb (by positivity) hg hp hm

end
end SharpLogRamsey.PivotDomains

end

end OAI
