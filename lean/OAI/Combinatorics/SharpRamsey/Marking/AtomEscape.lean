import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.RawLowerTail

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankBudgets
open Filter Real
open scoped Topology BigOperators
noncomputable section
lemma atom_escape {q C K : ℝ} {r : ℕ} (hq : 0<q) (hr : 2≤r)
    (hsmall : 20*C*Real.exp K ≤ q) :
    2*(C*Real.exp K/q^r)*q^(r-2) ≤ 1/(10*q) := by
  have hp : q^r=q^(r-2)*q^2 := by rw [←pow_add]; congr 1; omega
  rw [hp]
  have he : 2*(C*Real.exp K/(q^(r-2)*q^2))*q^(r-2) = 2*C*Real.exp K/q^2 := by
    field_simp
  rw [he]
  apply (div_le_iff₀ (by positivity : 0<q^2)).mpr
  have he : 1/(10*q)*q^2=q/10 := by field_simp
  rw [he]
  linarith

lemma low_hit_budget {q C K : ℝ} {d r r' : ℕ} (hq : 1≤q)
    (hr : d+2 ≤ r+r') :
    100*q^(d+1)*(C*Real.exp K/q^r')*(C*Real.exp K/q^r) ≤
      100*C^2*Real.exp (2*K)/q := by
  have hq0 : 0<q := by linarith
  have hpow : q^(d+1)*q ≤ q^r*q^r' := by
    rw [←pow_succ, ←pow_add]
    exact pow_le_pow_right₀ hq hr
  have H := mul_le_mul_of_nonneg_left hpow (show 0≤100*C^2*Real.exp (2*K) by positivity)
  have he : Real.exp (2*K)=(Real.exp K)^2 := by rw [←Real.exp_nat_mul]; congr 1
  rw [he] at H ⊢
  apply (le_div_iff₀ hq0).mpr
  have hden : 0<q^r'*q^r := by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  field_simp
  nlinarith [sq_nonneg C]

theorem eventually_polynomial_exp_neg_rpow_lt (C a b c ε : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a*Real.exp (-c*x^b) < ε := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound
    (show 0 < ε/(2*(|C|+1)) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    _ ≤ (|C|+1)*x^a*Real.exp (-c*x^b) := by
      gcongr
    _ ≤ (|C|+1)*(ε/(2*(|C|+1))*Real.exp (c*x^b))*Real.exp (-c*x^b) := by
      gcongr
    _ = ε/2 := by
      rw [mul_assoc (|C|+1), mul_assoc, ← Real.exp_add,
        show c*x^b+-c*x^b=0 by ring, Real.exp_zero]
      field_simp
    _ < ε := by linarith

def error (σ η D C : ℝ) (d : ℕ) : ℝ :=
  100*C^2*Real.exp (2*scaleK σ η D)/Real.exp σ +
  d*Real.exp (-(3/(20*d))*σ^beta η) +
  Real.exp 1*Real.exp (-(1/10)*σ^beta η) +
  4*C*σ^(-(1999*beta η)) +
  C*(σ^(-(2*beta η))+σ^(-(4*beta η))) +
  2*C*Real.exp (scaleK σ η D)/Real.exp σ

theorem eventually_error {η : ℝ} (hη : 0<η) (C ε : ℝ) (hC : 0≤C)
    (hε : 0<ε) (d : ℕ) (hd : 0<d) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, D ≤ σ^(1-η/2) → error σ η D C d < ε := by
  have hb : 0<beta η := by unfold beta; positivity
  have hε7 : 0<ε/7 := by positivity
  have h₁ := eventually_exp_K_over_q hη (100*C^2) 2 (ε/7) (by positivity) (by norm_num) hε7
  have h₂ := eventually_polynomial_exp_neg_rpow_lt d 0 (beta η) (3/(20*d)) (ε/7)
    hb (by positivity) hε7
  have h₃ := eventually_polynomial_exp_neg_rpow_lt (Real.exp 1) 0 (beta η) (1/10) (ε/7)
    hb (by norm_num) hε7
  have h₄ : Tendsto (fun σ : ℝ => 4*C*σ^(-(1999*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show 0<1999*beta η by positivity)).const_mul (4*C)
  have h₅ : Tendsto (fun σ : ℝ => C*σ^(-(2*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul C
  have h₆ : Tendsto (fun σ : ℝ => C*σ^(-(4*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show 0<4*beta η by positivity)).const_mul C
  have h₇ := eventually_exp_K_over_q hη (2*C) 1 (ε/7) (by positivity) (by norm_num) hε7
  filter_upwards [h₁,h₂,h₃,h₄.eventually (gt_mem_nhds hε7),
    h₅.eventually (gt_mem_nhds hε7),h₆.eventually (gt_mem_nhds hε7),h₇]
    with σ h₁ h₂ h₃ h₄ h₅ h₆ h₇ D hD
  simp only [Real.rpow_zero,mul_one] at h₂ h₃
  have h₁ := h₁ D hD
  have h₇ := h₇ D hD
  simp only [one_mul] at h₇
  unfold error
  linarith
end
end SharpLogRamsey.HighRankBudgets

namespace SharpLogRamsey.SimultaneousExtraction
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

lemma markov_complement (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (ht : ∑ z, p z=1)
    (f g : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    1-(∑ z, p z*f z)/A-(∑ z, p z*g z)/B ≤
      ∑ z ∈ univ.filter (fun z => f z ≤ A ∧ g z ≤ B), p z := by
  have H (z : Ω) : p z*(1-f z/A-g z/B) ≤
      if f z ≤ A ∧ g z ≤ B then p z else 0 := by
    by_cases h : f z ≤ A ∧ g z ≤ B
    · rw [ite_eq_left h]
      have h0 : 0 ≤ f z/A := div_nonneg (hf z) hA.le
      have h1 : 0 ≤ g z/B := div_nonneg (hg z) hB.le
      nlinarith [hp z]
    · rw [ite_eq_right h]
      have he : 1 ≤ f z/A+g z/B := by
        by_cases he : f z ≤ A
        · have hh : B < g z := lt_of_not_ge (fun hh => h ⟨he,hh⟩)
          have hh' : 1 ≤ g z/B := (one_le_div hB).mpr hh.le
          linarith [div_nonneg (hf z) hA.le]
        · have hh' : 1 ≤ f z/A := (one_le_div hA).mpr (le_of_not_ge he)
          linarith [div_nonneg (hg z) hB.le]
      exact mul_nonpos_of_nonneg_of_nonpos (hp z) (by linarith)
  have HH := sum_le_sum (fun z (_ : z∈univ) => H z)
  simpa only [sum_filter, mul_sub, mul_one, mul_div_assoc, sum_sub_distrib,
    sum_div, ht] using HH

theorem simultaneous_mass (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (ht : ∑ z, p z=1)
    (f g : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (E S A B : ℝ) (hA : 0<A) (hB : 0<B)
    (hE : ∑ z, p z*f z ≤ E) (hS : ∑ z, p z*g z ≤ S) :
    1-E/A-S/B ≤ ∑ z ∈ univ.filter (fun z => f z ≤ A ∧ g z ≤ B), p z := by
  have H := markov_complement p hp ht f g hf hg A B hA hB
  have H₁ := div_le_div_of_nonneg_right hE hA.le
  have H₂ := div_le_div_of_nonneg_right hS hB.le
  linarith

def retained {k ℓ : ℕ} (S : Finset (Fin ℓ)) (h : k ≤ S.card) : Fin k ↪o Fin ℓ :=
  (Fin.castLEOrderEmb h).comp (S.orderEmbOfFin rfl)

lemma retained_mem {k ℓ : ℕ} (S : Finset (Fin ℓ)) (h : k ≤ S.card) (i : Fin k) :
    retained S h i ∈ S := by
  exact S.orderEmbOfFin_mem rfl _

theorem coverage_selection {ℓ : ℕ} (good : Fin ℓ → Prop)
    (h : ((univ.filter (fun i => ¬good i)).card:ℝ) ≤ (ℓ:ℝ)/2) :
    ∃ e : Fin (ℓ/2) ↪o Fin ℓ, ∀ i, good (e i) := by
  let S := univ.filter good
  have he : S.card+(univ.filter (fun i => ¬good i)).card=ℓ := by
    simpa [S] using card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ))) good
  have hh : ℓ/2 ≤ S.card := by
    have h' : (ℓ:ℝ) ≤ 2*S.card := by
      have he' : (S.card:ℝ)+(univ.filter (fun i => ¬good i)).card=ℓ := by exact_mod_cast he
      linarith
    have hh' : ℓ ≤ 2*S.card := by exact_mod_cast h'
    omega
  refine ⟨retained S hh, fun i => ?_⟩
  exact (mem_filter.mp (retained_mem S hh i)).2
end
end SharpLogRamsey.SimultaneousExtraction

namespace SharpLogRamsey.HighRankAssembly
open scoped BigOperators
open Finset Classical HighRankDecoder HighRankCoverageProbability FiniteEventBounds
open FiniteMarginals
noncomputable section
variable {K Ω : Type*} [Field K] [Fintype K] [Fintype Ω]
variable {d : ℕ}
local notation "V" => (Fin (d+1) → K)
local notation "A" => Projectivization K (Module.Dual K V)
local notation "B" => Projectivization K V
local notation "q" => (Nat.card K : ℝ)
local instance flat_JoinedHighRankAssembly_6 : Fintype B := Fintype.ofFinite _
local instance flat_JoinedHighRankAssembly_7 : Finite (Module.Dual K V) :=
  Finite.of_injective ((↑) : Module.Dual K V → (V → K)) DFunLike.coe_injective
local instance flat_JoinedHighRankAssembly_8 : Fintype A := Fintype.ofFinite _

theorem low_hit_with_cutoff (hd : 2 ≤ d)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (M : ℝ) (hM : ∀ b, marginal w a b ≤ M)
    (p : B × A → ℝ) (hp : ∀ t, 0 ≤ p t)
    (good : B → Prop) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ y, good y → (∑ c, p (y,c)) ≤ N) :
    (∑ t, p t * indicator
      ((∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep = 0), w z) < 2/(5*q))) ≤
    (∑ y ∈ univ.filter (fun y => ¬good y), ∑ c, p (y,c)) +
      100*q^(d+1)*M*N := by
  let p' : B × A → ℝ := fun t => if good t.1 then p t else 0
  have hdim : Module.finrank K V = (d-2)+3 := by simp; omega
  have HH := HighRankLowHit.low_hit_mass hdim w hw ht a M hM p' N hN0 (by
    intro y
    by_cases hy : good y
    · simpa [p',hy] using hN y hy
    · simpa [p',hy] using hN0)
  have he : (d-2)+3 = d+1 := by omega
  rw [he] at HH
  have H : (∑ t, p t * indicator
      ((∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep = 0), w z) < 2/(5*q))) ≤
      (∑ y ∈ univ.filter (fun y => ¬good y), ∑ c, p (y,c)) +
      (∑ t, p' t * indicator
        ((∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep = 0), w z) < 2/(5*q))) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro y _
    by_cases hy : good y
    · simp [p',hy]
    · simp only [hy,not_false_eq_true,ite_true,ite_false,p',zero_mul,sum_const_zero,add_zero]
      apply sum_le_sum
      intro c _
      unfold indicator
      split_ifs <;> simp [hp]
  exact H.trans (add_le_add_right HH _)

theorem coverage_source (hd : 2 ≤ d)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B) (p : B × A → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hpt : ∑ t, p t = 1)
    (hincident : ∀ t, p t ≠ 0 → t.2.rep t.1.rep = 0)
    (U : Finset B) (hsupp : ∀ t, p t ≠ 0 → t.1 ∈ U)
    (good : B → Prop) (h r r' T : ℕ)
    (hr : 2 ≤ r) (hrd : r ≤ d) (hrank : d+2 ≤ r+r') (hhd : 2*d ≤ h)
    (C κ Ebad Eheavy I : ℝ) (hC : 0 ≤ C)
    (hfirst : ∀ x, marginal w a x ≤ C*Real.exp κ/q^r')
    (hsecond : ∀ y, marginal w b y ≤ C*Real.exp κ/q^r)
    (htarget : ∀ y, good y → (∑ c, p (y,c)) ≤ C*Real.exp κ/q^r)
    (hcard : (U.card:ℝ) ≤ C*q^r)
    (hbad : (∑ y ∈ univ.filter (fun y => ¬good y), ∑ c, p (y,c)) ≤ Ebad)
    (hheavy : (∑ t ∈ U ×ˢ univ, if Real.exp κ/q^d < p t then p t else 0) ≤ Eheavy)
    (hconflict : (∑ t, p t*conflictMass w (fun z => (a z).rep) b t.1 t.2) ≤ I)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*q)+1)
    (hescape : 20*C*Real.exp κ ≤ q) :
    (∑ t, p t*mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted (fun z => (a z).rep) b z₁ z₂ r T t.1 t.2))) ≤
      Ebad + 100*C^2*Real.exp (2*κ)/q +
      (d*Real.exp (-3*(h:ℝ)/(20*d*q)) + Real.exp (1-(h:ℝ)/(10*q))) +
      2*h*I + Eheavy + 2*C*Real.exp κ/q := by
  have hq : 2 ≤ q := by exact_mod_cast Finite.one_lt_card (α := K)
  have hq0 : 0 < q := by linarith
  obtain ⟨e⟩ := HighRankBudgets.block_embedding h d r hrd
  have hdim : Module.finrank K V = d+1 := by simp
  have HC := HighRankAveraged.averaged_coverage w hw ht p hp hpt hincident U hsupp
    (fun z => (a z).rep) b h d r (h/d) T hdim hr hrd e
    (C*Real.exp κ/q^r) (Real.exp κ/q^d) (by positivity) (by positivity)
    (by intro y; simpa [marginal, sum_filter] using hsecond y) hT
  have HL := (low_hit_with_cutoff hd w hw ht a (C*Real.exp κ/q^r') hfirst
    p hp good (C*Real.exp κ/q^r) (by positivity) htarget).trans
    (add_le_add hbad (HighRankBudgets.low_hit_budget (by linarith : 1 ≤ q) hrank))
  have HG := HighRankBudgets.growth_tail hq
    (show 0 ≤ C*Real.exp κ/q^r by positivity) hrd (by omega : 0 < d) hhd
    (HighRankBudgets.atom_escape hq0 hr hescape)
  have HX : (if r < d then (U.card:ℝ)*(2*q^(d-r-1))*(Real.exp κ/q^d) else 0) ≤
      2*C*Real.exp κ/q := by
    split_ifs with hrd'
    · have he : q^d = q^r*q^(d-r-1)*q := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      calc
        _ ≤ (C*q^r)*(2*q^(d-r-1))*(Real.exp κ/q^d) := by gcongr
        _ = _ := by rw [he]; field_simp
    · positivity
  have HI := mul_le_mul_of_nonneg_left hconflict (show 0 ≤ 2*(h:ℝ) by positivity)
  linarith only [HC,HL,HG,HX,HI,hheavy]

theorem size_source (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B) {h r T : ℕ} (hr : 0 < r) (hrd : r ≤ d)
    (X : Finset B) (hsupp : ∀ y, y ∉ X → marginal w b y = 0)
    (C κ u : ℝ) (hC : 0 < C) (hu : 0 < u) (huA : u ≤ 2*C*Real.exp κ)
    (hu20 : u ≤ 1/20) (hCu : 20*Real.exp (1/2)*u ≤ 1)
    (hcap : ∀ y ∈ X, marginal w b y ≤ C*Real.exp κ/q^r)
    (hcard : (X.card : ℝ) ≤ C*q^r)
    (hT : (h:ℝ)/(10*q) ≤ T) (hTn : d+2 ≤ T) (z₁ : Fin h → Ω) :
    (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂ *
      ((HighRankSize.domain (fun z => (a z).rep) b z₁ z₂ r T).card : ℝ)) ≤
      (10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d) := by
  have HU : u ≤ 2*(C*Real.exp κ) := by nlinarith only [huA]
  have HS := HighRankSize.expected_domain (n := d+1) (by omega) hr (by omega)
    w hw ht (fun z => (a z).rep) b z₁ X hsupp (C*Real.exp κ) u
    (by positivity) hu HU hu20 hCu
    (by simpa only [Nat.card_eq_fintype_card] using hcap)
    (by simpa only [Nat.card_eq_fintype_card] using hT) hTn
  simp only [← Nat.card_eq_fintype_card, Nat.cast_add, Nat.cast_one] at HS
  have hn : d+1-r-1 = d-r := by omega
  have hp : q^r*q^(d-r)=q^d := by rw [← pow_add]; congr 1; omega
  apply HS.trans
  calc
    _ ≤ (10*(d+1)*(C*Real.exp κ)/u)^(d+1)*(C*q^r)*(1+2^(d+1+1))*(2*q^(d+1-r-1)) := by
      gcongr
    _ = _ := by
      rw [hn]
      rw [show d+1+1=d+2 by omega]
      calc
        _ = (10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*(q^r*q^(d-r))) := by ring
        _ = _ := by rw [hp]

omit [Fintype Ω] in

lemma domain_raw_rows (a : Ω → A) (b : Ω → B) {h : ℕ}
    (z₁ z₂ : Fin h → Ω) (r T : ℕ) :
    HighRankSize.domain (fun z : A × B => z.1.rep) Prod.snd
      (fun i => (a (z₁ i), b (z₁ i))) (fun i => (a (z₂ i), b (z₂ i))) r T =
    HighRankSize.domain (fun z => (a z).rep) b z₁ z₂ r T := rfl
end
end SharpLogRamsey.HighRankAssembly

namespace SharpLogRamsey.SimultaneousExtraction
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω R F : Type*} [Fintype Ω] [Fintype R] [Fintype F]

def independentWeight (p : Ω → ℝ) (w : R → ℝ) (u : Ω × R) : ℝ := p u.1*w u.2

lemma independent_total (p : Ω → ℝ) (w : R → ℝ)
    (hp : ∑ x, p x = 1) (hw : ∑ z, w z = 1) :
    ∑ u, independentWeight p w u = 1 := by
  simp [independentWeight, Fintype.sum_prod_type, ← mul_sum, hp, hw]

def missed {ℓ : ℕ} (f : Ω → Fin ℓ → F) (D : R → Finset F) (u : Ω × R) : ℕ :=
  (univ.filter (fun i => f u.1 i ∉ D u.2)).card

omit [Fintype F] in
lemma missed_mean {ℓ : ℕ} (p : Ω → ℝ) (w : R → ℝ)
    (f : Ω → Fin ℓ → F) (D : R → Finset F) :
    (∑ u, independentWeight p w u * (missed f D u : ℝ)) =
      ∑ i, ∑ x, p x * ∑ z, w z * (if f x i ∉ D z then 1 else 0) := by
  have he (u : Ω × R) : (missed f D u : ℝ) =
      ∑ i : Fin ℓ, if f u.1 i ∉ D u.2 then (1:ℝ) else 0 := by
    rw [← sum_filter]
    simp only [missed, sum_const, nsmul_eq_mul, mul_one]
  simp_rw [he, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  simp [independentWeight]

omit [Fintype F] in
lemma domain_size_mean (p : Ω → ℝ) (w : R → ℝ) (hp : ∑ x, p x = 1)
    (D : R → Finset F) :
    (∑ u, independentWeight p w u * ((D u.2).card : ℝ)) =
      ∑ z, w z * ((D z).card : ℝ) := by
  simp [independentWeight, Fintype.sum_prod_type, mul_assoc, ← mul_sum,
    ← sum_mul, hp]

omit [Fintype F] in

theorem tuple_extraction {ℓ : ℕ} (hℓ : 0 < ℓ)
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hpt : ∑ x, p x = 1)
    (w : R → ℝ) (hw : ∀ z, 0 ≤ w z) (hwt : ∑ z, w z = 1)
    (f : Ω → Fin ℓ → F) (D : R → Finset F) (ε S : ℝ) (hS : 0 < S)
    (hcoverage : ∀ i, (∑ x, p x * ∑ z, w z *
      (if f x i ∉ D z then (1:ℝ) else 0)) ≤ ε)
    (hsize : (∑ z, w z * ((D z).card : ℝ)) ≤ S) :
    1-2*ε-1/4 ≤
      ∑ u ∈ univ.filter (fun u : Ω × R =>
        ((D u.2).card : ℝ) ≤ 4*S ∧
        ∃ e : Fin (ℓ/2) ↪o Fin ℓ, ∀ i, f u.1 (e i) ∈ D u.2),
        independentWeight p w u := by
  have hℓ' : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  have hmean : (∑ u, independentWeight p w u * (missed f D u : ℝ)) ≤ ℓ*ε := by
    rw [missed_mean]
    simpa using sum_le_sum (fun i (_ : i∈univ) => hcoverage i)
  have HS := simultaneous_mass (independentWeight p w)
    (fun u => mul_nonneg (hp u.1) (hw u.2)) (independent_total p w hpt hwt)
    (fun u => (missed f D u : ℝ)) (fun u => ((D u.2).card : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (ℓ*ε) S (ℓ/2) (4*S) (by positivity) (by positivity) hmean
    (by rw [domain_size_mean p w hpt]; exact hsize)
  have he : 1-(ℓ:ℝ)*ε/((ℓ:ℝ)/2)-S/(4*S) = 1-2*ε-1/4 := by
    field_simp [hℓ'.ne',hS.ne']
  rw [he] at HS
  apply HS.trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨_,hf,hs⟩ := mem_filter.mp hu
    refine mem_filter.mpr ⟨mem_univ _, hs, ?_⟩
    apply coverage_selection (fun i => f u.1 i ∈ D u.2)
    convert hf using 1
    congr 1
    congr 1
    ext i
    simp
  · intro u _ _
    exact mul_nonneg (hp u.1) (hw u.2)
end
end SharpLogRamsey.SimultaneousExtraction

namespace SharpLogRamsey.HighRankAssembly
open scoped BigOperators Classical
open Finset HighRankDecoder HighRankCoverageProbability FiniteEventBounds
open FiniteMarginals SimultaneousExtraction
noncomputable section
variable {K Ω Ξ : Type*} [Field K] [Fintype K] [Fintype Ω] [Fintype Ξ]
variable {d : ℕ}
local instance flat_JoinedHighRankAssembly_9 : Finite (Module.Dual K (Fin (d+1) → K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1) → K) → ((Fin (d+1) → K) → K)) DFunLike.coe_injective
local instance flat_JoinedHighRankAssembly_10 : Fintype (Projectivization K (Fin (d+1) → K)) := Fintype.ofFinite _
local instance flat_JoinedHighRankAssembly_11 : Fintype (Projectivization K (Module.Dual K (Fin (d+1) → K))) := Fintype.ofFinite _
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1) → K))
local notation "B" => Projectivization K (Fin (d+1) → K)
local notation "q" => (Nat.card K : ℝ)

omit [Fintype Ξ] in
lemma row_pair_total (w : Ω → ℝ) (ht : ∑ z, w z = 1) (h : ℕ) :
    (∑ z : (Fin h → Ω) × (Fin h → Ω), ProductLaw.weight w z.1*ProductLaw.weight w z.2) = 1 := by
  have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z = 1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    congr!
  exact independent_total (ProductLaw.weight w) (ProductLaw.weight w) hnt hnt

lemma decoder_miss_mean (w : Ω → ℝ) (a : Ω → A) (b : Ω → B)
    (p : Ξ → ℝ) (f : Ξ → B × A) (h r T : ℕ) :
    (∑ x, p x * ∑ z : (Fin h → Ω) × (Fin h → Ω),
      (ProductLaw.weight w z.1*ProductLaw.weight w z.2) *
      (if f x ∉ HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T then (1:ℝ) else 0)) =
    ∑ t, marginal p f t * mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted (fun z => (a z).rep) b z₁ z₂ r T t.1 t.2)) := by
  rw [sum_marginal]
  apply sum_congr rfl
  intro x _
  congr 1
  simp [HighRankSize.domain, mean2, Fintype.sum_prod_type, indicator, mul_sum]

omit [Fintype Ξ] in
lemma row_pair_size (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B) (h r T : ℕ) (S : ℝ)
    (hS : ∀ z₁ : Fin h → Ω, (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂ *
      ((HighRankSize.domain (fun z => (a z).rep) b z₁ z₂ r T).card:ℝ)) ≤ S) :
    (∑ z : (Fin h → Ω) × (Fin h → Ω),
      (ProductLaw.weight w z.1*ProductLaw.weight w z.2) *
      ((HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T).card:ℝ)) ≤ S := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ z₁ : Fin h → Ω, ProductLaw.weight w z₁ *
        ∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂ *
          ((HighRankSize.domain (fun z => (a z).rep) b z₁ z₂ r T).card:ℝ) := by
      simp only [mul_sum, mul_assoc]
    _ ≤ ∑ z₁ : Fin h → Ω, ProductLaw.weight w z₁ *S :=
      sum_le_sum (fun z₁ _ => mul_le_mul_of_nonneg_left (hS z₁) (ProductLaw.nonneg w hw z₁))
    _ = S := by
      have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z = 1 := by
        convert ProductLaw.total (ι := Fin h) w ht using 1
        congr!
      rw [← sum_mul, hnt, one_mul]

theorem extraction_source (hd : 2 ≤ d) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B)
    (p : Ξ → ℝ) (hp : ∀ x, 0 ≤ p x) (hpt : ∑ x, p x = 1)
    (f : Ξ → Fin ℓ → B × A)
    (U : Fin ℓ → Finset B) (good : Fin ℓ → B → Prop)
    (h r r' T : ℕ) (hr : 2 ≤ r) (hrd : r ≤ d)
    (hrank : d+2 ≤ r+r') (hhd : 2*d ≤ h)
    (C κ u Ebad Eheavy I : ℝ) (hC : 0 < C)
    (hu : 0 < u) (huA : u ≤ 2*C*Real.exp κ)
    (hu20 : u ≤ 1/20) (hCu : 20*Real.exp (1/2)*u ≤ 1)
    (hfirst : ∀ x, marginal w a x ≤ C*Real.exp κ/q^r')
    (hsecond : ∀ y, marginal w b y ≤ C*Real.exp κ/q^r)
    (X : Finset B) (hX : ∀ y, y ∉ X → marginal w b y = 0)
    (hXcard : (X.card:ℝ) ≤ C*q^r)
    (hincident : ∀ i t, marginal p (fun x => f x i) t ≠ 0 → t.2.rep t.1.rep = 0)
    (hsupp : ∀ i t, marginal p (fun x => f x i) t ≠ 0 → t.1 ∈ U i)
    (htarget : ∀ i y, good i y → (∑ c, marginal p (fun x => f x i) (y,c)) ≤ C*Real.exp κ/q^r)
    (hcard : ∀ i, ((U i).card:ℝ) ≤ C*q^r)
    (hbad : ∀ i, (∑ y ∈ univ.filter (fun y => ¬good i y),
      ∑ c, marginal p (fun x => f x i) (y,c)) ≤ Ebad)
    (hheavy : ∀ i, (∑ t ∈ (U i) ×ˢ univ,
      if Real.exp κ/q^d < marginal p (fun x => f x i) t
      then marginal p (fun x => f x i) t else 0) ≤ Eheavy)
    (hconflict : ∀ i, (∑ t, marginal p (fun x => f x i) t *
      conflictMass w (fun z => (a z).rep) b t.1 t.2) ≤ I)
    (hTlo : (h:ℝ)/(10*q) ≤ T) (hThi : (T:ℝ) ≤ (h:ℝ)/(10*q)+1)
    (hTn : d+2 ≤ T) (hescape : 20*C*Real.exp κ ≤ q) :
    let S := (10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d)
    let E := Ebad + 100*C^2*Real.exp (2*κ)/q +
      (d*Real.exp (-3*(h:ℝ)/(20*d*q)) + Real.exp (1-(h:ℝ)/(10*q))) +
      2*h*I + Eheavy + 2*C*Real.exp κ/q
    let W := fun z : (Fin h → Ω) × (Fin h → Ω) => ProductLaw.weight w z.1*ProductLaw.weight w z.2
    let D := fun z : (Fin h → Ω) × (Fin h → Ω) => HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T
    1-2*E-1/4 ≤
      ∑ v ∈ univ.filter (fun v : Ξ × ((Fin h → Ω) × (Fin h → Ω)) =>
        ((D v.2).card:ℝ) ≤ 4*S ∧
        ∃ e : Fin (ℓ/2) ↪o Fin ℓ, ∀ i, f v.1 (e i) ∈ D v.2),
        p v.1*W v.2 := by
  dsimp only
  let W := fun z : (Fin h → Ω) × (Fin h → Ω) => ProductLaw.weight w z.1*ProductLaw.weight w z.2
  let D := fun z : (Fin h → Ω) × (Fin h → Ω) => HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T
  have hW : ∀ z, 0 ≤ W z := fun z => mul_nonneg (ProductLaw.nonneg w hw z.1) (ProductLaw.nonneg w hw z.2)
  have hWt : ∑ z, W z = 1 := row_pair_total w ht h
  have hq : 0 < q := by exact_mod_cast Nat.card_pos (α := K)
  have hpos : 0 < ((10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d)) := by
    positivity
  have HX := tuple_extraction hℓ p hp hpt W hW hWt f D
    (Ebad + 100*C^2*Real.exp (2*κ)/q +
      (d*Real.exp (-3*(h:ℝ)/(20*d*q)) + Real.exp (1-(h:ℝ)/(10*q))) +
      2*h*I + Eheavy + 2*C*Real.exp κ/q)
    ((10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d)) hpos
  refine (HX ?_ ?_).trans ?_
  · intro i
    have HC := coverage_source hd w hw ht a b (marginal p (fun x => f x i))
      (marginal_nonneg p hp _) (by rw [marginal_total]; exact hpt)
      (hincident i) (U i) (hsupp i) (good i) h r r' T hr hrd hrank hhd C κ Ebad Eheavy I hC.le
      hfirst hsecond (htarget i) (hcard i) (hbad i) (hheavy i) (hconflict i) hThi hescape
    have Hmean := (decoder_miss_mean w a b p (fun x => f x i) h r T).le.trans HC
    convert Hmean using 1
    congr!
  · apply row_pair_size w hw ht a b h r T
    intro z₁
    exact size_source w hw ht a b (by omega) hrd X hX C κ u hC hu huA hu20 hCu
      (fun y _ => hsecond y) hXcard hTlo hTn z₁
  · apply le_of_eq
    congr!
end
end SharpLogRamsey.HighRankAssembly

end

end OAI
