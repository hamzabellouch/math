import OAI.Combinatorics.BalancedRyser.Selection.SelectionPrecheck

namespace OAI

open Filter Real
open scoped BigOperators Topology

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

theorem Parameters.small_tail_product (p : Parameters) (hp : p.Admissible) :
    p.a * p.C ≤ p.c / 100 := by
  rcases hp with ⟨hc, hC, hc₀, hc₀', ha, ha'⟩
  have hb : p.a < p.c / (100 * (p.C + 1)) :=
    (lt_min_iff.mp (lt_min_iff.mp ha').2).2
  have hden : 0 < 100 * (p.C + 1) := by positivity
  have hmul := (lt_div_iff₀ hden).mp hb
  nlinarith

theorem Parameters.tailSlots_le_twice (p : Parameters) (q : ℕ)
    (haq : 1 ≤ p.a * q) :
    (p.tailSlots q : ℝ) ≤ 2 * p.a * q := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ p.a * q by linarith)
  unfold Parameters.tailSlots
  linarith

variable {I V : Type*} [Fintype I] [Fintype V]

theorem tail_check_of_concentration (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 0 < q) (hcard : S.remaining.card = Fintype.card I - t)
    (hsmall : (S.remaining.card : ℝ) ≤ 2 * p.a * q)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (hL : ∀ i ∈ S.remaining,
      |((domain G S i).card : ℝ) - p.sizeScale q t * (slotVertices G i).card| ≤
        (q : ℝ) ^ ((4 : ℝ) / 5))
    (hD : ∀ v ∈ currentVertices G S,
      (degree G S v : ℝ) ≤ p.degreeScale q (Fintype.card I) t * (neighbors G v).card +
        (q : ℝ) ^ ((4 : ℝ) / 5)) :
    (∀ i ∈ S.remaining, 3 ≤ (domain G S i).card) ∧
    (∀ v ∈ currentVertices G S, ∀ i ∈ S.remaining,
      8 * (degree G S v : ℝ) ≤ ((domain G S i).card : ℝ)) := by
  have hac := p.small_tail_product hp
  rcases hp with ⟨hc, hC, hc₀, hc₀', ha, ha'⟩
  rcases hG with ⟨hcardI, hno, hslots, hdegrees, hrest⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hs : 0 < p.sizeScale q t := hsmin.trans_le hscale
  have hqn : (q : ℝ) ≤ Fintype.card I := by rw [hcardI]; norm_num; nlinarith
  have hn : (0 : ℝ) < Fintype.card I := hqR.trans_le hqn
  have hsc : p.smin * p.c * q ≤ p.sizeScale q t * p.c * q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hc.le) hqR.le
  have he' : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.sizeScale q t * p.c * q / 100 := by
    linarith
  have hlow (i : I) (hi : i ∈ S.remaining) :
      p.sizeScale q t * p.c * q / 2 ≤ ((domain G S i).card : ℝ) :=
    SelectionBarriers.domain_barrier hscale hc hqR (by linarith) (hslots i).1
      (hL i hi) hsmin
  constructor
  · intro i hi
    have h := hlow i hi
    have : (3 : ℝ) ≤ (domain G S i).card := by linarith
    exact_mod_cast this
  · intro v hv i hi
    have hratio : (S.remaining.card : ℝ) / Fintype.card I ≤ 2 * p.a := by
      apply (div_le_iff₀ hn).2
      exact hsmall.trans (mul_le_mul_of_nonneg_left hqn (by positivity))
    have hdegree : (degree G S v : ℝ) ≤
        p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q +
          (q : ℝ) ^ ((4 : ℝ) / 5) := by
      have hscale0 : 0 ≤ p.degreeScale q (Fintype.card I) t := by
        unfold Parameters.degreeScale
        positivity
      have hhdeg := mul_le_mul_of_nonneg_left (hdegrees v) hscale0
      have hd := (hD v hv).trans (add_le_add hhdeg le_rfl)
      have hid : p.degreeScale q (Fintype.card I) t * (p.C * q) =
          p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q := by
        rw [Parameters.degreeScale, ← hcard]
        ring
      rwa [hid] at hd
    have hratio' : p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q ≤
        p.sizeScale q t * (2 * p.a) * p.C * q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio hs.le) hC.le) hqR.le
    have hmain : p.sizeScale q t * (2 * p.a) * p.C * q ≤
        p.sizeScale q t * p.c * q / 50 := by
      have h := mul_le_mul_of_nonneg_left hac
        (show 0 ≤ 2 * p.sizeScale q t * q by positivity)
      nlinarith
    have hdom := hlow i hi
    linarith

theorem exists_tail_check_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      0 < q ∧ (p.tailSlots q : ℝ) ≤ 2 * p.a * q ∧
      6 ≤ p.smin * p.c * q ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100 := by
  have ha := hp.2.2.2.2.1
  have hc := hp.1
  have hsmin : 0 < p.smin := Real.exp_pos _
  have he := SelectionBarriers.eventually_selection_error_le
    (δ := p.smin * p.c / 100) (by positivity)
  have hq₁ : ∀ᶠ q : ℕ in atTop, 1 / p.a ≤ (q : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 / p.a))
  have hq₂ : ∀ᶠ q : ℕ in atTop, 6 / (p.smin * p.c) ≤ (q : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (6 / (p.smin * p.c)))
  apply eventually_atTop.mp
  filter_upwards [he, hq₁, hq₂, eventually_ge_atTop 1] with q he hq₁ hq₂ hq
  have haq : 1 ≤ p.a * q := by
    have h := (div_le_iff₀ ha).mp hq₁
    nlinarith
  have hlarge : 6 ≤ p.smin * p.c * q := by
    have h := (div_le_iff₀ (mul_pos hsmin hc)).mp hq₂
    nlinarith
  refine ⟨by omega, p.tailSlots_le_twice q haq, hlarge, ?_⟩
  convert he using 1; ring

end
end Balanced.Selection.Process

end OAI
