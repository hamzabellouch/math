import OAI.Combinatorics.BalancedRyser.Selection.SelectionBarriers
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcess

namespace OAI

open Filter Real
open scoped BigOperators Topology

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem degree_eq_sum_domain_neighbors (G : Input I V) (S : State I V) (v : V) :
    (∑ i ∈ S.remaining, ((neighbors G v) ∩ domain G S i).card) = degree G S v := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    ((neighbors G v) ∩ S.alive) S.remaining G.slot
  have hleft (i : I) : ((neighbors G v) ∩ S.alive).filter (fun w => G.slot w = i) =
      (neighbors G v) ∩ domain G S i := by
    ext w
    simp [domain, and_assoc]
  have hright : ((neighbors G v) ∩ S.alive).filter (fun w => G.slot w ∈ S.remaining) =
      (neighbors G v) ∩ currentVertices G S := by
    ext w
    simp [currentVertices, and_assoc]
  simpa only [hleft, hright, degree] using h

omit [Fintype I] in

theorem hazard_le_degree_div (G : Input I V) (S : State I V) (v : V)
    {m : ℝ} (hS : S.remaining.Nonempty) (hm : 0 < m)
    (hL : ∀ i ∈ S.remaining, m ≤ ((domain G S i).card : ℝ)) :
    hazard G S v ≤ (degree G S v : ℝ) / ((S.remaining.card : ℝ) * m) := by
  apply SelectionBarriers.finite_hazard_le S.remaining
    (fun i => ((domain G S i).card : ℝ))
    (fun i => (((neighbors G v) ∩ domain G S i).card : ℝ))
    (by exact_mod_cast Finset.card_pos.mpr hS) hm hL
    (fun _ _ => Nat.cast_nonneg _)
  exact le_of_eq (by exact_mod_cast degree_eq_sum_domain_neighbors G S v)

theorem precheck_of_concentration (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 0 < q) (halpha : p.Pstar < (q : ℝ))
    (hh : p.a * q ≤ (S.remaining.card : ℝ))
    (hcard : S.remaining.card = Fintype.card I - t)
    (hscale : p.smin ≤ p.sizeScale q t)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q)
    (hL : ∀ i ∈ S.remaining,
      |((domain G S i).card : ℝ) - p.sizeScale q t * (slotVertices G i).card| ≤
        (q : ℝ) ^ ((4 : ℝ) / 5))
    (hD : ∀ v ∈ currentVertices G S,
      (degree G S v : ℝ) ≤ p.degreeScale q (Fintype.card I) t * (neighbors G v).card +
        (q : ℝ) ^ ((4 : ℝ) / 5)) :
    Precheck p q t G S := by
  rcases hp with ⟨hc, hC, hc₀, hc₀', ha, ha'⟩
  rcases hG with ⟨hcardI, hno, hslots, hdegrees, hrest⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hs : 0 < p.sizeScale q t := hsmin.trans_le hscale
  have hhR : (0 : ℝ) < S.remaining.card := (mul_pos ha hqR).trans_le hh
  have hS : S.remaining.Nonempty := Finset.card_pos.mp (by exact_mod_cast hhR)
  have hP : 0 < p.Pstar := by unfold Parameters.Pstar; positivity
  have hqn : (q : ℝ) ≤ Fintype.card I := by rw [hcardI]; norm_num; nlinarith
  have hm : 0 < p.sizeScale q t * p.c * q - (q : ℝ) ^ ((4 : ℝ) / 5) := by
    have hsc : p.smin * p.c * q ≤ p.sizeScale q t * p.c * q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hc.le) hqR.le
    have hpos : 0 < p.sizeScale q t * p.c * q := by positivity
    linarith
  have hlow (i : I) (hi : i ∈ S.remaining) :
      p.sizeScale q t * p.c * q - (q : ℝ) ^ ((4 : ℝ) / 5) ≤
        ((domain G S i).card : ℝ) := by
    have hinit := mul_le_mul_of_nonneg_left (hslots i).1 hs.le
    have hhL := (abs_le.mp (hL i hi)).1
    nlinarith
  refine ⟨hS, div_nonneg hP.le hqR.le, (div_lt_one hqR).2 halpha, ?_, ?_⟩
  · intro i hi
    constructor
    · exact Finset.card_pos.mp (by exact_mod_cast hm.trans_le (hlow i hi))
    · exact SelectionBarriers.domain_barrier hscale hc hqR he₁ (hslots i).1
        (hL i hi) hsmin
  · intro v hv
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
    calc
      hazard G S v ≤ (degree G S v : ℝ) /
          ((S.remaining.card : ℝ) * (p.sizeScale q t * p.c * q -
            (q : ℝ) ^ ((4 : ℝ) / 5))) := hazard_le_degree_div G S v hS hm hlow
      _ ≤ (p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q +
            (q : ℝ) ^ ((4 : ℝ) / 5)) /
          ((S.remaining.card : ℝ) * (p.sizeScale q t * p.c * q -
            (q : ℝ) ^ ((4 : ℝ) / 5))) :=
        div_le_div_of_nonneg_right hdegree (mul_nonneg hhR.le hm.le)
      _ ≤ (2 * p.C / p.c + 2) / q :=
        SelectionBarriers.hazard_barrier_arithmetic hqR hqn ha hh hsmin hscale hc hC.le he₁ he₂
      _ ≤ p.alpha q := by
        unfold Parameters.alpha Parameters.Pstar
        apply div_le_div_of_nonneg_right _ hqR.le
        exact add_le_add (div_le_div_of_nonneg_right (by linarith) hc.le) (by norm_num)

omit [Fintype I] [Fintype V] in

theorem exists_precheck_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      0 < q ∧ p.Pstar < (q : ℝ) ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
  have hb := SelectionBarriers.eventually_selection_error_budgets (smin := p.smin)
    hp.2.2.2.2.1 (Real.exp_pos _) hp.1
  have hlarge : ∀ᶠ q : ℕ in atTop, p.Pstar < (q : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop p.Pstar)
  have hconditions : ∀ᶠ q : ℕ in atTop,
      0 < q ∧ p.Pstar < (q : ℝ) ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
    filter_upwards [hb, hlarge, eventually_ge_atTop 1] with q hb hl hq
    exact ⟨by omega, hl, hb⟩
  exact eventually_atTop.mp hconditions

end
end Balanced.Selection.Process

end OAI
