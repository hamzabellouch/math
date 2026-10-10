import OAI.Combinatorics.BalancedRyser.Selection.SelectionCensorMassBounds
import OAI.Combinatorics.BalancedRyser.Selection.SelectionConcentrationAsymptotics

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

def sourceDegreeCensorBound (p : Parameters) (q : ℕ) : ℝ :=
  2 * (q : ℝ) ^ (1 / 8 : ℝ) /
    (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q

theorem postcheckTail_nonneg_of_admissible {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 ≤ postcheckTail p q := by
  have hP := Parameters.Pstar_pos hp
  have hC := hp.2.1
  unfold postcheckTail postcheckMean
  positivity

theorem sourceDegreeCensorBound_nonneg {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 ≤ sourceDegreeCensorBound p q := by
  have he := postcheckTail_nonneg_of_admissible hp q
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hc := hp.1
  unfold sourceDegreeCensorBound
  positivity

theorem eventually_small_power_error (A B : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      A * (q : ℝ) ^ (1 / 8 : ℝ) + B ≤ (q : ℝ) ^ (4 / 5 : ℝ) / 2 := by
  have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 27 / 40)).comp
    tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun q : ℕ => A * (q : ℝ) ^ (-(27 / 40 : ℝ)) +
      B * (q : ℝ) ^ (-(4 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa using (h₁.const_mul A).add (h₂.const_mul B)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (0 : ℕ)] with q hq hqpos
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hp : 0 < (q : ℝ) ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hqr _
  have he : (A * (q : ℝ) ^ (1 / 8 : ℝ) + B) / (q : ℝ) ^ (4 / 5 : ℝ) =
      A * (q : ℝ) ^ (-(27 / 40 : ℝ)) + B * (q : ℝ) ^ (-(4 / 5 : ℝ)) := by
    rw [add_div, mul_div_assoc, ← Real.rpow_sub hqr]
    norm_num
    rw [Real.rpow_neg hqr.le, div_eq_mul_inv]
  have hdiv : (A * (q : ℝ) ^ (1 / 8 : ℝ) + B) / (q : ℝ) ^ (4 / 5 : ℝ) ≤ 1 / 2 :=
    he.trans_le hq.le
  have h := (div_le_iff₀ hp).mp hdiv
  linarith

theorem tendsto_domain_drift_budget {p : Parameters} (hp : p.Admissible) :
    Tendsto (fun q : ℕ => (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin))
      atTop (𝓝 0) := by
  convert (tendsto_polynomial_mul_postcheckTail p hp 2).const_mul (3 / p.smin) using 1
  · funext q
    ring
  · simp

theorem eventually_source_drift_budgets {p : Parameters} (hp : p.Admissible) :
    ∀ᶠ q : ℕ in atTop,
      (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 ∧
      (3 * (q : ℝ)) * (p.C * q * sourceDegreeCensorBound p q / (p.smin * p.a / 3)) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 := by
  let b := p.smin * p.a / 3
  let A := 6 * p.C / (p.a * p.smin * p.c * b)
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hc := hp.1
  have hb : 0 < b := by dsimp [b]; positivity
  have htail : Tendsto (fun q : ℕ => (3 * p.C / b) * ((q : ℝ) ^ 2 * postcheckTail p q))
      atTop (𝓝 0) := by
    simpa using (tendsto_polynomial_mul_postcheckTail p hp 2).const_mul (3 * p.C / b)
  filter_upwards [(tendsto_domain_drift_budget hp).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_small_power_error 0 1, eventually_small_power_error A 1,
    eventually_gt_atTop (0 : ℕ)] with q hd ht hsmall hlarge hq
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  constructor
  · exact hd.le.trans (by simpa using hsmall)
  · have he : (3 * (q : ℝ)) *
        (p.C * q * sourceDegreeCensorBound p q / (p.smin * p.a / 3)) =
        A * (q : ℝ) ^ (1 / 8 : ℝ) +
          (3 * p.C / b) * ((q : ℝ) ^ 2 * postcheckTail p q) := by
        dsimp [sourceDegreeCensorBound, A, b]
        field_simp
        ring
    rw [he]
    linarith

theorem card_vertices_le_slots_mul_order {q : ℕ} {G : Input I V}
    {c C : ℝ} (hG : GraphBounds G q c C) : Fintype.card V ≤ Fintype.card I * q := by
  classical
  have he : Fintype.card V = ∑ i : I, (slotVertices G i).card := by
    simpa only [Finset.card_univ, slotVertices] using
      (Finset.card_eq_sum_card_fiberwise (f := G.slot)
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _))
  rw [he]
  calc
    _ ≤ ∑ _i : I, q := Finset.sum_le_sum (fun i _ => (hG.2.2.1 i).2)
    _ = _ := by simp

theorem source_track_tail_sum_le_error {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hT : 1 ≤ T) (hTq : T ≤ 3 * q) :
    2 * Fintype.card I * (T + 1 : ℕ) *
        Real.exp (-((q : ℝ) ^ (4 / 5 : ℝ) / 2) ^ 2 /
          (8 * (T : ℝ) * (domainTrackJumpBound p q) ^ 2)) +
      2 * Fintype.card V * (T + 1 : ℕ) *
        Real.exp (-((q : ℝ) ^ (4 / 5 : ℝ) / 2) ^ 2 /
          (8 * (T : ℝ) * (degreeTrackJumpBound p q) ^ 2)) ≤
      trackConcentrationError p q := by
  let E := Real.exp (-((q : ℝ) ^ (7 / 20 : ℝ) /
    (96 * (trackJumpCoefficient p) ^ 2)))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hdom := source_azuma_exp_le (by omega : 0 < q) hT hTq
    (domainTrackJumpBound_pos hp q) (trackJumpCoefficient_pos hp)
    (trackJumpBounds_le hp (by omega : 1 ≤ q)).1
  have hdeg := source_azuma_exp_le (by omega : 0 < q) hT hTq
    (degreeTrackJumpBound_pos hp q) (trackJumpCoefficient_pos hp)
    (trackJumpBounds_le hp (by omega : 1 ≤ q)).2
  have hn : (Fintype.card I : ℝ) ≤ 3 * q := by
    exact_mod_cast (show Fintype.card I ≤ 3 * q by rw [hG.1]; omega)
  have hm : (Fintype.card V : ℝ) ≤ 3 * (q : ℝ) ^ 2 := by
    have h := card_vertices_le_slots_mul_order hG
    have hnN : Fintype.card I ≤ 3 * q := by rw [hG.1]; omega
    have h' := h.trans (Nat.mul_le_mul_right q hnN)
    exact_mod_cast (by simpa [pow_two, Nat.mul_assoc] using h')
  have ht : ((T + 1 : ℕ) : ℝ) ≤ 4 * q := by
    exact_mod_cast (show T + 1 ≤ 4 * q by omega)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hc : 2 * (Fintype.card I : ℝ) * (T + 1 : ℕ) +
      2 * (Fintype.card V : ℝ) * (T + 1 : ℕ) ≤ 48 * (q : ℝ) ^ 3 := by
    calc
      _ ≤ 2 * (3 * (q : ℝ)) * (4 * q) +
          2 * (3 * (q : ℝ) ^ 2) * (4 * q) := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (q : ℝ),
        mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hqR)]
  calc
    _ ≤ (2 * (Fintype.card I : ℝ) * (T + 1 : ℕ) +
        2 * (Fintype.card V : ℝ) * (T + 1 : ℕ)) * E := by
      rw [add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdom (by positivity))
        (mul_le_mul_of_nonneg_left hdeg (by positivity))
    _ ≤ 48 * (q : ℝ) ^ 3 * E := mul_le_mul_of_nonneg_right hc hE
    _ = _ := rfl

theorem source_true_count_failure_probability_le {p : Parameters} (hp : p.Admissible)
    {q : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hDd : (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin) ≤
      (q : ℝ) ^ (4 / 5 : ℝ) / 2)
    (hDv : (3 * (q : ℝ)) * (p.C * q * sourceDegreeCensorBound p q /
      (p.smin * p.a / 3)) ≤ (q : ℝ) ^ (4 / 5 : ℝ) / 2) :
    (snapshotPathLaw p q G).real {ω | ¬ (∀ t S,
      t ≤ p.lastMainTime q (Fintype.card I) → (ω t).1 = some S →
      (∀ i ∈ S.remaining,
        |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤
          (q : ℝ) ^ (4 / 5 : ℝ)) ∧
      (∀ v ∈ currentVertices G S, (degree G S v : ℝ) ≤
        p.degreeScale q (Fintype.card I) t * degree G initialState v +
          (q : ℝ) ^ (4 / 5 : ℝ)))} ≤ trackConcentrationError p q := by
  let T := p.lastMainTime q (Fintype.card I)
  have hTq : T ≤ 3 * q := by
    exact (Nat.sub_le _ _).trans (by rw [hG.1]; omega)
  have hTpos : 1 ≤ T := by
    have hh := Parameters.tailSlots_le_order hp q
    dsimp [T, Parameters.lastMainTime]
    rw [hG.1]
    omega
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hb : 0 < p.smin * p.a / 3 := by positivity
  have he := postcheckTail_nonneg_of_admissible hp q
  have hev := sourceDegreeCensorBound_nonneg hp q
  apply (true_count_failure_probability_le hp hG hq hPq hTpos le_rfl he hev
    (fun i j _ S hpre _ => domainOverflowMass_le_postcheckTail p q j (by omega) G hG S hpre i)
    (fun v j hj S hpre hcard _ => degreeCensorMass_le_source p hp q j hq hPq G hG
      (by omega) S hpre (by have hn := Nat.sub_le (Fintype.card I) (p.tailSlots q); dsimp [T, Parameters.lastMainTime] at hj; omega) v)
    ((q : ℝ) ^ (4 / 5 : ℝ) / 2) ((q : ℝ) ^ (4 / 5 : ℝ))
    (by positivity) (by positivity) ?_ ?_).trans
      (source_track_tail_sum_le_error hp hG hq hTpos hTq)
  · intro t ht
    have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht.trans hTq
    have hh := (mul_le_mul_of_nonneg_right htR (div_nonneg
      (mul_nonneg (Nat.cast_nonneg q) he) hs.le)).trans hDd
    linarith
  · intro t ht
    have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht.trans hTq
    have hh := (mul_le_mul_of_nonneg_right htR (div_nonneg
      (mul_nonneg (mul_nonneg hp.2.1.le (Nat.cast_nonneg q)) hev) hb.le)).trans hDv
    linarith

theorem exists_source_concentration_threshold {p : Parameters} (hp : p.Admissible) :
    ∃ Q : ℕ, ∀ q ≥ Q,
      2 ≤ q ∧ 2 * p.Pstar ≤ q ∧
      (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 ∧
      (3 * (q : ℝ)) * (p.C * q * sourceDegreeCensorBound p q / (p.smin * p.a / 3)) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 := by
  apply Filter.eventually_atTop.1
  filter_upwards [Parameters.eventually_scale_regime p,
    eventually_source_drift_budgets hp] with q hq hd
  exact ⟨hq.1, hq.2, hd.1, hd.2⟩

end Balanced.Selection.Process

end

end OAI
