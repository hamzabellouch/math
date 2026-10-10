import OAI.Probability.LatticePassage.PositiveMoment
import OAI.Probability.LatticePassage.CoordinatePath
import OAI.Probability.LatticePassage.GeodesicSimple

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

theorem geodesic_tail_split (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (t : ℝ) (ht : 0 ≤ t) :
    environmentLaw.real {ω : Environment | ∃ p : lattice.Walk x y,
      p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
    (2 : ℝ)^(latticeDistance x y) * exp (-t/2) +
      (8/3 : ℝ) * exp (5*t) * (1/2 : ℝ)^R := by
  classical
  obtain ⟨q,hq,hlen⟩ := coordinate_path x y
  let A := {ω : Environment | t ≤ pathCost ω q}
  let B := {ω : Environment | ∃ a ∈ ({x} : Finset Vertex), ∃ b,
    ∃ p : lattice.Walk a b, p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ t}
  have hsub : environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
      p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      environmentLaw (A ∪ B) := by
    apply measure_mono_ae
    filter_upwards [all_edge_weights_positive] with ω hω
    rintro ⟨p,hp,hcost,hl⟩
    by_cases ha : t ≤ pathCost ω q
    · exact Or.inl ha
    · right
      refine ⟨x, Finset.mem_singleton_self x, y, p, hp, hl, ?_⟩
      rw [hcost]
      exact (passageTime_le_pathCost ω (fun e => (hω e).le) q).trans
        (le_of_lt (lt_of_not_ge ha))
  have hsub' := ENNReal.toReal_mono (measure_ne_top _ _) hsub
  change environmentLaw.real _ ≤ environmentLaw.real (A ∪ B) at hsub'
  have ha : environmentLaw.real A ≤ (2 : ℝ)^latticeDistance x y * exp (-t/2) := by
    apply (costly_trail_probability q hq.isTrail t).trans
    gcongr
    norm_num
  have hb : environmentLaw.real B ≤ (8/3 : ℝ) * exp (5*t) * (1/2 : ℝ)^R := by
    simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using
      no_long_cheap_paths {x} R hR t ht
  exact hsub'.trans ((measureReal_union_le A B).trans (add_le_add ha hb))

private lemma tail_numerics (l R : ℕ) (hl : 40*l ≤ R) :
    (2 : ℝ)^l * exp (-((log 2)*R/10)/2) +
      (8/3 : ℝ) * exp (5*((log 2)*R/10)) * (1/2 : ℝ)^R ≤
      (11/3 : ℝ) * exp (-(log 2 / 40) * R) := by
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl' : 40*(l : ℝ) ≤ R := by exact_mod_cast hl
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hp (n : ℕ) : (2 : ℝ)^n = exp ((n : ℝ)*log 2) := by
    rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  have hm (n : ℕ) : (1/2 : ℝ)^n = exp (-((n : ℝ)*log 2)) := by
    rw [exp_neg, ← hp]
    simp [one_div]
  rw [hp, hm]
  have h₁ : exp ((l : ℝ)*log 2) * exp (-((log 2)*R/10)/2) ≤
      exp (-(log 2/40)*R) := by
    rw [← exp_add, exp_le_exp]
    nlinarith
  have h₂ : exp (5*((log 2)*R/10)) * exp (-((R : ℝ)*log 2)) ≤
      exp (-(log 2/40)*R) := by
    rw [← exp_add, exp_le_exp]
    nlinarith
  nlinarith

theorem simple_geodesic_length_tail (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    environmentLaw.real {ω : Environment | ∃ p : lattice.Walk x y,
      p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      (11/3 : ℝ) * exp (-(log 2 / 40) * R) := by
  exact (geodesic_tail_split x y R hR ((log 2)*R/10) (by positivity)).trans
    (tail_numerics (latticeDistance x y) R hscale)

theorem geodesic_length_tail (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    environmentLaw.real {ω : Environment | ∃ p : lattice.Walk x y,
      pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      (11/3 : ℝ) * exp (-(log 2 / 40) * R) := by
  have hsub : environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
      pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
        p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} := by
    apply measure_mono_ae
    filter_upwards [all_minimizing_walks_simple] with ω hω
    rintro ⟨p,hp,hl⟩
    exact ⟨p,hω x y p hp,hp,hl⟩
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
    (simple_geodesic_length_tail x y R hR hscale)

theorem geodesic_length_tail_source : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ z : Vertex, z ≠ (0,0) → ∀ R : ℕ,
      40 * (z.1.natAbs + z.2.natAbs) ≤ R →
      environmentLaw.real {ω : Environment | ∃ p : lattice.Walk (0,0) z,
        pathCost ω p = passageTime ω (0,0) z ∧ R ≤ p.length} ≤
        C * exp (-c * R) := by
  refine ⟨log 2 / 40, 11/3, by positivity, by norm_num, ?_⟩
  intro z hz R hR
  have hl : 0 < z.1.natAbs + z.2.natAbs := by
    by_contra h
    have he : z.1 = 0 ∧ z.2 = 0 := by
      have hn : z.1.natAbs = 0 ∧ z.2.natAbs = 0 := by omega
      simpa only [Int.natAbs_eq_zero] using hn
    exact hz (Prod.ext he.1 he.2)
  exact geodesic_length_tail (0,0) z R (by omega) (by
    simpa only [latticeDistance, sub_zero] using hR)

end CompanionFPP

end OAI
