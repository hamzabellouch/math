import OAI.Probability.LatticePassage.PathCounting

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

private noncomputable def candidateTrails (n : ℕ) (x : Vertex) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact (startingWalks n x).filter fun q => q.2.IsTrail ∧ q.2.length = n

theorem cheap_fixed_length (n : ℕ) (x : Vertex) (t : ℝ) :
    environmentLaw {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
      p.IsTrail ∧ p.length = n+1 ∧ pathCost ω p ≤ t} ≤
    ((4 * 3^n : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t))) := by
  classical
  let S := candidateTrails (n+1) x
  have hs (q : Σ y : Vertex, lattice.Walk x y) (hq : q ∈ S) :
      q.2.IsTrail ∧ q.2.length = n+1 := (mem_filter.mp hq).2
  have hcard : S.card ≤ 4 * 3^n := (card_filter_le _ _).trans (card_startingWalks n x)
  calc
    _ ≤ environmentLaw (⋃ q ∈ S, {ω : Environment | pathCost ω q.2 ≤ t}) := by
      apply measure_mono
      rintro ω ⟨y,p,hp,hl,hcost⟩
      have hmem : (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ S := by
        apply mem_filter.mpr
        exact ⟨hl ▸ trail_mem_starting p hp, hp, hl⟩
      exact Set.mem_iUnion.mpr ⟨⟨y,p⟩, Set.mem_iUnion.mpr ⟨hmem,hcost⟩⟩
    _ ≤ ∑ q ∈ S, environmentLaw {ω : Environment | pathCost ω q.2 ≤ t} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ S, (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) /
        ENNReal.ofReal (exp (-5 * t))) := by
      apply sum_le_sum
      intro q hq
      simpa only [(hs q hq).2] using cheap_trail_probability q.2 (hs q hq).1 t
    _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) /
        ENNReal.ofReal (exp (-5 * t))) := by simp
    _ ≤ _ := by gcongr

theorem cheap_long_trail_one_start (n : ℕ) (x : Vertex) (t : ℝ) :
    environmentLaw {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
      p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} ≤
    ((4 * 3^n : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t))) := by
  apply le_trans _ (cheap_fixed_length n x t)
  apply measure_mono_ae
  filter_upwards [all_edge_weights_positive] with ω hω
  rintro ⟨y,p,hp,hl,hcost⟩
  have he := p.append_take_drop_eq (n+1)
  have ht : (p.take (n+1)).IsTrail :=
    SimpleGraph.Walk.IsTrail.of_append_left (q := p.drop (n+1)) (by simpa only [he] using hp)
  have hlen : (p.take (n+1)).length = n+1 := by
    rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hl]
  have hcost' : pathCost ω (p.take (n+1)) ≤ pathCost ω p := by
    have hn := pathCost_nonneg ω (fun e => (hω e).le) (p.drop (n+1))
    have hc := congrArg (pathCost ω) he
    rw [pathCost_append] at hc
    linarith
  exact ⟨_, p.take (n+1), ht, hlen, hcost'.trans hcost⟩

theorem no_long_cheap_trails (V : Finset Vertex) (n : ℕ) (t : ℝ) :
    environmentLaw {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} ≤
    (V.card : ℝ≥0∞) * (((4 * 3^n : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t)))) := by
  calc
    _ = environmentLaw (⋃ x ∈ V, {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
        p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t}) := by
      congr 1
      ext ω
      simp
    _ ≤ ∑ x ∈ V, environmentLaw {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
        p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ V, (((4 * 3^n : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t)))) :=
      sum_le_sum (fun x _ => cheap_long_trail_one_start n x t)
    _ = _ := by simp

private lemma count_laplace_identity (n : ℕ) (t : ℝ) :
    ((4 * 3^n : ℕ) : ℝ) * ((1 / 6 : ℝ)^(n+1) / exp (-5 * t)) =
      (4 / 3 : ℝ) * exp (5*t) * (1 / 2 : ℝ)^(n+1) := by
  have hpow : (3 : ℝ)^n * (1 / 6 : ℝ)^n = (1 / 2 : ℝ)^n := by
    rw [← mul_pow]
    norm_num
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [neg_mul, exp_neg, div_eq_mul_inv, inv_inv]
  rw [pow_succ, pow_succ]
  calc
    _ = (4 * (3^n * (1 / 6 : ℝ)^n) * (1 / 6)) * exp (5*t) := by ring
    _ = _ := by rw [hpow]; ring

theorem no_long_cheap_paths (V : Finset Vertex) (R : ℕ) (hR : 1 ≤ R)
    (t : ℝ) (_ht : 0 ≤ t) :
    environmentLaw.real {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ t} ≤
      (8 / 3 : ℝ) * V.card * exp (5*t) * (1 / 2 : ℝ)^R := by
  cases R with
  | zero => omega
  | succ n =>
    have h := (measure_mono (μ := environmentLaw) (show
        {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
          p.IsPath ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} ⊆
        {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
          p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} from by
          rintro ω ⟨x,hx,y,p,hp,hl,hc⟩
          exact ⟨x,hx,y,p,hp.isTrail,hl,hc⟩)).trans (no_long_cheap_trails V n t)
    have hne : ENNReal.ofReal (exp (-5*t)) ≠ 0 := by positivity
    have hfin : (V.card : ℝ≥0∞) * (((4 * 3^n : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 6 : ℝ)^(n+1) / ENNReal.ofReal (exp (-5*t)))) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.div_ne_top (by simp) hne))
    have hr := ENNReal.toReal_mono hfin h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 6),
      ENNReal.toReal_ofReal (exp_pos _).le] at hr
    rw [count_laplace_identity] at hr
    change environmentLaw.real _ ≤ _ at hr
    apply hr.trans
    have hn : (0 : ℝ) ≤ (V.card : ℝ) * exp (5*t) * (1 / 2 : ℝ)^(n+1) := by positivity
    nlinarith

end CompanionFPP

end OAI
