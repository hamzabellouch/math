import OAI.NumberTheory.PiExponent.Statement

namespace OAI

namespace PiExponent

 theorem eventualLowerBound_iff_integer (x : ℝ) :
    EventualLowerBound x ↔ IntegerEventualLowerBound x := by
  unfold EventualLowerBound IntegerEventualLowerBound
  constructor
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    refine ⟨Q, by exact_mod_cast hQ, ?_⟩
    intro p q hq
    have hq0 : 0 ≤ q := le_trans (by omega) hq
    have hnat : Q ≤ q.toNat := by omega
    have heq : (q.toNat : ℝ) = (q : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hq0)
    simpa only [heq] using hb p q.toNat hnat
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    have hQ0 : 0 ≤ Q := by omega
    refine ⟨Q.toNat, by omega, ?_⟩
    intro p q hq
    have hqi : Q ≤ (q : ℤ) := by omega
    simpa using hb p q hqi

theorem finite_rat_den_le_abs_sub_lt_one (x : ℝ) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1}.Finite := by
  classical
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective f := by
    intro a b hab
    have hp := Prod.mk.inj hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hp.1, hp.2]
  let t : Set (ℤ × ℕ) := ⋃ (q : ℕ) (_ : q ∈ Set.Icc 1 N),
    Set.Icc ⌈(x - 1) * q⌉ ⌊(x + 1) * q⌋ ×ˢ {q}
  have ht : t.Finite :=
    Set.Finite.biUnion (Set.finite_Icc _ _) fun q _ =>
      Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_singleton _)
  have hsub : f '' {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1} ⊆ t := by
    rintro _ ⟨r, ⟨hrN, hr⟩, rfl⟩
    have hrden : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
    have hrlow : x - 1 < (r : ℝ) := by linarith [(abs_lt.mp hr).2]
    have hrhigh : (r : ℝ) < x + 1 := by linarith [(abs_lt.mp hr).1]
    have hnlow : (x - 1) * r.den ≤ (r.num : ℝ) := by
      rw [Rat.cast_def] at hrlow
      exact ((lt_div_iff₀ hrden).mp hrlow).le
    have hnhigh : (r.num : ℝ) ≤ (x + 1) * r.den := by
      rw [Rat.cast_def] at hrhigh
      exact ((div_lt_iff₀ hrden).mp hrhigh).le
    simp only [t, Set.mem_iUnion]
    refine ⟨r.den, ⟨r.pos, hrN⟩, ?_⟩
    exact ⟨⟨Int.ceil_le.mpr hnlow, Int.le_floor.mpr hnhigh⟩, rfl⟩
  exact (ht.subset hsub).of_finite_image hinj.injOn

theorem two_mem_approximationExponents {x : ℝ} (hx : Irrational x) :
    (2 : ℝ) ∈ ApproximationExponents x := by
  refine ⟨by norm_num, ?_⟩
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hf := finite_rat_den_le_abs_sub_lt_one x 1
  apply (hi.sdiff hf).mono
  intro r hr
  have hrden : 1 ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hrone : |x - (r : ℝ)| < 1 :=
    hr.1.trans_le (by
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by nlinarith : (1 : ℝ) ≤ (r.den : ℝ)^2))
  have hr2 : 2 ≤ r.den := by
    by_contra h
    exact hr.2 ⟨by omega, hrone⟩
  refine ⟨hr2, abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r)), ?_⟩
  simpa only [Set.mem_ofPred_eq, Real.rpow_neg (Nat.cast_nonneg r.den),
    Real.rpow_two, one_div] using hr.1

theorem finite_goodRationalApproximations_of_eventualLowerBound {x ν : ℝ}
    (hx : EventualLowerBound x) (hν : 2 < ν) :
    (GoodRationalApproximations x ν).Finite := by
  obtain ⟨Q, hQ, hb⟩ := hx ν hν
  apply (finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hltQ : r.den < Q := by
    by_contra h
    have h := hb r.num r.den (by omega)
    rw [← Rat.cast_def] at h
    exact (not_lt_of_ge h) hr.2.2
  refine ⟨hltQ.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast r.pos) (by linarith)

theorem irrationalityExponent_eq_two_of_eventualLowerBound {x : ℝ}
    (hi : Irrational x) (hx : EventualLowerBound x) :
    irrationalityExponent x = 2 := by
  have htwo := two_mem_approximationExponents hi
  have hbound : ∀ ν ∈ ApproximationExponents x, ν ≤ 2 := by
    intro ν hν
    by_contra h
    exact (finite_goodRationalApproximations_of_eventualLowerBound hx (by linarith)).not_infinite hν.2
  apply le_antisymm
  · exact csSup_le ⟨2, htwo⟩ hbound
  · exact le_csSup ⟨2, hbound⟩ htwo

theorem pi_irrationalityExponent_eq_two_of_eventualLowerBound
    (h : PiEventualLowerBound) : irrationalityExponent Real.pi = 2 :=
  irrationalityExponent_eq_two_of_eventualLowerBound irrational_pi h

theorem eventualLowerBound_of_not_unbounded_approximations {x : ℝ}
    (h : ∀ ν : ℝ, 2 < ν →
      ¬ ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ), Q ≤ q ∧
        |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) :
    EventualLowerBound x := by
  intro ν hν
  have hbad := h ν hν
  push Not at hbad
  obtain ⟨Q, hQ⟩ := hbad
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  intro p q hq
  exact (hQ p q ((le_max_left Q 2).trans hq)).le

end PiExponent

end OAI
