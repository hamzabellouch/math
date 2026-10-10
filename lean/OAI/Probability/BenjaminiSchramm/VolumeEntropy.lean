import OAI.Probability.BenjaminiSchramm.ProbabilityUpper

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem inverse_sqrt_div_min_bound (a s : ℝ) (ha : 0 < a) (hs : 1 ≤ s) :
    (1 / s ^ 2) / min a (1/s) ≤ (1 + 1/a) / s := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rcases le_total a (1/s) with h | h
  · rw [min_eq_left h]
    apply (div_le_iff₀ ha).mpr
    have hinv : 1/s^2 ≤ 1/s := by
      apply one_div_le_one_div_of_le hs0
      nlinarith
    have he : (1 + 1/a) / s * a = (a+1)/s := by field_simp
    rw [he]
    exact hinv.trans (div_le_div_of_nonneg_right (by linarith) hs0.le)
  · rw [min_eq_right h]
    have he : (1/s^2)/(1/s) = 1/s := by field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ hs0.le
    exact le_add_of_nonneg_right (one_div_nonneg.mpr ha.le)

theorem critical_volume_upper_of_susceptibility_upper
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hpc1 : (pc G : ℝ) < 1) (A : ℝ) (hA : 0 < A)
    (hχ : ∀ p : unitInterval, p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x n, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n := by
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  obtain ⟨d,_hd,hdeg⟩ := exists_degree_bound G hqt
  let D : ℝ := (pc G : ℝ) * (1-pc G)
  have hD : 0 < D := by dsimp [D]; positivity
  let L : ℝ := 2 + 2 * (d : ℝ) / D
  have hL : 0 < L := by dsimp [L]; positivity
  let a : ℝ := (pc G : ℝ) / 2
  have ha : 0 < a := half_pos hpc0
  let C : ℝ := 1 + 2 * L * A * (1 + 1/a)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun x n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnR
  have hs0 : 0 < Real.sqrt n := lt_of_lt_of_le zero_lt_one hs
  by_cases hn1 : n = 1
  · subst n
    norm_num only [Nat.cast_one]
    change (law (pc G)).real (volumeEvent G x 1) ≤ C / 1
    rw [div_one]
    apply (measureReal_le_one).trans
    have hc0 : 0 ≤ 2 * L * A * (1 + 1/a) := by positivity
    dsimp only [C]
    linarith
  have hn2 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  let δ : ℝ := min a (1 / Real.sqrt n)
  have hδ : 0 < δ := lt_min ha (one_div_pos.mpr hs0)
  have hδa : δ ≤ a := min_le_left _ _
  have hδs : δ ≤ 1 / Real.sqrt n := min_le_right _ _
  let p : unitInterval := ⟨(pc G : ℝ) - δ,⟨by dsimp [a] at hδa; linarith,
    by linarith [(pc G).2.2]⟩⟩
  have hp : p < pc G := by change (pc G : ℝ)-δ < pc G; linarith
  have hp0 : 0 < (p : ℝ) := by
    change 0 < (pc G : ℝ)-δ
    dsimp only [a] at hδa
    linarith
  have hp1 : (p : ℝ) < 1 := lt_trans hp hpc1
  let h : unitInterval := ⟨1 / (n : ℝ),⟨by positivity,
    (div_le_one (by positivity : 0 < (n : ℝ))).mpr hnR⟩⟩
  have hh : (h : ℝ) ∈ Set.Ioo 0 1 := ⟨by dsimp [h]; positivity,
    (div_lt_one (by positivity : 0 < (n : ℝ))).mpr hn2⟩
  have hsq : ((p : ℝ) - pc G) ^ 2 ≤ h := by
    have he := (sq_le_sq₀ hδ.le (one_div_pos.mpr hs0).le).mpr hδs
    have hs2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    change ((pc G : ℝ)-δ-pc G)^2 ≤ 1/(n : ℝ)
    have hi : (1 / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
      rw [div_pow,one_pow,hs2]
    rw [hi] at he
    nlinarith
  have hbound (Q : Finset E) : markedConnectionPolynomial G Q x h (pc G) ≤
      L * A * (1 + 1/a) / Real.sqrt n := by
    have ht := markedConnection_entropy_uniform G Q x p (pc G) h ⟨hp0,hp1⟩
      ⟨hpc0,hpc1⟩ hh d
      (fun z => (incident_filter_card_le_degree G hloc Q z).trans (hdeg z))
      D hD le_rfl hsq
    have hb := (markedConnection_le_susceptibility G hloc hqt Q x h p hp).trans
      (mul_le_mul_of_nonneg_left (hχ p hp x) h.2.1)
    change _ ≤ L * markedConnectionPolynomial G Q x h p at ht
    apply (ht.trans (mul_le_mul_of_nonneg_left hb hL.le)).trans
    have he : (h : ℝ) * (A / ((pc G : ℝ) - p)) = A * ((1/(Real.sqrt n)^2)/δ) := by
      dsimp [h,p]
      rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
      ring
    rw [he]
    have hi := mul_le_mul_of_nonneg_left
      (inverse_sqrt_div_min_bound a (Real.sqrt n) ha hs) (mul_nonneg hL.le hA.le)
    dsimp only [δ]
    convert hi using 1 <;> ring
  have hvol := volume_probability_le_of_finite_tails G x n (pc G)
    (2 * (L * A * (1 + 1/a) / Real.sqrt n)) (fun Q =>
      (finiteClusterTail_le_markedConnection G Q x n (pc G) h
        (by change 1 ≤ 1/(n : ℝ)*n; rw [div_mul_cancel₀ _ (by positivity)])).trans
      (mul_le_mul_of_nonneg_left (hbound Q) (by norm_num : (0 : ℝ) ≤ 2)))
  change (law (pc G)).real (volumeEvent G x n) ≤ C / Real.sqrt n
  apply hvol.trans
  dsimp [C]
  have hi : 0 ≤ 1 / Real.sqrt n := (one_div_pos.mpr hs0).le
  have he : (1 + 2 * L * A * (1 + 1/a)) / Real.sqrt n =
      1 / Real.sqrt n + 2 * (L * A * (1 + 1/a) / Real.sqrt n) := by ring
  rw [he]
  exact le_add_of_nonneg_left hi

end Percolation.BenjaminiSchramm

end OAI
