import OAI.Probability.BenjaminiSchramm.GhostEntropy

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_entropy_uniform
    (G : BondGraph V E) (Q : Finset E) (x : V) (p q h : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) (hq : (q : ℝ) ∈ Set.Ioo 0 1)
    (hh : (h : ℝ) ∈ Set.Ioo 0 1) (d : ℕ)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (D : ℝ) (hD : 0 < D) (hden : D ≤ (q : ℝ) * (1-q))
    (hsmall : ((p : ℝ) - q) ^ 2 ≤ h) :
    markedConnectionPolynomial G Q x h q ≤
      (2 + 2 * (d : ℝ) / D) * markedConnectionPolynomial G Q x h p := by
  apply (markedConnection_entropy_comparison G Q x p q h hp hq hh d hdeg).trans
  apply mul_le_mul_of_nonneg_right _ (by
    rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg p h _)
  apply add_le_add_right
  have hd : 0 ≤ 2 * (d : ℝ) := by positivity
  have hden0 : 0 < (q : ℝ) * (1-q) := hD.trans_le hden
  calc
    2 * (d : ℝ) * ((p : ℝ) - q) ^ 2 / ((q : ℝ) * (1-q) * h) ≤
        2 * (d : ℝ) * h / ((q : ℝ) * (1-q) * h) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hd)
        (mul_nonneg hden0.le hh.1.le)
    _ = 2 * (d : ℝ) / ((q : ℝ) * (1-q)) := by field_simp [hh.1.ne']
    _ ≤ 2 * (d : ℝ) / D := div_le_div_of_nonneg_left hd hD hden

theorem percolationProbability_upper_of_uniform_critical_volume [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hpc1 : (pc G : ℝ) < 1)
    (C : ℝ) (hC : 0 < C)
    (hvolume : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧ ∀ p : unitInterval, pc G < p →
      (p : ℝ) - pc G < η → ∀ x,
      percolationProbability G p x ≤ A * ((p : ℝ) - pc G) := by
  obtain ⟨d,_hd,hdeg⟩ := exists_degree_bound G hqt
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  let D : ℝ := (pc G : ℝ) * (1-pc G) / 2
  have hD : 0 < D := by dsimp [D]; positivity
  let L : ℝ := 2 + 2 * (d : ℝ) / D
  have hL : 0 < L := by dsimp [L]; positivity
  let η : ℝ := min (1/4) ((1-pc G)/2)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  refine ⟨12 * L * C,η,by positivity,hη,fun p hp hnear x => ?_⟩
  let δ : ℝ := (p : ℝ) - pc G
  have hδ : 0 < δ := sub_pos.mpr hp
  have hδsmall : δ < 1/4 := hnear.trans_le (min_le_left _ _)
  have hδnear : δ < (1-pc G)/2 := hnear.trans_le (min_le_right _ _)
  have hp1 : (p : ℝ) < 1 := by dsimp [δ] at hδnear; linarith
  have hp0 : 0 < (p : ℝ) := hpc0.trans hp
  have hden : D ≤ (p : ℝ) * (1-p) := by
    have ht : (1-(pc G : ℝ))/2 ≤ 1-(p : ℝ) := by dsimp [δ] at hδnear; linarith
    have hm := mul_le_mul (show (pc G : ℝ) ≤ p from hp.le) ht
      (by positivity : 0 ≤ (1-(pc G : ℝ))/2) hp0.le
    dsimp [D]
    nlinarith
  let h : unitInterval := ⟨δ ^ 2,⟨sq_nonneg _,by nlinarith⟩⟩
  have hh : (h : ℝ) ∈ Set.Ioo 0 1 := ⟨sq_pos_of_pos hδ,by dsimp [h]; nlinarith⟩
  let m : ℕ := ⌊1/δ⌋₊
  have hm1 : 1 ≤ m := (Nat.le_floor_iff (one_div_pos.mpr hδ).le).mpr
    ((le_div_iff₀ hδ).mpr (by norm_num only [Nat.cast_one,one_mul]; linarith))
  have hm : 0 < m := hm1
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hfloor : (m : ℝ) ≤ 1/δ := Nat.floor_le (one_div_pos.mpr hδ).le
  have hδm : δ * m ≤ 1 := by
    have hh := (le_div_iff₀ hδ).mp hfloor
    nlinarith
  have hscale : (h : ℝ) * (m : ℝ) ^ 2 ≤ 1 := by
    dsimp [h]
    have hh := (sq_le_sq₀ (mul_nonneg hδ.le hmR.le) zero_le_one).mpr hδm
    nlinarith
  have hfloor' : 1/δ < (m : ℝ) + 1 := Nat.lt_floor_add_one (1/δ)
  have hinv : 1 / (m : ℝ) ≤ 2 * δ := by
    have hmR1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hh := (div_lt_iff₀ hδ).mp hfloor'
    apply (div_le_iff₀ hmR).mpr
    nlinarith
  have hghost (Q : Finset E) : markedConnectionPolynomial G Q x h p ≤ 6 * L * C * δ := by
    have hc := critical_ghost_bound_at_square_scale G C hC.le hvolume Q x (pc G) h
      le_rfl m hm hscale
    have ht := markedConnection_entropy_uniform G Q x (pc G) p h ⟨hpc0,hpc1⟩ ⟨hp0,hp1⟩
      hh d (fun z => (incident_filter_card_le_degree G hloc Q z).trans (hdeg z))
      D hD hden (by dsimp [h,δ]; nlinarith)
    change _ ≤ L * markedConnectionPolynomial G Q x h (pc G) at ht
    have hb := ht.trans (mul_le_mul_of_nonneg_left hc hL.le)
    have hi := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 3 * L * C by positivity)
    have he : L * (3 * C / (m : ℝ)) = (3 * L * C) * (1/m) := by ring
    rw [he] at hb
    nlinarith
  have hθ := percolationProbability_le_of_marked_bounds G x p h hh.1 (6 * L * C * δ) hghost
  dsimp [δ] at hθ
  nlinarith

theorem percolationProbability_upper_of_critical_volume [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hpc1 : (pc G : ℝ) < 1)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧ ∀ p : unitInterval, pc G < p →
      (p : ℝ) - pc G < η → ∀ x,
      percolationProbability G p x ≤ A * ((p : ℝ) - pc G) := by
  obtain ⟨C,hC,hvolume⟩ := uniform_critical_volume_upper_of_powerTail G hqt hvol
  exact percolationProbability_upper_of_uniform_critical_volume G hloc hqt hpc1 C hC hvolume

end Percolation.BenjaminiSchramm

end OAI
