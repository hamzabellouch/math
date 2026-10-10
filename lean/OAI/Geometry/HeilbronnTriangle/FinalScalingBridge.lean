import OAI.Geometry.HeilbronnTriangle.Definitions
import OAI.Geometry.HeilbronnTriangle.FinalScaling
import OAI.Geometry.HeilbronnTriangle.AlterationAsymptotics

namespace OAI


noncomputable section

namespace Problem355

theorem triangleAreasAtLeast_of_scaled
    {P : Finset Point} {n : ℕ} {r : ℝ} (hn : 3 ≤ n) (hr : 64 ≤ r)
    (hsize : (n : ℝ) ≤ Real.rpow r (100000 * (heilbronnK : ℝ)))
    (harea : ∀ p ∈ P, ∀ q ∈ P, ∀ s ∈ P,
      p ≠ q → p ≠ s → q ≠ s →
        r ^ 2 / 64 ≤ (n : ℝ) ^ 2 * triangleArea p q s) :
    triangleAreasAtLeast P (Real.rpow (n : ℝ) (-2 + heilbronnExponent)) := by
  have hK : 0 < (heilbronnK : ℝ) := by
    by_contra h
    have he : 100000 * (heilbronnK : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt h)
    have hp : Real.rpow r (100000 * (heilbronnK : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) he
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  intro p hp q hq s hs hpq hps hqs
  exact scaled_area_implies_heilbronn_power hn0 hr hK hsize
    (harea p hp q hq s hs hpq hps hqs)

theorem heilbronn_power_lower_bound_of_scaled_configurations
    (hconfig : ∀ m : ℕ, ∃ n : ℕ, ∃ P : Finset Point, ∃ r : ℝ,
      m ≤ n ∧ 3 ≤ n ∧ P.card = n ∧ pointsInUnitSquare P ∧
      64 ≤ r ∧ (n : ℝ) ≤ Real.rpow r (100000 * (heilbronnK : ℝ)) ∧
      (∀ p ∈ P, ∀ q ∈ P, ∀ s ∈ P,
        p ≠ q → p ≠ s → q ≠ s →
          r ^ 2 / 64 ≤ (n : ℝ) ^ 2 * triangleArea p q s)) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨n₀, P₀, r₀, _, hn₀, _, _, hr₀, hsize₀, _⟩ := hconfig 0
  have hK : 0 < (heilbronnK : ℝ) := by
    by_contra h
    have he : 100000 * (heilbronnK : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt h)
    have hp : Real.rpow r₀ (100000 * (heilbronnK : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) he
    have hn' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith
  refine ⟨one_div_pos.mpr (mul_pos (by norm_num) hK), ?_⟩
  choose n P r hlarge hthree hcard hsquare hr hsize harea using hconfig
  refine ⟨n, P, Filter.tendsto_atTop_mono hlarge Filter.tendsto_id, ?_⟩
  intro j
  refine ⟨hthree j, hcard j, hsquare j, ?_⟩
  exact triangleAreasAtLeast_of_scaled (hthree j) (hr j) (hsize j) (harea j)

theorem heilbronn_power_lower_bound_of_floor_configurations
    (r N τ : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hscale : ∀ᶠ j in Filter.atTop, 0 < N j ∧ 0 < τ j ∧ τ j ≤ (N j) ^ 3)
    (hsize : ∀ᶠ j in Filter.atTop,
      (⌊r j * Real.sqrt ((N j) ^ 3 / τ j)⌋₊ : ℝ) ≤
        Real.rpow (r j) (100000 * (heilbronnK : ℝ)))
    (hconfig : ∀ᶠ j in Filter.atTop, ∃ P : Finset Point,
      P.card = ⌊r j * Real.sqrt ((N j) ^ 3 / τ j)⌋₊ ∧
      pointsInUnitSquare P ∧ triangleAreasAtLeast P (τ j / (16 * (N j) ^ 3))) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  have ha : Filter.Tendsto (fun j => r j * Real.sqrt ((N j) ^ 3 / τ j))
      Filter.atTop Filter.atTop := tendsto_real_sample_atTop hr (hscale.mono fun _ hj => hj.2)
  obtain ⟨hn, hfloor⟩ := floor_sample_properties ha
  apply heilbronn_power_lower_bound_of_scaled_configurations
  intro m
  have hevent := (hn.eventually_ge_atTop m).and
    (hfloor.and ((hr.eventually_ge_atTop 64).and (hscale.and (hsize.and hconfig))))
  obtain ⟨j, hm, ⟨hthree, hhalf⟩, hr64, ⟨hN, hτ, hτN⟩, hbound, P, hcard,
      hsquare, harea⟩ := hevent.exists
  refine ⟨⌊r j * Real.sqrt ((N j) ^ 3 / τ j)⌋₊, P, r j,
    hm, hthree, hcard, hsquare, hr64, hbound, ?_⟩
  intro p hp q hq s hs hpq hps hqs
  exact sample_size_scaled_area (by linarith) hN hτ hhalf
    (harea p hp q hq s hs hpq hps hqs)

end Problem355

end

end OAI
