import OAI.NumberTheory.Ostmann.Construction.PrimeLogLogIntervalMass

namespace OAI

/-! # A rich upper block with finitely many possible scales -/

namespace Ostmann

open scoped BigOperators

/-- The number of density increments depends on the initial density and
subdivision ratio, and is independent of the requested minimum block scale. -/
theorem exists_prime_rich_block {C : ℝ} (hMertens : MertensEstimate C)
    (M : ℕ) (hM : 0 < M) (d : ℝ) (hd : 0 < d) :
    ∃ H : ℕ, ∀ (K : ℕ), 1 ≤ K → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ a : ℝ, max C 0 ≤ a →
      d * (5 * K * (M : ℝ) ^ H) ≤
        weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
          a (a + 5 * K * (M : ℝ) ^ H) →
      ∃ (j : ℕ) (U : ℝ), j ≤ H ∧ a ≤ U ∧
        U + 5 * K * (M : ℝ) ^ j ≤ a + 5 * K * (M : ℝ) ^ H ∧
        ∀ u v : ℝ, U ≤ u → u ≤ v → v ≤ U + 5 * K * (M : ℝ) ^ j →
          4 * (5 * K * (M : ℝ) ^ j / M) ≤ v - u →
          (d / 4) * (v - u) ≤
            weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹) u v := by
  let A := Real.exp 1 + 1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hstep : 0 < d / (4 * M) := by positivity
  obtain ⟨H, hH⟩ := exists_nat_gt ((2 * A - d) / (d / (4 * M)))
  have hdepth : 2 * A < d + H * (d / (4 * M)) := by
    have h := (div_lt_iff₀ hstep).mp hH
    linarith
  refine ⟨H, ?_⟩
  intro K hK P hP a ha hroot
  let L := 5 * (K : ℝ) * (M : ℝ) ^ H
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hL : 0 < L := by dsimp [L]; positivity
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have hroot' : d ≤ (φ (a + L) - φ a) / L := by
    apply (le_div_iff₀ hL).mpr
    rw [weightedCDF_sub _ _ _ a (a + L) (by linarith)]
    exact hroot
  have hupper : ∀ w : List (Fin M), w.length ≤ H → intervalNodeDensity φ a L w ≤ 2 * A := by
    intro w hw
    have hwidth := intervalNode_width_pos hM a L hL w
    have hbound := intervalNode_bounds hM a L hL.le w
    have hwl := intervalNode_width_lower hM a L hL.le H w hw
    have he : L / (M : ℝ) ^ H = 5 * K := by dsimp [L]; field_simp
    rw [he] at hwl
    have hW1 : 1 ≤ (intervalNode a L w).2 := by
      have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    have hm := prime_loglog_interval_mass_upper hMertens P hP
      (intervalNode a L w).1 ((intervalNode a L w).1 + (intervalNode a L w).2)
      (ha.trans hbound.1) (by linarith)
    rw [intervalNodeDensity_weightedCDF hM P _ _ a L hL w]
    apply (div_le_iff₀ hwidth).mpr
    dsimp [A] at *
    nlinarith [Real.exp_pos 1]
  obtain ⟨w, hw, hgood⟩ := exists_rich_interval_node hM H φ a L d (2 * A)
    hL hd hroot' hupper hdepth
  let j := H - w.length
  have hpow : (M : ℝ) ^ H = (M : ℝ) ^ j * (M : ℝ) ^ w.length := by
    rw [← pow_add]
    congr 1
    dsimp [j]
    omega
  have hwidth : (intervalNode a L w).2 = 5 * K * (M : ℝ) ^ j := by
    rw [intervalNode_width hM]
    dsimp [L]
    rw [hpow]
    field_simp
  have hbound := intervalNode_bounds hM a L hL.le w
  refine ⟨j, (intervalNode a L w).1, Nat.sub_le _ _, hbound.1, ?_, ?_⟩
  · simpa only [hwidth] using hbound.2
  · intro u v hu huv hv hlong
    have hh := rich_interval_node_subinterval hM φ hmono a L (d / 2) hL (by positivity)
      w hgood u v hu huv (by rwa [hwidth]) (by rwa [hwidth])
    rw [weightedCDF_sub _ _ _ u v huv] at hh
    convert hh using 1; ring

/-- The selected block comes from the original long prime interval; a
positive-density starting block is constructed by averaging. -/
theorem exists_rich_prime_subblock {C : ℝ} (hMertens : MertensEstimate C)
    (M : ℕ) (hM : 0 < M) (d : ℝ) (hd : 0 < d) :
    ∃ H : ℕ, ∀ (K : ℕ), 1 ≤ K → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ a L : ℝ, max C 0 ≤ a → 0 ≤ L →
      2 * (Real.exp 1 + 1) * (5 * K * (M : ℝ) ^ H + 1) < d * L →
      d * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) a (a + L) →
      ∃ (j : ℕ) (U : ℝ), j ≤ H ∧ a ≤ U ∧
        U + 5 * K * (M : ℝ) ^ j ≤ a + L ∧
        ∀ u v : ℝ, U ≤ u → u ≤ v → v ≤ U + 5 * K * (M : ℝ) ^ j →
          4 * (5 * K * (M : ℝ) ^ j / M) ≤ v - u →
          (d / 8) * (v - u) ≤
            weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹) u v := by
  obtain ⟨H, hH⟩ := exists_prime_rich_block hMertens M hM (d / 2) (by positivity)
  refine ⟨H, ?_⟩
  intro K hK P hP a L ha hL hlarge hroot
  let B := 5 * (K : ℝ) * (M : ℝ) ^ H
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hB : 0 < B := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    dsimp [B]
    positivity
  have hroot' : d * L ≤ φ (a + L) - φ a := by
    rwa [weightedCDF_sub _ _ _ a (a + L) (by linarith)]
  obtain ⟨b, hab, hbL, hb⟩ := exists_dense_fixed_block φ a L B d (Real.exp 1 + 1)
    hL hB hd (by positivity)
    (by
      intro u v hu huv _
      rw [weightedCDF_sub _ _ _ u v huv]
      exact prime_loglog_interval_mass_upper hMertens P hP u v (ha.trans hu) huv)
    hroot' hlarge
  rw [weightedCDF_sub _ _ _ b (b + B) (by linarith)] at hb
  obtain ⟨j, U, hj, hbU, hUb, hgood⟩ := hH K hK P hP b (ha.trans hab) hb
  refine ⟨j, U, hj, hab.trans hbU, hUb.trans hbL, ?_⟩
  intro u v hu huv hv hlen
  have h := hgood u v hu huv hv hlen
  convert h using 1; ring

end Ostmann

end OAI
