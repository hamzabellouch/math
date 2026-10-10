import OAI.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_six_variable_patch_expansion (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N P : ℕ} [NeZero N] [NeZero P] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (P : ℝ) ≤ Real.exp p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ f : (Fin 6 → ℤ) → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      (∀ y : Fin 6 → ℤ, (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
        ∃ F : (Fin 6 → ℤ) → ℂ,
          Nonempty (NativeIntegerExpansion (fun _ : Fin 6 => 1) s p F) ∧
          (∀ x, ‖F x‖ ≤ 1) ∧
          ∀ (x : Fin 6 → ℤ) (δ : ℝ), 0 ≤ δ →
            (∀ k, |(x k : ℝ)| ≤ (N : ℝ)) → (∀ k, (P : ℤ) ∣ x k - y k) →
            (∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ (N : ℝ) * δ) →
            ‖f x - F x‖ ≤ Real.exp p * δ) →
      ∃ F : (Fin 6 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 6 => 1) s ((p + C) ^ C) F) ∧
        (∀ x : Fin 6 → ZMod N, ‖F (fun k => ((x k).val : ℤ))‖ ≤ 1) ∧
        (𝔼 x : Fin 6 → ZMod N,
          ‖f (fun k => ((x k).val : ℤ)) - F (fun k => ((x k).val : ℤ))‖) ≤
            Real.exp (p + 110) * (ρ + 1 / N) := by
  obtain ⟨A, _, hpartition⟩ := exists_interval_residue_partition a
  obtain ⟨B, _, hweighted⟩ := exists_positive_weighted_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := 6 * Q + X + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B + R)
  refine ⟨C, hC, ?_⟩
  intro s N P _ _ p ρ hs hp hP hρ hprec f hf hlocal
  classical
  obtain ⟨n, _hn, hcard, ψ, hψ, hsum, hdiam⟩ := hpartition N P hp hP hρ hprec
  let J := Fin 6 → Fin n × ZMod P
  let v := fun (x : Fin 6 → ZMod N) (k : Fin 6) => ((x k).val : ℤ)
  have hv (x : Fin 6 → ZMod N) (k : Fin 6) : |(v x k : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x k).val))]
    exact Nat.cast_le.mpr (x k).val_lt.le
  let w := productPartitionWeight (fun _ : Fin 6 => ψ)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ k j x, 0 ≤ (fun _ : Fin 6 => ψ) k j x :=
    fun _ j x => ((hψ j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hchoose (j : J) : ∃ y : Fin 6 → ZMod N,
      ∀ x, (∀ k, x k ∉ E) → 0 < w j x → (∀ k, y k ∉ E) ∧ 0 < w j y := by
    by_cases h : ∃ y, (∀ k, y k ∉ E) ∧ 0 < w j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hwx => False.elim (h ⟨x, hx, hwx⟩)⟩
  choose y hy using hchoose
  choose S hS hSnorm hSlocal using fun j => hlocal (v (y j)) (hv (y j))
  have hgood (j : J) (x : Fin 6 → ZMod N)
      (hx : x ∉ coordinateExceptional E) (hwx : 0 < w j x) :
      ‖f (v x) - S j (v x)‖ ≤ Real.exp p * ρ := by
    have hx' := (not_mem_coordinateExceptional E x).mp hx
    obtain ⟨hy', hwy⟩ := hy j x hx' hwx
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j (y j) hwy
    apply hSlocal j (v x) ρ hρ.le (hv x)
    · intro k
      exact (hdiam (j k) (x k) (y j k) (hx' k) (hy' k) (hposx k) (hposy k)).2
    · intro k
      simpa only [v, Int.cast_natCast] using
        (hdiam (j k) (x k) (y j k) (hx' k) (hy' k) (hposx k) (hposy k)).1
  have herr := complex_partition_approximation_mean_error (coordinateExceptional E)
    w (fun j x => S j (v x)) (fun x => f (v x))
    (mul_nonneg (Real.exp_nonneg p) hρ.le) hw hwSum
    (fun j x => hSnorm j (v x)) (fun x => hf (v x)) hgood
  let q := (p + A) ^ A
  let r := 6 * q + p + 6
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith only [hq]
  have hqr : q ≤ r := by dsimp only [r]; linarith only [hq, hp]
  have h6r : (Fintype.card (Fin 6) : ℝ) ≤ r := by
    norm_num
    dsimp only [r]
    linarith only [hq, hp]
  have hJ : (Fintype.card J : ℝ) ≤ Real.exp r := by
    simp only [J, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp q) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 6
      _ = Real.exp (6 * q) := (Real.exp_nat_mul _ 6).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [r]; linarith only [hp])
  have hfamily (j : J) : ∃ g : (Fin 6 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 6 => 1) s ((r + B) ^ B) g) ∧
      ∀ x : Fin 6 → ZMod N, g (v x) = (w j x : ℂ) * S j (v x) := by
    obtain ⟨g, hg, he⟩ := hweighted ((Classical.choice (hS j)).mono hpr) hr h6r
      (fun k => ψ (j k)) (fun k => (hψ (j k)).mono hs hqr)
    refine ⟨g, hg, ?_⟩
    intro x
    simpa only [w, productPartitionWeight, Complex.ofReal_prod] using he x
  choose g hG he using hfamily
  let F := fun x => ∑ j : J, g j x
  have hcoeff : (∑ _j : J, ‖(1 : ℂ)‖) ≤ Real.exp r := by simpa using hJ
  have hcost : (r + B) ^ B + r ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hF : NativeIntegerExpansion (fun _ : Fin 6 => 1) s ((p + C) ^ C) F := by
    simpa only [F, one_mul] using
      ((NativeIntegerExpansion.weightedSum (fun j => Classical.choice (hG j))
        (fun _ => 1) hr hJ hcoeff).mono hcost)
  have heval (x : Fin 6 → ZMod N) : F (v x) = ∑ j : J, (w j x : ℂ) * S j (v x) := by
    apply Finset.sum_congr rfl
    intro j _
    exact he j x
  refine ⟨F, ⟨hF⟩, ?_, ?_⟩
  · intro x
    rw [show F (fun k => ((x k).val : ℤ)) = F (v x) from rfl, heval]
    exact norm_positive_partition_sum_le_one (fun j => w j x) (fun j => S j (v x))
      (fun j => hw j x) (hwSum x) (fun j => hSnorm j (v x))
  · have hdensity : ((coordinateExceptional (ι := Fin 6) E).card : ℝ) /
        Fintype.card (Fin 6 → ZMod N) ≤ 6 * (E.card : ℝ) / N := by
      simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
        coordinateExceptional_density_le (ι := Fin 6) E
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have hexp : 1 ≤ Real.exp p := Real.one_le_exp hp
    have hρexp : ρ ≤ Real.exp p * ρ := le_mul_of_one_le_left hρ.le hexp
    have hNexp : (1 : ℝ) / N ≤ Real.exp p * (1 / N) := le_mul_of_one_le_left hN hexp
    have h110 : (110 : ℝ) ≤ Real.exp 110 := by linarith [Real.add_one_le_exp (110 : ℝ)]
    have hbound : Real.exp p * ρ +
        2 * ((coordinateExceptional (ι := Fin 6) E).card : ℝ) /
          Fintype.card (Fin 6 → ZMod N) ≤ Real.exp (p + 110) * (ρ + 1 / N) := by
      calc
        _ = Real.exp p * ρ + 2 * (((coordinateExceptional (ι := Fin 6) E).card : ℝ) /
            Fintype.card (Fin 6 → ZMod N)) := by ring
        _ ≤ Real.exp p * ρ + 2 * (6 * (E.card : ℝ) / N) := by gcongr
        _ = Real.exp p * ρ + 12 * ((E.card : ℝ) / N) := by ring
        _ ≤ Real.exp p * ρ + 12 * (6 * ρ + 3 / N) := by gcongr
        _ = Real.exp p * ρ + 72 * ρ + 36 * (1 / N) := by ring
        _ ≤ Real.exp p * ρ + 72 * (Real.exp p * ρ) + 36 * (Real.exp p * (1 / N)) := by
          gcongr
        _ = Real.exp p * (73 * ρ + 36 * (1 / N)) := by ring
        _ ≤ Real.exp p * (110 * (ρ + 1 / N)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg p)
          linarith only [hρ.le, hN]
        _ = 110 * Real.exp p * (ρ + 1 / N) := by ring
        _ ≤ Real.exp 110 * Real.exp p * (ρ + 1 / N) := by gcongr
        _ = _ := by rw [← Real.exp_add, add_comm 110 p]
    change (𝔼 x : Fin 6 → ZMod N, ‖f (v x) - F (v x)‖) ≤ _
    simpa only [heval] using herr.trans hbound

end Erdos3

end

end OAI
