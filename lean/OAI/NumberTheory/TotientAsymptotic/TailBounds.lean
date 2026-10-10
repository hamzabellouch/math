import OAI.NumberTheory.TotientAsymptotic.Renewal

namespace OAI

/-! Uniform finite tail bounds and nonnegative coefficients from exponential random variables. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma alpha_le (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) : alpha s ≤ lam / rho := by
  have h : lam * s ≤ lam := by nlinarith [lam_pos, hs.2]
  have he : Real.exp lam = 1 / rho := Real.exp_log (div_pos zero_lt_one rho_pos)
  unfold alpha
  calc
    lam * Real.exp (lam * s) ≤ lam * Real.exp lam :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) lam_pos.le
    _ = lam / rho := by rw [he]; ring

def tailPrimeBound (H : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp ((11/10 : ℝ) * (lam/rho) * H * (rho^H)⁻¹))⌉₊

def tailCofactorBound (H : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp (2 * (lam/rho) * (P H : ℝ) * (rho^(P H))⁻¹))⌉₊

lemma one_le_tailPrimeBound (H : ℕ) : 1 ≤ tailPrimeBound H := by
  have h : (1 : ℝ) ≤ Real.exp
      (Real.exp ((11/10 : ℝ) * (lam/rho) * H * (rho^H)⁻¹)) :=
    Real.one_le_exp (Real.exp_pos _).le
  exact_mod_cast h.trans (Nat.le_ceil _)

lemma index_inv_pow_mono {h H : ℕ} (hh : h ≤ H) :
    (h : ℝ) * (rho^h)⁻¹ ≤ (H : ℝ) * (rho^H)⁻¹ := by
  have hr := rho_pos
  apply mul_le_mul (by exact_mod_cast hh)
  · exact (inv_le_inv₀ (pow_pos rho_pos _) (pow_pos rho_pos _)).2
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le hh)
  · positivity
  · positivity

lemma witness_prime_bound {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) (i : Fin H) :
    1 ≤ η.Q i ∧ η.Q i ≤ tailPrimeBound H := by
  by_cases hi : i.val < P H
  · rw [hη.1 i hi]
    exact ⟨le_rfl, one_le_tailPrimeBound H⟩
  · have himem : i.val ∈ Finset.Ico (P H) H := by simp; omega
    obtain ⟨hprime, hlo, hhi, hineq⟩ := hη.2.2.1 i.val himem
    have ht : tailPrime η i.val = η.Q i := by simp [tailPrime, i.isLt]
    rw [ht] at hprime
    have hQ : (1 : ℝ) < η.Q i := by exact_mod_cast hprime.one_lt
    have hlog : Real.log (η.Q i : ℝ) > 0 := Real.log_pos hQ
    have hupper : tailLog η i.val ≤
        (11/10 : ℝ) * (lam/rho) * H * (rho^H)⁻¹ := by
      apply hhi.trans
      calc
        _ = (11/10 : ℝ) * alpha s * ((i.val : ℝ) * (rho^i.val)⁻¹) := by ring
        _ ≤ (11/10 : ℝ) * (lam/rho) * ((H : ℝ) * (rho^H)⁻¹) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (alpha_le s hs) (by norm_num)
          · exact index_inv_pow_mono (Nat.le_of_lt i.isLt)
          · have := rho_pos; positivity
          · have := lam_pos; have := rho_pos; positivity
        _ = _ := by ring
    change Real.log (Real.log (tailPrime η i.val : ℝ)) ≤ _ at hupper
    rw [ht] at hupper
    have hh := (Real.log_le_iff_le_exp hlog).1 hupper
    have hh' := (Real.log_le_iff_le_exp (lt_trans zero_lt_one hQ)).1 hh
    have hb : (η.Q i : ℝ) ≤ (tailPrimeBound H : ℝ) := hh'.trans (Nat.le_ceil _)
    exact ⟨hprime.pos, by exact_mod_cast hb⟩

lemma witness_cofactor_bound {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) :
    1 ≤ η.cofactor ∧ η.cofactor ≤ tailCofactorBound H := by
  have hpos : (0 : ℝ) < η.cofactor := by exact_mod_cast hη.2.1
  have hlog : Real.log (η.cofactor : ℝ) ≤
      Real.exp (2 * (lam/rho) * (P H : ℝ) * (rho^(P H))⁻¹) := by
    apply hη.2.2.2.2.trans
    apply Real.exp_le_exp.mpr
    have hr := rho_pos
    gcongr
    exact alpha_le s hs
  have hb : (η.cofactor : ℝ) ≤ (tailCofactorBound H : ℝ) :=
    ((Real.log_le_iff_le_exp hpos).1 hlog).trans (Nat.le_ceil _)
  exact ⟨hη.2.1, by exact_mod_cast hb⟩

def tailUniverse (H : ℕ) : Set (TailDatum H) :=
  {η | (∀ i, η.Q i ∈ Set.Icc 1 (tailPrimeBound H)) ∧
    η.cofactor ∈ Set.Icc 1 (tailCofactorBound H)}

lemma tailUniverse_finite (H : ℕ) : (tailUniverse H).Finite := by
  let F : TailDatum H → (Fin H → ℕ) × ℕ := fun η => (η.Q, η.cofactor)
  have hF : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa [F, Prod.mk.injEq] using h
  have hf := (Set.Finite.pi (fun _ : Fin H => Set.finite_Icc 1 (tailPrimeBound H))).prod
    (Set.finite_Icc 1 (tailCofactorBound H))
  have hp := hf.preimage hF.injOn
  convert hp using 1
  ext η
  simp [tailUniverse, F, Pi.le_def, forall_and, and_assoc, and_left_comm, and_comm]

lemma witness_mem_tailUniverse {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) : η ∈ tailUniverse H := by
  exact ⟨fun i => witness_prime_bound hs hη i, witness_cofactor_bound hs hη⟩

theorem finite_tail_data (H : ℕ) :
    {η : TailDatum H | ∃ s ∈ Set.Ico (0 : ℝ) 1, IsWitness H s η}.Finite := by
  apply (tailUniverse_finite H).subset
  rintro η ⟨s, hs, hη⟩
  exact witness_mem_tailUniverse hs hη

lemma witnesses_finite (H : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    (witnesses H s d).Finite := by
  apply (finite_tail_data H).subset
  intro η hη
  exact ⟨s, hs, hη.1⟩



lemma witness_w_bound {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) :
    w η ≤ tailCofactorBound H * (tailPrimeBound H)^(H-P H) := by
  have hp : ∏ h ∈ Finset.Ico (P H) H, tailPrime η h ≤
      (tailPrimeBound H)^(H-P H) := by
    calc
      _ ≤ ∏ _h ∈ Finset.Ico (P H) H, tailPrimeBound H := by
        apply Finset.prod_le_prod
        intro h hh
        have hhH := (Finset.mem_Ico.mp hh).2
        simpa [tailPrime, hhH] using (witness_prime_bound hs hη ⟨h, hhH⟩).2
      _ = _ := by simp
  exact Nat.mul_le_mul (witness_cofactor_bound hs hη).2 hp

lemma witness_totient_bound {H : ℕ} {s : ℝ} {d : ℕ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (η : TailDatum H) (hη : η ∈ witnesses H s d) :
    d ≤ tailCofactorBound H * (tailPrimeBound H)^(H-P H) := by
  rw [← hη.2]
  exact (Nat.totient_le _).trans (witness_w_bound hs hη.1)

lemma tailLog_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {l : ℕ} (hl : l ∈ Finset.Ico (P H) H) :
    0 ≤ tailLog η l := by
  have hr := rho_pos
  exact (by have := alpha_pos s; positivity :
    (0 : ℝ) ≤ (9/10 : ℝ) * alpha s * l * (rho^l)⁻¹).trans (hη.2.2.1 l hl).2.1

lemma D_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {h : ℕ} (hh : H ≤ h) : 0 ≤ D h η := by
  unfold D
  apply Finset.sum_nonneg
  intro l hl
  have hlH := (Finset.mem_Ico.mp hl).2
  exact mul_nonneg (a_pos (by omega)).le (tailLog_nonneg hη hl)

def tailMass {H : ℕ} (η : TailDatum H) : ℝ := ∑ l ∈ Finset.Ico (P H) H, tailLog η l

lemma tailMass_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) : 0 ≤ tailMass η :=
  Finset.sum_nonneg (fun _ hl => tailLog_nonneg hη hl)

lemma D_le_log {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {h : ℕ} (hh : H ≤ h) :
    D h η ≤ Real.log (h+1 : ℝ) * tailMass η := by
  unfold D tailMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hlH := (Finset.mem_Ico.mp hl).2
  have hj : 1 ≤ h-l := by omega
  apply mul_le_mul_of_nonneg_right _ (tailLog_nonneg hη hl)
  apply (a_le_log hj).trans
  apply Real.log_le_log (by positivity)
  have hsub : h-l ≤ h := Nat.sub_le _ _
  exact_mod_cast Nat.add_le_add_right hsub 1

lemma D_le_linear {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {h : ℕ} (hh : H ≤ h) : D h η ≤ h * tailMass η := by
  apply (D_le_log hη hh).trans
  apply mul_le_mul_of_nonneg_right _ (tailMass_nonneg hη)
  have hlog := Real.log_le_sub_one_of_pos (x := (h+1 : ℝ)) (by positivity)
  linarith

lemma maxD_nonneg {H : ℕ} {s : ℝ} {T : Finset (TailDatum H)}
    (hT : ∀ η ∈ T, IsWitness H s η) {h : ℕ} (hh : H ≤ h) : 0 ≤ maxD h T := by
  classical
  unfold maxD
  split_ifs with ht
  · obtain ⟨η, hη⟩ := ht
    exact (D_nonneg (hT η hη) hh).trans (Finset.le_sup' (s := T) (D h) hη)
  · exact le_rfl

lemma maxD_le_linear {H : ℕ} {s : ℝ} {T : Finset (TailDatum H)}
    (hT : ∀ η ∈ T, IsWitness H s η) {h : ℕ} (hh : H ≤ h) :
    maxD h T ≤ (h : ℝ) * ∑ η ∈ T, tailMass η := by
  classical
  unfold maxD
  split_ifs with ht
  · apply Finset.sup'_le
    intro η hη
    apply (D_le_linear (hT η hη) hh).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.single_le_sum (fun ξ hξ => tailMass_nonneg (hT ξ hξ)) hη
  · have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [hz]

theorem summable_tail_threshold {H : ℕ} {s : ℝ} {T : Finset (TailDatum H)}
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Summable (fun n : ℕ => rho^(H+n) * maxD (H+n) T) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) * rho^n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖rho‖ < 1 by simpa [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one)
  have hshift : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ) * rho^(H+n)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff H).2 hs
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg rho_pos.le _)
      (maxD_nonneg hT (by omega)))
    (fun n => ?_)
    (hshift.mul_right (∑ η ∈ T, tailMass η))
  have hb := mul_le_mul_of_nonneg_left
    (maxD_le_linear hT (h := H+n) (by omega)) (pow_nonneg rho_pos.le (H+n))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb

lemma finite_witness_subsets (H : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    {T : Finset (TailDatum H) | (↑T : Set (TailDatum H)) ⊆ witnesses H s d}.Finite := by
  have h := (witnesses_finite H hs d).finite_subsets
  exact h.preimage Finset.coe_injective.injOn


open MeasureTheory ProbabilityTheory
open scoped Classical

private instance expOne_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure zero_lt_one

def exponentialProduct : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

instance exponentialProduct_probability : IsProbabilityMeasure exponentialProduct := by
  unfold exponentialProduct
  infer_instance

lemma expOne_real_Ioi {t : ℝ} (ht : 0 ≤ t) :
    (expMeasure 1).real (Set.Ioi t) = Real.exp (-t) := by
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one, ite_eq_left ht, one_mul]
  ring

lemma expOne_Ioi {t : ℝ} (ht : 0 ≤ t) :
    expMeasure 1 (Set.Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
  rw [← expOne_real_Ioi ht, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma exponential_box_probability (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hbs : Summable b) :
    exponentialProduct.real (Set.univ.pi (fun n => Set.Ioi (b n))) =
      Real.exp (-(∑' n, b n)) := by
  have hp : HasProd (fun n : ℕ => ENNReal.ofReal (Real.exp (-b n)))
      (ENNReal.ofReal (Real.exp (-∑' n, b n))) := by
    have hs := hbs.hasSum.neg.rexp
    have he := (ENNReal.continuous_ofReal.tendsto (Real.exp (-∑' n, b n))).comp hs
    unfold HasProd
    convert he using 1
    ext T
    exact (ENNReal.ofReal_prod_of_nonneg (fun n _ => Real.exp_nonneg (-b n))).symm
  unfold Measure.real exponentialProduct
  rw [Measure.infinitePi_pi_univ _ (fun _ => measurableSet_Ioi)]
  simp_rw [expOne_Ioi (hb _)]
  rw [hp.tprod_eq, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

def witnessEvent {H : ℕ} (s : ℝ) (η : TailDatum H) : Set (ℕ → ℝ) :=
  Set.univ.pi (fun n => Set.Ioi ((gamma / alpha s) * rho^(H+n) * D (H+n) η))

lemma measurableSet_witnessEvent {H : ℕ} (s : ℝ) (η : TailDatum H) :
    MeasurableSet (witnessEvent s η) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi)

lemma threshold_coefficient_pos (H n : ℕ) (s : ℝ) :
    0 < (gamma / alpha s) * rho^(H+n) :=
  mul_pos (div_pos gamma_pos (alpha_pos s)) (pow_pos rho_pos _)

lemma witnessEvent_intersection {H : ℕ} (s : ℝ) (T : Finset (TailDatum H)) (ht : T.Nonempty) :
    (⋂ η ∈ T, witnessEvent s η) =
      Set.univ.pi (fun n => Set.Ioi ((gamma / alpha s) * rho^(H+n) * maxD (H+n) T)) := by
  classical
  ext u
  simp only [Set.mem_iInter, witnessEvent, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioi]
  constructor
  · intro h n
    unfold maxD
    rw [dite_eq_left ht]
    rw [mul_comm ((gamma / alpha s) * rho^(H+n))]
    apply (lt_div_iff₀ (threshold_coefficient_pos H n s)).mp
    rw [Finset.sup'_lt_iff ht]
    intro η hη
    apply (lt_div_iff₀ (threshold_coefficient_pos H n s)).mpr
    simpa only [mul_comm] using h η hη n
  · intro h η hη n
    apply lt_of_le_of_lt _ (h n)
    apply mul_le_mul_of_nonneg_left _ (threshold_coefficient_pos H n s).le
    unfold maxD
    rw [dite_eq_left ht]
    exact Finset.le_sup' (s := T) (D (H+n)) hη

lemma witnessEvent_intersection_probability {H : ℕ} {s : ℝ}
    (T : Finset (TailDatum H)) (ht : T.Nonempty) (hT : ∀ η ∈ T, IsWitness H s η) :
    exponentialProduct.real (⋂ η ∈ T, witnessEvent s η) =
      Real.exp (-(gamma / alpha s) * ∑' n, rho^(H+n) * maxD (H+n) T) := by
  rw [witnessEvent_intersection s T ht]
  have hs : Summable (fun n => (gamma / alpha s) * rho^(H+n) * maxD (H+n) T) := by
    simpa only [mul_assoc] using (summable_tail_threshold hT).mul_left (gamma / alpha s)
  rw [exponential_box_probability _ (fun n => mul_nonneg
    (threshold_coefficient_pos H n s).le (maxD_nonneg hT (by omega))) hs]
  congr 1
  simp only [mul_assoc, tsum_mul_left, neg_mul]

lemma coefficient_eq_union_probability (H : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    (∑ᶠ T : Finset (TailDatum H),
      if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
        (-1 : ℝ)^(T.card-1) * Real.exp (-(gamma / alpha s) *
          ∑' n : ℕ, rho^(H+n) * maxD (H+n) T)
      else 0) =
    exponentialProduct.real (⋃ η ∈ (witnesses_finite H hs d).toFinset, witnessEvent s η) := by
  classical
  let W := (witnesses_finite H hs d).toFinset
  have hW (T : Finset (TailDatum H)) :
      (↑T : Set (TailDatum H)) ⊆ witnesses H s d ↔ T ⊆ W := by
    constructor
    · intro h η hη
      exact ((witnesses_finite H hs d).mem_toFinset).mpr (h hη)
    · intro h η hη
      exact ((witnesses_finite H hs d).mem_toFinset).mp (h hη)
  rw [finsum_eq_sum_of_support_subset _ (s := W.powerset.filter Finset.Nonempty)]
  · rw [measureReal_biUnion_eq_sum_powerset (fun η _ => measurableSet_witnessEvent s η)]
    apply Finset.sum_congr rfl
    intro T hT
    obtain ⟨hTW, ht⟩ := Finset.mem_filter.mp hT
    have hsub : (↑T : Set (TailDatum H)) ⊆ witnesses H s d :=
      (hW T).mpr (Finset.mem_powerset.mp hTW)
    rw [ite_eq_left ⟨ht, hsub⟩, witnessEvent_intersection_probability T ht
      (fun η hη => (hsub hη).1)]
    congr 1
    have hc : T.card + 1 = T.card - 1 + 2 := by
      have := Finset.card_pos.mpr ht
      omega
    rw [hc, pow_add]
    norm_num
  · intro T hT
    have ht : T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d := by
      by_contra h
      simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((hW T).mp ht.2), ht.1⟩

theorem AH_nonneg (H : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ∀ r : ℝ, 1 ≤ r → 0 ≤ f r ∧ f r ≤ 1) :
    0 ≤ AH H f s := by
  classical
  unfold AH
  apply mul_nonneg (mul_nonneg (pow_nonneg rho_pos.le _)
    (pow_nonneg (div_pos gamma_pos (alpha_pos s)).le _))
  apply finsum_nonneg
  intro d
  split_ifs with hd
  · apply mul_nonneg (div_nonneg (hf _ (one_le_ell_ratio hd)).1 (Nat.cast_nonneg d))
    rw [coefficient_eq_union_probability H hs d]
    exact measureReal_nonneg
  · exact le_rfl

end TotientAsymptotic

end

end OAI
