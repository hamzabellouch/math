import OAI.NumberTheory.TotientAsymptotic.PPTResidualCount
import OAI.NumberTheory.TotientAsymptotic.PPTTailMass
import OAI.NumberTheory.TotientAsymptotic.CandidateNormalMass

namespace OAI

/-!
The actual finite label universe for the common prime product and the
small left tail. Products are counted as integers. Repeated prime lists
only enlarge the reciprocal-mass majorant.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def pptPrimeProductFamily (N h : ℕ) : Finset ℕ :=
  (Fintype.piFinset (fun _ : Fin h => Nat.primesLE N)).image (fun p => ∏ i, p i)

lemma mem_pptPrimeProductFamily {N h n : ℕ} :
    n ∈ pptPrimeProductFamily N h ↔
      ∃ p : Fin h → ℕ, (∀ i, p i ≤ N ∧ (p i).Prime) ∧ n = ∏ i, p i := by
  classical
  simp only [pptPrimeProductFamily, Finset.mem_image, Fintype.mem_piFinset, Nat.mem_primesLE]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, he.symm⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, he.symm⟩

lemma ppt_prime_product_family_mass (N h : ℕ) :
    (∑ n ∈ pptPrimeProductFamily N h, (n.totient : ℝ)⁻¹) ≤
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹)^h := by
  classical
  let P := Fintype.piFinset (fun _ : Fin h => Nat.primesLE N)
  have himage := Finset.sum_image_le_of_nonneg (s := P) (g := fun p => ∏ i, p i)
    (f := fun n : ℕ => (n.totient : ℝ)⁻¹)
    (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n.totient))
  apply himage.trans
  calc
    _ ≤ ∑ p ∈ P, reciprocalShiftWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime (i : Fin h) : (p i).Prime :=
        (Nat.mem_primesLE.mp (Fintype.mem_piFinset.mp hp i)).2
      have hnat := totient_prime_product_lower Finset.univ p 1 (fun i _ => hprime i)
      simp only [Nat.totient_one, one_mul] at hnat
      have hpos : (0 : ℝ) < (∏ i, (p i-1) : ℕ) := by
        exact_mod_cast Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hprime i).one_lt)
      exact inv_anti₀ hpos (Nat.cast_le.mpr hnat)
    _ = ∏ _i : Fin h, ∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹ := by
      rw [Finset.prod_univ_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [reciprocalShiftWeight, Nat.cast_prod, Finset.prod_inv_distrib]
    _ = _ := by simp

lemma ppt_all_factor_lengths_mass (N H : ℕ) :
    (∑ h ∈ Finset.range (H+1), ∑ n ∈ pptPrimeProductFamily N h, (n.totient : ℝ)⁻¹) ≤
      (H+1 : ℕ)*(max 1 (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹))^H := by
  let P : ℝ := ∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹
  have hP : 0 ≤ P := Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ h ∈ Finset.range (H+1), (max 1 P)^H := by
      apply Finset.sum_le_sum
      intro h hh
      have hhH : h ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
      exact (ppt_prime_product_family_mass N h).trans
        ((pow_le_pow_left₀ hP (le_max_right _ _) h).trans
          (pow_le_pow_right₀ (le_max_left _ _) hhH))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl

/-- Each prime sublist of a candidate gives an actual label in this
finite universe, retaining its exact length. -/
lemma ppt_prime_sublist_label {k N : ℕ} (p : Fin k → ℕ) (I : Finset (Fin k))
    (hp : ∀ i, p i ≤ N ∧ (p i).Prime) :
    (∏ i ∈ I, p i) ∈ pptPrimeProductFamily N I.card := by
  classical
  let e : Fin I.card ↪o Fin k := I.orderEmbOfFin rfl
  apply mem_pptPrimeProductFamily.mpr
  refine ⟨p ∘ e, fun i => hp (e i), ?_⟩
  have he : Finset.univ.image e = I := I.image_orderEmbOfFin_univ rfl
  calc
    _ = ∏ i ∈ Finset.univ.image e, p i := by rw [he]
    _ = _ := by
      rw [Finset.prod_image]
      · rfl
      · exact fun i _ j _ hij => e.injective hij

/-- Common and tail labels together with all lengths, all terminal
window indices, and all paired grid labels have a finite explicit mass.
No assertion about the number of bad integers enters this bound. -/
theorem ppt_all_residual_label_mass {A t δ : ℝ} {H N : ℕ}
    (ht0 : 0 < t) (ht : 1 ≤ Real.log t) (hδ : 0 < δ) (hmesh : 1/t ≤ δ)
    (hdim : (H : ℝ) ≤ A*Real.log t) :
    (∑ b ∈ Finset.range (H+1), ∑ _g ∈ collisionGridFamilies δ b,
      ∑ _j ∈ Finset.range (H+1),
      ∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily N h,
      ∑ k ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily N k,
        (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹) ≤
      ((H+1 : ℕ) : ℝ)^4 *
        (max 1 (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹))^(2*H) *
          Real.exp (2*A*(Real.log t)^2) := by
  classical
  let F : ℝ := ∑ h ∈ Finset.range (H+1),
    ∑ a ∈ pptPrimeProductFamily N h, (a.totient : ℝ)⁻¹
  let P : ℝ := max 1 (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹)
  let E : ℝ := Real.exp (2*A*(Real.log t)^2)
  have hF0 : 0 ≤ F := Finset.sum_nonneg (fun h _ =>
    Finset.sum_nonneg (fun a _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
  have hF := ppt_all_factor_lengths_mass N H
  change F ≤ (H+1 : ℕ)*P^H at hF
  have hinner :
      (∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily N h,
        ∑ k ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily N k,
          (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹) = F*F := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, F]
  have hsum := Finset.sum_le_sum (s := Finset.range (H+1))
    (fun b hb => ppt_grid_card_bound ht0 ht hδ hmesh
      ((Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))).trans hdim))
  have hgrid : (∑ b ∈ Finset.range (H+1), ((collisionGridFamilies δ b).card : ℝ)) ≤
      (H+1 : ℕ)*E := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, E] using hsum
  have hF2 : F^2 ≤ ((H+1 : ℕ)*P^H)^2 :=
    pow_le_pow_left₀ hF0 hF 2
  calc
    _ = (∑ b ∈ Finset.range (H+1), ((collisionGridFamilies δ b).card : ℝ))*
        ((H+1 : ℕ)*F^2) := by
      simp only [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two]
      exact (Finset.sum_mul _ _ _).symm
    _ ≤ ((H+1 : ℕ)*E)*((H+1 : ℕ)*((H+1 : ℕ)*P^H)^2) := by
      exact mul_le_mul hgrid (mul_le_mul_of_nonneg_left hF2 (Nat.cast_nonneg _))
        (by positivity) (by positivity)
    _ = _ := by rw [Nat.mul_comm 2 H, pow_mul]; ring

/-- The complete weighted label universe has exponential-square mass at
its actual local cutoff. This is the entropy budget consumed by
`ppt_finite_residual_block_decay`. -/
theorem ppt_residual_labels_exponential_mass {A : ℝ} (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z : ℝ in atTop,
      ∀ (H : ℕ) (δ : ℝ),
        (H : ℝ) ≤ A*Real.log (B z) →
        0 < δ → 1/B z ≤ δ →
        (∑ b ∈ Finset.range (H+1), ∑ _g ∈ collisionGridFamilies δ b,
          ∑ _j ∈ Finset.range (H+1),
          ∑ h ∈ Finset.range (H+1), ∑ a ∈ pptPrimeProductFamily (discardPrimeBound (B z)) h,
          ∑ k ∈ Finset.range (H+1), ∑ c ∈ pptPrimeProductFamily (discardPrimeBound (B z)) k,
            (a.totient : ℝ)⁻¹*(c.totient : ℝ)⁻¹) ≤
          Real.exp (M*(Real.log (B z))^2) := by
  obtain ⟨D, hD, hprime⟩ := candidate_total_prime_mass
  let C : ℝ := 4*D+1
  let K₁ : ℝ := |Real.log (A+1)|+1
  let K₂ : ℝ := |Real.log C|+1
  let M : ℝ := 4*K₁+2*A*K₂+2*A
  have hK₁ : 0 < K₁ := by dsimp only [K₁]; positivity
  have hK₂ : 0 < K₂ := by dsimp only [K₂]; positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hD]
  refine ⟨M, by dsimp only [M]; positivity, ?_⟩
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with z ht2 hte
  intro H δ hdim hδ hmesh
  let t : ℝ := B z
  let P : ℝ := max 1 (∑ p ∈ Nat.primesLE (discardPrimeBound t), ((p-1 : ℕ) : ℝ)⁻¹)
  have ht : 0 < t := by dsimp only [t]; linarith only [ht2]
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith only [ht2]
  have hlog : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hte
  have hP1 : 1 ≤ P := le_max_left _ _
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  have hPC : P ≤ C*t := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le hC ht1
    · have hp := hprime t ht2
      have hc : D*(2*t+2) ≤ C*t := by dsimp only [C]; nlinarith only [hD, ht1]
      exact hp.trans hc
  have hH : (H : ℝ)+1 ≤ (A+1)*t := by
    have hh := hdim.trans (mul_le_mul_of_nonneg_left (Real.log_le_self ht.le) hA)
    nlinarith only [hh, ht1]
  have hlogH : Real.log ((H : ℝ)+1) ≤ K₁*Real.log t := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < H+1) hH
    rw [Real.log_mul (by positivity : A+1 ≠ 0) ht.ne'] at hh
    have hk : Real.log (A+1) ≤ |Real.log (A+1)| * Real.log t :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
    dsimp only [K₁]
    nlinarith only [hh, hk]
  have hlogP : Real.log P ≤ K₂*Real.log t := by
    have hh := Real.log_le_log hP0 hPC
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hC)) ht.ne'] at hh
    have hk : Real.log C ≤ |Real.log C| * Real.log t :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
    dsimp only [K₂]
    nlinarith only [hh, hk]
  have hlogH2 : 4*Real.log ((H : ℝ)+1) ≤ 4*K₁*(Real.log t)^2 := by
    have hh := le_mul_of_one_le_right (mul_nonneg hK₁.le (zero_le_one.trans hlog)) hlog
    nlinarith only [hlogH, hh]
  have hlogP2 : (2*(H : ℝ))*Real.log P ≤ 2*A*K₂*(Real.log t)^2 := by
    have hh := mul_le_mul hdim hlogP (Real.log_nonneg hP1)
      (mul_nonneg hA (zero_le_one.trans hlog))
    nlinarith only [hh]
  have hraw := ppt_all_residual_label_mass (N := discardPrimeBound t) ht hlog hδ hmesh hdim
  apply hraw.trans
  change ((H+1 : ℕ) : ℝ)^4*P^(2*H)*Real.exp (2*A*(Real.log t)^2) ≤ _
  rw [show ((H+1 : ℕ) : ℝ) = (H : ℝ)+1 by push_cast; rfl]
  rw [show ((H : ℝ)+1)^4 = Real.exp (4*Real.log ((H : ℝ)+1)) by
      have he := Real.exp_nat_mul (Real.log ((H : ℝ)+1)) 4
      rw [Real.exp_log (by positivity : (0 : ℝ) < H+1)] at he
      norm_num only [Nat.cast_ofNat] at he
      exact he.symm,
    show P^(2*H) = Real.exp ((2*(H : ℝ))*Real.log P) by
      rw [show 2*(H : ℝ) = ((2*H : ℕ) : ℝ) by push_cast; rfl,
        Real.exp_nat_mul, Real.exp_log hP0],
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [M]
  nlinarith only [hlogH2, hlogP2]

end TotientAsymptotic

end

end OAI
