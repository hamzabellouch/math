import OAI.Probability.SATVariance.FrozenReplacement

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def SetSAT {u s : ℕ} (S : Finset (Assignment u)) (ω : Stream u s) (g : ℕ) : Prop :=
  ∃ a ∈ S, ∀ i < g, Satisfies (ω i) a

def blockKill (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) : ℝ :=
  (streamLaw u s {ω | ¬ SetSAT S ω g}).toReal

lemma setSAT_univ {u s : ℕ} (ω : Stream u s) (g : ℕ) :
    SetSAT Finset.univ ω g ↔ PrefixSAT ω g := by
  simp [SetSAT, PrefixSAT]

lemma measurableSet_setSAT (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) :
    MeasurableSet {ω : Stream u s | SetSAT S ω g} := by
  simp only [SetSAT, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  by_cases ha : a ∈ S
  · simp only [ha, true_and, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact (Set.toFinite {c : Clause u s | Satisfies c a}).measurableSet.preimage
      (measurable_pi_apply i)
  · simp only [ha, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

lemma blockKill_nonneg (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) :
    0 ≤ blockKill u s S g := ENNReal.toReal_nonneg

lemma blockKill_le_one {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    blockKill u s S g ≤ 1 := by
  let := streamLaw_probability u s hsu
  exact measureReal_le_one (μ := streamLaw u s)

lemma blockKill_empty {u s : ℕ} (hsu : s ≤ u) (g : ℕ) :
    blockKill u s ∅ g = 1 := by
  let := streamLaw_probability u s hsu
  simp [blockKill, SetSAT]

lemma blockKill_compl {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    blockKill u s S g = 1 - (streamLaw u s {ω | SetSAT S ω g}).toReal := by
  let := streamLaw_probability u s hsu
  have he : {ω : Stream u s | ¬ SetSAT S ω g} = {ω | SetSAT S ω g}ᶜ := rfl
  rw [blockKill, he, measure_compl (measurableSet_setSAT u s S g) (measure_ne_top _ _),
    measure_univ, ENNReal.toReal_sub_of_le prob_le_one (by simp), ENNReal.toReal_one]

lemma clauseLaw_kills_toReal {u s : ℕ} {S : Finset (Assignment u)} (hS : S.Nonempty) :
    (clauseLaw u s {c | Kills S c}).toReal = killRatio u (frozen S).card s := by
  rw [clauseLaw_kills hS]
  simp [killRatio, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_comm]

lemma blockKill_one {u s : ℕ} (hsu : s ≤ u) {S : Finset (Assignment u)} (hS : S.Nonempty) :
    blockKill u s S 1 = killRatio u (frozen S).card s := by
  let := clauseLaw_probability u s hsu
  have he : {ω : Stream u s | ¬ SetSAT S ω 1} =
      Set.pi ({0} : Finset ℕ) (fun _ => {c : Clause u s | Kills S c}) := by
    ext ω
    simp [SetSAT, Kills]
  rw [blockKill, he, streamLaw, Measure.infinitePi_pi]
  · simpa using clauseLaw_kills_toReal hS
  · intro _ _
    exact (Set.toFinite _).measurableSet

lemma blockKill_individual {u s : ℕ} (hsu : s ≤ u) {S : Finset (Assignment u)}
    (hS : S.Nonempty) (g : ℕ) :
    1 - (1 - killRatio u (frozen S).card s)^g ≤ blockKill u s S g := by
  let := clauseLaw_probability u s hsu
  let := streamLaw_probability u s hsu
  have hsub : {ω : Stream u s | SetSAT S ω g} ⊆
      Set.pi (Finset.range g) (fun _ => {c : Clause u s | ¬ Kills S c}) := by
    rintro ω ⟨a, ha, hω⟩ i hi hk
    exact hk a ha (hω i (Finset.mem_range.mp hi))
  have ht := measure_mono (μ := streamLaw u s) hsub
  rw [streamLaw, Measure.infinitePi_pi _ (fun _ _ => (Set.toFinite _).measurableSet)] at ht
  have he : clauseLaw u s {c | ¬ Kills S c} = 1-clauseLaw u s {c | Kills S c} := by
    exact (measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _)).trans
      (by rw [measure_univ]; rfl)
  simp only [he, Finset.prod_const, Finset.card_range] at ht
  have ht' := ENNReal.toReal_mono (by finiteness) ht
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le prob_le_one (by simp),
    ENNReal.toReal_one, clauseLaw_kills_toReal hS] at ht'
  rw [blockKill_compl hsu]
  change ((streamLaw u s) {ω | SetSAT S ω g}).toReal ≤ _ at ht'
  linarith

lemma set_survival_le {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    streamLaw u s {ω | SetSAT S ω g} ≤
      (S.card : ℝ≥0∞) * (1-((2 : ℝ≥0∞)^s)⁻¹)^g := by
  have he : {ω : Stream u s | SetSAT S ω g} =
      ⋃ a : S, {ω | ∀ i < g, Satisfies (ω i) a} := by
    ext ω
    simp [SetSAT]
  rw [he]
  apply (measure_iUnion_fintype_le _ _).trans_eq
  simp [assignment_survival hsu]

lemma frozen_card_le {u : ℕ} (S : Finset (Assignment u)) : (frozen S).card ≤ u := by
  simpa using Finset.card_le_univ (frozen S)

lemma rate_toReal (s : ℕ) :
    (1-((2 : ℝ≥0∞)^s)⁻¹).toReal = 1-((2 : ℝ)^s)⁻¹ := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))
    (by simp)]
  simp

lemma real_rate_nonneg (s : ℕ) : 0 ≤ 1-((2 : ℝ)^s)⁻¹ := by
  exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num)))

lemma survival_exp_bound {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    (streamLaw u s {ω | SetSAT S ω g}).toReal ≤
      (S.card : ℝ) * Real.exp (-((2 : ℝ)^s)⁻¹ * g) := by
  have ht := ENNReal.toReal_mono (by finiteness) (set_survival_le hsu S g)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow, rate_toReal] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he : 1-((2 : ℝ)^s)⁻¹ ≤ Real.exp (-((2 : ℝ)^s)⁻¹) := by
    linarith [Real.add_one_le_exp (-((2 : ℝ)^s)⁻¹)]
  calc
    _ ≤ (Real.exp (-((2 : ℝ)^s)⁻¹))^g := pow_le_pow_left₀ (real_rate_nonneg s) he g
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma blockKill_exp_full {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    1 - (2 : ℝ)^u * Real.exp (-((2 : ℝ)^s)⁻¹ * g) ≤ blockKill u s S g := by
  have hScard : (S.card : ℝ) ≤ (2 : ℝ)^u := by
    exact_mod_cast (by simpa using Finset.card_le_univ S : S.card ≤ 2^u)
  have ht := (survival_exp_bound hsu S g).trans
    (mul_le_mul_of_nonneg_right hScard (Real.exp_nonneg _))
  rw [blockKill_compl hsu]
  linarith

lemma blockKill_exp_individual {u s : ℕ} (hu : 0 < u) (hsu : s ≤ u)
    {S : Finset (Assignment u)} (hS : S.Nonempty) (g : ℕ) :
    1 - Real.exp (-(g : ℝ)*killRatio u (frozen S).card s) ≤ blockKill u s S g := by
  have hk : killRatio u (frozen S).card s ≤ 1 :=
    (killRatio_le_half_pow hu (frozen_card_le S) hsu).trans
      (pow_le_one₀ (by norm_num) (by norm_num))
  have he : 1-killRatio u (frozen S).card s ≤
      Real.exp (-killRatio u (frozen S).card s) := by
    linarith [Real.add_one_le_exp (-killRatio u (frozen S).card s)]
  have ht := pow_le_pow_left₀ (sub_nonneg.mpr hk) he g
  rw [← Real.exp_nat_mul] at ht
  have hm := blockKill_individual hsu hS g
  have hx : (g : ℝ) * (-killRatio u (frozen S).card s) =
      -(g : ℝ) * killRatio u (frozen S).card s := by ring
  rw [hx] at ht
  exact le_trans (sub_le_sub_left ht 1) hm

lemma one_sub_exp_neg_two_mul_ge {h : ℝ} (h₀ : 0 ≤ h) (h₁ : h ≤ 1/2) :
    h ≤ 1-Real.exp (-2*h) := by
  have hre : Real.exp (-2*h) ≤ (1+2*h)⁻¹ := by
    have he := Real.add_one_le_exp (2*h)
    rw [show -2*h = -(2*h) by ring, Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith)
  have hi : (1+2*h)⁻¹ ≤ 1-h := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1+2*h)).2
    nlinarith
  linarith

lemma blockKill_long {u s g : ℕ} (hu : 0 < u) (hsu : s ≤ u)
    (hg : (2 : ℝ)^(s+1)*u ≤ g) (S : Finset (Assignment u)) :
    (1 : ℝ)/3 ≤ blockKill u s S g := by
  have he : -((2 : ℝ)^s)⁻¹ * g ≤ -2*u := by
    have h2 : (0 : ℝ) < (2 : ℝ)^s := by positivity
    rw [pow_succ] at hg
    have h := mul_le_mul_of_nonneg_left hg (le_of_lt (inv_pos.mpr h2))
    have hc : ((2 : ℝ)^s)⁻¹ * ((2:ℝ)^s*2*u) = 2*u := by field_simp
    rw [hc] at h
    linarith
  have hexp : (2 : ℝ)*Real.exp (-2) ≤ 2/3 := by
    have ht : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    have hi := inv_anti₀ (by norm_num : (0 : ℝ)<3) ht
    rw [Real.exp_neg]
    linarith
  have hh : (2 : ℝ)^u * Real.exp (-2*u) ≤ 2/3 := by
    have hi : (1 : ℕ) ≤ u := hu
    calc
      _ = (2*Real.exp (-2))^u := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      _ ≤ ((2 : ℝ)/3)^u := pow_le_pow_left₀ (by positivity) hexp u
      _ ≤ ((2 : ℝ)/3)^1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
      _ = _ := by norm_num
  have hb := blockKill_exp_full hsu S g
  have ht := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (by positivity : (0 : ℝ) ≤ (2:ℝ)^u)
  linarith

def replacementK (k : ℕ) : ℝ := ((2 : ℝ)^k * ((k-1 : ℕ) : ℝ))^(k-1)

lemma replacementK_succ (r : ℕ) : replacementK (r+1) = ((2 : ℝ)^(r+1)*r)^r := by
  simp [replacementK]

lemma replacement_numeric {u b r g : ℕ} (hr : 2 ≤ r) (hbu : b ≤ u)
    (hru : r+1 ≤ u) (hg : 1 ≤ g) {R : ℝ} (hR : 0 ≤ R)
    (hind : 1-Real.exp (-(g : ℝ)*killRatio u b (r+1)) ≤ R)
    (hlong : (2 : ℝ)^(r+2)*u ≤ g → (1 : ℝ)/3 ≤ R) :
    killRatio u b r - replacementK (r+1)/(g : ℝ)^r ≤ R := by
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hu₀ : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hquarter : killRatio u b r ≤ 1/4 := by
    apply (killRatio_le_half_pow (by omega) hbu (by omega)).trans
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) hr
    norm_num at h ⊢
    exact h
  have hK : (2 : ℝ)*(r+1) ≤ (2 : ℝ)^(r+1)*r := by
    have h2 : (4 : ℝ) ≤ (2 : ℝ)^(r+1) := by
      calc
        _ = (2 : ℝ)^2 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    nlinarith
  rw [replacementK_succ, ← div_pow]
  by_cases hrb : r+1 ≤ b
  · by_cases hlarge : 2 ≤ (g : ℝ)/(r+1) * (killRatio u b r)^((r : ℝ)⁻¹)
    · have hp := frozen_power (by omega : 1 ≤ r) hbu hrb
      have hex : ((r : ℝ)+1)/r = 1+(r : ℝ)⁻¹ := by field_simp
      rw [hex, Real.rpow_add_of_nonneg (killRatio_nonneg u b r) zero_le_one
        (by positivity), Real.rpow_one] at hp
      have hs : 2*killRatio u b r ≤ (g : ℝ)*killRatio u b (r+1) := by
        have h₁ := mul_le_mul_of_nonneg_left hlarge (killRatio_nonneg u b r)
        have h₂ := mul_le_mul_of_nonneg_left hp hg₀.le
        calc
          2*killRatio u b r = killRatio u b r*2 := by ring
          _ ≤ killRatio u b r * ((g : ℝ)/(r+1) * (killRatio u b r)^((r : ℝ)⁻¹)) := h₁
          _ = (g : ℝ) * (killRatio u b r * (killRatio u b r)^((r : ℝ)⁻¹)/(r+1)) := by ring
          _ ≤ _ := h₂
      have ht := Real.exp_le_exp.mpr (neg_le_neg hs)
      simp only [← neg_mul] at ht
      have hh := one_sub_exp_neg_two_mul_ge (killRatio_nonneg u b r) (by linarith :
        killRatio u b r ≤ 1/2)
      have herr : 0 ≤ ((2:ℝ)^(r+1)*r/g)^r := by positivity
      linarith
    · have hroot : (killRatio u b r)^((r : ℝ)⁻¹) ≤ 2*(r+1)/(g : ℝ) := by
        apply (le_div_iff₀ hg₀).2
        have hh := (not_le.mp hlarge).le
        rw [div_mul_eq_mul_div] at hh
        have hh' := (div_le_iff₀ (by positivity : (0:ℝ)<r+1)).mp hh
        linarith
      have hbound : killRatio u b r ≤ ((2:ℝ)^(r+1)*r/g)^r := by
        calc
          killRatio u b r = ((killRatio u b r)^((r : ℝ)⁻¹))^r :=
            (Real.rpow_inv_natCast_pow (killRatio_nonneg u b r) (by omega : r ≠ 0)).symm
          _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (killRatio_nonneg u b r) _)
            (hroot.trans (div_le_div_of_nonneg_right hK hg₀.le)) r
      linarith
  · by_cases hbr : b < r
    · rw [killRatio_eq_zero hbr]
      have herr : 0 ≤ ((2:ℝ)^(r+1)*r/g)^r := by positivity
      linarith
    · have hbr : b = r := by omega
      subst b
      by_cases hlong' : (2 : ℝ)^(r+2)*u ≤ g
      · have hh := hlong hlong'
        have herr : 0 ≤ ((2:ℝ)^(r+1)*r/g)^r := by positivity
        linarith
      · have hg' : (g : ℝ) ≤ (2 : ℝ)^(r+2)*u := (not_le.mp hlong').le
        have hd : (r : ℝ)/(2*u) ≤ (2 : ℝ)^(r+1)*r/g := by
          apply (div_le_div_iff₀ (by positivity) hg₀).2
          rw [show r+2 = (r+1)+1 by omega, pow_succ] at hg'
          nlinarith [mul_le_mul_of_nonneg_left hg' hr₀.le]
        have hh := (killRatio_le_density_pow hbu (by omega : r ≤ u)).trans
          (pow_le_pow_left₀ (by positivity) hd r)
        linarith

lemma one_replacement {u r g : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hg : 1 ≤ g)
    (S : Finset (Assignment u)) :
    blockKill u r S 1 - replacementK (r+1)/(g : ℝ)^r ≤ blockKill u (r+1) S g := by
  by_cases hS : S.Nonempty
  · rw [blockKill_one (by omega) hS]
    apply replacement_numeric hr (frozen_card_le S) hru hg (blockKill_nonneg _ _ _ _)
    · exact blockKill_exp_individual (by omega) hru hS g
    · intro hlong
      apply blockKill_long (by omega) hru _ S
      simpa [Nat.add_assoc] using hlong
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [blockKill_empty (by omega), blockKill_empty hru]
    have hK : 0 ≤ replacementK (r+1)/(g : ℝ)^r := by
      rw [replacementK_succ]
      positivity
    linarith

end RandomKSAT

end

end OAI
