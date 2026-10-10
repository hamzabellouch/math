import Mathlib

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section



def DiscreteConvex (F : ℕ → ℝ) : Prop :=
  Monotone (fun n => F (n + 1) - F n)

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma of_step (h : ∀ n, F (n+1) - F n ≤ F (n+2) - F (n+1)) :
    DiscreteConvex F := by
  exact monotone_nat_of_le_succ h

lemma step (h : DiscreteConvex F) (n : ℕ) :
    F (n+1) - F n ≤ F (n+2) - F (n+1) := by
  exact h (Nat.le_succ n)

lemma sub_zero_le (h : DiscreteConvex F) (n : ℕ) :
    F n - F 0 ≤ (n : ℝ) * (F (n+1) - F n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hs := h.step n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith

lemma secant_le (h : DiscreteConvex F) {n m : ℕ} (hnm : n ≤ m) :
    (m : ℝ) * (F n - F 0) ≤ (n : ℝ) * (F m - F 0) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hs := h.sub_zero_le n
    have hd := h hnm
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ht : F n - F 0 ≤ (n : ℝ) * (F (m+1) - F m) := by
      calc F n - F 0 ≤ (n : ℝ) * (F (n+1) - F n) := hs
           _ ≤ (n : ℝ) * (F (m+1) - F m) := mul_le_mul_of_nonneg_left hd hn0
    push_cast
    nlinarith

lemma le_endpoint (h : DiscreteConvex F) (h0 : F 0 = 0)
    {n m : ℕ} (hnm : n ≤ m) (hm : 0 < m) (B : ℝ) (hB : 0 ≤ B)
    (hend : F m ≤ B) : F n ≤ B := by
  have hs := h.secant_le hnm
  rw [h0, sub_zero, sub_zero] at hs
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  have hh : (m : ℝ) * F n ≤ (m : ℝ) * B := calc
    (m : ℝ) * F n ≤ (n : ℝ) * F m := hs
    _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_left hend hn0
    _ ≤ (m : ℝ) * B := mul_le_mul_of_nonneg_right hnm' hB
  exact (mul_le_mul_iff_right₀ hm0).mp hh


lemma bump (h : DiscreteConvex F) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hgap : 2 * ε ≤ F (n+2) - 2 * F (n+1) + F n) :
    DiscreteConvex (fun k => F k + if k = n+1 then ε else 0) := by
  apply of_step
  intro k
  by_cases hk : k = n
  · subst k
    have hne : n ≠ n+1 := by omega
    have hne' : n+2 ≠ n+1 := by omega
    simp only [ite_eq_right hne, ite_eq_right hne', ite_true, add_zero]
    linarith
  · have hmid : k+1 ≠ n+1 := by omega
    have hlo : F k ≤ F k + if k = n+1 then ε else 0 := by
      split_ifs <;> linarith
    have hhi : F (k+2) ≤ F (k+2) + if k+2 = n+1 then ε else 0 := by
      split_ifs <;> linarith
    simp only [ite_eq_right hmid, add_zero]
    have hs := h.step k
    linarith

end DiscreteConvex




def convexMinorants (I : Set ℕ) (f : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {F | F 0 = 0 ∧ DiscreteConvex F ∧ ∀ n ∈ I, F n ≤ f n}


def convexEnvelope (I : Set ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup ((fun F : ℕ → ℝ => F n) '' convexMinorants I f)

namespace ConvexEnvelope

variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

include hunbounded in
lemma bddAbove (n : ℕ) :
    BddAbove ((fun F : ℕ → ℝ => F n) '' convexMinorants I f) := by
  obtain ⟨k, hnk, hkI⟩ := hunbounded n
  refine ⟨max 0 (f k), ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  exact hF.2.1.le_endpoint hF.1 (Nat.le_of_lt hnk) (by omega)
    _ (le_max_left _ _) ((hF.2.2 k hkI).trans (le_max_right _ _))

include hunbounded in
lemma le_envelope {F : ℕ → ℝ} (hF : F ∈ convexMinorants I f) (n : ℕ) :
    F n ≤ convexEnvelope I f n := by
  exact le_csSup (bddAbove hunbounded n) ⟨F, hF, rfl⟩

include hunbounded hne in
lemma zero : convexEnvelope I f 0 = 0 := by
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨F, hF, rfl⟩
    exact le_of_eq hF.1
  · obtain ⟨F, hF⟩ := hne
    simpa only [hF.1] using le_envelope hunbounded hF 0

include hunbounded hne in
lemma convex : DiscreteConvex (convexEnvelope I f) := by
  apply DiscreteConvex.of_step
  intro n
  have hh : convexEnvelope I f (n+1) ≤
      (convexEnvelope I f n + convexEnvelope I f (n+2)) / 2 := by
    apply csSup_le (hne.image _)
    rintro _ ⟨F, hF, rfl⟩
    have hc := hF.2.1.step n
    have hl := le_envelope hunbounded hF n
    have hr := le_envelope hunbounded hF (n+2)
    linarith
  linarith

include hne in
lemma below {n : ℕ} (hn : n ∈ I) : convexEnvelope I f n ≤ f n := by
  apply csSup_le (hne.image _)
  rintro _ ⟨F, hF, rfl⟩
  exact hF.2.2 n hn

include hunbounded hne in
lemma mem : convexEnvelope I f ∈ convexMinorants I f :=
  ⟨zero hunbounded hne, convex hunbounded hne, fun _ hn => below hne hn⟩

include hunbounded hne in

lemma contact (n : ℕ)
    (hgap : 0 < convexEnvelope I f (n+2) - 2 * convexEnvelope I f (n+1) +
      convexEnvelope I f n) :
    n+1 ∈ I ∧ convexEnvelope I f (n+1) = f (n+1) := by
  let F := convexEnvelope I f
  let δ := F (n+2) - 2 * F (n+1) + F n
  have hδ : 0 < δ := hgap
  have hF : F ∈ convexMinorants I f := mem hunbounded hne
  have maximal : ∀ ε : ℝ, 0 < ε → 2*ε ≤ δ →
      (n+1 ∈ I → F (n+1)+ε ≤ f (n+1)) → False := by
    intro ε hε hεgap hεobs
    let G := fun k => F k + if k = n+1 then ε else 0
    have hG : G ∈ convexMinorants I f := by
      refine ⟨?_, hF.2.1.bump n hε.le hεgap, ?_⟩
      · simp [G, hF.1]
      · intro k hk
        by_cases he : k = n+1
        · subst k
          simpa [G] using hεobs hk
        · simpa [G, he] using hF.2.2 k hk
    have hle := le_envelope hunbounded hG (n+1)
    simp only [G, ite_true] at hle
    change F (n+1) + ε ≤ F (n+1) at hle
    linarith
  have hi : n+1 ∈ I := by
    by_contra hn
    exact maximal (δ/4) (by positivity) (by linarith) (by simp [hn])
  refine ⟨hi, ?_⟩
  have hle := hF.2.2 (n+1) hi
  by_contra hneq
  have hlt : F (n+1) < f (n+1) := lt_of_le_of_ne hle hneq
  let ε := min (δ/4) ((f (n+1) - F (n+1))/2)
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hε₁ : ε ≤ δ/4 := min_le_left _ _
  have hε₂ : ε ≤ (f (n+1) - F (n+1))/2 := min_le_right _ _
  exact maximal ε hε (by linarith) (by intro _; linarith)

end ConvexEnvelope

namespace DiscreteConvex

variable {F : ℕ → ℝ}


lemma slopes_tendsto (h : DiscreteConvex F) (h0 : F 0 = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ F n) :
    Tendsto (fun n => F (n+1) - F n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hn : ∀ᶠ n : ℕ in atTop, b / δ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      (eventually_ge_atTop _)
  filter_upwards [hq, hn, eventually_ge_atTop 1] with n hqn hbn hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs := h.sub_zero_le n
  rw [h0, sub_zero] at hs
  have hb : b ≤ δ * n := (div_le_iff₀ hδ).mp hbn |>.trans_eq (mul_comm _ _)
  have hd : δ * n ≤ F (n+1) - F n := by nlinarith
  exact hb.trans hd

end DiscreteConvex



lemma quadratic_upper_of_curvature {F : ℕ → ℝ} {lam : ℝ} (N : ℕ)
    (h : ∀ n, N ≤ n → F (n+2) - 2*F (n+1) + F n ≤ 2*lam) (k : ℕ) :
    F (N+k) ≤ F N + (k : ℝ) * (F (N+1) - F N) + lam * k * (k-1) := by
  have hs (k : ℕ) : F (N+k+1) - F (N+k) ≤
      F (N+1) - F N + 2*lam*k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := h (N+k) (Nat.le_add_right _ _)
      have e₁ : N + (k+1) + 1 = N+k+2 := by omega
      have e₂ : N + (k+1) = N+k+1 := by omega
      rw [e₁, e₂]
      push_cast
      linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := hs k
    have e : N + (k+1) = N+k+1 := by omega
    rw [e]
    push_cast
    nlinarith




lemma large_curvature {F : ℕ → ℝ} {lam μ : ℝ} (hμ : 0 < μ) (hlamμ : lam < μ)
    (hq : ∀ᶠ n : ℕ in atTop, μ * (n : ℝ)^2 ≤ F n) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ 2*lam < F (n+2) - 2*F (n+1) + F n := by
  intro N
  by_contra! h
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hq
  let C := |F (N+1) - F N - lam| + |F N|
  obtain ⟨k, hk⟩ := exists_nat_gt (max (max (Q : ℝ) 1) (C / (μ-lam)))
  have hkQ : (Q : ℝ) < k := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkC : C / (μ-lam) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk1
  have hQN : Q ≤ N+k := by exact Nat.le_trans (Nat.le_of_lt (Nat.cast_lt.mp hkQ)) (Nat.le_add_left _ _)
  have hlo := hQ (N+k) hQN
  have hhi := quadratic_upper_of_curvature N h k
  have hNC : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlow : μ * (k : ℝ)^2 ≤ F (N+k) := by
    push_cast at hlo
    calc μ * (k : ℝ)^2 ≤ μ * ((N : ℝ) + k)^2 := by gcongr; linarith
         _ ≤ F (N+k) := hlo
  have hF0 : F N ≤ |F N| * k := calc
    F N ≤ |F N| := le_abs_self _
    _ ≤ |F N| * k := le_mul_of_one_le_right (abs_nonneg _) hk1.le
  have hF1 : (F (N+1) - F N - lam) * k ≤ |F (N+1) - F N - lam| * k :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hk0.le
  have hup : F (N+k) ≤ lam * (k : ℝ)^2 + C*k := by
    dsimp [C]
    nlinarith [hhi]
  have hlarge : C < (k : ℝ) * (μ-lam) := (div_lt_iff₀ (sub_pos.mpr hlamμ)).mp hkC
  have hstrict := mul_lt_mul_of_pos_right hlarge hk0
  nlinarith

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma increment_mono (h : DiscreteConvex F) {i j : ℕ} (hij : i ≤ j) (k : ℕ) :
    F (i+k) - F i ≤ F (j+k) - F j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h (Nat.add_le_add_right hij k)
    have e₁ : i + (k+1) = i+k+1 := by omega
    have e₂ : j + (k+1) = j+k+1 := by omega
    rw [e₁, e₂]
    linarith

lemma increment_lower (h : DiscreteConvex F) (q k : ℕ) :
    (k : ℝ) * (F (q+1) - F q) ≤ F (q+k) - F q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h (Nat.le_add_right q k)
    have e : q + (k+1) = q+k+1 := by omega
    rw [e]
    push_cast
    nlinarith

lemma increment_upper (h : DiscreteConvex F) (q k r : ℕ) (hkr : q+k ≤ r+1) :
    F (q+k) - F q ≤ (k : ℝ) * (F (r+1) - F r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h (show q+k ≤ r by omega)
    have ih' := ih (by omega)
    have e : q + (k+1) = q+k+1 := by omega
    rw [e]
    push_cast
    nlinarith

lemma summable_exp_neg_slope (h : DiscreteConvex F) (h0 : F 0 = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ F n) :
    Summable (fun n => Real.exp (-(F (n+1) - F n))) := by
  have hgeo : Summable (fun n : ℕ => Real.exp (-δ) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using hδ)
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [hq, eventually_ge_atTop 1] with n hqn hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs := h.sub_zero_le n
  rw [h0, sub_zero] at hs
  have hd : δ * n ≤ F (n+1) - F n := by nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by nlinarith)

end DiscreteConvex


def normalizedTailTerm (F : ℕ → ℝ) (q k : ℕ) : ℝ :=
  Real.exp (F (k+1) + F q - F (q+k+1))

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma tail_term_bound (h : DiscreteConvex F) {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    normalizedTailTerm F q k ≤
      Real.exp (F 1) * Real.exp (-(F (k+2) - F (k+1))) := by
  have hi := h.increment_mono hq (k+1)
  have e₁ : 1+(k+1) = k+2 := by omega
  have e₂ : q+(k+1) = q+k+1 := by omega
  rw [e₁, e₂] at hi
  rw [normalizedTailTerm, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma tail_term_tendsto (h : DiscreteConvex F)
    (hs : Tendsto (fun n => F (n+1) - F n) atTop atTop) (k : ℕ) :
    Tendsto (fun q => normalizedTailTerm F q k) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot.2
  intro b
  have hsl := hs (eventually_ge_atTop (max 0 (F (k+1) - b)))
  filter_upwards [hsl] with q hq
  have hs0 : 0 ≤ F (q+1) - F q := (le_max_left _ _).trans hq
  have hsb : F (k+1) - b ≤ F (q+1) - F q := (le_max_right _ _).trans hq
  have hi := h.increment_lower q (k+1)
  have e : q+(k+1) = q+k+1 := by omega
  rw [e] at hi
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast at hi
  change F (k+1) + F q - F (q+k+1) ≤ b
  nlinarith

lemma tail_summable (h : DiscreteConvex F)
    (hsum : Summable (fun n => Real.exp (-(F (n+1) - F n))))
    {q : ℕ} (hq : 1 ≤ q) : Summable (normalizedTailTerm F q) := by
  have hmajor := ((summable_nat_add_iff 1).mpr hsum).mul_left (Real.exp (F 1))
  apply hmajor.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < normalizedTailTerm F q k from Real.exp_pos _)]
  simpa only [Nat.add_assoc] using h.tail_term_bound hq k



lemma tail_tsum_tendsto (h : DiscreteConvex F)
    (hsum : Summable (fun n => Real.exp (-(F (n+1) - F n))))
    (hs : Tendsto (fun n => F (n+1) - F n) atTop atTop) :
    Tendsto (fun q => ∑' k, normalizedTailTerm F q k) atTop (𝓝 0) := by
  have hmajor := ((summable_nat_add_iff 1).mpr hsum).mul_left (Real.exp (F 1))
  have hh := tendsto_tsum_of_dominated_convergence hmajor
    (fun k => h.tail_term_tendsto hs k) (show ∀ᶠ q : ℕ in atTop, ∀ k,
      ‖normalizedTailTerm F q k‖ ≤
        Real.exp (F 1) * Real.exp (-(F (k+1+1) - F (k+1))) from ?_)
  · simpa using hh
  · filter_upwards [eventually_ge_atTop 1] with q hq k
    rw [Real.norm_eq_abs, abs_of_pos (show 0 < normalizedTailTerm F q k from Real.exp_pos _)]
    simpa only [Nat.add_assoc] using h.tail_term_bound hq k

end DiscreteConvex


end
end BackwardIntertwiners

end OAI
