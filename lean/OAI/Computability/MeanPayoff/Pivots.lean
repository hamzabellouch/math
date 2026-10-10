import OAI.Computability.MeanPayoff.RawSolutions

namespace OAI

section

end

namespace MeanPayoff.Label

variable {n : ℕ}

def MaxClaim (A : Vec (Fin n)) (D : ℤ) (x : Vec (Fin n)) (i : Fin n) : Prop :=
  32 * (A i + D - x i) ≤ D

def MinClaim (A : Vec (Fin n)) (D : ℤ) (y : Vec (Fin n)) (i : Fin n) : Prop :=
  32 * (y i - A i) ≤ D

def MaxWitness (F : Vec (Fin n) → Vec (Fin n)) (A : Vec (Fin n))
    (D : ℤ) (a : Fin n → ℚ) (x : Vec (Fin n)) : Prop :=
  Subsolution F A (shift A D) x ∧ mass a (lowerActive A x) ≤ 1

def MinWitness (F : Vec (Fin n) → Vec (Fin n)) (A : Vec (Fin n))
    (D : ℤ) (b : Fin n → ℚ) (y : Vec (Fin n)) : Prop :=
  Supersolution F A (shift A D) y ∧ mass b (upperActive (shift A D) y) ≤ 1

def Good (F : Vec (Fin n) → Vec (Fin n)) (A : Vec (Fin n)) (D : ℤ)
    (a b : Fin n → ℚ) (labels : Fin n → Bool) : Prop :=
  (∀ x, MaxWitness F A D a x → ∀ i, MaxClaim A D x i → labels i = true) ∧
  (∀ y, MinWitness F A D b y → ∀ i, MinClaim A D y i → labels i = false)

def peak (hn : 0 < n) (x k : Vec (Fin n)) : ℤ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => x i - k i)

def gap (hn : 0 < n) (x k : Vec (Fin n)) (i : Fin n) : ℤ :=
  peak hn x k - (x i - k i)

def near (hn : 0 < n) (x k : Vec (Fin n)) (r : ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => gap hn x k i < r)

theorem le_peak (hn : 0 < n) (x k : Vec (Fin n)) (i : Fin n) :
    x i - k i ≤ peak hn x k := by
  exact Finset.le_sup' (fun j => x j - k j) (Finset.mem_univ i)

theorem peak_le (hn : 0 < n) (x k : Vec (Fin n)) {s : ℤ}
    (h : ∀ i, x i - k i ≤ s) : peak hn x k ≤ s := by
  exact (Finset.sup'_le_iff _ _).mpr (fun i _ => h i)

theorem peak_attained (hn : 0 < n) (x k : Vec (Fin n)) :
    ∃ i, x i - k i = peak hn x k := by
  obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ) ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => x i - k i)
  exact ⟨i, he.symm⟩

theorem gap_nonneg (hn : 0 < n) (x k : Vec (Fin n)) (i : Fin n) :
    0 ≤ gap hn x k i := sub_nonneg.mpr (le_peak hn x k i)

theorem centerSub_of_support {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A u x k : Vec (Fin n)} {s H : ℤ}
    (hx : Subsolution F A u x) (hH : 0 ≤ H)
    (hdev : ∀ i, x i - k i ≤ s)
    (hout : ∀ i, x i = A i → 2 * H ≤ s - (x i - k i)) :
    Subsolution F (fun i => k i - H) (fun i => k i + H) (centerSub x k s H) ∧
    lowerActive (fun i => k i - H) (centerSub x k s H) ⊆ lowerActive A x := by
  have hs : ∀ i, k i - H < centerSub x k s H i → A i < x i := by
    intro i hi
    have hxi := hx.1.1 i
    have hi' : k i - H < x i - s + H := by
      simpa only [centerSub, lt_max_iff, lt_self_iff_false, or_false] using hi
    by_contra h
    have he : x i = A i := le_antisymm (le_of_not_gt h) hxi
    have := hout i he
    omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i
    exact le_max_right _ _
  · intro i
    change max (x i - s + H) (k i - H) ≤ k i + H
    have := hdev i
    exact max_le (by omega) (by omega)
  · intro i hi
    have hf := hx.2 i (hs i hi)
    have hi' : k i - H < x i - s + H := by
      simpa only [centerSub, lt_max_iff, lt_self_iff_false, or_false] using hi
    have hm : F (shift x (-s + H)) i ≤ F (centerSub x k s H) i := by
      apply laws.mono
      intro j
      simp [shift, centerSub, sub_eq_add_neg, add_assoc]
    rw [laws.translation] at hm
    change F x i + (-s + H) ≤ _ at hm
    change max (x i - s + H) (k i - H) ≤ _
    rw [max_eq_left (le_of_lt hi')]
    omega
  · intro i hi
    simp only [lowerActive, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hs i hi

theorem centerSuper_of_support {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A u y k : Vec (Fin n)} {s H : ℤ}
    (hy : Supersolution F A u y) (hH : 0 ≤ H)
    (hdev : ∀ i, k i - y i ≤ s)
    (hout : ∀ i, y i = u i → 2 * H ≤ s - (k i - y i)) :
    Supersolution F (fun i => k i - H) (fun i => k i + H) (centerSuper y k s H) ∧
    upperActive (fun i => k i + H) (centerSuper y k s H) ⊆ upperActive u y := by
  have hs : ∀ i, centerSuper y k s H i < k i + H → y i < u i := by
    intro i hi
    have hyi := hy.1.2 i
    have hi' : y i + s - H < k i + H := by
      simpa only [centerSuper, min_lt_iff, lt_self_iff_false, or_false] using hi
    by_contra h
    have he : y i = u i := le_antisymm hyi (le_of_not_gt h)
    have := hout i he
    omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i
    change k i - H ≤ min (y i + s - H) (k i + H)
    have := hdev i
    exact le_min (by omega) (by omega)
  · intro i
    exact min_le_right _ _
  · intro i hi
    have hf := hy.2 i (hs i hi)
    have hi' : y i + s - H < k i + H := by
      simpa only [centerSuper, min_lt_iff, lt_self_iff_false, or_false] using hi
    have hm : F (centerSuper y k s H) i ≤ F (shift y (s - H)) i := by
      apply laws.mono
      intro j
      simp [shift, centerSuper, sub_eq_add_neg, add_assoc]
    rw [laws.translation] at hm
    change _ ≤ F y i + (s - H) at hm
    change _ ≤ min (y i + s - H) (k i + H)
    rw [min_eq_left (le_of_lt hi')]
    omega
  · intro i hi
    simp only [upperActive, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hs i hi

theorem centerSub_active (hn : 0 < n) (x k : Vec (Fin n)) (H : ℤ) :
    lowerActive (fun i => k i - H) (centerSub x k (peak hn x k) H) =
      near hn x k (2 * H) := by
  ext i
  simp only [lowerActive, near, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [centerSub, lt_max_iff, lt_self_iff_false, or_false]
  dsimp only [gap]
  omega

theorem centerSuper_active (hn : 0 < n) (y k : Vec (Fin n)) (H : ℤ) :
    upperActive (fun i => k i + H) (centerSuper y k (peak hn k y) H) =
      near hn k y (2 * H) := by
  ext i
  simp only [upperActive, near, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [centerSuper, min_lt_iff, lt_self_iff_false, or_false]
  dsimp only [gap]
  omega

theorem centerSub_claim (hn : 0 < n) (x k : Vec (Fin n)) (H : ℤ)
    {i : Fin n} (hi : 32 * gap hn x k i ≤ 2 * H) :
    MaxClaim (fun j => k j - H) (2 * H) (centerSub x k (peak hn x k) H) i := by
  have := le_max_left (x i - peak hn x k + H) (k i - H)
  dsimp [MaxClaim, centerSub, gap] at *
  omega

theorem centerSuper_claim (hn : 0 < n) (y k : Vec (Fin n)) (H : ℤ)
    {i : Fin n} (hi : 32 * gap hn k y i ≤ 2 * H) :
    MinClaim (fun j => k j - H) (2 * H) (centerSuper y k (peak hn k y) H) i := by
  have := min_le_left (y i + peak hn k y - H) (k i + H)
  dsimp [MinClaim, centerSuper, gap] at *
  omega

theorem max_outside_gap (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    {A x k : Vec (Fin n)} {t : ℤ}
    (_hx : Subsolution F A (shift A (4096 * t)) x)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MaxClaim A (4096 * t) x j)
    {i : Fin n} (hi : x i = A i) : 2944 * t ≤ gap hn x k i := by
  obtain ⟨j, hj⟩ := hrel
  have hp := le_peak hn x k j
  have hkj := hkhi j
  have hki := hklo i
  dsimp [MaxClaim] at hj
  dsimp [gap]
  omega

theorem min_outside_gap (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    {A y k : Vec (Fin n)} {t : ℤ}
    (_hy : Supersolution F A (shift A (4096 * t)) y)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MinClaim A (4096 * t) y j)
    {i : Fin n} (hi : y i = A i + 4096 * t) : 2944 * t ≤ gap hn k y i := by
  obtain ⟨j, hj⟩ := hrel
  have hp := le_peak hn k y j
  have hkj := hklo j
  have hki := hkhi i
  dsimp [MinClaim] at hj
  dsimp [gap]
  omega

theorem translate_max (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A x k : Vec (Fin n)} {t H : ℤ}
    (ht : 0 < t) (hH : 0 ≤ H) (hHD : H ≤ 1024 * t)
    (hx : Subsolution F A (shift A (4096 * t)) x)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MaxClaim A (4096 * t) x j) :
    Subsolution F (fun i => k i - H) (fun i => k i + H)
      (centerSub x k (peak hn x k) H) ∧
    near hn x k (2 * H) ⊆ lowerActive A x := by
  have hc := centerSub_of_support laws hx hH (le_peak hn x k) (fun i hi => by
    have hh := max_outside_gap hn hx hklo hkhi hrel hi
    dsimp [gap] at hh
    omega)
  rw [centerSub_active] at hc
  exact hc

theorem translate_min (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A y k : Vec (Fin n)} {t H : ℤ}
    (ht : 0 < t) (hH : 0 ≤ H) (hHD : H ≤ 1024 * t)
    (hy : Supersolution F A (shift A (4096 * t)) y)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MinClaim A (4096 * t) y j) :
    Supersolution F (fun i => k i - H) (fun i => k i + H)
      (centerSuper y k (peak hn k y) H) ∧
    near hn k y (2 * H) ⊆ upperActive (shift A (4096 * t)) y := by
  have hc := centerSuper_of_support laws hy hH (le_peak hn k y) (fun i hi => by
    have hh := min_outside_gap hn hy hklo hkhi hrel hi
    dsimp [gap] at hh
    omega)
  rw [centerSuper_active] at hc
  exact hc

theorem mass_scale (a : Fin n → ℚ) (c : ℚ) (S : Finset (Fin n)) :
    mass (fun i => c * a i) S = c * mass a S := by
  exact Finset.mul_sum S a c |>.symm

theorem translate_max_witness (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A x k : Vec (Fin n)} {t H : ℤ} {a' : Fin n → ℚ}
    (ht : 0 < t) (hH : 0 ≤ H) (hHD : H ≤ 1024 * t)
    (hx : Subsolution F A (shift A (4096 * t)) x)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MaxClaim A (4096 * t) x j)
    (hmass : mass a' (near hn x k (2 * H)) ≤ 1) :
    MaxWitness F (fun i => k i - H) (2 * H) a'
      (centerSub x k (peak hn x k) H) := by
  have hc := (translate_max hn laws ht hH hHD hx hklo hkhi hrel).1
  have hb : shift (fun i => k i - H) (2 * H) = (fun i => k i + H) := by
    funext i
    simp only [shift]
    omega
  refine ⟨?_, ?_⟩
  · rwa [hb]
  · rwa [centerSub_active]

theorem translate_min_witness (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A y k : Vec (Fin n)} {t H : ℤ} {b' : Fin n → ℚ}
    (ht : 0 < t) (hH : 0 ≤ H) (hHD : H ≤ 1024 * t)
    (hy : Supersolution F A (shift A (4096 * t)) y)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MinClaim A (4096 * t) y j)
    (hmass : mass b' (near hn k y (2 * H)) ≤ 1) :
    MinWitness F (fun i => k i - H) (2 * H) b'
      (centerSuper y k (peak hn k y) H) := by
  have hc := (translate_min hn laws ht hH hHD hy hklo hkhi hrel).1
  have hb : shift (fun i => k i - H) (2 * H) = (fun i => k i + H) := by
    funext i
    simp only [shift]
    omega
  refine ⟨?_, ?_⟩
  · rwa [hb]
  · rwa [hb, centerSuper_active]

def downStep (A : Vec (Fin n)) (t : ℤ) (k : Vec (Fin n))
    (labels : Fin n → Bool) : Vec (Fin n) := fun i =>
  if labels i then k i else max (A i + 1536 * t) (k i - t)

def upStep (A : Vec (Fin n)) (t : ℤ) (k : Vec (Fin n))
    (labels : Fin n → Bool) : Vec (Fin n) := fun i =>
  if labels i then min (A i + 2560 * t) (k i + t) else k i

theorem downStep_bounds {A k : Vec (Fin n)} {t : ℤ} (ht : 0 ≤ t)
    (labels : Fin n → Bool) (hl : ∀ i, A i + 1536 * t ≤ k i) (i : Fin n) :
    A i + 1536 * t ≤ downStep A t k labels i ∧
    k i - t ≤ downStep A t k labels i ∧ downStep A t k labels i ≤ k i := by
  dsimp [downStep]
  split
  · exact ⟨hl i, by omega, le_rfl⟩
  · exact ⟨le_max_left _ _, le_max_right _ _, max_le (hl i) (by omega)⟩

theorem upStep_bounds {A k : Vec (Fin n)} {t : ℤ} (ht : 0 ≤ t)
    (labels : Fin n → Bool) (hu : ∀ i, k i ≤ A i + 2560 * t) (i : Fin n) :
    upStep A t k labels i ≤ A i + 2560 * t ∧
    upStep A t k labels i ≤ k i + t ∧ k i ≤ upStep A t k labels i := by
  dsimp [upStep]
  split
  · exact ⟨min_le_left _ _, min_le_right _ _, le_min (hu i) (by omega)⟩
  · exact ⟨hu i, by omega, le_rfl⟩

theorem downStep_peak (hn : 0 < n) {A x k : Vec (Fin n)} {t : ℤ}
    (ht : 0 ≤ t) (labels : Fin n → Bool)
    (hl : ∀ i, A i + 1536 * t ≤ k i)
    (hprotect : ∀ i, gap hn x k i ≤ t → labels i = true) :
    peak hn x (downStep A t k labels) = peak hn x k := by
  apply le_antisymm
  · apply peak_le
    intro i
    have hi := downStep_bounds ht labels hl i
    have hp := le_peak hn x k i
    by_cases hg : gap hn x k i ≤ t
    · simp only [downStep, hprotect i hg, ↓reduceIte]
      exact hp
    · dsimp [gap] at hg
      omega
  · obtain ⟨i, hi⟩ := peak_attained hn x k
    have hg : gap hn x k i ≤ t := by dsimp [gap]; omega
    have hp := le_peak hn x (downStep A t k labels) i
    simp only [downStep, hprotect i hg, ↓reduceIte] at hp
    omega

theorem upStep_peak (hn : 0 < n) {A y k : Vec (Fin n)} {t : ℤ}
    (ht : 0 ≤ t) (labels : Fin n → Bool)
    (hu : ∀ i, k i ≤ A i + 2560 * t)
    (hprotect : ∀ i, gap hn k y i ≤ t → labels i = false) :
    peak hn (upStep A t k labels) y = peak hn k y := by
  apply le_antisymm
  · apply peak_le
    intro i
    have hi := upStep_bounds ht labels hu i
    have hp := le_peak hn k y i
    by_cases hg : gap hn k y i ≤ t
    · simp only [upStep, hprotect i hg, Bool.false_eq_true, ↓reduceIte]
      exact hp
    · dsimp [gap] at hg
      omega
  · obtain ⟨i, hi⟩ := peak_attained hn k y
    have hg : gap hn k y i ≤ t := by dsimp [gap]; omega
    have hp := le_peak hn (upStep A t k labels) y i
    simp only [upStep, hprotect i hg, Bool.false_eq_true, ↓reduceIte] at hp
    omega

theorem down_protection (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A x k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hx : MaxWitness F A (4096 * t) a x)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MaxClaim A (4096 * t) x j) {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 16 * t) (32 * t) a b labels) :
    peak hn x (downStep A t k labels) = peak hn x k := by
  apply downStep_peak hn ht.le labels hklo
  intro i hi
  have hc := translate_max hn laws ht (H := 16 * t) (by omega) (by omega)
    hx.1 hklo hkhi hrel
  have hm := (mass_mono (fun i => (ha i).le) hc.2).trans hx.2
  have hw := translate_max_witness hn laws ht (H := 16 * t) (by omega) (by omega)
    hx.1 hklo hkhi hrel hm
  have hi' := centerSub_claim hn x k (16 * t) (i := i) (by omega)
  have he : 2 * (16 * t) = 32 * t := by omega
  rw [he] at hw hi'
  exact hgood.1 _ hw i hi'

theorem up_protection (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A y k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (hb : ∀ i, 0 < b i)
    (hy : MinWitness F A (4096 * t) b y)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MinClaim A (4096 * t) y j) {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 16 * t) (32 * t) a b labels) :
    peak hn (upStep A t k labels) y = peak hn k y := by
  apply upStep_peak hn ht.le labels hkhi
  intro i hi
  have hc := translate_min hn laws ht (H := 16 * t) (by omega) (by omega)
    hy.1 hklo hkhi hrel
  have hm := (mass_mono (fun i => (hb i).le) hc.2).trans hy.2
  have hw := translate_min_witness hn laws ht (H := 16 * t) (by omega) (by omega)
    hy.1 hklo hkhi hrel hm
  have hi' := centerSuper_claim hn y k (16 * t) (i := i) (by omega)
  have he : 2 * (16 * t) = 32 * t := by omega
  rw [he] at hw hi'
  exact hgood.2 _ hw i hi'

theorem down_stationary_heavy (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A y k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (hy : MinWitness F A (4096 * t) b y)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hclaim : ∃ j, MinClaim A (4096 * t) y j ∧ A j + 1920 * t ≤ k j)
    {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 16 * t) (32 * t) a (fun i => 4/3 * b i) labels)
    (hstop : downStep A t k labels = k) :
    (3/4 : ℚ) < mass b (near hn k y (32 * t)) := by
  by_contra hmass
  have hm : mass (fun i => (4/3 : ℚ) * b i) (near hn k y (2 * (16 * t))) ≤ 1 := by
    rw [show (2 : ℤ) * (16 * t) = 32 * t by ring, mass_scale]
    linarith
  obtain ⟨j, hj, hkj⟩ := hclaim
  have hw := translate_min_witness hn laws ht (H := 16 * t) (by omega) (by omega)
    hy.1 hklo hkhi ⟨j, hj⟩ hm
  rw [show (2 : ℤ) * (16 * t) = 32 * t by ring] at hw
  obtain ⟨i, hi⟩ := peak_attained hn k y
  have hic := centerSuper_claim hn y k (16 * t) (i := i) (by dsimp [gap]; omega)
  rw [show (2 : ℤ) * (16 * t) = 32 * t by ring] at hic
  have hil := hgood.2 _ hw i hic
  have his := congrFun hstop i
  simp only [downStep, hil, Bool.false_eq_true, ↓reduceIte] at his
  have hp := le_peak hn k y j
  have hiy := hy.1.1.1 i
  dsimp [MinClaim] at hj
  have hcap : k i = A i + 1536 * t := by omega
  linarith only [hp, hj, hkj, hiy, hi, hcap, ht]

theorem up_stationary_heavy (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A x k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (hx : MaxWitness F A (4096 * t) a x)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hclaim : ∃ j, MaxClaim A (4096 * t) x j ∧ k j ≤ A j + 2176 * t)
    {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 16 * t) (32 * t) (fun i => 4/3 * a i) b labels)
    (hstop : upStep A t k labels = k) :
    (3/4 : ℚ) < mass a (near hn x k (32 * t)) := by
  by_contra hmass
  have hm : mass (fun i => (4/3 : ℚ) * a i) (near hn x k (2 * (16 * t))) ≤ 1 := by
    rw [show (2 : ℤ) * (16 * t) = 32 * t by ring, mass_scale]
    linarith
  obtain ⟨j, hj, hkj⟩ := hclaim
  have hw := translate_max_witness hn laws ht (H := 16 * t) (by omega) (by omega)
    hx.1 hklo hkhi ⟨j, hj⟩ hm
  rw [show (2 : ℤ) * (16 * t) = 32 * t by ring] at hw
  obtain ⟨i, hi⟩ := peak_attained hn x k
  have hic := centerSub_claim hn x k (16 * t) (i := i) (by dsimp [gap]; omega)
  rw [show (2 : ℤ) * (16 * t) = 32 * t by ring] at hic
  have hil := hgood.1 _ hw i hic
  have his := congrFun hstop i
  simp only [upStep, hil, ↓reduceIte] at his
  have hp := le_peak hn x k j
  have hix := hx.1.1.2 i
  dsimp [MaxClaim] at hj
  dsimp [shift] at hix
  omega

theorem near_mono_up (hn : 0 < n) {y k k' : Vec (Fin n)} {r : ℤ}
    (hkk' : k ≤ k') (hpeak : peak hn k' y = peak hn k y) :
    near hn k y r ⊆ near hn k' y r := by
  intro i hi
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  dsimp [gap] at hi ⊢
  rw [hpeak]
  exact (sub_le_sub_left (sub_le_sub_right (hkk' i) _) _).trans_lt hi

theorem max_mark_safe (hn : 0 < n) {A x k : Vec (Fin n)} {t : ℤ}
    (hpeak : peak hn x k ≤ 2048 * t) {i : Fin n}
    (hi : MaxClaim A (4096 * t) x i) : A i + 1920 * t ≤ k i := by
  have := le_peak hn x k i
  dsimp [MaxClaim] at hi
  omega

theorem min_mark_safe (hn : 0 < n) {A y k : Vec (Fin n)} {t : ℤ}
    (hpeak : peak hn k y ≤ 2048 * t) {i : Fin n}
    (hi : MinClaim A (4096 * t) y i) : k i ≤ A i + 2176 * t := by
  have := le_peak hn k y i
  dsimp [MinClaim] at hi
  omega

def reweight (a : Fin n → ℚ) (favorable : Fin n → Bool) : Fin n → ℚ := fun i =>
  if favorable i then 4/5 * a i else 8/5 * a i

theorem reweight_pos {a : Fin n → ℚ} (ha : ∀ i, 0 < a i)
    (labels : Fin n → Bool) (i : Fin n) : 0 < reweight a labels i := by
  dsimp [reweight]
  split <;> exact mul_pos (by norm_num) (ha i)

theorem reweight_mass (a : Fin n → ℚ) (labels : Fin n → Bool) (S : Finset (Fin n)) :
    mass (reweight a labels) S =
      8/5 * mass a S - 4/5 * mass a (S.filter (fun i => labels i = true)) := by
  unfold mass reweight
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases labels i <;> simp
  ring

theorem reweight_survives {a : Fin n → ℚ} (ha : ∀ i, 0 ≤ a i)
    {labels : Fin n → Bool} {S N : Finset (Fin n)}
    (hNS : N ⊆ S) (hlabels : ∀ i ∈ N, labels i = true)
    (hS : mass a S ≤ 1) (hN : (3/4 : ℚ) < mass a N) :
    mass (reweight a labels) S < 1 := by
  have hnq : N ⊆ S.filter (fun i => labels i = true) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨hNS hi, hlabels i hi⟩
  have hm := mass_mono ha hnq
  rw [reweight_mass]
  linarith

theorem provisional_max_labels (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A x k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hx : MaxWitness F A (4096 * t) a x)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MaxClaim A (4096 * t) x j) {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 1024 * t) (2048 * t) a b labels) :
    ∀ i ∈ near hn x k (32 * t), labels i = true := by
  have hc := translate_max hn laws ht (H := 1024 * t) (by omega) le_rfl
    hx.1 hklo hkhi hrel
  have hm := (mass_mono (fun i => (ha i).le) hc.2).trans hx.2
  have hw := translate_max_witness hn laws ht (H := 1024 * t) (by omega) le_rfl
    hx.1 hklo hkhi hrel hm
  rw [show (2 : ℤ) * (1024 * t) = 2048 * t by ring] at hw
  intro i hi
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hic := centerSub_claim hn x k (1024 * t) (i := i) (by omega)
  rw [show (2 : ℤ) * (1024 * t) = 2048 * t by ring] at hic
  exact hgood.1 _ hw i hic

theorem provisional_min_labels (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A y k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (hb : ∀ i, 0 < b i)
    (hy : MinWitness F A (4096 * t) b y)
    (hklo : ∀ i, A i + 1536 * t ≤ k i)
    (hkhi : ∀ i, k i ≤ A i + 2560 * t)
    (hrel : ∃ j, MinClaim A (4096 * t) y j) {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 1024 * t) (2048 * t) a b labels) :
    ∀ i ∈ near hn k y (32 * t), labels i = false := by
  have hc := translate_min hn laws ht (H := 1024 * t) (by omega) le_rfl
    hy.1 hklo hkhi hrel
  have hm := (mass_mono (fun i => (hb i).le) hc.2).trans hy.2
  have hw := translate_min_witness hn laws ht (H := 1024 * t) (by omega) le_rfl
    hy.1 hklo hkhi hrel hm
  rw [show (2 : ℤ) * (1024 * t) = 2048 * t by ring] at hw
  intro i hi
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hic := centerSuper_claim hn y k (1024 * t) (i := i) (by omega)
  rw [show (2 : ℤ) * (1024 * t) = 2048 * t by ring] at hic
  exact hgood.2 _ hw i hic

def override (A kd kf : Vec (Fin n)) (t : ℤ) (labels : Fin n → Bool) : Fin n → Bool :=
  fun i => if kd i < A i + 1920*t then false
    else if A i + 2176*t < kf i then true else labels i

theorem max_survives (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A x k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hx : MaxWitness F A (4096*t) a x)
    (hklo : ∀ i, A i + 1536*t ≤ k i) (hkhi : ∀ i, k i ≤ A i + 2560*t)
    (hrel : ∃ j, MaxClaim A (4096*t) x j)
    (hm : (3/4 : ℚ) < mass a (near hn x k (32*t))) {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 1024*t) (2048*t) a b labels) :
    MaxWitness F A (4096*t) (reweight a labels) x := by
  refine ⟨hx.1, le_of_lt ?_⟩
  have hc := translate_max hn laws ht (H := 16*t) (by omega) (by omega)
    hx.1 hklo hkhi hrel
  rw [show (2 : ℤ)*(16*t)=32*t by ring] at hc
  exact reweight_survives (fun i => (ha i).le) hc.2
    (provisional_max_labels hn laws ht ha hx hklo hkhi hrel hgood) hx.2 hm

theorem min_survives (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A y k : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (hb : ∀ i, 0 < b i) (hy : MinWitness F A (4096*t) b y)
    (hklo : ∀ i, A i + 1536*t ≤ k i) (hkhi : ∀ i, k i ≤ A i + 2560*t)
    (hrel : ∃ j, MinClaim A (4096*t) y j)
    (hm : (3/4 : ℚ) < mass b (near hn k y (32*t))) {labels : Fin n → Bool}
    (hgood : Good F (fun i => k i - 1024*t) (2048*t) a b labels) :
    MinWitness F A (4096*t) (reweight b (fun i => !(labels i))) y := by
  refine ⟨hy.1, le_of_lt ?_⟩
  have hc := translate_min hn laws ht (H := 16*t) (by omega) (by omega)
    hy.1 hklo hkhi hrel
  rw [show (2 : ℤ)*(16*t)=32*t by ring] at hc
  apply reweight_survives (fun i => (hb i).le) hc.2 _ hy.2 hm
  intro i hi
  simp only [provisional_min_labels hn laws ht hb hy hklo hkhi hrel hgood i hi,
    Bool.not_false]

theorem override_good (hn : 0 < n) {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {A kd kf : Vec (Fin n)} {t : ℤ} {a b : Fin n → ℚ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hklo : ∀ i, A i + 1536*t ≤ kf i) (hkhi : ∀ i, kf i ≤ A i + 2560*t)
    (hmaxsafe : ∀ x, MaxWitness F A (4096*t) a x →
      ∀ i, MaxClaim A (4096*t) x i → A i + 1920*t ≤ kd i)
    (hminsafe : ∀ y, MinWitness F A (4096*t) b y →
      ∀ i, MinClaim A (4096*t) y i → kf i ≤ A i + 2176*t)
    (hmaxmass : ∀ x, MaxWitness F A (4096*t) a x →
      (∃ i, MaxClaim A (4096*t) x i ∧ kf i ≤ A i + 2176*t) →
      (3/4 : ℚ) < mass a (near hn x kf (32*t)))
    (hminmass : ∀ y, MinWitness F A (4096*t) b y →
      (∃ i, MinClaim A (4096*t) y i ∧ A i + 1920*t ≤ kd i) →
      (3/4 : ℚ) < mass b (near hn kf y (32*t)))
    {provisional continuation : Fin n → Bool}
    (hp : Good F (fun i => kf i - 1024*t) (2048*t) a b provisional)
    (hc : Good F A (4096*t) (reweight a provisional)
      (reweight b (fun i => !(provisional i))) continuation) :
    Good F A (4096*t) a b (override A kd kf t continuation) := by
  constructor
  · intro x hx i hi
    have hs := hmaxsafe x hx i hi
    simp only [override, ite_eq_right (not_lt.mpr hs)]
    split
    · rfl
    · rename_i hnmark
      have hm := hmaxmass x hx ⟨i, hi, le_of_not_gt hnmark⟩
      have hw := max_survives hn laws ht ha hx hklo hkhi ⟨i, hi⟩ hm hp
      exact hc.1 x hw i hi
  · intro y hy i hi
    have hs := hminsafe y hy i hi
    dsimp only [override]
    split
    · rfl
    · rename_i hnmark
      simp only [ite_eq_right (not_lt.mpr hs)]
      have hm := hminmass y hy ⟨i, hi, le_of_not_gt hnmark⟩
      have hw := min_survives hn laws ht hb hy hklo hkhi ⟨i, hi⟩ hm hp
      exact hc.2 y hw i hi

theorem budget_exists (a b : Fin n → ℚ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∃ B : ℕ, ∀ i, 1 < (32/25 : ℚ)^B * (a i*b i) := by
  classical
  have h : ∀ i, ∃ B : ℕ, 1 < (32/25 : ℚ)^B * (a i*b i) := by
    intro i
    obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (1/(a i*b i)) (by norm_num : (1 : ℚ) < 32/25)
    exact ⟨B, (div_lt_iff₀ (mul_pos (ha i) (hb i))).mp hB⟩
  choose B hB using h
  refine ⟨Finset.univ.sup B, fun i => ?_⟩
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 32/25)
    (Finset.le_sup (f := B) (Finset.mem_univ i))
  exact (hB i).trans_le (mul_le_mul_of_nonneg_right hp (mul_pos (ha i) (hb i)).le)

noncomputable def budget (a b : Fin n → ℚ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) : ℕ :=
  Nat.find (budget_exists a b ha hb)

theorem budget_spec (a b : Fin n → ℚ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∀ i, 1 < (32/25 : ℚ)^budget a b ha hb * (a i*b i) :=
  Nat.find_spec (budget_exists a b ha hb)

theorem budget_zero_iff (a b : Fin n → ℚ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    budget a b ha hb = 0 ↔ ∀ i, 1 < a i*b i := by
  simp [budget, Nat.find_eq_zero]

theorem budget_decreases {a b a' b' : Fin n → ℚ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (ha' : ∀ i, 0 < a' i) (hb' : ∀ i, 0 < b' i)
    (hbase : ¬ ∀ i, 1 < a i*b i)
    (hprod : ∀ i, (32/25 : ℚ)*(a i*b i) ≤ a' i*b' i) :
    budget a' b' ha' hb' < budget a b ha hb := by
  have hp : 0 < budget a b ha hb := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hbase ((budget_zero_iff a b ha hb).mp hz)
  obtain ⟨B, hB⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hs := budget_spec a b ha hb
  rw [hB] at hs
  have hs' : ∀ i, 1 < (32/25 : ℚ)^B * (a' i*b' i) := by
    intro i
    have hi := hs i
    rw [pow_succ, mul_assoc] at hi
    exact hi.trans_le (mul_le_mul_of_nonneg_left (hprod i) (by positivity))
  have hmin := Nat.find_min' (budget_exists a' b' ha' hb') hs'
  change budget a' b' ha' hb' ≤ B at hmin
  omega

theorem reweight_product (a b : Fin n → ℚ) (labels : Fin n → Bool) (i : Fin n) :
    reweight a labels i * reweight b (fun j => !(labels j)) i =
      (32/25 : ℚ)*(a i*b i) := by
  cases h : labels i <;> simp [reweight, h] <;> ring

end MeanPayoff.Label

end OAI
