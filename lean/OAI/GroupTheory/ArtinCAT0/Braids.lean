import OAI.GroupTheory.ArtinCAT0.Pairing

namespace OAI

namespace ArtinCAT0

section BraidAlgebra

variable {G : Type*} [Group G]

/-- The length-three and distant commutation relations on m successive letters.
The letters are zero-indexed here. -/
def BraidRelations (m : ℕ) (s : ℕ → G) : Prop :=
  (∀ i, i + 1 < m → s i * s (i+1) * s i = s (i+1) * s i * s (i+1)) ∧
  (∀ i j, i < m → j < m → i + 2 ≤ j → Commute (s i) (s j))

def braidLoop (s : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => s n * braidLoop s n * s n

def braidCenter (s : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => braidCenter s n * braidLoop s (n+1)

def braidDelta (s : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => braidDelta s n * s n

lemma commute_braidLoop {g : G} {s : ℕ → G} {n : ℕ}
    (hc : ∀ i < n, Commute g (s i)) : Commute g (braidLoop s n) := by
  induction n with
  | zero => exact Commute.one_right g
  | succ n ih =>
    exact ((hc n (by omega)).mul_right (ih (fun i hi => hc i (by omega)))).mul_right
      (hc n (by omega))

lemma commute_braidCenter {g : G} {s : ℕ → G} {n : ℕ}
    (hc : ∀ i < n, Commute g (s i)) : Commute g (braidCenter s n) := by
  induction n with
  | zero => exact Commute.one_right g
  | succ n ih =>
    exact (ih (fun i hi => hc i (by omega))).mul_right (commute_braidLoop hc)

lemma commute_braidDelta {g : G} {s : ℕ → G} {n : ℕ}
    (hc : ∀ i < n, Commute g (s i)) : Commute g (braidDelta s n) := by
  induction n with
  | zero => exact Commute.one_right g
  | succ n ih =>
    exact (ih (fun i hi => hc i (by omega))).mul_right (hc n (by omega))

lemma braid_loop_step {a b C : G} (hab : a*b*a = b*a*b) (hbC : Commute b C) :
    Commute a (b * (a*C*a) * b) := by
  change a * (b * (a*C*a) * b) = b * (a*C*a) * b * a
  calc
    a * (b * (a*C*a) * b) = (a*b*a)*C*a*b := by group
    _ = (b*a*b)*C*a*b := by rw [hab]
    _ = b*a*(b*C)*a*b := by group
    _ = b*a*(C*b)*a*b := by rw [hbC.eq]
    _ = b*a*C*(b*a*b) := by group
    _ = b*a*C*(a*b*a) := by rw [← hab]
    _ = b * (a*C*a) * b * a := by group

lemma braidLoop_commute {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n i : ℕ} (hn : n ≤ m) (hi : i + 1 < n) : Commute (s i) (braidLoop s n) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more k ih₀ ih₁ =>
    by_cases h : i + 1 < k+1
    · exact ((hs.2 i (k+1) (by omega) (by omega) (by omega)).mul_right
        (ih₁ (by omega) h)).mul_right (hs.2 i (k+1) (by omega) (by omega) (by omega))
    · have he : i = k := by omega
      subst i
      exact braid_loop_step (hs.1 k (by omega))
        (commute_braidLoop (fun j hj => (hs.2 j (k+1) (by omega) (by omega) (by omega)).symm))

lemma braidLoops_commute {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ m) : Commute (braidLoop s j) (braidLoop s k) := by
  rcases lt_or_eq_of_le hjk with hlt | rfl
  · exact (commute_braidLoop (fun i hi => (braidLoop_commute hs hk (by omega)).symm)).symm
  · exact Commute.refl _

lemma braid_center_step {s L : G} (hc : Commute L (s*L*s)) :
    Commute s (L*(s*L*s)) := by
  change L*(s*L*s) = (s*L*s)*L at hc
  change s * (L * (s*L*s)) = L * (s*L*s) * s
  calc
    s * (L * (s*L*s)) = ((s*L*s)*L)*s := by group
    _ = (L*(s*L*s))*s := by rw [← hc]

lemma braidCenter_commute {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n i : ℕ} (hn : n ≤ m) (hi : i < n) : Commute (s i) (braidCenter s n) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one =>
    have he : i = 0 := by omega
    subst i
    simp only [braidCenter, braidLoop, mul_one, one_mul]
    exact (Commute.refl _).mul_right (Commute.refl _)
  | more k ih₀ ih₁ =>
    by_cases h : i < k+1
    · exact (ih₁ (by omega) h).mul_right (braidLoop_commute hs hn (by omega))
    · have he : i = k+1 := by omega
      subst i
      have hpre : Commute (s (k+1)) (braidCenter s k) :=
        commute_braidCenter (fun j hj => (hs.2 j (k+1) (by omega) (by omega) (by omega)).symm)
      have hlast := braid_center_step (braidLoops_commute hs (j := k+1) (k := k+2) (by omega) hn)
      simpa only [braidCenter, braidLoop, mul_assoc] using hpre.mul_right hlast

lemma braidDelta_shift {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n i : ℕ} (hn : n ≤ m) (hi : i + 1 < n) :
    braidDelta s n * s i = s (i+1) * braidDelta s n := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more k ih₀ ih₁ =>
    by_cases h : i+1 < k+1
    · rw [braidDelta, mul_assoc, ← (hs.2 i (k+1) (by omega) (by omega) (by omega)).eq,
        ← mul_assoc, ih₁ (by omega) h, mul_assoc]
    · have he : i = k := by omega
      subst i
      have hc : Commute (s (k+1)) (braidDelta s k) :=
        commute_braidDelta (fun j hj => (hs.2 j (k+1) (by omega) (by omega) (by omega)).symm)
      simp only [braidDelta]
      calc
        braidDelta s k * s k * s (k+1) * s k = braidDelta s k * (s k*s (k+1)*s k) := by group
        _ = braidDelta s k * (s (k+1)*s k*s (k+1)) := by rw [hs.1 k (by omega)]
        _ = (braidDelta s k * s (k+1)) * s k * s (k+1) := by group
        _ = (s (k+1) * braidDelta s k) * s k * s (k+1) := by rw [hc.symm.eq]
        _ = s (k+1) * (braidDelta s k * s k * s (k+1)) := by group

lemma braidDelta_conjugate {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {i : ℕ} (hi : i + 1 < m) :
    braidDelta s m * s i * (braidDelta s m)⁻¹ = s (i+1) := by
  rw [braidDelta_shift hs (le_refl m) hi]
  group

lemma braid_conjugate {a b : G} (h : a*b*a = b*a*b) : (a*b)*a*(a*b)⁻¹ = b := by
  rw [h]
  group

lemma braidCenter_two {s : ℕ → G} (h : s 0*s 1*s 0 = s 1*s 0*s 1) :
    braidCenter s 2 = (s 0*s 1)^3 := by
  simp only [braidCenter, braidLoop, mul_one, one_mul]
  calc
    s 0*s 0*(s 1*(s 0*s 0)*s 1) = s 0*(s 0*s 1*s 0)*s 0*s 1 := by group
    _ = s 0*(s 1*s 0*s 1)*s 0*s 1 := by rw [h]
    _ = (s 0*s 1)^3 := by simp only [pow_succ, pow_zero]; group

lemma braidLoop_congr {s t : ℕ → G} {n : ℕ} (he : ∀ i < n, s i = t i) :
    braidLoop s n = braidLoop t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [braidLoop, he n (by omega), ih (fun i hi => he i (by omega))]

lemma braidCenter_congr {s t : ℕ → G} {n : ℕ} (he : ∀ i < n, s i = t i) :
    braidCenter s n = braidCenter t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [braidCenter, braidLoop_congr he, ih (fun i hi => he i (by omega))]

lemma map_braidLoop {H : Type*} [Group H] (f : G →* H) (s : ℕ → G) (n : ℕ) :
    f (braidLoop s n) = braidLoop (fun i => f (s i)) n := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => simp only [braidLoop, map_mul, ih]

lemma map_braidCenter {H : Type*} [Group H] (f : G →* H) (s : ℕ → G) (n : ℕ) :
    f (braidCenter s n) = braidCenter (fun i => f (s i)) n := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => simp only [braidCenter, map_mul, map_braidLoop, ih]

lemma braidDelta_pow_conjugate {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {i k : ℕ} (hik : i+k < m) :
    (braidDelta s m)^k * s i * ((braidDelta s m)^k)⁻¹ = s (i+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (by omega)
    calc
      (braidDelta s m)^(k+1) * s i * ((braidDelta s m)^(k+1))⁻¹ =
        braidDelta s m * ((braidDelta s m)^k * s i * ((braidDelta s m)^k)⁻¹) *
          (braidDelta s m)⁻¹ := by rw [pow_succ']; group
      _ = braidDelta s m * s (i+k) * (braidDelta s m)⁻¹ := by rw [hi]
      _ = s (i+(k+1)) := by simpa only [Nat.add_assoc] using braidDelta_conjugate hs (by omega : i+k+1 < m)

lemma braidCenter_shift_conjugate {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n k : ℕ} (hnk : n+k ≤ m) :
    (braidDelta s m)^k * braidCenter s n * ((braidDelta s m)^k)⁻¹ =
      braidCenter (fun i => s (i+k)) n := by
  let f : G →* G := (MulAut.conj ((braidDelta s m)^k)).toMonoidHom
  change f (braidCenter s n) = _
  rw [map_braidCenter]
  apply braidCenter_congr
  intro i hi
  exact braidDelta_pow_conjugate hs (by omega)

end BraidAlgebra

section BraidLengths

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

lemma lengthPairing_braid_equal (hG : GeometricAction G X) (x : X)
    {g a b : G} (hga : Commute g a) (hgb : Commute g b) (hab : a*b*a = b*a*b) :
    lengthPairing x g a = lengthPairing x g b := by
  have he : lengthPairing x g (a*b*a) = lengthPairing x g (b*a*b) := congrArg _ hab
  rw [lengthPairing_centralizer hG x (hga.mul_right hgb) hga,
    lengthPairing_centralizer hG x hga hgb,
    lengthPairing_centralizer hG x (hgb.mul_right hga) hgb,
    lengthPairing_centralizer hG x hgb hga] at he
  linarith

lemma lengthPairing_braid_constant (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {m n : ℕ} (hs : BraidRelations m s) (hn : n ≤ m)
    (hc : ∀ i < n, Commute g (s i)) {i : ℕ} (hi : i < n) :
    lengthPairing x g (s i) = lengthPairing x g (s 0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← lengthPairing_braid_equal hG x (hc i (by omega)) (hc (i+1) hi) (hs.1 i (by omega))]
    exact ih (by omega)

lemma lengthPairing_braidLoop (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {n : ℕ} {α : ℝ}
    (hc : ∀ i < n, Commute g (s i)) (he : ∀ i < n, lengthPairing x g (s i) = α) :
    lengthPairing x g (braidLoop s n) = 2 * (n : ℝ) * α := by
  induction n with
  | zero => simp [braidLoop, lengthPairing_one hG.2.1]
  | succ n ih =>
    rw [braidLoop,
      lengthPairing_centralizer hG x ((hc n (by omega)).mul_right (commute_braidLoop (fun i hi => hc i (by omega))))
        (hc n (by omega)),
      lengthPairing_centralizer hG x (hc n (by omega)) (commute_braidLoop (fun i hi => hc i (by omega))),
      ih (fun i hi => hc i (by omega)) (fun i hi => he i (by omega)), he n (by omega)]
    push_cast
    ring

lemma lengthPairing_braidCenter (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {n : ℕ} {α : ℝ}
    (hc : ∀ i < n, Commute g (s i)) (he : ∀ i < n, lengthPairing x g (s i) = α) :
    lengthPairing x g (braidCenter s n) = (n : ℝ) * (n+1) * α := by
  induction n with
  | zero => simp [braidCenter, lengthPairing_one hG.2.1]
  | succ n ih =>
    rw [braidCenter,
      lengthPairing_centralizer hG x (commute_braidCenter (fun i hi => hc i (by omega))) (commute_braidLoop hc),
      ih (fun i hi => hc i (by omega)) (fun i hi => he i (by omega)),
      lengthPairing_braidLoop hG x hc he]
    push_cast
    ring

lemma braidCenter_length_sq (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m n i : ℕ} (hs : BraidRelations m s) (hn : n ≤ m) (hi : i < n) :
    stableLengthAt x (braidCenter s n)^2 =
      (n : ℝ) * (n+1) * lengthPairing x (s i) (braidCenter s n) := by
  have hc : ∀ j < n, Commute (braidCenter s n) (s j) :=
    fun j hj => (braidCenter_commute hs hn hj).symm
  have he : ∀ j < n, lengthPairing x (braidCenter s n) (s j) =
      lengthPairing x (braidCenter s n) (s i) := by
    intro j hj
    rw [lengthPairing_braid_constant hG x hs hn hc hj,
      lengthPairing_braid_constant hG x hs hn hc hi]
  rw [← lengthPairing_self hG.2.1 x, lengthPairing_braidCenter hG x hc he,
    lengthPairing_symmetric x (hc i hi)]

omit [ProperSpace X] [Nonempty X] in
lemma braid_generator_length (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m i : ℕ} (hs : BraidRelations m s) (hi : i < m) :
    stableLengthAt x (s i) = stableLengthAt x (s 0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← braid_conjugate (hs.1 i (by omega)), stableLength_conjugate hG.2.1]
    exact ih (by omega)

lemma braid_nonadjacent_pairing (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m i j : ℕ} (hs : BraidRelations m s)
    (hi : i < m) (hj : j < m) (hij : i+2 ≤ j) :
    lengthPairing x (s i) (s j) = lengthPairing x (s 0) (s 2) := by
  have he₁ : lengthPairing x (s i) (s j) = lengthPairing x (s 0) (s j) := by
    rw [lengthPairing_symmetric x (hs.2 i j hi hj hij),
      lengthPairing_braid_constant hG x hs (n := j-1) (by omega)
        (fun k hk => (hs.2 k j (by omega) hj (by omega)).symm) (by omega),
      lengthPairing_symmetric x (hs.2 0 j (by omega) hj (by omega)).symm]
  rw [he₁]
  have hj₂ : 2 ≤ j := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj₂
  clear he₁ hij hi hj₂
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2+(k+1) = (2+k)+1 by omega,
      ← lengthPairing_braid_equal hG x (hs.2 0 (2+k) (by omega) (by omega) (by omega))
        (hs.2 0 ((2+k)+1) (by omega) (by omega) (by omega)) (hs.1 (2+k) (by omega))]
    exact ih (by omega)

lemma lengthPairing_disjoint_centers (hG : GeometricAction G X) (x : X)
    {s t : ℕ → G} {n k : ℕ} {α : ℝ}
    (hc : ∀ i < n, ∀ j < k, Commute (s i) (t j))
    (he : ∀ i < n, ∀ j < k, lengthPairing x (s i) (t j) = α) :
    lengthPairing x (braidCenter s n) (braidCenter t k) =
      (n : ℝ)*(n+1)*((k : ℝ)*(k+1))*α := by
  have hct (i : ℕ) (hi : i < n) : Commute (s i) (braidCenter t k) :=
    commute_braidCenter (hc i hi)
  rw [lengthPairing_symmetric x (commute_braidCenter (fun i hi => (hct i hi).symm)).symm,
    lengthPairing_braidCenter hG x (fun i hi => (hct i hi).symm)
      (fun i hi => by rw [lengthPairing_symmetric x (hct i hi).symm,
        lengthPairing_braidCenter hG x (hc i hi) (he i hi)])]
  ring

lemma lengthPairing_braidDelta (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {n : ℕ} {α : ℝ}
    (hc : ∀ i < n, Commute g (s i)) (he : ∀ i < n, lengthPairing x g (s i) = α) :
    lengthPairing x g (braidDelta s n) = (n : ℝ) * α := by
  induction n with
  | zero => simp [braidDelta, lengthPairing_one hG.2.1]
  | succ n ih =>
    rw [braidDelta,
      lengthPairing_centralizer hG x (commute_braidDelta (fun i hi => hc i (by omega))) (hc n (by omega)),
      ih (fun i hi => hc i (by omega)) (fun i hi => he i (by omega)), he n (by omega)]
    push_cast
    ring

lemma equiangular_product_sq (hG : GeometricAction G X) (x : X)
    {t : ℕ → G} {n : ℕ} {q v : ℝ}
    (hc : ∀ i j, i < j → j < n → Commute (t i) (t j))
    (hQ : ∀ i < n, stableLengthAt x (t i)^2 = q)
    (hP : ∀ i j, i < j → j < n → lengthPairing x (t i) (t j) = v) :
    stableLengthAt x (braidDelta t n)^2 = (n : ℝ)*q + (n : ℝ)*(n-1)*v := by
  induction n with
  | zero => simp [braidDelta, stableLength_one hG.2.1]
  | succ n ih =>
    rw [braidDelta, stableLength_product_sq,
      ih (fun i j hij hj => hc i j hij (by omega)) (fun i hi => hQ i (by omega))
        (fun i j hij hj => hP i j hij (by omega)), hQ n (by omega),
      lengthPairing_symmetric x (commute_braidDelta (fun i hi => (hc i n hi (by omega)).symm)).symm,
      lengthPairing_braidDelta hG x (fun i hi => (hc i n hi (by omega)).symm)
        (fun i hi => by rw [lengthPairing_symmetric x (hc i n hi (by omega)).symm, hP i n hi (by omega)])]
    push_cast
    ring

lemma braid_loop_character (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m n : ℕ} (hs : BraidRelations m s) (hn : n+2 ≤ m) :
    lengthPairing x (s 0) (braidLoop s (n+2)) =
      lengthPairing x (s 0) (braidLoop s 2) + 2*(n : ℝ)*lengthPairing x (s 0) (s 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, braidLoop,
      lengthPairing_centralizer hG x ((hs.2 0 (n+2) (by omega) (by omega) (by omega)).mul_right
        (braidLoop_commute hs (by omega) (by omega)))
        (hs.2 0 (n+2) (by omega) (by omega) (by omega)),
      lengthPairing_centralizer hG x (hs.2 0 (n+2) (by omega) (by omega) (by omega))
        (braidLoop_commute hs (by omega) (by omega)),
      ih (by omega), braid_nonadjacent_pairing hG x hs (by omega) (by omega) (by omega)]
    push_cast
    ring

lemma braid_center_character (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m n : ℕ} (hs : BraidRelations m s) (hn : n+2 ≤ m) :
    lengthPairing x (s 0) (braidCenter s (n+2)) =
      lengthPairing x (s 0) (braidCenter s 2) + (n : ℝ)*lengthPairing x (s 0) (braidLoop s 2) +
        (n : ℝ)*(n+1)*lengthPairing x (s 0) (s 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, braidCenter,
      lengthPairing_centralizer hG x (braidCenter_commute hs (by omega) (by omega))
        (braidLoop_commute hs (by omega) (by omega)),
      ih (by omega), braid_loop_character hG x hs (n := n+1) hn]
    push_cast
    ring

omit [ProperSpace X] [Nonempty X] in
lemma lengthPairing_le_self_of_equal_length (hG : GeometricAction G X) (x : X)
    {g h : G} (hc : Commute g h) (hL : stableLengthAt x g = stableLengthAt x h) :
    lengthPairing x g h ≤ stableLengthAt x g ^ 2 := by
  have he := stableLength_product_sq x g h⁻¹
  rw [stableLength_inv hG.2.1, ← hL, lengthPairing_inv hG.1 hG.2.1 x hc] at he
  nlinarith [sq_nonneg (stableLengthAt x (g*h⁻¹))]

/-- Quantitative braid constraint, in a division-free form. -/
lemma braid_forty_squared (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} (hs : BraidRelations 39 s) :
    143 * stableLengthAt x ((s 0)^2)^2 ≤ 57 * stableLengthAt x ((s 0*s 1)^3)^2 := by
  let q := stableLengthAt x (s 0)^2
  let v := lengthPairing x (s 0) (s 2)
  let β := lengthPairing x (s 0) (braidLoop s 2)
  have hodd : 0 ≤ 20*q + 380*v := by
    have he := equiangular_product_sq hG x (t := fun i => s (2*i)) (n := 20)
      (q := q) (v := v)
      (fun i j hij hj => hs.2 (2*i) (2*j) (by omega) (by omega) (by omega))
      (fun i hi => by dsimp [q]; rw [braid_generator_length hG x hs (by omega)])
      (fun i j hij hj => braid_nonadjacent_pairing hG x hs (by omega) (by omega) (by omega))
    norm_num at he
    rw [← he]
    positivity
  have hpc₂ : lengthPairing x (s 0) (braidCenter s 2) = 2*q + β := by
    change lengthPairing x (s 0) (braidCenter s 1 * braidLoop s 2) = _
    rw [lengthPairing_centralizer hG x (braidCenter_commute hs (by norm_num) (by norm_num))
      (braidLoop_commute hs (by norm_num) (by norm_num))]
    have he : braidCenter s 1 = (s 0)^2 := by simp [braidCenter, braidLoop, pow_two]
    rw [he, lengthPairing_pow_right hG.1 hG.2.1 x (Commute.refl _), lengthPairing_self hG.2.1]
    norm_num
    rfl
  have hQ₂ := braidCenter_length_sq hG x hs (n := 2) (i := 0) (by norm_num) (by norm_num)
  rw [hpc₂] at hQ₂
  norm_num at hQ₂
  have hpc₁₉ := braid_center_character hG x hs (n := 17) (by norm_num)
  rw [hpc₂] at hpc₁₉
  norm_num at hpc₁₉
  have hQ₁₉ := braidCenter_length_sq hG x hs (n := 19) (i := 0) (by norm_num) (by norm_num)
  rw [hpc₁₉] at hQ₁₉
  norm_num at hQ₁₉
  let t : ℕ → G := fun i => s (i+20)
  have hc (i : ℕ) (hi : i < 19) (j : ℕ) (hj : j < 19) : Commute (s i) (t j) :=
    hs.2 i (j+20) (by omega) (by omega) (by omega)
  have hP := lengthPairing_disjoint_centers hG x (n := 19) (k := 19) (α := v) hc
    (fun i hi j hj => braid_nonadjacent_pairing hG x hs (by omega) (by omega) (by omega))
  norm_num at hP
  have hc' : Commute (braidCenter s 19) (braidCenter t 19) :=
    (commute_braidCenter (fun i hi => (commute_braidCenter (hc i hi)).symm)).symm
  have hL : stableLengthAt x (braidCenter s 19) = stableLengthAt x (braidCenter t 19) := by
    rw [← braidCenter_shift_conjugate hs (by norm_num : 19+20 ≤ 39), stableLength_conjugate hG.2.1]
  have hbound := lengthPairing_le_self_of_equal_length hG x hc' hL
  rw [hP] at hbound
  have hraw : 572*q ≤ 57*stableLengthAt x (braidCenter s 2)^2 := by
    change stableLengthAt x (braidCenter s 19)^2 = 380*(2*q + β + 17*β + 306*v) at hQ₁₉
    linarith
  rw [braidCenter_two (hs.1 0 (by norm_num))] at hraw
  rw [stableLength_pow hG.2.1]
  norm_num
  dsimp [q] at hraw
  nlinarith

lemma braid_forty_ratio (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} (hs : BraidRelations 39 s) (hD : 0 < stableLengthAt x ((s 0)^2)) :
    (stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)))^2 ≥ 143/513 ∧
    stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)) > 1/2 ∧
    stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)) =
      stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 1)^2)) := by
  have hsq := braid_forty_squared hG x hs
  have hbd : (stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)))^2 ≥ 143/513 := by
    rw [div_pow, ge_iff_le, le_div_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hD))]
    nlinarith
  refine ⟨hbd, ?_, ?_⟩
  · have hp : 0 ≤ stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)) :=
      div_nonneg (stableLength_nonneg hG.2.1 x _) (by positivity)
    nlinarith
  · rw [stableLength_pow hG.2.1 x (s 1), braid_generator_length hG x hs (by norm_num),
      stableLength_pow hG.2.1 x (s 0)]

end BraidLengths

section TokenInvariant

abbrev SelectedPositions := {s : Finset ℕ // s.card ≤ 3}

def swapPositions (i : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.map (Equiv.swap i (i+1)).toEmbedding

@[simp] lemma mem_swapPositions (i k : ℕ) (s : Finset ℕ) :
    k ∈ swapPositions i s ↔ Equiv.swap i (i+1) k ∈ s := by
  simp [swapPositions]

@[simp] lemma card_swapPositions (i : ℕ) (s : Finset ℕ) :
    (swapPositions i s).card = s.card := Finset.card_map _

@[simp] lemma swapPositions_twice (i : ℕ) (s : Finset ℕ) :
    swapPositions i (swapPositions i s) = s := by
  ext k
  simp

def selectedPrefix (i : ℕ) (s : Finset ℕ) : ℕ := (s.filter (· < i)).card

lemma selectedPrefix_swap (i j : ℕ) (s : Finset ℕ) (hij : j ≠ i+1) :
    selectedPrefix j (swapPositions i s) = selectedPrefix j s := by
  have he : (swapPositions i s).filter (· < j) =
      swapPositions i (s.filter (· < j)) := by
    ext k
    simp only [Finset.mem_filter, mem_swapPositions]
    have hk : k < j ↔ Equiv.swap i (i+1) k < j := by
      rw [Equiv.swap_apply_def]
      split_ifs <;> omega
    exact and_congr_right (fun _ => hk)
  simp [selectedPrefix, he]

lemma selectedPrefix_succ (i : ℕ) (s : Finset ℕ) :
    selectedPrefix (i+1) s = selectedPrefix i s + if i ∈ s then 1 else 0 := by
  by_cases hi : i ∈ s
  · have he : s.filter (· < i+1) = insert i (s.filter (· < i)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro ⟨hk, hki⟩
        by_cases he : k = i
        · exact Or.inl he
        · exact Or.inr ⟨hk, by omega⟩
      · rintro (rfl | ⟨hk, hki⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hk, by omega⟩
    unfold selectedPrefix
    rw [he, Finset.card_insert_of_notMem (by simp)]
    simp [hi]
  · have he : s.filter (· < i+1) = s.filter (· < i) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨hk, hki⟩
        refine ⟨hk, ?_⟩
        by_contra hn
        have heq : k = i := by omega
        exact hi (heq ▸ hk)
      · intro ⟨hk, hki⟩
        exact ⟨hk, by omega⟩
    unfold selectedPrefix
    rw [he]
    simp [hi]

lemma selectedPrefix_zero_of_three (s : SelectedPositions) (i : ℕ)
    (h₀ : i ∈ s.val) (h₁ : i+1 ∈ s.val) (h₂ : i+2 ∈ s.val) :
    selectedPrefix i s.val = 0 := by
  have hc : ({i, i+1, i+2} : Finset ℕ).card = 3 := by
    simp
  have hsub : {i, i+1, i+2} ⊆ s.val := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> assumption
  have he : s.val = {i, i+1, i+2} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hc]; exact s.property)).symm
  simp [selectedPrefix, he]

lemma selected_not_four (s : SelectedPositions) (i j : ℕ) (hij : i+2 ≤ j)
    (hi : i ∈ s.val) (hi' : i+1 ∈ s.val) (hj : j ∈ s.val) : j+1 ∉ s.val := by
  intro hj'
  have hc : ({i, i+1, j, j+1} : Finset ℕ).card = 4 := by
    simp [show i ≠ j by omega, show i ≠ j+1 by omega, show i+1 ≠ j by omega]
  have hsub : {i, i+1, j, j+1} ⊆ s.val := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  have := s.property
  omega

lemma swapPositions_distant (i j : ℕ) (s : Finset ℕ) (hij : i+2 ≤ j) :
    swapPositions i (swapPositions j s) = swapPositions j (swapPositions i s) := by
  ext k
  simp only [mem_swapPositions]
  by_cases h₀ : k = i
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show i ≠ j by omega, show i ≠ j+1 by omega,
      show i+1 ≠ j by omega]
  by_cases h₁ : k = i+1
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show i ≠ j by omega, show i ≠ j+1 by omega,
      show i+1 ≠ j by omega]
  by_cases h₂ : k = j
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show j ≠ i by omega, show j ≠ i+1 by omega,
      show j+1 ≠ i by omega]
  by_cases h₃ : k = j+1
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show j ≠ i by omega, show j ≠ i+1 by omega,
      show j+1 ≠ i by omega]
  simp [Equiv.swap_apply_of_ne_of_ne, h₀, h₁, h₂, h₃]

lemma swapPositions_braid (i : ℕ) (s : Finset ℕ) :
    swapPositions i (swapPositions (i+1) (swapPositions i s)) =
      swapPositions (i+1) (swapPositions i (swapPositions (i+1) s)) := by
  ext k
  simp only [mem_swapPositions]
  by_cases h₀ : k = i
  · subst k
    simp [Equiv.swap_apply_def, Nat.add_assoc]
  by_cases h₁ : k = i+1
  · subst k
    simp [Equiv.swap_apply_def, Nat.add_assoc]
  by_cases h₂ : k = i+2
  · subst k
    simp [Equiv.swap_apply_def, Nat.add_assoc]
  simp [Equiv.swap_apply_def, h₀, h₁, h₂, Nat.add_assoc]

variable {H : Type*} [Group H]

def tokenRecord (u v : H) (i : ℕ) (s : Finset ℕ) : H :=
  if i ∈ s ∧ i+1 ∈ s then (if selectedPrefix i s = 0 then u else v) else 1

@[simp] lemma tokenRecord_swap (u v : H) (i : ℕ) (s : Finset ℕ) :
    tokenRecord u v i (swapPositions i s) = tokenRecord u v i s := by
  simp only [tokenRecord, mem_swapPositions, Equiv.swap_apply_left, Equiv.swap_apply_right,
    selectedPrefix_swap i i s (by omega)]
  simp only [and_comm]

abbrev TokenState (H : Type*) := SelectedPositions × H

def tokenPerm (u v : H) (i : ℕ) : Equiv.Perm (TokenState H) where
  toFun p := (⟨swapPositions i p.1.val, by simpa using p.1.property⟩,
    tokenRecord u v i p.1.val * p.2)
  invFun p := (⟨swapPositions i p.1.val, by simpa using p.1.property⟩,
    (tokenRecord u v i p.1.val)⁻¹ * p.2)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp

lemma tokenRecord_distant (u v : H) (i j : ℕ) (s : Finset ℕ) (hij : i+2 ≤ j) :
    tokenRecord u v i (swapPositions j s) = tokenRecord u v i s ∧
    tokenRecord u v j (swapPositions i s) = tokenRecord u v j s := by
  constructor
  · simp only [tokenRecord, mem_swapPositions,
      Equiv.swap_apply_of_ne_of_ne (by omega : i ≠ j) (by omega : i ≠ j+1),
      Equiv.swap_apply_of_ne_of_ne (by omega : i+1 ≠ j) (by omega : i+1 ≠ j+1),
      selectedPrefix_swap j i s (by omega)]
  · simp only [tokenRecord, mem_swapPositions,
      Equiv.swap_apply_of_ne_of_ne (by omega : j ≠ i) (by omega : j ≠ i+1),
      Equiv.swap_apply_of_ne_of_ne (by omega : j+1 ≠ i) (by omega : j+1 ≠ i+1),
      selectedPrefix_swap i j s (by omega)]

lemma tokenPerm_distant (u v : H) (i j : ℕ) (hij : i+2 ≤ j) :
    Commute (tokenPerm u v i) (tokenPerm u v j) := by
  apply Equiv.ext
  intro p
  apply Prod.ext
  · apply Subtype.ext
    exact swapPositions_distant i j p.1.val hij
  · change tokenRecord u v i (swapPositions j p.1.val) *
        (tokenRecord u v j p.1.val * p.2) =
      tokenRecord u v j (swapPositions i p.1.val) *
        (tokenRecord u v i p.1.val * p.2)
    rw [(tokenRecord_distant u v i j p.1.val hij).1,
      (tokenRecord_distant u v i j p.1.val hij).2]
    by_cases hi : i ∈ p.1.val ∧ i+1 ∈ p.1.val
    · have hnj : ¬(j ∈ p.1.val ∧ j+1 ∈ p.1.val) :=
        fun hj => selected_not_four p.1 i j hij hi.1 hi.2 hj.1 hj.2
      simp [tokenRecord, hnj]
    · simp [tokenRecord, hi]

lemma tokenPerm_braid (u v : H) (h : u*v*u = v*u*v) (i : ℕ) :
    tokenPerm u v i * tokenPerm u v (i+1) * tokenPerm u v i =
      tokenPerm u v (i+1) * tokenPerm u v i * tokenPerm u v (i+1) := by
  apply Equiv.ext
  intro p
  apply Prod.ext
  · apply Subtype.ext
    exact swapPositions_braid i p.1.val
  · change tokenRecord u v i (swapPositions (i+1) (swapPositions i p.1.val)) *
        (tokenRecord u v (i+1) (swapPositions i p.1.val) *
          (tokenRecord u v i p.1.val * p.2)) =
      tokenRecord u v (i+1) (swapPositions i (swapPositions (i+1) p.1.val)) *
        (tokenRecord u v i (swapPositions (i+1) p.1.val) *
          (tokenRecord u v (i+1) p.1.val * p.2))
    have hp₀ (s : Finset ℕ) := selectedPrefix_swap i i s (by omega)
    have hp₁ (s : Finset ℕ) := selectedPrefix_swap (i+1) i s (by omega)
    have hz : i ∈ p.1.val → i+1 ∈ p.1.val → i+2 ∈ p.1.val →
        selectedPrefix i p.1.val = 0 := selectedPrefix_zero_of_three p.1 i
    by_cases h₀ : i ∈ p.1.val <;> by_cases h₁ : i+1 ∈ p.1.val <;>
      by_cases h₂ : i+2 ∈ p.1.val <;>
      simp_all [tokenRecord, selectedPrefix_succ, mem_swapPositions,
        Equiv.swap_apply_def, Nat.add_assoc, ← mul_assoc]

end TokenInvariant

end ArtinCAT0

end OAI
