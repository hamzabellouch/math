import OAI.GroupTheory.ArtinCAT0.Model

namespace OAI

namespace ArtinCAT0

section Comparison

variable {X : Type*} [MetricSpace X]

lemma segment_reverse {x y : X} {γ : ℝ → X} (h : Segment x y γ) :
    Segment y x (fun t => γ (1 - t)) := by
  refine ⟨by simpa using h.2.1, by simpa using h.1, ?_⟩
  intro s hs t ht
  rw [h.2.2 (1 - s) (by constructor <;> linarith [hs.1, hs.2])
    (1 - t) (by constructor <;> linarith [ht.1, ht.2])]
  rw [dist_comm y x]
  congr 1
  rw [show (1 - s) - (1 - t) = t - s by ring, abs_sub_comm t s]

lemma segment_isometry {Z : Type*} [MetricSpace Z] {x y : X} {γ : ℝ → X}
    (h : Segment x y γ) {f : X → Z} (hf : Isometry f) :
    Segment (f x) (f y) (f ∘ γ) := by
  refine ⟨congrArg f h.1, congrArg f h.2.1, ?_⟩
  intro s hs t ht
  simpa only [Function.comp_apply, hf.dist_eq] using h.2.2 s hs t ht

lemma comparison_common_start (hX : CAT0 X) {x y z : X} {γ η : ℝ → X}
    (hγ : Segment x y γ) (hη : Segment x z η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    dist (γ t) (η t) ≤ t * dist y z := by
  have hc := hX.2 x y z γ η hγ hη t ht t ht
  have h₀ := dist_nonneg (x := γ t) (y := η t)
  have h₁ := dist_nonneg (x := y) (y := z)
  have h₂ : 0 ≤ t * dist y z := mul_nonneg ht.1 h₁
  nlinarith [sq_nonneg (dist (γ t) (η t) - t * dist y z)]

lemma segment_unique (hX : CAT0 X) {x y : X} {γ η : ℝ → X}
    (hγ : Segment x y γ) (hη : Segment x y η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    γ t = η t := by
  have h := comparison_common_start hX hγ hη ht
  simpa using h

lemma comparison_convexity (hX : CAT0 X) {a b c d : X} {γ η : ℝ → X}
    (hγ : Segment a b γ) (hη : Segment c d η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    dist (γ t) (η t) ≤ (1 - t) * dist a c + t * dist b d := by
  obtain ⟨ζ, hζ⟩ := hX.1 a d
  have h₁ := comparison_common_start hX hγ hζ ht
  have h₂ := comparison_common_start hX (segment_reverse hζ) (segment_reverse hη)
    (show 1 - t ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2])
  simp only [sub_sub_cancel] at h₂
  calc
    dist (γ t) (η t) ≤ dist (γ t) (ζ t) + dist (ζ t) (η t) := dist_triangle _ _ _
    _ ≤ t * dist b d + (1 - t) * dist a c := add_le_add h₁ h₂
    _ = _ := add_comm _ _

lemma midpoint_comparison (hX : CAT0 X) (z : X) {x y : X} {γ : ℝ → X}
    (hγ : Segment x y γ) :
    dist z (γ (1 / 2)) ^ 2 ≤ (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  obtain ⟨η, hη⟩ := hX.1 x z
  have hc := hX.2 x y z γ η hγ hη (1 / 2) (by constructor <;> norm_num)
    1 (by constructor <;> norm_num)
  rw [hη.2.1, dist_comm (γ _), dist_comm x z, dist_comm y z] at hc
  nlinarith

lemma quadrilateral (hX : CAT0 X) (p q r s : X) :
    dist p r ^ 2 + dist q s ^ 2 ≤
      dist p q ^ 2 + dist q r ^ 2 + dist r s ^ 2 + dist s p ^ 2 := by
  obtain ⟨γ, hγ⟩ := hX.1 p r
  have hq := midpoint_comparison hX q hγ
  have hs := midpoint_comparison hX s hγ
  have ht := dist_triangle q (γ (1 / 2)) s
  rw [dist_comm (γ _)] at ht
  rw [dist_comm q p] at hq
  rw [dist_comm s r] at hs
  have hsum : dist q s ^ 2 ≤ (dist q (γ (1 / 2)) + dist s (γ (1 / 2))) ^ 2 := by
    nlinarith [dist_nonneg (x := q) (y := s),
      dist_nonneg (x := q) (y := γ (1 / 2)), dist_nonneg (x := s) (y := γ (1 / 2))]
  nlinarith [sq_nonneg (dist q (γ (1 / 2)) - dist s (γ (1 / 2)))]

end Comparison

section StableLengths

open Filter Topology

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

noncomputable def stableLengthAt (x : X) (g : G) : ℝ :=
  sInf ((fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ)) '' Set.Ici 1)

lemma displacement_subadditive (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : Subadditive (fun n : ℕ => dist x ((g ^ n) • x)) := by
  intro m n
  calc
    dist x ((g ^ (m + n)) • x) ≤
        dist x ((g ^ m) • x) + dist ((g ^ m) • x) ((g ^ m) • ((g ^ n) • x)) := by
      simpa only [pow_add, mul_smul] using dist_triangle x ((g ^ m) • x) ((g ^ m) • ((g ^ n) • x))
    _ = dist x ((g ^ m) • x) + dist x ((g ^ n) • x) := by rw [(hi (g ^ m)).dist_eq]

lemma stableLength_tendsto (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) :
    Tendsto (fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ)) atTop (𝓝 (stableLengthAt x g)) := by
  have hb : BddBelow (Set.range (fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    positivity
  simpa only [Subadditive.lim, stableLengthAt] using (displacement_subadditive hi x g).tendsto_lim hb

lemma stableLength_nonneg (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : 0 ≤ stableLengthAt x g :=
  ge_of_tendsto' (stableLength_tendsto hi x g) (fun _ => by positivity)

lemma stableLength_le_displacement (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : stableLengthAt x g ≤ dist x (g • x) := by
  have hb : BddBelow (Set.range (fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    positivity
  simpa only [Subadditive.lim, stableLengthAt, pow_one, Nat.cast_one, div_one] using
    (displacement_subadditive hi x g).lim_le_div hb (n := 1) (by decide)

lemma displacement_change_base (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g : G) : dist x (g • x) ≤ dist y (g • y) + 2 * dist x y := by
  have h₁ := dist_triangle x y (g • x)
  have h₂ := dist_triangle y (g • y) (g • x)
  rw [(hi g).dist_eq, dist_comm y x] at h₂
  linarith

lemma stableLength_basepoint (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g : G) : stableLengthAt x g = stableLengthAt y g := by
  suffices h : ∀ x y : X, stableLengthAt x g ≤ stableLengthAt y g from
    le_antisymm (h x y) (h y x)
  intro x y
  have he : Tendsto (fun n : ℕ => 2 * dist x y / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := le_of_tendsto_of_tendsto' (stableLength_tendsto hi x g)
    ((stableLength_tendsto hi y g).add he) (fun n => ?_)
  · simpa only [add_zero] using h
  · simpa only [add_div] using
      div_le_div_of_nonneg_right (displacement_change_base hi x y (g ^ n)) (Nat.cast_nonneg n)

lemma stableLength_one (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X) :
    stableLengthAt x (1 : G) = 0 := by
  apply le_antisymm
  · simpa using stableLength_le_displacement hi x (1 : G)
  · exact stableLength_nonneg hi x 1

lemma stableLength_inv (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X) (g : G) :
    stableLengthAt x g⁻¹ = stableLengthAt x g := by
  apply tendsto_nhds_unique (stableLength_tendsto hi x g⁻¹)
  convert stableLength_tendsto hi x g using 1
  ext n
  congr 1
  rw [← (hi (g ^ n)).dist_eq x ((g⁻¹ ^ n) • x)]
  simp only [← mul_smul, inv_pow, mul_inv_cancel, one_smul, dist_comm]

lemma stableLength_conjugate (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g h : G) : stableLengthAt x (h * g * h⁻¹) = stableLengthAt x g := by
  have hc : ∀ n : ℕ, dist x (((h * g * h⁻¹) ^ n) • x) =
      dist (h⁻¹ • x) ((g ^ n) • (h⁻¹ • x)) := by
    intro n
    rw [← (hi h⁻¹).dist_eq x (((h * g * h⁻¹) ^ n) • x)]
    rw [conj_pow]
    simp only [mul_smul, inv_smul_smul]
  have ht := stableLength_tendsto hi (h⁻¹ • x) g
  simp only [← hc] at ht
  rw [stableLength_basepoint hi (h⁻¹ • x) x g] at ht
  exact tendsto_nhds_unique (stableLength_tendsto hi x (h * g * h⁻¹)) ht

lemma stableLength_pow (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (k : ℕ) : stableLengthAt x (g ^ k) = k * stableLengthAt x g := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [stableLength_one hi]
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsub : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id
  have ht := (stableLength_tendsto hi x g).comp hsub
  have ht' := ht.const_mul (k : ℝ)
  apply tendsto_nhds_unique (stableLength_tendsto hi x (g ^ k))
  convert ht' using 1
  ext n
  simp only [Function.comp_apply, ← pow_mul, Nat.cast_mul]
  field_simp

lemma stableLength_mul_le (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) {g h : G} (hc : Commute g h) :
    stableLengthAt x (g * h) ≤ stableLengthAt x g + stableLengthAt x h := by
  apply le_of_tendsto_of_tendsto' (stableLength_tendsto hi x (g * h))
    ((stableLength_tendsto hi x g).add (stableLength_tendsto hi x h))
  intro n
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [hc.mul_pow, mul_smul]
  have htri := dist_triangle x ((g ^ n) • x) ((g ^ n) • ((h ^ n) • x))
  simpa only [(hi (g ^ n)).dist_eq] using htri

lemma displacement_inv (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : dist x (g⁻¹ • x) = dist x (g • x) := by
  rw [← (hi g).dist_eq x (g⁻¹ • x), smul_inv_smul, dist_comm]

lemma action_dist (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g h : G) : dist (g • x) (h • x) = dist x ((g⁻¹ * h) • x) := by
  rw [← (hi g⁻¹).dist_eq (g • x) (h • x), inv_smul_smul, mul_smul]

lemma commuting_displacement_quadrilateral (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    dist x ((g * h) • x) ^ 2 + dist x ((g * h⁻¹) • x) ^ 2 ≤
      2 * dist x (g • x) ^ 2 + 2 * dist x (h • x) ^ 2 := by
  have hq := quadrilateral hX x (g • x) ((g * h) • x) (h • x)
  have h₁ : dist (g • x) ((g * h) • x) = dist x (h • x) := by
    rw [mul_smul, (hi g).dist_eq]
  have h₂ : dist ((g * h) • x) (h • x) = dist x (g • x) := by
    rw [hc.eq, mul_smul, (hi h).dist_eq, dist_comm]
  have h₃ : dist (g • x) (h • x) = dist x ((g * h⁻¹) • x) := by
    rw [action_dist hi, ← displacement_inv hi x (g⁻¹ * h)]
    simp only [mul_inv_rev, inv_inv, ← hc.inv_right.eq]
  rw [h₁, h₂, h₃, dist_comm (h • x) x] at hq
  linarith

lemma length_parallelogram_le (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    stableLengthAt x (g * h) ^ 2 + stableLengthAt x (g * h⁻¹) ^ 2 ≤
      2 * stableLengthAt x g ^ 2 + 2 * stableLengthAt x h ^ 2 := by
  apply le_of_tendsto_of_tendsto'
    (((stableLength_tendsto hi x (g * h)).pow 2).add ((stableLength_tendsto hi x (g * h⁻¹)).pow 2))
    ((((stableLength_tendsto hi x g).pow 2).const_mul 2).add
      (((stableLength_tendsto hi x h).pow 2).const_mul 2))
  intro n
  have hd := commuting_displacement_quadrilateral hX hi x (hc.pow_pow n n)
  have hdiv := div_le_div_of_nonneg_right hd (sq_nonneg (n : ℝ))
  simpa only [div_pow, hc.mul_pow, hc.inv_right.mul_pow, inv_pow, add_div, mul_div_assoc] using hdiv

lemma length_parallelogram (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    stableLengthAt x (g * h) ^ 2 + stableLengthAt x (g * h⁻¹) ^ 2 =
      2 * stableLengthAt x g ^ 2 + 2 * stableLengthAt x h ^ 2 := by
  have h₁ := length_parallelogram_le hX hi x hc
  have hcomm : Commute (g * h) (g * h⁻¹) :=
    (Commute.refl g).mul_left hc.symm |>.mul_right (hc.inv_right.mul_left (Commute.refl h).inv_right)
  have he₁ : (g * h) * (g * h⁻¹) = g ^ 2 := by
    calc (g * h) * (g * h⁻¹) = g * (h * g) * h⁻¹ := by group
         _ = g * (g * h) * h⁻¹ := by rw [hc.symm.eq]
         _ = g ^ 2 := by simp only [pow_two]; group
  have he₂ : (g * h) * (g * h⁻¹)⁻¹ = h ^ 2 := by
    calc (g * h) * (g * h⁻¹)⁻¹ = g * (h * h) * g⁻¹ := by group
         _ = (h * h) * g * g⁻¹ := by rw [(hc.mul_right hc).eq]
         _ = h ^ 2 := by simp only [pow_two]; group
  have h₂ := length_parallelogram_le hX hi x hcomm
  rw [he₁, he₂, stableLength_pow hi, stableLength_pow hi] at h₂
  norm_num at h₂
  nlinarith

noncomputable def lengthPairing (x : X) (g h : G) : ℝ :=
  (stableLengthAt x (g * h) ^ 2 - stableLengthAt x g ^ 2 - stableLengthAt x h ^ 2) / 2

lemma lengthPairing_symmetric (x : X) {g h : G} (hc : Commute g h) :
    lengthPairing x g h = lengthPairing x h g := by
  unfold lengthPairing
  rw [hc.eq]
  ring

lemma lengthPairing_self (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : lengthPairing x g g = stableLengthAt x g ^ 2 := by
  unfold lengthPairing
  rw [← pow_two, stableLength_pow hi]
  norm_num
  ring

lemma lengthPairing_one (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : lengthPairing x g 1 = 0 := by
  simp [lengthPairing, stableLength_one hi]

lemma lengthPairing_polarization (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    lengthPairing x g h =
      (stableLengthAt x (g * h) ^ 2 - stableLengthAt x (g * h⁻¹) ^ 2) / 4 := by
  unfold lengthPairing
  linarith [length_parallelogram hX hi x hc]

lemma lengthPairing_inv (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    lengthPairing x g h⁻¹ = -lengthPairing x g h := by
  rw [lengthPairing_polarization hX hi x hc.inv_right,
    lengthPairing_polarization hX hi x hc, inv_inv]
  ring

lemma lengthPairing_conjugate (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g h k : G) :
    lengthPairing x (k * g * k⁻¹) (k * h * k⁻¹) = lengthPairing x g h := by
  have he : (k * g * k⁻¹) * (k * h * k⁻¹) = k * (g * h) * k⁻¹ := by group
  simp only [lengthPairing, he, stableLength_conjugate hi]

lemma lengthPairing_jensen (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h k : G} (hgh : Commute g h) (hgk : Commute g k) (hhk : Commute h k) :
    lengthPairing x (g * h) k + lengthPairing x (g * h⁻¹) k =
      2 * lengthPairing x g k := by
  rw [lengthPairing_polarization hX hi x (hgk.mul_left hhk),
    lengthPairing_polarization hX hi x (hgk.mul_left hhk.inv_left),
    lengthPairing_polarization hX hi x hgk]
  have h₁ := length_parallelogram hX hi x (hgh.mul_left hhk.symm)
  have h₂ := length_parallelogram hX hi x (hgh.mul_left hhk.symm.inv_left)
  have e₁ : g * k * h = g * h * k := by rw [mul_assoc, hhk.symm.eq, ← mul_assoc]
  have e₂ : g * k * h⁻¹ = g * h⁻¹ * k := by rw [mul_assoc, hhk.symm.inv_right.eq, ← mul_assoc]
  have e₃ : g * k⁻¹ * h = g * h * k⁻¹ := by rw [mul_assoc, hhk.symm.inv_left.eq, ← mul_assoc]
  have e₄ : g * k⁻¹ * h⁻¹ = g * h⁻¹ * k⁻¹ := by rw [mul_assoc, hhk.symm.inv_left.inv_right.eq, ← mul_assoc]
  rw [e₁, e₂] at h₁
  rw [e₃, e₄] at h₂
  linarith

lemma lengthPairing_mul_left (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h k : G} (hgh : Commute g h) (hgk : Commute g k) (hhk : Commute h k) :
    lengthPairing x (g * h) k = lengthPairing x g k + lengthPairing x h k := by
  have h₁ := lengthPairing_jensen hX hi x hgh hgk hhk
  have h₂ := lengthPairing_jensen hX hi x hgh.symm hhk hgk
  have he : h * g⁻¹ = (g * h⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv]
  have he' : lengthPairing x (h * g⁻¹) k = -lengthPairing x (g * h⁻¹) k := by
    rw [he, lengthPairing_symmetric x (hgk.mul_left hhk.inv_left).inv_left,
      lengthPairing_inv hX hi x (hgk.mul_left hhk.inv_left).symm,
      lengthPairing_symmetric x (hgk.mul_left hhk.inv_left).symm]
  rw [← hgh.eq, he'] at h₂
  linarith

lemma lengthPairing_mul_right (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h k : G} (hgh : Commute g h) (hgk : Commute g k) (hhk : Commute h k) :
    lengthPairing x g (h * k) = lengthPairing x g h + lengthPairing x g k := by
  rw [lengthPairing_symmetric x (hgh.mul_right hgk),
    lengthPairing_mul_left hX hi x hhk hgh.symm hgk.symm,
    lengthPairing_symmetric x hgh.symm, lengthPairing_symmetric x hgk.symm]

lemma lengthPairing_pow_right (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℕ) :
    lengthPairing x g (h ^ n) = n * lengthPairing x g h := by
  induction n with
  | zero => simp [lengthPairing_one hi]
  | succ n hn =>
    rw [pow_succ, lengthPairing_mul_right hX hi x (hc.pow_right n) hc (Commute.self_pow h n).symm, hn]
    push_cast
    ring

lemma lengthPairing_pow_left (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℕ) :
    lengthPairing x (g ^ n) h = n * lengthPairing x g h := by
  rw [lengthPairing_symmetric x (hc.pow_left n), lengthPairing_pow_right hX hi x hc.symm,
    lengthPairing_symmetric x hc.symm]

lemma stableLength_product_sq (x : X) (g h : G) :
    stableLengthAt x (g * h) ^ 2 =
      stableLengthAt x g ^ 2 + stableLengthAt x h ^ 2 + 2 * lengthPairing x g h := by
  unfold lengthPairing
  ring

lemma stableLength_zpow (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (n : ℤ) : stableLengthAt x (g ^ n) = |(n : ℝ)| * stableLengthAt x g := by
  cases n with
  | ofNat n => simp [stableLength_pow hi]
  | negSucc n =>
    rw [show (Int.negSucc n : ℝ) = -((n : ℝ) + 1) by simp [Int.cast_negSucc],
      abs_neg, abs_of_nonneg (by positivity)]
    simp [zpow_negSucc, stableLength_inv hi, stableLength_pow hi]

lemma lengthPairing_zpow_right (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℤ) :
    lengthPairing x g (h ^ n) = n * lengthPairing x g h := by
  cases n with
  | ofNat n => simp [lengthPairing_pow_right hX hi x hc]
  | negSucc n =>
    simp [zpow_negSucc, lengthPairing_inv hX hi x (hc.pow_right _),
      lengthPairing_pow_right hX hi x hc, Int.cast_negSucc]
    ring

end StableLengths

section CompactAttainment

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X] [ProperSpace X]

lemma finite_movers_of_compact
    (hp : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite)
    {K : Set X} (hK : IsCompact K) (o : X) (A : ℝ) (hA : 0 ≤ A) :
    {g : G | ∃ p ∈ K, dist p (g • p) ≤ A}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall o
  refine (hp (Metric.closedBall o (R + A)) (isCompact_closedBall o (R + A))).subset ?_
  rintro g ⟨p, hpK, hdist⟩
  have hpR := hR hpK
  change dist p o ≤ R at hpR
  have hgR : dist (g • p) o ≤ R + A := by
    have ht := dist_triangle (g • p) p o
    rw [dist_comm (g • p) p] at ht
    linarith
  refine ⟨g • p, ⟨p, ?_, rfl⟩, hgR⟩
  change dist p o ≤ R + A
  linarith

lemma exists_displacement_minimizer [Nonempty X] (hG : GeometricAction G X) (g : G) :
    ∃ x : X, ∀ y : X, dist x (g • x) ≤ dist y (g • y) := by
  classical
  let hi := hG.2.1
  let o : X := Classical.choice inferInstance
  let A := dist o (g • o)
  have hA : 0 ≤ A := dist_nonneg
  obtain ⟨K, hK, hcover⟩ := hG.2.2.2
  let Q : Set G := {q | (∃ p ∈ K, dist p (q • p) ≤ A) ∧ ∃ h : G, h⁻¹ * g * h = q}
  have hQ : Q.Finite := (finite_movers_of_compact hG.2.2.1 hK o A hA).subset
    (fun _ hq => hq.1)
  let S : Set ℝ := ⋃ q ∈ Q, (fun p : X => dist p (q • p)) '' K
  have hS : IsCompact S := hQ.isCompact_biUnion (fun q _ => hK.image (continuous_id.dist (hi q).continuous))
  have hnear : ∀ y : X, dist y (g • y) ≤ A → dist y (g • y) ∈ S := by
    intro y hdy
    obtain ⟨h, p, hp, rfl⟩ := hcover y
    have hd : dist p ((h⁻¹ * g * h) • p) = dist (h • p) (g • (h • p)) := by
      rw [← (hi h).dist_eq]
      simp only [mul_smul, smul_inv_smul]
    apply Set.mem_iUnion.mpr
    refine ⟨h⁻¹ * g * h, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact ⟨⟨p, hp, hd ▸ hdy⟩, h, rfl⟩
    · exact ⟨p, hp, hd⟩
  have ho : A ∈ S := hnear o le_rfl
  obtain ⟨a, ha, hmin⟩ := hS.exists_isMinOn ⟨A, ho⟩ continuous_id.continuousOn
  obtain ⟨q, hq, p, hp, rfl⟩ := Set.mem_iUnion₂.mp ha
  obtain ⟨h, hh⟩ := hq.2
  have hd : dist (h • p) (g • (h • p)) = dist p (q • p) := by
    rw [← hh, ← (hi h).dist_eq p ((h⁻¹ * g * h) • p)]
    simp only [mul_smul, smul_inv_smul]
  refine ⟨h • p, fun y => ?_⟩
  rw [hd]
  by_cases hy : dist y (g • y) ≤ A
  · exact hmin (hnear y hy)
  · exact (hmin ho).trans (le_of_lt (lt_of_not_ge hy))

end CompactAttainment

section AxialLengths

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

lemma segment_point_eq_of_dist (hX : CAT0 X) {a b c : X} {γ : ℝ → X}
    (hγ : Segment a c γ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hab : dist a b = t * dist a c) (hbc : dist b c = (1 - t) * dist a c) :
    γ t = b := by
  obtain ⟨η, hη⟩ := hX.1 a b
  have hc := hX.2 a c b γ η hγ hη t ht 1 (by constructor <;> norm_num)
  rw [hη.2.1, dist_comm c b, hab, hbc] at hc
  have he : (t ^ 2 - t * 1) * dist a c ^ 2 +
      ((1 : ℝ)^2 - t * 1) * (t * dist a c)^2 +
      t * 1 * ((1 - t) * dist a c)^2 = 0 := by ring
  rw [he] at hc
  have hd : dist (γ t) b = 0 := by nlinarith [dist_nonneg (x := γ t) (y := b)]
  exact dist_eq_zero.mp hd

lemma minimizer_displacement_two (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (g : G) {x : X}
    (hm : ∀ y : X, dist x (g • x) ≤ dist y (g • y)) :
    dist x ((g ^ 2) • x) = 2 * dist x (g • x) := by
  obtain ⟨γ, hγ⟩ := hX.1 x (g • x)
  have hη := segment_isometry hγ (hi g)
  have hd := comparison_common_start hX (segment_reverse hγ) hη
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Function.comp_apply] at hd
  have hlow := hm (γ (1 / 2))
  have hu := dist_triangle x (g • x) (g • (g • x))
  rw [(hi g).dist_eq] at hu
  rw [pow_two, mul_smul]
  linarith

lemma powerStepDistance (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (n : ℕ) :
    dist ((g ^ n) • x) ((g ^ (n + 1)) • x) = dist x (g • x) := by
  rw [pow_succ, mul_smul, (hi (g ^ n)).dist_eq]

lemma extension_numeric {D R N : ℝ} (hN : 0 < N)
    (hc : (2 * D) ^ 2 ≤ ((1 / N) ^ 2 - (1 / N) * 1) * (N * D) ^ 2 +
      ((1 : ℝ)^2 - (1 / N) * 1) * D^2 + (1 / N) * 1 * R^2) :
    ((N + 1) * D) ^ 2 ≤ R ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hc hN.le
  have he : N * (((1 / N) ^ 2 - (1 / N) * 1) * (N * D) ^ 2 +
      ((1 : ℝ)^2 - (1 / N) * 1) * D^2 + (1 / N) * 1 * R^2) =
      (2 * N - N ^ 2 - 1) * D^2 + R^2 := by
    field_simp
    ring
  rw [he] at h
  nlinarith

lemma minimizer_displacement_pow (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (g : G) {x : X}
    (hm : ∀ y : X, dist x (g • x) ≤ dist y (g • y)) (n : ℕ) :
    dist x ((g ^ n) • x) = n * dist x (g • x) := by
  have htwo := minimizer_displacement_two hX hi g hm
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
    let D := dist x (g • x)
    let N : ℝ := n + 1
    have hN : 0 < N := by dsimp [N]; positivity
    have htrad : (1 / N : ℝ) ∈ Set.Icc 0 1 := by
      constructor
      · positivity
      · apply (div_le_one hN).mpr
        dsimp [N]
        linarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨γ, hγ⟩ := hX.1 ((g ^ (n + 1)) • x) x
    have hγd : dist ((g ^ (n + 1)) • x) x = N * D := by rw [dist_comm, hn1]; simp [N, D]
    have hγt : γ (1 / N) = (g ^ n) • x := by
      apply segment_point_eq_of_dist hX hγ htrad
      · rw [dist_comm, powerStepDistance hi, hγd]
        change D = 1 / N * (N * D)
        field_simp
      · rw [dist_comm, hn, hγd]
        change (n : ℝ) * D = (1 - 1 / N) * (N * D)
        rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul, mul_div_cancel_left₀ _ hN.ne']
        dsimp [N]
        ring
    obtain ⟨η, hη⟩ := hX.1 ((g ^ (n + 1)) • x) ((g ^ (n + 2)) • x)
    have hc := hX.2 ((g ^ (n + 1)) • x) x ((g ^ (n + 2)) • x)
      γ η hγ hη (1 / N) htrad 1 (by constructor <;> norm_num)
    have hnext : dist ((g ^ (n + 1)) • x) ((g ^ (n + 2)) • x) = D :=
      powerStepDistance hi x g (n + 1)
    have hlocal : dist ((g ^ n) • x) ((g ^ (n + 2)) • x) = 2 * D := by
      rw [pow_add, mul_smul, (hi (g ^ n)).dist_eq, htwo]
    rw [hγt, hη.2.1, hlocal, hγd, hnext] at hc
    have hlo := extension_numeric hN hc
    have hup := dist_triangle x ((g ^ (n + 1)) • x) ((g ^ (n + 2)) • x)
    rw [hn1, hnext] at hup
    have he : ((n + 2 : ℕ) : ℝ) * D = (N + 1) * D := by push_cast; dsimp [N]; ring
    change dist x ((g ^ (n + 2)) • x) = ((n + 2 : ℕ) : ℝ) * D
    rw [he]
    have hp : 0 ≤ (N + 1) * D := mul_nonneg (by linarith) dist_nonneg
    have hu : dist x ((g ^ (n + 2)) • x) ≤ (N + 1) * D := by
      dsimp [N]
      push_cast at hup
      linarith
    nlinarith [dist_nonneg (x := x) (y := (g ^ (n + 2)) • x)]

open Filter Topology

lemma stableLength_minimizer (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (g : G) {x : X}
    (hm : ∀ y : X, dist x (g • x) ≤ dist y (g • y)) :
    stableLengthAt x g = dist x (g • x) := by
  apply tendsto_nhds_unique (stableLength_tendsto hi x g)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [minimizer_displacement_pow hX hi g hm]
  simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

lemma lengthPairing_basepoint (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g h : G) : lengthPairing x g h = lengthPairing y g h := by
  simp only [lengthPairing, stableLength_basepoint hi x y]

lemma stableLength_finiteOrder (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) {g : G} (hg : IsOfFinOrder g) : stableLengthAt x g = 0 := by
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  have hp := stableLength_pow hi x g n
  rw [he, stableLength_one hi] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left (ne_of_gt (Nat.cast_pos.mpr hn))

lemma finiteOrder_of_fixedPoint
    (hp : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite)
    (x : X) {g : G} (hg : g • x = x) : IsOfFinOrder g := by
  have hstab : (MulAction.stabilizer G x : Set G).Finite := by
    refine (hp {x} isCompact_singleton).subset ?_
    intro h hh
    exact ⟨x, ⟨x, Set.mem_singleton x, hh⟩, Set.mem_singleton x⟩
  let : Finite (MulAction.stabilizer G x) := hstab.to_subtype
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp
    (isOfFinOrder_of_finite (⟨g, hg⟩ : MulAction.stabilizer G x))
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  exact congrArg Subtype.val he

lemma stableLength_eq_zero_iff_finiteOrder [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (x : X) (g : G) :
    stableLengthAt x g = 0 ↔ IsOfFinOrder g := by
  refine ⟨fun hzero => ?_, stableLength_finiteOrder hG.2.1 x⟩
  obtain ⟨p, hp⟩ := exists_displacement_minimizer hG g
  rw [stableLength_basepoint hG.2.1 x p g, stableLength_minimizer hG.1 hG.2.1 g hp] at hzero
  exact finiteOrder_of_fixedPoint hG.2.2.1 p (dist_eq_zero.mp hzero).symm

lemma lengthPairing_zpow_left (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℤ) :
    lengthPairing x (g ^ n) h = n * lengthPairing x g h := by
  rw [lengthPairing_symmetric x (hc.zpow_left n), lengthPairing_zpow_right hX hi x hc.symm,
    lengthPairing_symmetric x hc.symm]

lemma stableLength_zpow_product_sq (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℤ) :
    stableLengthAt x ((g ^ n) * h) ^ 2 =
      (n : ℝ)^2 * stableLengthAt x g ^ 2 + stableLengthAt x h ^ 2 +
        2 * (n : ℝ) * lengthPairing x g h := by
  rw [stableLength_product_sq, stableLength_zpow hi, lengthPairing_zpow_left hX hi x hc,
    mul_pow, sq_abs]
  ring

lemma nonpos_of_nat_mul_le {a b : ℝ} (h : ∀ n : ℕ, (n : ℝ) * a ≤ b) : a ≤ 0 := by
  by_contra! ha
  obtain ⟨n, hn⟩ := exists_nat_gt (b / a)
  exact (not_lt_of_ge (h n)) ((div_lt_iff₀ ha).mp hn)

lemma zero_of_int_mul_le {a b : ℝ} (h : ∀ n : ℤ, (n : ℝ) * a ≤ b) : a = 0 := by
  have h₁ := nonpos_of_nat_mul_le (fun n => h n)
  have h₂ : -a ≤ 0 := nonpos_of_nat_mul_le (b := b) (fun n => by
    have hn := h (-(n : ℤ))
    push_cast at hn
    nlinarith)
  linarith

lemma lengthPairing_zero_of_length_zero (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (hzero : stableLengthAt x g = 0) :
    lengthPairing x g h = 0 := by
  have hz : -2 * lengthPairing x g h = 0 := zero_of_int_mul_le
    (b := stableLengthAt x h ^ 2) (fun n => by
      have he := stableLength_zpow_product_sq hX hi x hc n
      rw [hzero] at he
      nlinarith [sq_nonneg (stableLengthAt x ((g ^ n) * h))])
  linarith

end AxialLengths

end ArtinCAT0

end OAI
