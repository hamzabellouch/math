import OAI.Analysis.Daugavet.UpperBounds

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma equivalentNorm_pos {N : Seminorm ℝ X} (hN : EquivalentNorm N) {x : X} (hx : x ≠ 0) :
    0 < N x := by
  obtain ⟨a, b, ha, hb, hbound⟩ := hN
  exact (mul_pos ha (norm_pos_iff.mpr hx)).trans_le (hbound x).1

lemma seminorm_normalize (N : Seminorm ℝ X) {x : X} (hx : 0 < N x) :
    N ((N x)⁻¹ • x) = 1 := by
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ hx.ne']

lemma cofinite_has_Nunit (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {F : Submodule ℝ X} (hF : Cofinite F) :
    ∃ y ∈ F, N y = 1 := by
  obtain ⟨y, hyF, hy⟩ := cofinite_has_unit hinf hF
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  refine ⟨(N y)⁻¹ • y, F.smul_mem _ hyF, seminorm_normalize N (equivalentNorm_pos hN hy0)⟩

def normOneSidedValues (N : Seminorm ℝ X) (x : X) (t : ℝ) (F : Submodule ℝ X) : Set ℝ :=
  {a | ∃ y ∈ F, N y = 1 ∧ a = N (x + t • y) - 1}

lemma normOneSidedValues_bddBelow (N : Seminorm ℝ X) (x : X) (t : ℝ) (F : Submodule ℝ X) :
    BddBelow (normOneSidedValues N x t F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y, hyF, hy, rfl⟩
  linarith [apply_nonneg N (x + t • y)]

lemma normOneSidedValues_nonempty (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) (x : X) (t : ℝ) {F : Submodule ℝ X} (hF : Cofinite F) :
    (normOneSidedValues N x t F).Nonempty := by
  obtain ⟨y, hyF, hy⟩ := cofinite_has_Nunit hinf hN hF
  exact ⟨_, y, hyF, hy, rfl⟩

lemma normD_outer_bddAbove (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {x : X} (hx : N x = 1) {t : ℝ} (ht : 0 ≤ t) :
    BddAbove {r | ∃ F : Submodule ℝ X, Cofinite F ∧ r = sInf (normOneSidedValues N x t F)} := by
  refine ⟨t, ?_⟩
  rintro a ⟨F, hF, rfl⟩
  obtain ⟨y, hyF, hy⟩ := cofinite_has_Nunit hinf hN hF
  have hinf := csInf_le (normOneSidedValues_bddBelow N x t F) ⟨y, hyF, hy, rfl⟩
  have hb := map_add_le_add N x (t • y)
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht, hx, hy, mul_one] at hb
  linarith

lemma normD_ge_neg_one (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {x : X} (hx : N x = 1) {t : ℝ} (ht : 0 ≤ t) : -1 ≤ D N x t := by
  apply le_trans (b := sInf (normOneSidedValues N x t ⊤))
  · apply le_csInf (normOneSidedValues_nonempty hinf hN x t cofinite_top)
    rintro r ⟨y, _, _, rfl⟩
    linarith [apply_nonneg N (x + t • y)]
  · exact le_csSup (normD_outer_bddAbove hinf hN hx ht) ⟨⊤, cofinite_top, rfl⟩

lemma normD_centers_bddBelow (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {t : ℝ} (ht : 0 ≤ t) :
    BddBelow {r | ∃ x : X, N x = 1 ∧ r = D N x t} := by
  refine ⟨-1, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact normD_ge_neg_one hinf hN hx ht

/-- Seminorm convexity with an explicit common endpoint bound. -/
lemma seminorm_segment_le (N : Seminorm ℝ X) {x y : X} {r M : ℝ}
    (hr : 0 ≤ r) (hr' : r ≤ 1) (hx : N x ≤ M) (hy : N y ≤ M) :
    N ((1 - r) • x + r • y) ≤ M := by
  have h := map_add_le_add N ((1 - r) • x) (r • y)
  rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hr'), abs_of_nonneg hr] at h
  have h₁ := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hr')
  have h₂ := mul_le_mul_of_nonneg_left hy hr
  nlinarith

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma equivalentNorm_supremum (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) :
    ∃ R : ℝ, 0 < R ∧ (∀ u : X, ‖u‖ ≤ 1 → N u ≤ R) ∧
      ∀ ε : ℝ, 0 < ε → ∃ x : X, ‖x‖ = 1 ∧ R / (1 + ε) < N x := by
  obtain ⟨a, b, ha, hb, hab⟩ := hN
  let S : Set ℝ := {r | ∃ x : X, ‖x‖ = 1 ∧ r = N x}
  obtain ⟨w, _, hw⟩ := cofinite_has_unit hinf (cofinite_top (X := X))
  have hS : S.Nonempty := ⟨N w, w, hw, rfl⟩
  have hSb : BddAbove S := by
    refine ⟨b, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    simpa only [hx, mul_one] using (hab x).2
  let R := sSup S
  have hSR : ∀ x : X, ‖x‖ = 1 → N x ≤ R := fun x hx => le_csSup hSb ⟨x, hx, rfl⟩
  have hR : 0 < R := by
    have hb := (hab w).1
    rw [hw, mul_one] at hb
    exact ha.trans_le (hb.trans (hSR w hw))
  refine ⟨R, hR, ?_, ?_⟩
  · intro u hu
    by_cases hu0 : u = 0
    · simpa only [hu0, map_zero] using hR.le
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      let x := ‖u‖⁻¹ • u
      have hx : ‖x‖ = 1 := norm_smul_inv_norm hu0
      have hid : u = ‖u‖ • x := by dsimp [x]; rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      calc
        N u = N (‖u‖ • x) := congrArg N hid
        _ = ‖u‖ * N x := by rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hn.le]
        _ ≤ ‖u‖ * R := mul_le_mul_of_nonneg_left (hSR x hx) hn.le
        _ ≤ R := by nlinarith
  · intro ε hε
    have hden : 0 < 1 + ε := by linarith
    have hlt : R / (1 + ε) < R := (div_lt_iff₀ hden).mpr (by nlinarith)
    obtain ⟨r, ⟨x, hx, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hS hlt
    exact ⟨x, hx, hr⟩

lemma seminorm_normalized_segment (N : Seminorm ℝ X) {x z : X} (hx : 0 < N x)
    (hz : 0 < N z) {t M : ℝ} (ht : 0 ≤ t) (htz : t * N x ≤ N z)
    (hxM : N x ≤ M) (hzM : N (x + z) ≤ M) :
    N ((N x)⁻¹ • x + t • ((N z)⁻¹ • z)) ≤ M / N x := by
  let r := t * N x / N z
  have hr : 0 ≤ r := div_nonneg (mul_nonneg ht hx.le) hz.le
  have hr' : r ≤ 1 := (div_le_one hz).mpr htz
  have hid : (N x)⁻¹ • x + t • ((N z)⁻¹ • z) =
      (1 - r) • ((N x)⁻¹ • x) + r • ((N x)⁻¹ • (x + z)) := by
    dsimp [r]
    match_scalars <;> field_simp [hx.ne', hz.ne']
    ring
  rw [hid]
  apply seminorm_segment_le N hr hr'
  · rw [seminorm_normalize N hx]
    exact (one_le_div hx).mpr hxM
  · rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), ← div_eq_inv_mul]
    exact (div_le_div_iff_of_pos_right hx).mpr hzM

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma normD_bound_at_original_unit (hsp : UnitSliceProperty X) (N : Seminorm ℝ X)
    {a b R : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : ∀ u : X, a * ‖u‖ ≤ N u ∧ N u ≤ b * ‖u‖)
    (hR : ∀ u : X, ‖u‖ ≤ 1 → N u ≤ R) {x : X} (hx : ‖x‖ = 1) :
    D N ((N x)⁻¹ • x) (a / (4 * b)) ≤ R / N x - 1 := by
  have hNx : 0 < N x := by have := (hab x).1; rw [hx, mul_one] at this; linarith
  have hNxb : N x ≤ b := by simpa only [hx, mul_one] using (hab x).2
  have hNxR : N x ≤ R := hR x hx.le
  let t := a / (4 * b)
  have ht : 0 < t := by dsimp [t]; positivity
  have htb : t * (4 * b) = a := div_mul_cancel₀ _ (by positivity)
  have htb' : t * b = a / 4 := by linarith
  unfold D
  refine csSup_le ?_ ?_
  · exact ⟨_, ⊤, cofinite_top, rfl⟩
  rintro q ⟨F, hF, rfl⟩
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := min (1 / 4 : ℝ) (δ * N x / (2 * b))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ * N x / (2 * b) := min_le_right _ _
  have hεδ' : b * ε ≤ δ * N x / 2 := by
    have hd := (le_div_iff₀ (show 0 < 2 * b by positivity)).mp hεδ
    nlinarith
  obtain ⟨v, e, hv, he, hzF, hfar⟩ := cofinite_diametral_correction hsp hx hF hε
  let z := v - x - e
  have hzlo : 1 < ‖z‖ := by
    have hn := norm_sub_le z (-e)
    have hid : z - -e = v - x := by dsimp [z]; abel
    rw [hid, norm_neg] at hn
    linarith
  have hNz : 0 < N z := (mul_pos ha (by linarith)).trans_le (hab z).1
  have htz : t * N x ≤ N z := by
    have hc := mul_le_mul_of_nonneg_left hNxb ht.le
    have hd := (hab z).1
    nlinarith
  have hend : N (x + z) ≤ R + b * ε := by
    have hid : x + z = v - e := by dsimp [z]; abel
    rw [hid]
    have hc := map_sub_le_add N v e
    have hb' := (hab e).2
    have hRv := hR v hv
    nlinarith
  have hxM : N x ≤ R + b * ε := by nlinarith
  have hvalue := seminorm_normalized_segment N hNx hNz ht.le htz hxM hend
  have hy : N ((N z)⁻¹ • z) = 1 := seminorm_normalize N hNz
  have hyF : (N z)⁻¹ • z ∈ F := F.smul_mem _ hzF
  have hinf := csInf_le (normOneSidedValues_bddBelow N ((N x)⁻¹ • x) t F)
    ⟨(N z)⁻¹ • z, hyF, hy, rfl⟩
  change sInf (normOneSidedValues N ((N x)⁻¹ • x) t F) ≤ _
  have hquot : (R + b * ε) / N x ≤ R / N x + δ := by
    apply (div_le_iff₀ hNx).mpr
    rw [add_mul, div_mul_cancel₀ R hNx.ne']
    nlinarith
  linarith

end ExactModuli

end

end OAI
