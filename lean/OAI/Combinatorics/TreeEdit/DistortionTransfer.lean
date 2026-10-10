import OAI.Combinatorics.TreeEdit.FiniteFourier

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma ratio_set_finite {β : Type*} [Finite β] (f : β → β → ℝ) :
    {r | ∃ x y, x ≠ y ∧ r = f x y}.Finite := by
  apply (Set.finite_range (fun xy : β × β => f xy.1 xy.2)).subset
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x,y), rfl⟩

lemma exists_realL1_injective (β : Type*) [Fintype β] : ∃ f : β → RealL1, Function.Injective f := by
  classical
  refine ⟨fun x => lp.single 1 0 ((Fintype.equivFin β x).val : ℝ), ?_⟩
  intro x y h
  have hh := congrArg (fun v : RealL1 => v 0) h
  simp only [lp.single_apply, Pi.single_eq_same] at hh
  exact (Fintype.equivFin β).injective (Fin.ext (Nat.cast_injective hh))

lemma c1_lower {W : Finset (List Bool)} {L : ℝ}
    (h : ∀ f : W → RealL1, Function.Injective f → L ≤ distortion W f) : L ≤ c1 W := by
  apply le_csInf
  · obtain ⟨f, hf⟩ := exists_realL1_injective W
    exact ⟨distortion W f, f, hf, rfl⟩
  · rintro D ⟨f, hf, rfl⟩
    exact h f hf

noncomputable def stretch (W : Finset (List Bool)) (f : W → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧ r = dist (f x) (f y) / (ed x.val y.val : ℝ)}

noncomputable def contraction (W : Finset (List Bool)) (f : W → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧ r = (ed x.val y.val : ℝ) / dist (f x) (f y)}

lemma stretch_nonneg {W : Finset (List Bool)} (hW : 2 ≤ W.card) (f : W → RealL1) : 0 ≤ stretch W f := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < W.card)
  apply le_trans (div_nonneg (dist_nonneg (x := f ⟨x,hx⟩) (y := f ⟨y,hy⟩)) (Nat.cast_nonneg _))
  apply le_csSup (ratio_set_finite _).bddAbove
  exact ⟨⟨x,hx⟩, ⟨y,hy⟩, fun h => hxy (congrArg Subtype.val h), rfl⟩

lemma contraction_nonneg {W : Finset (List Bool)} (hW : 2 ≤ W.card) (f : W → RealL1) : 0 ≤ contraction W f := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < W.card)
  apply le_trans (div_nonneg (Nat.cast_nonneg (ed x y)) (dist_nonneg (x := f ⟨x,hx⟩) (y := f ⟨y,hy⟩)))
  apply le_csSup (ratio_set_finite _).bddAbove
  exact ⟨⟨x,hx⟩, ⟨y,hy⟩, fun h => hxy (congrArg Subtype.val h), rfl⟩

lemma dist_le_stretch {W : Finset (List Bool)} (f : W → RealL1) (x y : W) :
    dist (f x) (f y) ≤ stretch W f * ed x.val y.val := by
  by_cases hxy : x = y
  · subst y; simp
  · have he : (0 : ℝ) < ed x.val y.val := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hxy (Subtype.ext (ed_eq_zero_iff.mp h)))
    apply (div_le_iff₀ he).mp
    exact le_csSup (ratio_set_finite _).bddAbove ⟨x, y, hxy, rfl⟩

lemma ed_le_contraction {W : Finset (List Bool)} (f : W → RealL1) (hf : Function.Injective f) (x y : W) :
    (ed x.val y.val : ℝ) ≤ contraction W f * dist (f x) (f y) := by
  by_cases hxy : x = y
  · subst y; simp
  · have hd : 0 < dist (f x) (f y) := dist_pos.mpr (fun h => hxy (hf h))
    apply (div_le_iff₀ hd).mp
    exact le_csSup (ratio_set_finite _).bddAbove ⟨x, y, hxy, rfl⟩

theorem binary_transfer {A Γ : Type*} [Fintype A] [AddCommGroup A] [Fintype Γ]
    {M P : ℕ} (hM : 0 < M) (hP : 0 < P) (w : A → Word Γ M) (z : A)
    (c : Γ → Word Bool P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcode : ∀ x y : Word Γ M,
      (P : ℝ) / 804 * ed x.val y.val ≤ ed (encode c x.val) (encode c y.val))
    (hsep : ∀ x, (M : ℝ) ≤ a * ed (w x).val (w (x + z)).val)
    (hobs : ∀ (F : A → RealL1) (C : ℝ), 0 ≤ C →
      (∀ x y, dist (F x) (F y) ≤ C * ed (w x).val (w y).val) →
      FiniteFourier.average (fun x => dist (F x) (F (x + z))) ≤ C * M * b) :
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = M * P) ∧
      (804 * a * b)⁻¹ ≤ c1 W := by
  classical
  let enc (x : A) := encode c (w x).val
  let W := Finset.univ.image enc
  have hmem (x : A) : enc x ∈ W := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hne (x : A) : enc x ≠ enc (x + z) := by
    intro he
    have hc := hcode (w x) (w (x + z))
    rw [← show enc x = encode c (w x).val from rfl,
      ← show enc (x + z) = encode c (w (x + z)).val from rfl, he, ed_self] at hc
    have he0 : (ed (w x).val (w (x + z)).val : ℝ) = 0 := by
      have hp : (0 : ℝ) < P := by exact_mod_cast hP
      nlinarith only [hc, hp, (Nat.cast_nonneg (ed (w x).val (w (x + z)).val) : (0 : ℝ) ≤ ed (w x).val (w (x + z)).val)]
    have hh := hsep x
    rw [he0, mul_zero] at hh
    exact (not_le_of_gt (by exact_mod_cast hM : (0 : ℝ) < M)) hh
  have hW : 2 ≤ W.card := by
    have hh := Finset.one_lt_card.mpr ⟨enc 0, hmem 0, enc (0 + z), hmem _, hne 0⟩
    omega
  refine ⟨W, hW, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    simp [enc, length_encode, (w x).property]
  · apply c1_lower
    intro f hf
    let F : A → RealL1 := fun x => f ⟨enc x, hmem x⟩
    let S := stretch W f
    let D := contraction W f
    have hS : 0 ≤ S := stretch_nonneg hW f
    have hD : 0 ≤ D := contraction_nonneg hW f
    have hlip (x y : A) : dist (F x) (F y) ≤ (S * P) * ed (w x).val (w y).val := by
      calc
        _ ≤ S * ed (enc x) (enc y) := dist_le_stretch (W := W) f ⟨enc x, hmem x⟩ ⟨enc y, hmem y⟩
        _ ≤ S * (P * (ed (w x).val (w y).val : ℝ)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast ed_encode_le c (w x).val (w y).val) hS
        _ = _ := by ring
    have hu := hobs F (S * P) (mul_nonneg hS (Nat.cast_nonneg _)) hlip
    have hl (x : A) : (P : ℝ) * M ≤ 804 * a * D * dist (F x) (F (x + z)) := by
      have hc := hcode (w x) (w (x + z))
      have hd := ed_le_contraction f hf ⟨enc x, hmem x⟩ ⟨enc (x + z), hmem _⟩
      calc
        _ ≤ P * (a * ed (w x).val (w (x + z)).val) := mul_le_mul_of_nonneg_left (hsep x) (by positivity)
        _ = a * (P * ed (w x).val (w (x + z)).val) := by ring
        _ ≤ a * (804 * ed (enc x) (enc (x + z))) := mul_le_mul_of_nonneg_left (by dsimp [enc]; linarith) ha.le
        _ ≤ a * (804 * (D * dist (F x) (F (x + z)))) := by gcongr
        _ = _ := by ring
    have hav := FiniteFourier.average_mono hl
    rw [FiniteFourier.average_const] at hav
    have he : FiniteFourier.average (fun x => 804 * a * D * dist (F x) (F (x + z))) =
      (804 * a * D) * FiniteFourier.average (fun x => dist (F x) (F (x + z))) := by
      simp only [FiniteFourier.average, ← Finset.mul_sum]
      ring
    rw [he] at hav
    have hh := hav.trans (mul_le_mul_of_nonneg_left hu (by positivity))
    have hPM : (0 : ℝ) < P * M := by positivity
    have hd : 1 ≤ 804 * a * b * distortion W f := by
      apply (mul_le_mul_iff_left₀ hPM).mp
      change 1 * (P * M : ℝ) ≤ (804 * a * b * (S * D)) * (P * M)
      convert hh using 1 <;> first | rfl | ring
    rw [inv_eq_one_div]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 804 * a * b)).mpr (by simpa only [mul_comm] using hd)

end TreeEdit

end OAI
