import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Deformation

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

lemma finite_upper_bound {α : Type*} [Finite α] (f : α → ℝ) :
    ∃ R : ℝ, ∀ i, f i < R := by
  obtain ⟨R, hR⟩ := (Set.finite_range f).bddAbove
  exact ⟨R + 1, fun i => (hR (mem_range_self i)).trans_lt (lt_add_one _)⟩

lemma finite_positive_lower_bound {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ f i := by
  classical
  have hh : ∀ s : Finset α, ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨r, hr, h⟩ := ih
      refine ⟨min r (f a), lt_min hr (hf a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h i hi)
  simpa using hh Finset.univ

omit [Fintype ι] in
lemma BoxLayout.Separated.mono {A : BoxLayout ι} {η δ : ℝ}
    (h : A.Separated δ) (hle : η ≤ δ) : A.Separated η := by
  intro i j hij
  obtain ⟨k, hk⟩ := h i j hij
  exact ⟨k, by linarith⟩

lemma BoxLayout.Separated.positive_margin {A : BoxLayout ι}
    (h : A.Separated 0) : ∃ η : ℝ, 0 < η ∧ A.Separated η := by
  classical
  let J := {p : ι × ι // p.1 ≠ p.2}
  have hs (p : J) : ∃ k, 0 < |A.center p.1.1 k - A.center p.1.2 k| -
      (A.width p.1.1 k + A.width p.1.2 k) := by
    obtain ⟨k, hk⟩ := h _ _ p.2
    exact ⟨k, by linarith⟩
  choose κ hκ using hs
  obtain ⟨δ, hδ, hm⟩ := finite_positive_lower_bound
    (fun p : J => |A.center p.1.1 (κ p) - A.center p.1.2 (κ p)| -
      (A.width p.1.1 (κ p) + A.width p.1.2 (κ p))) hκ
  refine ⟨δ / 8, by positivity, ?_⟩
  intro i j hij
  let p : J := ⟨(i, j), hij⟩
  refine ⟨κ p, ?_⟩
  have hh := hm p
  dsimp [p] at hh ⊢
  linarith

omit [Fintype ι] in
lemma BoxLayout.center_injective {A : BoxLayout ι}
    (hp : A.Positive) (hs : A.Separated 0) : Function.Injective A.center := by
  intro i j hij
  by_contra hne
  obtain ⟨k, hk⟩ := hs i j hne
  rw [hij, sub_self, abs_zero] at hk
  linarith [hp i k, hp j k]

omit [Fintype ι] in
lemma centerSeparated_of_norm {a : ι → Space} {D : ℝ}
    (hD : 0 ≤ D) (ha : ∀ i j, i ≠ j → D < ‖a i - a j‖) : CenterSeparated a D := by
  intro i j hij
  by_contra! h
  have hh : ‖a i - a j‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr (by
    intro k
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h k)
  exact (ha i j hij).not_ge hh

lemma exists_expansion {a b : ι → Space} (ha : Function.Injective a)
    (hb : Function.Injective b) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ R + 2 ≤ Λ ∧
      CenterSeparated (fun i k => Λ * a i k) D ∧
      CenterSeparated (fun i k => Λ * b i k) D := by
  obtain ⟨La, hLa⟩ := finite_upper_bound (fun p : ι × ι => D / ‖a p.1 - a p.2‖)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound (fun p : ι × ι => D / ‖b p.1 - b p.2‖)
  let Λ := max 1 (max (R + 2) (max La Lb))
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛR : R + 2 ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hΛa : La ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hΛb : Lb ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hh (c : ι → Space) (hc : Function.Injective c)
      (hLc : ∀ i j, D / ‖c i - c j‖ < Λ) :
      CenterSeparated (fun i k => Λ * c i k) D := by
    apply centerSeparated_of_norm hD
    intro i j hij
    have hpos : 0 < ‖c i - c j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hc.ne hij))
    have he : (fun k => Λ * c i k) - (fun k => Λ * c j k) = Λ • (c i - c j) := by
      ext k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Λ)]
    exact (div_lt_iff₀ hpos).mp (hLc i j)
  exact ⟨Λ, hΛ, hΛR, hh a ha (fun i j => (hLa (i,j)).trans_le hΛa),
    hh b hb (fun i j => (hLb (i,j)).trans_le hΛb)⟩

lemma exists_parking (a b : ι → Space) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ p : ι → Space,
      (∀ i j, D < |a i 0 - p j 0|) ∧
      (∀ i j, D < |b i 0 - p j 0|) ∧
      (∀ i j, i ≠ j → D < |p i 0 - p j 0|) ∧
      (∀ i, 2 + R < p i 0) := by
  classical
  obtain ⟨La, hLa⟩ := finite_upper_bound (fun i => a i 0)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound (fun i => b i 0)
  let K := max (3 + R) (max La Lb) + D + 1
  let e := Fintype.equivFin ι
  let p : ι → Space := fun i => ![K + (D + 1) * (e i).val, 0, 0]
  have hKs : 2 + R < K := by dsimp [K]; have := le_max_left (3 + R) (max La Lb); linarith
  have hKa : ∀ i, D < K - a i 0 := by
    intro i
    have := (le_max_left La Lb).trans (le_max_right (3 + R) (max La Lb))
    have := hLa i
    dsimp [K]
    linarith
  have hKb : ∀ i, D < K - b i 0 := by
    intro i
    have := (le_max_right La Lb).trans (le_max_right (3 + R) (max La Lb))
    have := hLb i
    dsimp [K]
    linarith
  have hpn : ∀ i, K ≤ p i 0 := by
    intro i
    dsimp [p]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  refine ⟨p, ?_, ?_, ?_, fun i => hKs.trans_le (hpn i)⟩
  · intro i j
    have := hKa i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - a i 0) (le_abs_self _)
  · intro i j
    have := hKb i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - b i 0) (le_abs_self _)
  · intro i j hij
    have hv : (e i).val ≠ (e j).val := by intro h; exact hij (e.injective (Fin.ext h))
    have hh : (1 : ℝ) ≤ |(e i).val - ((e j).val : ℝ)| := by
      rcases lt_or_gt_of_ne hv with hl | hl
      · have hcast : ((e i).val : ℝ) + 1 ≤ (e j).val := by exact_mod_cast hl
        rw [abs_of_nonpos (by linarith : ((e i).val : ℝ) - (e j).val ≤ 0)]
        linarith
      · have hcast : ((e j).val : ℝ) + 1 ≤ (e i).val := by exact_mod_cast hl
        rw [abs_of_nonneg (by linarith : 0 ≤ ((e i).val : ℝ) - (e j).val)]
        linarith
    have he : p i 0 - p j 0 = (D + 1) * (((e i).val : ℝ) - (e j).val) := by dsimp [p]; ring
    rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ D + 1)]
    nlinarith

theorem guarded_solid_box_motion (A B : BoxLayout ι) (safe : Set ι)
    (hA : A.Positive) (hB : B.Positive)
    (hsA : A.Separated 0) (hsB : B.Separated 0)
    (hvol : ∀ i, ∏ k, A.width i k = ∏ k, B.width i k)
    (hgA : A.Guarded safe) (hgB : B.Guarded safe) :
    ∃ η : ℝ, 0 < η ∧ Nonempty (BoxMotion A B safe η) := by
  classical
  obtain ⟨ηA, hηA, hmA⟩ := hsA.positive_margin
  obtain ⟨ηB, hηB, hmB⟩ := hsB.positive_margin
  let η := min ηA ηB
  have hη : 0 < η := lt_min hηA hηB
  have hmA' := hmA.mono (min_le_left ηA ηB)
  have hmB' := hmB.mono (min_le_right ηA ηB)
  obtain ⟨RA, hRA⟩ := finite_upper_bound (fun p : ι × Fin 3 => A.width p.1 p.2)
  obtain ⟨RB, hRB⟩ := finite_upper_bound (fun p : ι × Fin 3 => B.width p.1 p.2)
  let R := max 1 (max RA RB)
  have hR : 1 ≤ R := le_max_left _ _
  have hAR : ∀ i k, A.width i k ≤ R := fun i k => (hRA (i,k)).le.trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hBR : ∀ i k, B.width i k ≤ R := fun i k => (hRB (i,k)).le.trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let D := 2 * R + 4 * η
  have hD : 0 ≤ D := by dsimp [D]; linarith
  obtain ⟨Λ, hΛ, hΛR, hΛA, hΛB⟩ := exists_expansion
    (BoxLayout.center_injective hA hsA) (BoxLayout.center_injective hB hsB) (R := R) hD
  let a : ι → Space := fun i k => Λ * A.center i k
  let b : ι → Space := fun i k => Λ * B.center i k
  obtain ⟨p, hpa, hpb, hpp, hpg⟩ := exists_parking a b (R := R) hD
  have hag : ∀ i ∈ safe, 2 + R < a i 0 := by
    intro i hi
    have hh : 2 < A.center i 0 := by have := hgA i hi; linarith [hA i 0]
    have hΛp : 0 < Λ := by linarith
    have hh' := mul_lt_mul_of_pos_left hh hΛp
    dsimp [a]
    nlinarith
  have hbg : ∀ i ∈ safe, 2 + R < b i 0 := by
    intro i hi
    have hh : 2 < B.center i 0 := by have := hgB i hi; linarith [hB i 0]
    have hΛp : 0 < Λ := by linarith
    have hh' := mul_lt_mul_of_pos_left hh hΛp
    dsimp [b]
    nlinarith
  have hga : (BoxLayout.mk a B.width).Guarded safe := by
    intro i hi
    change 2 < a i 0 - B.width i 0
    linarith [hag i hi, hBR i 0]
  have hgb : (BoxLayout.mk b B.width).Guarded safe := by
    intro i hi
    change 2 < b i 0 - B.width i 0
    linarith [hbg i hi, hBR i 0]
  have hgp : (BoxLayout.mk p B.width).Guarded safe := by
    intro i _
    change 2 < p i 0 - B.width i 0
    linarith [hpg i, hBR i 0]
  have hsize : ∀ i j k, B.width i k + B.width j k + 4 * η ≤ D := by
    intro i j k
    dsimp [D]
    linarith [hBR i k, hBR j k]
  obtain ⟨HA, hHA⟩ := finite_upper_bound (fun i => a i 1)
  obtain ⟨HB, hHB⟩ := finite_upper_bound (fun i => b i 1)
  obtain ⟨HP, hHP⟩ := finite_upper_bound (fun i => p i 1)
  let H := max HA (max HB HP) + D + 1
  have hhA : ∀ i, D < H - a i 1 := by
    intro i
    have := le_max_left HA (max HB HP)
    have := hHA i
    dsimp [H]; linarith
  have hhB : ∀ i, D < H - b i 1 := by
    intro i
    have := (le_max_left HB HP).trans (le_max_right HA (max HB HP))
    have := hHB i
    dsimp [H]; linarith
  have hhP : ∀ i, D < H - p i 1 := by
    intro i
    have := (le_max_right HB HP).trans (le_max_right HA (max HB HP))
    have := hHP i
    dsimp [H]; linarith
  let m₁ := expandCenters hA hmA' hgA hΛ
  let m₂ := reshapeMotion hA hB hAR hBR hvol (le_refl D) hΛA hag
  let m₃ := evacuateToParking hB hsize hΛA hpa hpp hhA hhP hD hga hgp
  let m₄ := evacuateToParking hB hsize hΛB hpb hpp hhB hhP hD hgb hgp
  let m₅ := expandCenters hB hmB' hgB hΛ
  exact ⟨η, hη, ⟨(((m₁.trans m₂).trans m₃).trans m₄.reverse).trans m₅.reverse⟩⟩

end BalancedTransport.Geometry
end

end OAI
