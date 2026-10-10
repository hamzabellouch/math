import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Routing
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryParking

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

lemma RationalConstant.max {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) :
    RationalConstant (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

lemma finite_upper_bound_nat {α : Type*} [Finite α] (f : α → ℝ) :
    ∃ R : ℕ, ∀ i, f i < (R : ℝ) := by
  obtain ⟨R,hR⟩ := finite_upper_bound f
  obtain ⟨N,hN⟩ := exists_nat_gt R
  exact ⟨N, fun i => (hR i).trans hN⟩

omit [Fintype ι] in
lemma scale_separation_mono {a : ι → Space} {D L N : ℝ} (hL : 0 ≤ L) (hLN : L ≤ N)
    (h : CenterSeparated (fun i k => L * a i k) D) :
    CenterSeparated (fun i k => N * a i k) D := by
  intro i j hij
  obtain ⟨k,hk⟩ := h i j hij
  refine ⟨k,hk.trans_le ?_⟩
  simp only [← mul_sub, abs_mul, abs_of_nonneg hL, abs_of_nonneg (hL.trans hLN)]
  exact mul_le_mul_of_nonneg_right hLN (abs_nonneg _)

lemma exists_nat_expansion {a b : ι → Space} (ha : Function.Injective a)
    (hb : Function.Injective b) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ L : ℕ, 1 ≤ (L : ℝ) ∧ R + 2 ≤ (L : ℝ) ∧
      CenterSeparated (fun i k => (L : ℝ) * a i k) D ∧
      CenterSeparated (fun i k => (L : ℝ) * b i k) D := by
  obtain ⟨L,hL,hLR,hLa,hLb⟩ := exists_expansion ha hb (R := R) hD
  obtain ⟨N,hN⟩ := exists_nat_gt L
  exact ⟨N,hL.trans hN.le,hLR.trans hN.le,
    scale_separation_mono (by linarith) hN.le hLa,
    scale_separation_mono (by linarith) hN.le hLb⟩

lemma exists_rational_parking (a b : ι → Space) {D R : ℝ} (hD : 0 ≤ D) :
    RationalConstant D → RationalConstant R →
    ∃ p : ι → Space, RationalCenters p ∧
      (∀ i j, D < |a i 0 - p j 0|) ∧
      (∀ i j, D < |b i 0 - p j 0|) ∧
      (∀ i j, i ≠ j → D < |p i 0 - p j 0|) ∧
      (∀ i, 2 + R < p i 0) := by
  classical
  intro Dr Rr
  obtain ⟨La, hLa⟩ := finite_upper_bound_nat (fun i => a i 0)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound_nat (fun i => b i 0)
  let K := max (3 + R) (max (La : ℝ) (Lb : ℝ)) + D + 1
  let e := Fintype.equivFin ι
  let p : ι → Space := fun i => ![K + (D + 1) * (e i).val, 0, 0]
  have hKs : 2 + R < K := by dsimp [K]; have := le_max_left (3 + R) (max (La : ℝ) (Lb : ℝ)); linarith
  have hKa : ∀ i, D < K - a i 0 := by
    intro i
    have := (le_max_left (La : ℝ) (Lb : ℝ)).trans (le_max_right (3 + R) (max (La : ℝ) (Lb : ℝ)))
    have := hLa i
    dsimp [K]
    linarith
  have hKb : ∀ i, D < K - b i 0 := by
    intro i
    have := (le_max_right (La : ℝ) (Lb : ℝ)).trans (le_max_right (3 + R) (max (La : ℝ) (Lb : ℝ)))
    have := hLb i
    dsimp [K]
    linarith
  have hpn : ∀ i, K ≤ p i 0 := by
    intro i
    dsimp [p]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have Kr : RationalConstant K :=
    ((RationalConstant.nat 3).add Rr |>.max
      ((RationalConstant.nat La).max (RationalConstant.nat Lb))).add Dr |>.add RationalConstant.one
  have pr : RationalCenters p := by
    intro i k
    fin_cases k
    · exact Kr.add ((Dr.add RationalConstant.one).mul (RationalConstant.nat _))
    · exact RationalConstant.zero
    · exact RationalConstant.zero
  refine ⟨p, pr, ?_, ?_, ?_, fun i => hKs.trans_le (hpn i)⟩
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

theorem elementary_guarded_solid_box_motion (A B : BoxLayout ι) (safe : Set ι)
    (Ar : RationalLayout A) (Br : RationalLayout B)
    (hA : A.Positive) (hB : B.Positive)
    (hsA : A.Separated 0) (hsB : B.Separated 0)
    (hvol : ∀ i, ∏ k, A.width i k = ∏ k, B.width i k)
    (hgA : A.Guarded safe) (hgB : B.Guarded safe) :
    ∃ η : ℚ, 0 < η ∧ ∃ m : BoxMotion A B safe (η : ℝ), ElementaryMotion m := by
  classical
  obtain ⟨ηA, hηA, hmA⟩ := hsA.positive_margin
  obtain ⟨ηB, hηB, hmB⟩ := hsB.positive_margin
  obtain ⟨q,hq,hqm⟩ := exists_rat_btwn (lt_min hηA hηB)
  let η : ℝ := q
  have hη : 0 < η := hq
  have ηr : RationalConstant η := RationalConstant.rat q
  have hmA' := hmA.mono (hqm.le.trans (min_le_left ηA ηB))
  have hmB' := hmB.mono (hqm.le.trans (min_le_right ηA ηB))
  obtain ⟨RA, hRA⟩ := finite_upper_bound_nat (fun p : ι × Fin 3 => A.width p.1 p.2)
  obtain ⟨RB, hRB⟩ := finite_upper_bound_nat (fun p : ι × Fin 3 => B.width p.1 p.2)
  let R : ℝ := max 1 (max (RA : ℝ) (RB : ℝ))
  have Rr : RationalConstant R := RationalConstant.one.max
    ((RationalConstant.nat RA).max (RationalConstant.nat RB))
  have hR : 1 ≤ R := le_max_left _ _
  have hAR : ∀ i k, A.width i k ≤ R := fun i k => (hRA (i,k)).le.trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hBR : ∀ i k, B.width i k ≤ R := fun i k => (hRB (i,k)).le.trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let D := 2 * R + 4 * η
  have hD : 0 ≤ D := by dsimp [D]; linarith
  obtain ⟨L, hΛ, hΛR, hΛA, hΛB⟩ := exists_nat_expansion
    (BoxLayout.center_injective hA hsA) (BoxLayout.center_injective hB hsB) (R := R) hD
  let Λ : ℝ := L
  have Λr : RationalConstant Λ := RationalConstant.nat L
  let a : ι → Space := fun i k => Λ * A.center i k
  let b : ι → Space := fun i k => Λ * B.center i k
  have ar : RationalCenters a := fun i k => Λr.mul (Ar.1 i k)
  have br : RationalCenters b := fun i k => Λr.mul (Br.1 i k)
  have Dr : RationalConstant D := ((RationalConstant.nat 2).mul Rr).add
    ((RationalConstant.nat 4).mul ηr)
  obtain ⟨p, pr, hpa, hpb, hpp, hpg⟩ := exists_rational_parking a b (R := R) hD Dr Rr
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
  obtain ⟨HA, hHA⟩ := finite_upper_bound_nat (fun i => a i 1)
  obtain ⟨HB, hHB⟩ := finite_upper_bound_nat (fun i => b i 1)
  obtain ⟨HP, hHP⟩ := finite_upper_bound_nat (fun i => p i 1)
  let H : ℝ := max (HA : ℝ) (max (HB : ℝ) (HP : ℝ)) + D + 1
  have Hr : RationalConstant H := ((RationalConstant.nat HA).max
    ((RationalConstant.nat HB).max (RationalConstant.nat HP))).add Dr |>.add RationalConstant.one
  have hhA : ∀ i, D < H - a i 1 := by
    intro i
    have := le_max_left (HA : ℝ) (max (HB : ℝ) (HP : ℝ))
    have := hHA i
    dsimp [H]; linarith
  have hhB : ∀ i, D < H - b i 1 := by
    intro i
    have := (le_max_left (HB : ℝ) (HP : ℝ)).trans (le_max_right (HA : ℝ) (max (HB : ℝ) (HP : ℝ)))
    have := hHB i
    dsimp [H]; linarith
  have hhP : ∀ i, D < H - p i 1 := by
    intro i
    have := (le_max_right (HB : ℝ) (HP : ℝ)).trans (le_max_right (HA : ℝ) (max (HB : ℝ) (HP : ℝ)))
    have := hHP i
    dsimp [H]; linarith
  let m₁ := expandCenters hA hmA' hgA hΛ
  let m₂ := reshapeMotion hA hB hAR hBR hvol (le_refl D) hΛA hag
  obtain ⟨m₃,e₃⟩ := elementary_evacuateToParking ar pr Br.2 Hr hB hsize hΛA hpa hpp hhA hhP hD hga hgp
  obtain ⟨m₄,e₄⟩ := elementary_evacuateToParking br pr Br.2 Hr hB hsize hΛB hpb hpp hhB hhP hD hgb hgp
  let m₅ := expandCenters hB hmB' hgB hΛ
  have e₁ : ElementaryMotion m₁ := ElementaryMotion.expansion Ar.1 Ar.2 Λr _ _ _ _
  have e₂ : ElementaryMotion m₂ := ElementaryMotion.reshape ar Ar.2 Br.2 _ _ _ _ _ _ _ _
  have e₅ : ElementaryMotion m₅ := ElementaryMotion.expansion Br.1 Br.2 Λr _ _ _ _
  exact ⟨q, by exact_mod_cast hq, _,
    (((e₁.trans e₂ ⟨ar,Ar.2⟩).trans e₃ ⟨ar,Br.2⟩).trans e₄.reverse ⟨pr,Br.2⟩).trans
      e₅.reverse ⟨br,Br.2⟩⟩

end BalancedTransport.Effectivity
end

end OAI
