import OAI.NumberTheory.TotientAsymptotic.SmoothTerminalEncoding

namespace OAI

/-! The terminal two-factor sum costs only two smooth Euler products. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma smooth_terminal_rectangle_mass (d N : ℕ) (hd : 0 < d)
    (E : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hE : ∀ w ∈ E,w.1.1*w.1.2=d ∧ 0 < w.2.1*w.2.2 ∧
      largestPrimeFactor (w.2.1*w.2.2) ≤ N) :
    (∑ w ∈ E,((w.2.1*w.2.2:ℕ):ℝ)⁻¹) ≤
      (2:ℝ)^d.primeFactorsList.length*(primeEulerProduct N)^2 := by
  classical
  let F := E.image Prod.fst
  let A := E.image (fun w => w.2.1)
  let B := E.image (fun w => w.2.2)
  have hF : (F.card:ℝ) ≤ (2:ℝ)^d.primeFactorsList.length := by
    exact_mod_cast two_factorizations_card_le hd F (by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      exact (hE w hw).1)
  have hA : (∑ a ∈ A,(a:ℝ)⁻¹) ≤ primeEulerProduct N := by
    apply smooth_residual_reciprocal_mass N A
    intro a ha
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ha
    have hh := hE w hw
    refine ⟨?_,smooth_divisor_bound hh.2.1 (dvd_mul_right _ _) hh.2.2⟩
    exact Nat.pos_of_ne_zero (by intro h; simp [h] at hh)
  have hB : (∑ b ∈ B,(b:ℝ)⁻¹) ≤ primeEulerProduct N := by
    apply smooth_residual_reciprocal_mass N B
    intro b hb
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
    have hh := hE w hw
    refine ⟨?_,smooth_divisor_bound hh.2.1 (dvd_mul_left _ _) hh.2.2⟩
    exact Nat.pos_of_ne_zero (by intro h; simp [h] at hh)
  have hsub : E ⊆ F ×ˢ (A ×ˢ B) := by
    intro w hw
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,Finset.mem_image.mpr ⟨w,hw,rfl⟩⟩⟩
  have hrectangle : (∑ w ∈ F ×ˢ (A ×ˢ B),((w.2.1*w.2.2:ℕ):ℝ)⁻¹)=
      (F.card:ℝ)*(∑ a ∈ A,(a:ℝ)⁻¹)*(∑ b ∈ B,(b:ℝ)⁻¹) := by
    rw [Finset.sum_product]
    have hi : (∑ z ∈ A ×ˢ B,((z.1*z.2:ℕ):ℝ)⁻¹)=
        (∑ a ∈ A,(a:ℝ)⁻¹)*(∑ b ∈ B,(b:ℝ)⁻¹) := by
      rw [Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Nat.cast_mul,mul_inv_rev]
      ring
    simp only [hi,Finset.sum_const,nsmul_eq_mul]
    ring
  have hEuler0 : 0 ≤ primeEulerProduct N :=
    (Finset.sum_nonneg (fun a _ => inv_nonneg.mpr (Nat.cast_nonneg a))).trans hA
  calc
    _ ≤ ∑ w ∈ F ×ˢ (A ×ˢ B),((w.2.1*w.2.2:ℕ):ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (F.card:ℝ)*(∑ a ∈ A,(a:ℝ)⁻¹)*(∑ b ∈ B,(b:ℝ)⁻¹) := hrectangle
    _ ≤ (2:ℝ)^d.primeFactorsList.length*(primeEulerProduct N)*(primeEulerProduct N) := by
      apply mul_le_mul _ hB (Finset.sum_nonneg (fun b _ => by positivity))
        (mul_nonneg (by positivity) hEuler0)
      exact mul_le_mul hF hA (Finset.sum_nonneg (fun a _ => by positivity)) (by positivity)
    _ = _ := by ring

theorem smooth_terminal_mass (d N : ℕ) (hd : 0 < d) (Q : Finset SmoothTerminalTriple)
    (hQ : ∀ z ∈ Q,TerminalConditions d N z) :
    (∑ z ∈ Q,(terminalFirst z:ℝ)⁻¹) ≤
      (2:ℝ)^d.primeFactorsList.length*(primeEulerProduct N)^2 := by
  classical
  let encode : {z // z ∈ Q} → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun z => terminalEncoding d hd z.val (hQ z.val z.property)
  let E := Q.attach.image encode
  have hi : Function.Injective encode := by
    intro z w he
    have hz := terminalEncoding_spec d N hd z.val (hQ z.val z.property)
    have hw := terminalEncoding_spec d N hd w.val (hQ w.val w.property)
    change d=(encode z).1.1*(encode z).1.2 ∧
      terminalMiddle z.val=(encode z).1.1*(encode z).2.1 ∧
      terminalLast z.val=(encode z).1.2*(encode z).2.2 ∧
      terminalFirst z.val=(encode z).2.1*(encode z).2.2 at hz
    change d=(encode w).1.1*(encode w).1.2 ∧
      terminalMiddle w.val=(encode w).1.1*(encode w).2.1 ∧
      terminalLast w.val=(encode w).1.2*(encode w).2.2 ∧
      terminalFirst w.val=(encode w).2.1*(encode w).2.2 at hw
    rw [he] at hz
    apply Subtype.ext
    apply Prod.ext
    · exact hz.2.2.2.trans hw.2.2.2.symm
    · exact Prod.ext (hz.2.1.trans hw.2.1.symm) (hz.2.2.1.trans hw.2.2.1.symm)
  have hsum : (∑ z ∈ Q,(terminalFirst z:ℝ)⁻¹)=
      ∑ w ∈ E,((w.2.1*w.2.2:ℕ):ℝ)⁻¹ := by
    rw [Finset.sum_image (fun z _ w _ h => hi h)]
    rw [← Finset.sum_attach Q (fun z => (terminalFirst z:ℝ)⁻¹)]
    apply Finset.sum_congr rfl
    intro z hz
    have hh := terminalEncoding_spec d N hd z.val (hQ z.val z.property)
    rw [show terminalFirst z.val=(encode z).2.1*(encode z).2.2 from hh.2.2.2]
  rw [hsum]
  apply smooth_terminal_rectangle_mass d N hd E
  intro w hw
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
  have hh := terminalEncoding_spec d N hd z.val (hQ z.val z.property)
  exact ⟨hh.1.symm,hh.2.2.2 ▸ (hQ z.val z.property).1,
    hh.2.2.2 ▸ (hQ z.val z.property).2.2⟩

end TotientAsymptotic

end

end OAI
