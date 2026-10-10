import OAI.NumberTheory.TotientAsymptotic.CollisionSieveTails

namespace OAI

/-! Two nested prime-pair tails, with the larger-prime coefficient allowed
 to depend on the smaller prime as in Ford's distinct-largest-prime case. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma two_prime_fiber_sum (E : Finset (ℕ × ℕ)) (s : ℕ) :
    (∑ q ∈ E.filter (fun q => q.2=s),((q.1*q.2:ℕ):ℝ)⁻¹)=
      (s:ℝ)⁻¹*(∑ q ∈ (E.filter (fun q => q.2=s)).image Prod.fst,(q:ℝ)⁻¹) := by
  rw [Finset.mul_sum,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [(Finset.mem_filter.mp hq).2,Nat.cast_mul,mul_inv_rev]
  · intro q hq r hr he
    exact Prod.ext he ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm)

lemma nested_prime_pair_tail {A y T : ℝ}
    (hA : 0 ≤ A)
    (htail : ∀ b : ℕ,0 < b → (b:ℝ) ≤ y → ∀ Q : Finset ℕ,
      (∀ q ∈ Q,T ≤ q ∧ q.Prime ∧ (b*q+1).Prime) →
      (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ A)
    (E : Finset (ℕ × ℕ)) (a : ℕ → ℕ) (b : ℕ)
    (hb : 0 < b) (hby : (b:ℝ) ≤ y)
    (hE : ∀ q ∈ E,T ≤ q.1 ∧ q.1.Prime ∧ (a q.2*q.1+1).Prime ∧
      0 < a q.2 ∧ (a q.2:ℝ) ≤ y ∧ T ≤ q.2 ∧ q.2.Prime ∧ (b*q.2+1).Prime) :
    (∑ q ∈ E,((q.1*q.2:ℕ):ℝ)⁻¹) ≤ A^2 := by
  classical
  let S := E.image Prod.snd
  have hmap : ∀ q ∈ E,q.2 ∈ S := fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩
  have houter : (∑ s ∈ S,(s:ℝ)⁻¹) ≤ A := by
    apply htail b hb hby S
    intro s hs
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    exact (hE q hq).2.2.2.2.2
  have hfiber (s : ℕ) (hs : s ∈ S) :
      (∑ q ∈ E.filter (fun q => q.2=s),((q.1*q.2:ℕ):ℝ)⁻¹) ≤ A*(s:ℝ)⁻¹ := by
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hs
    have hw := hE q hq
    have ha : 0 < a s := he ▸ hw.2.2.2.1
    have hay : (a s:ℝ) ≤ y := he ▸ hw.2.2.2.2.1
    have hi := htail (a s) ha hay ((E.filter (fun q => q.2=s)).image Prod.fst) (by
      intro p hp
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hr,her⟩ := Finset.mem_filter.mp hr
      have hw := hE r hr
      exact ⟨hw.1,hw.2.1,by simpa only [her] using hw.2.2.1⟩)
    rw [two_prime_fiber_sum]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (Nat.cast_nonneg s))
  calc
    _ = ∑ s ∈ S,∑ q ∈ E.filter (fun q => q.2=s),((q.1*q.2:ℕ):ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun q => ((q.1*q.2:ℕ):ℝ)⁻¹)).symm
    _ ≤ ∑ s ∈ S,A*(s:ℝ)⁻¹ := Finset.sum_le_sum hfiber
    _ = A*(∑ s ∈ S,(s:ℝ)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ A*A := mul_le_mul_of_nonneg_left houter hA
    _ = _ := (pow_two _).symm

 theorem distinct_prime_reciprocal_tail : ∃ C : ℝ,0 < C ∧ ∀ (y T : ℝ),
    Real.exp 2 ≤ y → 1 < T → ∀ (E : Finset (ℕ × ℕ)) (a : ℕ → ℕ) (b : ℕ),
    0 < b → (b:ℝ) ≤ y →
    (∀ q ∈ E,T ≤ q.1 ∧ q.1.Prime ∧ (a q.2*q.1+1).Prime ∧
      0 < a q.2 ∧ (a q.2:ℝ) ≤ y ∧ T ≤ q.2 ∧ q.2.Prime ∧ (b*q.2+1).Prime) →
    (∑ q ∈ E,((q.1*q.2:ℕ):ℝ)⁻¹) ≤ C*(B y)^2/(Real.log T)^2 := by
  obtain ⟨C,hC,hbound⟩ := collision_pair_reciprocal_tail
  refine ⟨C^2,by positivity,?_⟩
  intro y T hy hT E a b hb hby hE
  have hy0 : 0 < y := (Real.exp_pos _).trans_le hy
  have hlogy : 2 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hy
  have hBy : 0 ≤ B y := Real.log_nonneg (by linarith)
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hh := nested_prime_pair_tail (show 0 ≤ C*B y/Real.log T by positivity)
    (fun b hb hby Q hQ => hbound y hy b hb hby Q T hT hQ) E a b hb hby hE
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
