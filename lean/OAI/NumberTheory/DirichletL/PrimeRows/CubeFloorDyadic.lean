import OAI.NumberTheory.DirichletL.PrimeRows.SmallPartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma bounded_dyadic_power_sum (p : ℝ) (hp : 0<p) :
    ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^p)≤C*H^p := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound p (p+1) hp (by linarith)
  refine ⟨(2:ℝ)^(p+1)*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^p≤(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^(p+1)≤(2:ℝ)^(p+1) :=
      Real.rpow_le_rpow hd.le (by linarith) (by linarith)
    unfold CompletedDyadic.kernelTerm
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh
      (Real.rpow_nonneg (show (0:ℝ)≤(2:ℝ)^n by positivity) p)
  calc
    _ ≤ ∑n∈F,(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := Finset.sum_le_sum hpoint
    _ = (2:ℝ)^(p+1)*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := (Finset.mul_sum _ _ _).symm
    _ ≤ (2:ℝ)^(p+1)*∑'n,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by positivity)
    _ ≤ (2:ℝ)^(p+1)*(C*(H⁻¹)^(-p)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

lemma retained_dyadic_partition (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) :
    (smallDyadicIndices H).biUnion (fun n=>rows∩dyadicRows 1 n)=rows := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_inter.mp hu).1
  · intro hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u (hrows u hu).1 (rowNorm_ge_one u)
    refine Finset.mem_biUnion.mpr ⟨n,?_,Finset.mem_inter.mpr ⟨hu,hn⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans (hrows u hu).2

lemma retained_dyadic_sum {A : Type*} [AddCommMonoid A] (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) (f : FreeRow→A) :
    (∑u∈rows,f u)=∑n∈smallDyadicIndices H,∑u∈rows∩dyadicRows 1 n,f u := by
  conv_lhs => rw [←retained_dyadic_partition rows H hrows]
  apply Finset.sum_biUnion
  intro m hm n hn hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.inter_subset_right) (Finset.inter_subset_right)

lemma bounded_freeRow_power_sum (p : ℝ) (hp : -1<p) :
    ∃C : ℝ,0<C ∧ ∀(rows : Finset FreeRow) (H : ℝ),0<H →
      (∀u∈rows,u.val≠1 ∧ rowNorm u≤H) →
      (∑u∈rows,rowNorm u^p)≤C*H^(1+p) := by
  obtain ⟨C,hC,hpow⟩ := bounded_dyadic_power_sum (1+p) (by linarith)
  let A := ProbeSelectedPrimeSums.annularPower 1 2 p
  have hA : 0≤A := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 p (by norm_num)
  refine ⟨256*(A+1)*C,by positivity,?_⟩
  intro rows H hH hrows
  rw [retained_dyadic_sum rows H hrows]
  have hdyad (n : ℕ) : (∑u∈rows∩dyadicRows 1 n,rowNorm u^p)≤256*(A+1)*((2:ℝ)^n)^(1+p) := by
    have hn : ∀u∈rows∩dyadicRows 1 n,(2:ℝ)^n≤rowNorm u ∧ rowNorm u≤2*(2:ℝ)^n := by
      intro u hu
      have hh := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [one_mul] using And.intro hh.1 hh.2.le
    have hb := dyadic_weighted_rows p 0 1 ((2:ℝ)^n) (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
      (rows∩dyadicRows 1 n) hn (fun u=>rowNorm u^p) (fun u hu=>by simp [rowNorm]) (0:ℂ) rfl
    simp only [frequencyWeight_ideal_norm,Complex.zero_re,neg_zero,Real.rpow_zero,one_mul,sub_zero] at hb
    exact hb.trans (by change 256*1*A*_≤_;gcongr <;> linarith)
  calc
    _ ≤ ∑n∈smallDyadicIndices H,256*(A+1)*((2:ℝ)^n)^(1+p) := Finset.sum_le_sum (fun n _=>hdyad n)
    _ = 256*(A+1)*∑n∈smallDyadicIndices H,((2:ℝ)^n)^(1+p) := (Finset.mul_sum _ _ _).symm
    _ ≤ 256*(A+1)*(C*H^(1+p)) :=
      mul_le_mul_of_nonneg_left (hpow H hH (smallDyadicIndices H) (fun n hn=>mem_smallDyadicIndices.mp hn)) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
