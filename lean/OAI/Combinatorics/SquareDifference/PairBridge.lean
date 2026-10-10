import OAI.Combinatorics.SquareDifference.RootModels

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

namespace PairBridge

open LiftTheory.SquareDifference

section Fourier

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [instNeZeropj : ∀j,NeZero (p j)]

lemma actualLiftPiece_eq {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) :
    actualLiftPiece p L f U x=liftPiece p L f U x := rfl

lemma actualSupportFamily_eq {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (Q : ℕ) :
    liftSupportFamily p Q=univ.filter (fun U : Finset J => ∏j∈U,p j≤Q) := rfl

noncomputable def sequenceCoeff (L : ℕ) (f : ℕ → ℝ) (a : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹*∑n∈range L,(f n:ℂ)*conj (prodChar p a (fun j => (n:ZMod (p j))))

lemma gateCoefficient_empty (L : ℕ) (f : ℕ → ℝ) (z a : ResidueSpace p) :
    gateCoefficient p L (fun n => (f n:ℂ)) ∅ z a=sequenceCoeff p L f a := by
  simp only [gateCoefficient,exactGate,prod_empty,Complex.ofReal_one,mul_one,
    sequenceCoeff,prodChar_nat_diagonal,neg_mul,LiftTheory.SquareDifference.expPhase_neg]

lemma actualPiece_polynomial (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    (fun x => (actualLiftPiece p L f U x:ℂ))=
      fourierPolynomial p (fun a => if primeSupport p a=U then sequenceCoeff p L f a else 0) := by
  funext x
  have h := LiftTheory.SquareDifference.liftPiece_freeze_fourier p L f U ∅ (0:ResidueSpace p) x
  have hc : LiftTheory.SquareDifference.coordinateFreeze p ∅ (0:ResidueSpace p) x=x := by
    funext j
    simp only [LiftTheory.SquareDifference.coordinateFreeze,notMem_empty,ite_false]
  rw [hc] at h
  simpa only [sdiff_empty,inter_empty,gateCoefficient_empty,actualLiftPiece_eq] using h

lemma polynomial_sum {T : Type*} (s : Finset T) (c : T → ResidueSpace p → ℂ) :
    (fun x => ∑t∈s,fourierPolynomial p (c t) x)=
      fourierPolynomial p (fun a => ∑t∈s,c t a) := by
  funext x
  simp only [fourierPolynomial,sum_mul]
  rw [sum_comm]

lemma actualLift_polynomial (L Q : ℕ) (f : ℕ → ℝ) :
    (fun x => (actualTruncatedLift p L Q f x:ℂ))=
      fourierPolynomial p (fun a => if supportDenominator p a≤Q then sequenceCoeff p L f a else 0) := by
  change (fun x => (((∑U∈liftSupportFamily p Q,actualLiftPiece p L f U x):ℝ):ℂ))=_
  simp only [Complex.ofReal_sum]
  have he (U : Finset J) (x : ResidueSpace p) := congrFun (actualPiece_polynomial p L f U) x
  simp_rw [he]
  rw [polynomial_sum]
  congr 1
  funext a
  simp only [actualSupportFamily_eq,sum_filter]
  rw [sum_eq_single (primeSupport p a)]
  · simp only [ite_true,LiftTheory.SquareDifference.supportDenominator]
    rfl
  · intro U _ hU
    by_cases h : ∏j∈U,p j≤Q
    · simp only [h,ite_true,Ne.symm hU,ite_false]
    · simp only [h,ite_false]
  · simp

lemma actualLift_fourier (L Q : ℕ) (f : ℕ → ℝ) (a : ResidueSpace p) :
    residueFourier p (fun x => (actualTruncatedLift p L Q f x:ℂ)) a=
      if supportDenominator p a≤Q then sequenceCoeff p L f a else 0 := by
  rw [actualLift_polynomial,residueFourier_polynomial]

lemma sequenceCoeff_bound {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (L : ℕ) (hL : 0<L) (f : ℕ → ℝ) (M : ℝ)
    (hf : ∀n<L,|f n|≤M) (a : ResidueSpace p) : ‖sequenceCoeff p L f a‖≤M := by
  rw [sequenceCoeff,norm_mul,norm_inv,Complex.norm_natCast]
  have hM : 0≤M := (abs_nonneg (f 0)).trans (hf 0 hL)
  have hs : ‖∑n∈range L,(f n:ℂ)*conj (prodChar p a (fun j => (n:ZMod (p j))))‖≤L*M := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n∈range L,M := by
        apply sum_le_sum
        intro n hn
        simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_conj,norm_prodChar,mul_one] using hf n (mem_range.mp hn)
      _ = _ := by simp
  have hL0 : (L:ℝ)≠0 := by exact_mod_cast hL.ne'
  calc
    _ ≤ (L:ℝ)⁻¹*(L*M) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg L))
    _ = M := by field_simp

lemma actualLift_pointwise_bound (hp : Pairwise fun i j => (p i).Coprime (p j))
    (L Q : ℕ) (hL : 0<L) (f : ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀n<L,|f n|≤M) (x : ResidueSpace p) :
    |actualTruncatedLift p L Q f x|≤(Q:ℝ)^2*M := by
  have h := congrFun (actualLift_polynomial p L Q f) x
  have hh : ‖fourierPolynomial p (fun a => if supportDenominator p a≤Q then sequenceCoeff p L f a else 0) x‖≤(Q:ℝ)^2*M := by
    unfold fourierPolynomial
    simp only [ite_mul,zero_mul]
    rw [←sum_filter]
    calc
      _ ≤ ∑a∈univ.filter (fun a => supportDenominator p a≤Q),‖sequenceCoeff p L f a*prodChar p a x‖ := norm_sum_le _ _
      _ ≤ ∑a∈univ.filter (fun a => supportDenominator p a≤Q),M := by
        apply sum_le_sum
        intro a _
        simpa only [norm_mul,norm_prodChar,mul_one] using sequenceCoeff_bound p L hL f M hf a
      _ = ((univ.filter (fun a => supportDenominator p a≤Q)).card:ℝ)*M := by simp
      _ ≤ (Q:ℝ)^2*M := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact_mod_cast bounded_frequency_card p hp Q _ (fun a ha => (mem_filter.mp ha).2)
  rw [←h,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

lemma actualLift_mean (L Q : ℕ) (hQ : 1≤Q) (f : ℕ → ℝ) :
    (𝔼 x,actualTruncatedLift p L Q f x)=(L:ℝ)⁻¹*∑n∈range L,f n := by
  have h := actualLift_fourier p L Q f (0:ResidueSpace p)
  have hc (x : ResidueSpace p) : prodChar p (0:ResidueSpace p) x=1 := by
    simp only [prodChar,Pi.zero_apply,zero_mul,AddChar.map_zero_eq_one,prod_const_one]
  have hd : supportDenominator p (0:ResidueSpace p)=1 := by
    simp only [supportDenominator,primeSupport,Pi.zero_apply,ne_eq,not_true_eq_false,filter_false,prod_empty]
  simp only [residueFourier,hc,map_one,mul_one,hd,ite_eq_left hQ,sequenceCoeff] at h
  apply Complex.ofReal_injective
  simpa only [expect_eq_sum_div_card,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast,
    Complex.ofReal_mul,Complex.ofReal_inv] using h

lemma actualFamily_polynomial (L : ℕ) (f : ℕ → ℝ) (F : Finset (Finset J)) :
    (fun x => ((∑U∈F,actualLiftPiece p L f U x:ℝ):ℂ))=
      fourierPolynomial p (fun a => if primeSupport p a∈F then sequenceCoeff p L f a else 0) := by
  simp only [Complex.ofReal_sum]
  have he (U : Finset J) (x : ResidueSpace p) := congrFun (actualPiece_polynomial p L f U) x
  simp_rw [he]
  rw [polynomial_sum]
  congr 1
  funext a
  by_cases ha : primeSupport p a∈F
  · rw [ite_eq_left ha,sum_eq_single (primeSupport p a)]
    · simp
    · intro U _ hU
      exact ite_eq_right (Ne.symm hU)
    · exact fun h => (h ha).elim
  · rw [ite_eq_right ha]
    apply sum_eq_zero
    intro U hU
    exact ite_eq_right (fun (he : primeSupport p a=U) => ha (he.symm ▸ hU))

lemma actualFamily_fourier (L : ℕ) (f : ℕ → ℝ) (F : Finset (Finset J)) (a : ResidueSpace p) :
    residueFourier p (fun x => ((∑U∈F,actualLiftPiece p L f U x:ℝ):ℂ)) a=
      if primeSupport p a∈F then sequenceCoeff p L f a else 0 := by
  rw [actualFamily_polynomial,residueFourier_polynomial]

lemma frozenFamily_fourier (L : ℕ) (f : ℕ → ℝ) (F : Finset (Finset J))
    (B : Finset J) (z a : ResidueSpace p) :
    residueFourier p (fun x => ((∑U∈F,actualLiftPiece p L f U (freezeCoordinates B z x):ℝ):ℂ)) a=
      ∑U∈F,if primeSupport p a=U\B then gateCoefficient p L (fun n => (f n:ℂ)) (U∩B) z a else 0 := by
  have he (U : Finset J) (x : ResidueSpace p) :
      (actualLiftPiece p L f U (freezeCoordinates B z x):ℂ)=
        fourierPolynomial p (fun a => if primeSupport p a=U\B then
          gateCoefficient p L (fun n => (f n:ℂ)) (U∩B) z a else 0) x :=
    liftPiece_freeze_fourier p L f U B z x
  simp_rw [Complex.ofReal_sum,he]
  rw [polynomial_sum,residueFourier_polynomial]

lemma frozen_lift_low_fourier (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (z a : ResidueSpace p) (ha : supportDenominator p a≤H) :
    residueFourier p (fun x => (actualTruncatedLift p L Q f (freezeCoordinates B z x):ℂ)) a=
      residueFourier p (fun x => ((∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
        actualLiftPiece p L f U (freezeCoordinates B z x):ℝ):ℂ)) a := by
  change residueFourier p (fun x => ((∑U∈liftSupportFamily p Q,
    actualLiftPiece p L f U (freezeCoordinates B z x):ℝ):ℂ)) a=_
  rw [frozenFamily_fourier,frozenFamily_fourier,sum_filter]
  apply sum_congr rfl
  intro U hU
  by_cases he : primeSupport p a=U\B
  · have hUH : ∏j∈U\B,p j≤H := by
      simpa only [supportDenominator,he] using ha
    simp only [he,hUH,ite_true]
  · simp only [he,ite_false,ite_self]

noncomputable def gatedSequence (B : Finset J) (z : ResidueSpace p) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏j∈B,p j:ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then f n else 0)

lemma frozen_low_lift_gated (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z x : ResidueSpace p) :
    (∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
      actualLiftPiece p L f U (freezeCoordinates B z x))=
      ∑U∈actualRemainingFamily p B H,actualLiftPiece p L (gatedSequence p B z f) U x := by
  change (∑U∈(LiftAnalysis.SquareDifference.supportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
    LiftAnalysis.SquareDifference.liftPiece p L f U (LiftAnalysis.SquareDifference.coordinateFreeze p B z x))=_
  rw [LiftAnalysis.SquareDifference.frozen_low_lift_identity p L Q H f B hHQ z x]
  simp only [actualLiftPiece,LiftAnalysis.SquareDifference.liftPiece,gatedSequence,mul_sum,div_eq_mul_inv]
  apply sum_congr rfl
  intro U hU
  apply sum_congr rfl
  intro n hn
  split_ifs <;> ring

lemma frozen_lift_fiber_fourier (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z a : ResidueSpace p)
    (ha : supportDenominator p a≤H) (hB : Disjoint (primeSupport p a) B) :
    residueFourier p (fun x => (actualTruncatedLift p L Q f (freezeCoordinates B z x):ℂ)) a=
      sequenceCoeff p L (gatedSequence p B z f) a := by
  rw [frozen_lift_low_fourier p L Q H f B z a ha]
  simp_rw [frozen_low_lift_gated p L Q H f B hHQ z]
  rw [actualFamily_fourier,ite_eq_left]
  exact mem_filter.mpr ⟨mem_univ _,hB,ha⟩

end Fourier

end PairBridge

end SquareDifference

end

end OAI
