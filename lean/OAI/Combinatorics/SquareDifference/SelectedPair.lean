import OAI.Combinatorics.SquareDifference.IntervalTruncation

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

lemma complex_scaled_bound {D a b E : ℝ} (hD : 0 < D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (S : ℂ) (h : ‖(D:ℂ)*S‖ ≤ E) :
    ‖(a:ℂ)*(b:ℂ)*S‖ ≤ a*b/D*E := by
  have he : (a:ℂ)*(b:ℂ)*S=((a*b/D:ℝ):ℂ)*((D:ℂ)*S) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hD.ne']
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (mul_nonneg ha hb) hD.le)]
  exact mul_le_mul_of_nonneg_left h (div_nonneg (mul_nonneg ha hb) hD.le)

lemma squarePair_bound_from_low {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime] (hp : ∀j,64 ≤ p j)
    (F G : ResidueSpace p → ℂ) (H M₁ M₂ E : ℝ) (hH : 0 < H)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hF : (𝔼 x,‖F x‖^2) ≤ M₁^2) (hG : (𝔼 x,‖G x‖^2) ≤ M₂^2)
    (hlow : ‖∑a∈univ.filter (fun a => (supportDenominator p a:ℝ) ≤ H),
      residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖ ≤ E) :
    ‖squarePairForm p F G‖ ≤ E+H^(-(1:ℝ)/3)*M₁*M₂ := by
  have ht := squarePair_tail_bound p hp F G H hH
  have hd : 0 ≤ H^(-(1:ℝ)/3) := Real.rpow_nonneg hH.le _
  have he : H^(-(2:ℝ)/3)=(H^(-(1:ℝ)/3))^2 := by
    rw [←Real.rpow_mul_natCast hH.le]
    congr 1 ; norm_num
  rw [he,mul_assoc] at ht
  have ht' := ht.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hF hG (expect_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _))
  have hb : ‖∑a∈univ.filter (fun a => H < (supportDenominator p a:ℝ)),
      residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖ ≤ H^(-(1:ℝ)/3)*M₁*M₂ := by
    have hh : (H^(-(1:ℝ)/3))^2*(M₁^2*M₂^2)=(H^(-(1:ℝ)/3)*M₁*M₂)^2 := by ring
    rw [hh] at ht'
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hd hM₁) hM₂)).mp ht'
  rw [squarePairForm_fourier]
  have hs := sum_filter_add_sum_filter_not (s:=univ)
    (p:=fun a : ResidueSpace p => (supportDenominator p a:ℝ) ≤ H)
    (f:=fun a => residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a)
  simp only [not_le] at hs
  rw [←hs]
  exact (norm_add_le _ _).trans (add_le_add hlow hb)

section KernelPair

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)
  (R : Finset I) (c : ∀i,ZMod (p i))

include hinj in
lemma actual_kernel_low_pair
    (H : ℝ) (hH : 1 ≤ H) (N : ℕ) (hN : 1 ≤ N)
    (hD : (rootSquareModulus p R:ℝ) ≤ (N:ℝ)^((1:ℝ)/1000))
    (hHn : H ≤ (N:ℝ)^((1:ℝ)/1000)) (hlarge : 8 ≤ (N:ℝ)^((1:ℝ)/16))
    (hcover : ∀b : ℚ,(b.den:ℝ) ≤ (N:ℝ)^((1:ℝ)/8) →
      b.den∣∏i,primaryModulus b.den (p i))
    (hcover' : ∀b : ℚ,b.den ≤ ⌈(rootSquareModulus p R:ℝ)*H⌉₊ →
      b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (hq : N < q) (F G : ZMod q → ℂ)
    (hF : (∑x,‖F x‖^2) ≤ N) (hG : (∑x,‖G x‖^2) ≤ N)
    (hord : ∀x y,F x*G y≠0 → x.val < y.val ∧ y.val ≤ N)
    (hsquare : ∀x y m,m∈range N.sqrt → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0)
    (s t : ∀i,ZMod (smallQuadraticModulus (p i)))
    (hr : ∀i∈R,smallRootSquare (p i) (c i)=t i-s i)
    (hs : ∀z,F z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=s i)
    (ht : ∀z,G z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=t i)
    (f g : ResidueSpace (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) → ℂ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ξ,(supportDenominator (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) ξ:ℝ) ≤ H →
      residueFourier _ f ξ=(a:ℂ)*sequenceResidueFourier _ N F ZMod.val ξ)
    (hg : ∀ξ,(supportDenominator (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) ξ:ℝ) ≤ H →
      residueFourier _ g ξ=(b:ℂ)*sequenceResidueFourier _ N G ZMod.val ξ) :
    ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) ξ:ℝ) ≤ H),
      residueFourier _ f (-ξ)*residueFourier _ g ξ*squareMultiplier _ ξ‖ ≤
      a*b/(rootSquareModulus p R:ℝ)*(kernelAbsoluteConstant*H^(-(1:ℝ)/3)) := by
  let m := OutsideModulus (fun i => smallQuadraticModulus (p i)) R
  have hk := actual_kernel_ordered_bilinear p R c hinj H hH N hN hD hHn hlarge hcover htwo hc hq F G hF hG hord hsquare
  rw [modelBilinear_root p hinj R c H _ N (Nat.le_ceil _) hcover' htwo hc F G s t hr hs ht] at hk
  have hd : (∏i∈R,smallQuadraticModulus (p i))=rootSquareModulus p R := rfl
  rw [hd] at hk
  let S : ℂ := ∑ξ : ResidueSpace m,(if (supportDenominator m ξ:ℝ) ≤ H then squareMultiplier m ξ else 0)*
    sequenceResidueFourier m N F ZMod.val (-ξ)*sequenceResidueFourier m N G ZMod.val ξ
  have hscaled := complex_scaled_bound (Nat.cast_pos.mpr (rootSquareModulus_pos p R)) ha hb S hk
  apply le_trans (le_of_eq ?_) hscaled
  congr 1
  change (∑ξ∈univ.filter (fun ξ : ResidueSpace m => (supportDenominator m ξ:ℝ) ≤ H),
    residueFourier m f (-ξ)*residueFourier m g ξ*squareMultiplier m ξ)=(a:ℂ)*(b:ℂ)*S
  dsimp only [S]
  simp only [mul_sum,ite_mul,mul_ite,zero_mul,mul_zero]
  rw [←sum_filter]
  apply sum_congr rfl
  intro ξ hξ
  have hξ' := (mem_filter.mp hξ).2
  have hneg : supportDenominator m (-ξ)=supportDenominator m ξ := by
    unfold supportDenominator primeSupport
    congr 1
    ext j
    simp only [mem_filter,mem_univ,true_and,Pi.neg_apply,neg_ne_zero]
  rw [hf (-ξ) (by rwa [hneg]),hg ξ hξ']
  ring

end KernelPair

end SquareDifference

end

end OAI
