import OAI.Combinatorics.SquareDifference.SelectedRoots

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section LowPair

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma interval_low_pair (hinj : Function.Injective (extendedPrime ps p)) (hp2 : ∀j,p j≠2)
    (B : Finset J) (a b L N Q H : ℕ) (hN : 1≤N) (hH : 1≤H) (hab : a+L≤b)
    (hHQ : H*(∏j∈B,p j)≤Q)
    (hD : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t)
    (z w : ResidueSpace p) (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j)) :
    ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H),
      residueFourier (OutsideModulus p B)
        (fun x => (intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (assembleOutside p B z x):ℂ)) (-ξ)*
      residueFourier (OutsideModulus p B)
        (fun x => (intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (assembleOutside p B w x):ℂ)) ξ*
      squareMultiplier (OutsideModulus p B) ξ‖≤
      ((N:ℝ)/L)^2*(smallModulus ps)*(∏j∈B,p j:ℝ)*
        (kernelAbsoluteConstant*(H:ℝ)^(-(1:ℝ)/3)) := by
  classical
  obtain ⟨c,hc,hr⟩ := selectedRoot_witnesses ps p hp2 B s t hst z w hzw
  let q := 2*N+1
  have hq : 2*N<q := by dsimp [q]; omega
  have : NeZero q := ⟨by omega⟩
  let F : ZMod q → ℂ := fun x => (selectedIndicator p (smallModulus ps) a L A s B z x.val:ℂ)
  let G : ZMod q → ℂ := fun x => (selectedIndicator p (smallModulus ps) b L A t B w x.val:ℂ)
  have hF := selectedIndicator_norm p (smallModulus ps) a L N A hA s B z q (by omega)
  have hG := selectedIndicator_norm p (smallModulus ps) b L N A hA t B w q (by omega)
  have hs (x : ZMod q) (hx : F x≠0) := selectedIndicator_mem p (smallModulus ps) a L A s B z x.val (by change ((selectedIndicator p (smallModulus ps) a L A s B z x.val:ℝ):ℂ)≠0 at hx; exact_mod_cast hx)
  have ht (x : ZMod q) (hx : G x≠0) := selectedIndicator_mem p (smallModulus ps) b L A t B w x.val (by change ((selectedIndicator p (smallModulus ps) b L A t B w x.val:ℝ):ℂ)≠0 at hx; exact_mod_cast hx)
  have hco (a : ℕ) (s : ZMod (smallModulus ps)) (z : ResidueSpace p)
      (ξ : ResidueSpace (OutsideModulus p B)) (hξ : (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H) :=
    actual_interval_outside_coefficient p (smallModulus ps) a L N Q H (by omega) A hA s B hHQ z q (by omega) ξ (by exact_mod_cast hξ)
  have hk := extended_kernel_low_pair ps p hinj hp2 B c H (by exact_mod_cast hH) N hN
    hD hHn hlarge hcover hc (by omega : N<q) F G hF hG
    (selectedIndicator_order p (smallModulus ps) a b L N hab A hA s t B z w)
    (selectedIndicator_square p (smallModulus ps) a b L N A hA hfree s t B z w hq)
    (selectedRootLabels ps p s z) (selectedRootLabels ps p t w) hr
    (fun x hx => selectedRootLabels_nat ps p hp2 B s z x.val (hs x hx).2.2.1 (hs x hx).2.2.2)
    (fun x hx => selectedRootLabels_nat ps p hp2 B t w x.val (ht x hx).2.2.1 (ht x hx).2.2.2)
    (fun x => (intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (assembleOutside p B z x):ℂ))
    (fun x => (intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (assembleOutside p B w x):ℂ))
    ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ)) ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ))
    (by positivity) (by positivity)
    (by intro ξ hξ; simpa only [F,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast] using hco a s z ξ hξ)
    (by intro ξ hξ; simpa only [G,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast] using hco b t w ξ hξ)
  have hM : (smallModulus ps:ℝ)≠0 := by
    unfold smallModulus
    exact_mod_cast (prod_ne_zero_iff.mpr (fun i _ => (NeZero.ne (smallQuadraticModulus (ps i)))))
  have hB : (∏j∈B,p j:ℝ)≠0 := by
    apply prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (Fact.out : (p j).Prime).ne_zero
  convert hk using 1
  change _= ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ))*
    ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ))/((smallModulus ps:ℝ)*(∏j∈B,p j:ℕ))*_
  push_cast
  field_simp

end LowPair

section PairTail

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma frozen_pair_tail (hp : ∀j,64≤p j) (B : Finset J) (F G : ResidueSpace p → ℝ)
    (R : ℝ) (hF : (𝔼 x,F x^2)≤R^2) (hG : (𝔼 x,G x^2)≤R^2)
    (z w : ResidueSpace p) (H : ℝ) (hH : 0<H) :
    ‖∑ξ∈univ.filter (fun ξ => H<(supportDenominator (OutsideModulus p B) ξ:ℝ)),
      residueFourier (OutsideModulus p B) (fun x => (F (assembleOutside p B z x):ℂ)) (-ξ)*
      residueFourier (OutsideModulus p B) (fun x => (G (assembleOutside p B w x):ℂ)) ξ*
      squareMultiplier (OutsideModulus p B) ξ‖≤ H^(-(1:ℝ)/3)*(∏j∈B,p j:ℝ)*R^2 := by
  let m := OutsideModulus p B
  have hf := outside_fiber_second_moment p B F z
  have hg := outside_fiber_second_moment p B G w
  have hB : 0≤(∏j∈B,p j:ℝ) := prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hfs : (𝔼 x,F (assembleOutside p B z x)^2)≤(∏j∈B,p j:ℝ)*R^2 := hf.trans (mul_le_mul_of_nonneg_left hF hB)
  have hgs : (𝔼 x,G (assembleOutside p B w x)^2)≤(∏j∈B,p j:ℝ)*R^2 := hg.trans (mul_le_mul_of_nonneg_left hG hB)
  have hk := squarePair_tail_bound m (fun j => hp j.val) (fun x => (F (assembleOutside p B z x):ℂ))
    (fun x => (G (assembleOutside p B w x):ℂ)) H hH
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs] at hk
  have hh : H^(-(2:ℝ)/3)=(H^(-(1:ℝ)/3))^2 := by
    rw [←Real.rpow_mul_natCast hH.le]; congr 1 ; norm_num
  rw [hh] at hk
  have hb0 : 0≤ H^(-(1:ℝ)/3)*(∏j∈B,p j:ℝ)*R^2 := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hb0).mp
  calc
    _ ≤ _ := hk
    _ ≤ (H^(-(1:ℝ)/3))^2*((∏j∈B,p j:ℝ)*R^2)*((∏j∈B,p j:ℝ)*R^2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hfs (sq_nonneg _)
      · exact hgs
      · exact expect_nonneg (fun _ _ => sq_nonneg _)
      · positivity
    _ = _ := by ring

lemma squarePair_split_bound (F G : ResidueSpace p → ℂ) (H e₁ e₂ : ℝ)
    (hlo : ‖∑a∈univ.filter (fun a => (supportDenominator p a:ℝ)≤H),residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖≤e₁)
    (hhi : ‖∑a∈univ.filter (fun a => H<(supportDenominator p a:ℝ)),residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖≤e₂) :
    ‖squarePairForm p F G‖≤e₁+e₂ := by
  rw [squarePairForm_fourier]
  have he := sum_filter_add_sum_filter_not univ (fun a : ResidueSpace p => (supportDenominator p a:ℝ)≤H)
    (fun a => residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a)
  simp only [not_le] at he
  rw [←he]
  exact (norm_add_le _ _).trans (add_le_add hlo hhi)

end PairTail

end SquareDifference

end

end OAI
