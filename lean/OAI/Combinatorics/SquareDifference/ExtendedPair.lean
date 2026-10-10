import OAI.Combinatorics.SquareDifference.PrimeExtension

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma coefficient_reindex {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (p : J → ℕ) (m : K → ℕ) [∀j,NeZero (p j)] [∀k,NeZero (m k)]
    (e : K ≃ J) (hm : m=fun k => p (e k)) {Ω : Type*} [Fintype Ω]
    (N : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (f : ResidueSpace p → ℂ) (a : ℝ) (H : ℝ)
    (hf : ∀ξ,(supportDenominator p ξ:ℝ)≤H →
      residueFourier p f ξ=(a:ℂ)*sequenceResidueFourier p N F n ξ) :
    ∀ξ,(supportDenominator m ξ:ℝ)≤H →
      residueFourier m (fun x => f ((residueReindex p m e hm).symm x)) ξ=
        (a:ℂ)*sequenceResidueFourier m N F n ξ := by
  intro ξ hξ
  obtain ⟨η,rfl⟩ := (residueReindex p m e hm).surjective ξ
  rw [supportDenominator_reindex] at hξ
  rw [residueFourier_reindex,sequenceResidueFourier_reindex]
  exact hf η hξ

lemma kernel_cover_from_bound {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (hinj : Function.Injective p) (N : ℕ) (hN : 1≤N)
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,p i=r) :
    ∀b : ℚ,(b.den:ℝ)≤(N:ℝ)^((1:ℝ)/8) → b.den∣∏i,primaryModulus b.den (p i) := by
  intro b hb
  apply primary_product_cover p hinj N hcover b.den b.den_pos
  have hh : (b.den:ℝ)≤N := hb.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ)≤N) (show (1:ℝ)/8≤1 by norm_num))
  exact_mod_cast hh

lemma kernel_cover_cutoff {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (hinj : Function.Injective p) (N : ℕ) (hN : 1≤N)
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,p i=r)
    (D H : ℝ) (hH : 0≤H) (hD : D≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) :
    ∀b : ℚ,b.den≤⌈D*H⌉₊ → b.den∣∏i,primaryModulus b.den (p i) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hh : D*H≤N := by
    calc
      _ ≤ (N:ℝ)^((1:ℝ)/1000)*(N:ℝ)^((1:ℝ)/1000) := mul_le_mul hD hHn hH (by positivity)
      _ = (N:ℝ)^((1:ℝ)/1000+1/1000) := (Real.rpow_add hn _ _).symm
      _ ≤ N := by
        have h := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ)≤N)
          (show (1:ℝ)/1000+1/1000≤1 by norm_num)
        simpa only [Real.rpow_one] using h
  intro b hb
  exact primary_product_cover p hinj N hcover b.den b.den_pos (hb.trans (Nat.ceil_le.mpr hh))

section Extended

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime]

lemma extended_kernel_low_pair (hinj : Function.Injective (extendedPrime ps p)) (hp2 : ∀j,p j≠2)
    (B : Finset J) (c : ∀i,ZMod (extendedPrime ps p i))
    (H : ℝ) (hH : 1≤H) (N : ℕ) (hN : 1≤N)
    (hD : ((∏s,smallQuadraticModulus (ps s))*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (hc : ∀i∈extendedRoots (S:=S) B,if extendedPrime ps p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (hq : N<q) (F G : ZMod q → ℂ)
    (hF : (∑x,‖F x‖^2)≤N) (hG : (∑x,‖G x‖^2)≤N)
    (hord : ∀x y,F x*G y≠0 → x.val<y.val ∧ y.val≤N)
    (hsquare : ∀x y m,m∈range N.sqrt → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0)
    (s t : ∀i,ZMod (smallQuadraticModulus (extendedPrime ps p i)))
    (hr : ∀i∈extendedRoots (S:=S) B,smallRootSquare (extendedPrime ps p i) (c i)=t i-s i)
    (hs : ∀z,F z≠0 → ∀i∈extendedRoots (S:=S) B,(z.val:ZMod (smallQuadraticModulus (extendedPrime ps p i)))=s i)
    (ht : ∀z,G z≠0 → ∀i∈extendedRoots (S:=S) B,(z.val:ZMod (smallQuadraticModulus (extendedPrime ps p i)))=t i)
    (f g : ResidueSpace (OutsideModulus p B) → ℂ) (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hf : ∀ξ,(supportDenominator (OutsideModulus p B) ξ:ℝ)≤H →
      residueFourier _ f ξ=(a:ℂ)*sequenceResidueFourier _ N F ZMod.val ξ)
    (hg : ∀ξ,(supportDenominator (OutsideModulus p B) ξ:ℝ)≤H →
      residueFourier _ g ξ=(b:ℂ)*sequenceResidueFourier _ N G ZMod.val ξ) :
    ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H),
      residueFourier _ f (-ξ)*residueFourier _ g ξ*squareMultiplier _ ξ‖≤
      a*b/((∏s,smallQuadraticModulus (ps s))*(∏j∈B,p j):ℝ)*
        (kernelAbsoluteConstant*H^(-(1:ℝ)/3)) := by
  let m := OutsideModulus (fun i => smallQuadraticModulus (extendedPrime ps p i)) (extendedRoots (S:=S) B)
  let e := outsideSumEquiv (S:=S) B
  have hm : m=fun i => OutsideModulus p B (e i) := extended_outside_modulus ps p B hp2
  let re := residueReindex (OutsideModulus p B) m e hm
  have hmod := extended_roots_modulus ps p B hp2
  have hD' : (rootSquareModulus (extendedPrime ps p) (extendedRoots (S:=S) B):ℝ)≤(N:ℝ)^((1:ℝ)/1000) := by
    simpa only [hmod,Nat.cast_mul,Nat.cast_prod] using hD
  have htwo : ∀i,extendedPrime ps p i=2 → i∈extendedRoots (S:=S) B := by
    intro i hi
    cases i with
    | inl s => exact inl_mem_extendedRoots B s
    | inr j => exact False.elim (hp2 j hi)
  have hk := actual_kernel_low_pair (extendedPrime ps p) hinj (extendedRoots (S:=S) B) c
    H hH N hN hD' hHn hlarge (kernel_cover_from_bound _ hinj N hN hcover)
    (kernel_cover_cutoff _ hinj N hN hcover _ H (by linarith) hD' hHn)
    htwo hc hq F G hF hG hord hsquare s t hr hs ht
    (fun x => f (re.symm x)) (fun x => g (re.symm x)) a b ha hb
    (coefficient_reindex _ m e hm N F ZMod.val f a H hf)
    (coefficient_reindex _ m e hm N G ZMod.val g b H hg)
  rw [low_pair_reindex _ m e hm f g H] at hk
  simpa only [hmod,Nat.cast_mul,Nat.cast_prod] using hk

end Extended

end SquareDifference

end

end OAI
