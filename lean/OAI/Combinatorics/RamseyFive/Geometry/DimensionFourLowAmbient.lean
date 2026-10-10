import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PowerValidation
import OAI.Combinatorics.RamseyFive.Geometry.Peeling
import OAI.Combinatorics.RamseyFive.Geometry.PlaneStrongExceptions
import OAI.Combinatorics.RamseyFive.Probability.DimensionFourStrong

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_four_low_ambient_tail {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (O : ℙ K V→Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
      (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (t : ℝ),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      O x=C a∪C b → (S.card:ℝ) ≤ 10*Real.exp (5*σ/2) →
      (S.card:ℝ) ≤ (Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) →
      (x∉badCenters S O (pointStrength S) ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 ∨
        (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P η σ D R)) →
      scale (K:=K) 4 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have ht := eventually_low_original_tail hη hη' Cb hCb
  have hd := eventually_dyad_power_payment hη hη'
  have hc := eventually_power_absorption hη hη' (11*2^200) 0 (1/200)
    (by positivity) (by norm_num) (by norm_num)
  have hs := eventually_four_ambient_degree hη hη'
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hd,hc,hs] with σ hσ ht hd hc hs
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c O F Lines Q t
    hdim hq hr hL hb₀ hbhi hτ hS ha hb hC hO hSn hLow hn hf hF hx hLines hxQ hgood hstrong ht₀
  have hS0 : (0:ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hδ : 0 < pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength]
    exact div_pos (by exact_mod_cast Nat.card_pos (α:=K)) hS0
  have hlarge : (11*2^200:ℝ) ≤ Real.exp (P η σ D R/200) := by
    simpa only [Real.rpow_zero,mul_one,one_div,div_eq_mul_inv,one_mul,mul_comm (200⁻¹:ℝ)] using hc D R hr
  have hcard : ((outsideAt x S (O x)).card:ℝ) ≤ Real.exp (3*σ) := by
    have he : (10:ℝ) ≤ Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr (outsideAt_card_le x S (O x))
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hm (H:F) : mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x F H) ≤ 2 := by
    rw [hO]
    exact (actual_radial_mass_bounds x S C hS a b c ha hb hC F hF hf hn H).2.2.trans (by norm_num)
  have hP0 : 0≤P η σ D R := by unfold P;rw [←hL];positivity
  have hmass : (pointStrength (K:=K) S:ℝ)*S.card≤Nat.card K := by
    rw [coe_pointStrength,div_mul_cancel₀ _ hS0.ne']
  have hlow : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp ((P η σ D R/200)/2) :=
    hLow.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hP0])) (sq_nonneg _))
  have hh := score_pair_low_moment x hdim S O (pointStrength S) hδ F
    (fun H hH => (hF H hH).1) S.card (P η σ D R/200) hS0 hmass hlow hlarge Lines hLines Q hxQ hm
    (off_radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) x hgood) 200 (le_refl _)
  have hpay := hd D R (P η σ D R/200) (outsideAt x S (O x)).card hr (le_refl _) hcard
  have hmoment : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200) ≤
        (scale (K:=K) 4 S.card)^2*Real.exp (P η σ D R/50) := by
    apply hh.trans
    change 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
      (((Nat.card K:ℝ)^4/S.card)^2*Real.exp (2*(P η σ D R/200))) ≤ _
    calc
      _ = ((Nat.card K:ℝ)^4/S.card)^2*(2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
          Real.exp (2*(P η σ D R/200))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
  have hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3 := by
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _≤10*Real.exp (5*σ/2) := hSn
      _≤Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _=_ := by rw [←Real.exp_add,hq,←Real.exp_nat_mul];congr 1;norm_num;ring
  have hchi : (10*2^200:ℝ)≤Real.exp (P η σ D R/100) := by
    have hh : Real.exp (P η σ D R/200)≤Real.exp (P η σ D R/100) := Real.exp_le_exp.mpr (by linarith only [hP0])
    linarith only [hlarge,hh]
  have hlow' : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (P η σ D R/100) :=
    hLow.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hP0])) (sq_nonneg _))
  apply ht 4 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
    ha hb hC (by convert hSn using 1; norm_num) hLow hn hf hF hx _ _ _ ht₀
  · intro u hu hu2
    have hh := power_tail_mul (fun z : DistinctPairs F => strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z) (strength_nonneg _ _) 200 u _ hu hmoment
    simp only [hO,strength] at hh
    convert hh using 1
    congr 2
  · intro H u hu hu2
    have hh := score_degree_low_normalized x hdim (outsideAt x S (O x)) (pointStrength S) hδ F
      (fun H hH => (hF H hH).1) H S.card u (P η σ D R/100) hS0 hu.le hu2 (hm H) hcap hlow' hchi
    simpa only [hO,show 2*(P η σ D R/100)=P η σ D R/50 by ring,scale] using hh
  · intro H
    have hh := hs D R K V x S O (pointStrength S) F Lines Q hdim hq hr hS hSn hδ
      (fun H hH => (hF H hH).1) hm hLines hxQ hstrong H
    simpa only [hO,scale] using hh

end

section
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_plane_half_ambient_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
      let Q := P η σ D R
      let a := (1/(100*(momentOrder σ Q:ℝ)))/2
      100000000≤Q/10000 ∧ Q/10000<σ/2-4*Q ∧
      20*Q≤σ/2-4*Q ∧ Real.exp (-Q)≤a ∧ a≤2 ∧ (1332096:ℝ)≤Real.exp Q := by
  have hh := eventually_hierarchy hη hη' 0 (1/100) 1000000000000 (by norm_num) (by norm_num)
  have ha := eventually_power_absorption hη hη' 2000400 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hc := eventually_power_absorption hη hη' 1332096 0 1 (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hh,ha,hc] with σ hσ hh ha hc
  intro D R hr
  have hh := hh D R 0 0 hr (by simp) (by positivity)
  have ha := ha D R hr
  have hc := hc D R hr
  dsimp only
  have hL : 0≤L η σ D := by linarith only [hh.1]
  have hLP : L η σ D≤P η σ D R := by linarith only [hh.2.2.2.2.2,hL]
  have hP : 1≤P η σ D R := by linarith only [hh.1,hLP]
  have hp := momentOrder_bounds hσ hP
  have hp0 : (0:ℝ)< momentOrder σ (P η σ D R) := Nat.cast_pos.mpr hp.2.1
  have hp1 : (1:ℝ)≤ momentOrder σ (P η σ D R) := by exact_mod_cast hp.2.1
  refine ⟨by linarith only [hh.1,hLP],by linarith only [hh.2.1,hP],by linarith only [hh.2.1,hP],?_,?_,?_⟩
  · rw [Real.exp_neg, ← one_div,div_div]
    apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ)*2)
    calc
      _≤100*(10002*σ)*2 := by gcongr;exact hp.2.2.2.2
      _=2000400*σ := by ring
      _≤_ := by simpa only [Real.rpow_one,one_mul] using ha
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ))).mpr
    linarith only [hp1]
  · simpa only [Real.rpow_zero,mul_one,one_mul] using hc
end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

noncomputable def ambientHalfStrongExceptions {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V]
    (σ P : ℝ) (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) : Finset (ℙ K V) :=
  if (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P) then ∅
  else badCenters S O (pointStrength S) ((1/(100*(momentOrder σ P:ℝ)))/2) Lines Q 1

lemma off_ambientHalfStrongExceptions {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V]
    (σ P : ℝ) (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (x : ℙ K V)
    (hx : x∉ambientHalfStrongExceptions σ P S O Lines Q) :
    x∉badCenters S O (pointStrength S) ((1/(100*(momentOrder σ P:ℝ)))/2) Lines Q 1 ∨
      (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P) := by
  by_cases h : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P)
  · exact Or.inr h
  · exact Or.inl (by simpa only [ambientHalfStrongExceptions,ite_eq_right h] using hx)

theorem eventually_literal_plane_half_exceptions {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
      (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
      2<q → Nat.card K=q → Real.exp σ=q → (Fintype.card I=4 ∨ Fintype.card I=5) →
      g≤2*σ → (∀j∈F,finrank K (Flat j)=3) →
      (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
      (X.card:ℝ)≤Real.exp (3*σ/2+g) →
      t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5) →
      S=peelSet (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
      Real.exp (3*σ/2+g)/4≤S.card → (S.card:ℝ)≤Real.exp (3*σ) →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
      (∀l∈Lines,finrank K l=2) →
      let O' := fun x => S∩O x
      ((radialExceptions S O' (pointStrength S) Lines Q q S.card (P η σ D R/200)).card:ℝ)≤
        (S.card:ℝ)*Real.exp (-L η σ D/1000)/2 ∧
      ((ambientHalfStrongExceptions σ (P η σ D R) S O' Lines Q).card:ℝ)≤
        (S.card:ℝ)*Real.exp (7*P η σ D R) := by
  have he := eventually_exception_payment_wide hη hη' 0 2664192 8 (by norm_num) (by norm_num) (by norm_num)
  have ha := eventually_plane_half_ambient_margins hη hη'
  filter_upwards [eventually_ge_atTop (1000:ℝ),he,ha] with σ hσ he ha
  intro D R hr q K I J _ _ _ _ _ _ g F hF Flat X S t ht0 O Lines Q hq hcard hσq hI
    hghi hFlat hcover hX ht hS hquarter hcardS hO hLines
  dsimp only
  let P := ParameterHierarchy.P η σ D R
  have ha := ha D R hr
  have hP : 0<P := by dsimp [P];linarith only [ha.1]
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hSn : (S.card:ℝ)≤Real.exp (3*σ/2+g) :=
    (Nat.cast_le.mpr (Finset.card_le_card (hS▸peel_subset (P/10000<g) F hF (fun j => flatPoints (Flat j)) X _ _))).trans hX
  have hδ : (pointStrength (K:=K) S:ℝ)=(q:ℝ)/S.card := by simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast,hcard]
  constructor
  · have hcount := literal_plane_radial_exceptions hq hcard hI σ g (P/10000) (P/200) hσq hσ
      ha.1 (by linarith only [hP]) hghi F hF Flat hFlat hcover X hX t ht ht0 S hS hquarter O hO
      (pointStrength S) hδ Lines hLines Q
    have hsub := radialExceptions_normalization S (fun x => S∩O x) (pointStrength S)
      Lines Q q (P/200) S.card (Real.exp (3*σ/2+g)) hn0 hSn
    have hpay := he D R (P/10000) (P/200) S.card hr (le_refl _) (le_refl _) hcardS
    simp only [zero_mul,zero_add] at hpay
    have hcount' := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcount
    calc
      _≤Real.exp (3*σ/2+g)*(2664192*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-P/200)) := by
        simpa only [neg_div] using hcount'
      _=Real.exp (3*σ/2+g)*(((Nat.clog 2 S.card:ℝ)+1)*(2664192*Real.exp (-P/200))) := by ring
      _≤Real.exp (3*σ/2+g)*(Real.exp (-L η σ D/1000)/8) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        simpa only [neg_div] using hpay
      _≤_ := by nlinarith only [mul_le_mul_of_nonneg_right hquarter (Real.exp_nonneg (-L η σ D/1000))]
  · by_cases hsmall : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P)
    · dsimp only [ambientHalfStrongExceptions]
      rw [ite_eq_left hsmall,Finset.card_empty,Nat.cast_zero]
      positivity
    · rw [ambientHalfStrongExceptions,ite_eq_right hsmall]
      let a : ℝ := (1/(100*(momentOrder σ P:ℝ)))/2
      have hlow : (q:ℝ)^2*Real.exp (-4*P)≤S.card := by rw [←hcard];exact (le_of_not_ge hsmall)
      have hglo : σ/2-4*P≤g := by
        have hh := hlow.trans hSn
        rw [←hσq,←Real.exp_nat_mul,←Real.exp_add] at hh
        have hh := Real.exp_le_exp.mp hh
        norm_num at hh
        linarith only [hh]
      have hen : P/10000<g := ha.2.1.trans_le hglo
      have hg20 : 20*P≤g := ha.2.2.1.trans hglo
      have hacut : Real.exp (-g/20)≤a :=
        (Real.exp_le_exp.mpr (by linarith only [hg20])).trans ha.2.2.2.1
      have hc := literal_plane_global_rich hq hcard hI σ g (P/10000) a hσq hσ ha.1 hen hghi hacut ha.2.2.2.2.1
        F hF Flat hFlat hcover X hX t ht ht0 S hS hquarter O hO (pointStrength S) hδ Lines hLines
      have hc := strong_exceptions_of_global S (fun x => S∩O x) (pointStrength S) a Lines Q hc
      have hnq : (q:ℝ)^2≤4*(S.card:ℝ)*Real.exp (4*P) := by
        have hh := mul_le_mul_of_nonneg_right hlow (Real.exp_nonneg (4*P))
        have hcan : ((q:ℝ)^2*Real.exp (-4*P))*Real.exp (4*P)=(q:ℝ)^2 := by
          rw [mul_assoc,←Real.exp_add];simp
        rw [hcan] at hh
        nlinarith only [hh,mul_nonneg hn0.le (Real.exp_nonneg (4*P))]
      exact ScoreScalars.strong_exception_payment (Nat.cast_nonneg q) hn0 (Nat.cast_nonneg _)
        ha.2.2.2.1 hnq hc ha.2.2.2.2.2
end SharpRamseyFive.ScoreGeometry

end OAI
