import Mathlib
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.GoodBox

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory
open MeasureTheory Complex
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryCorrelations.SourceRoughRealScale
open Classical Finset
open scoped Pointwise
open SourceRoughFourier SourceRoughCountIntegration SourcePrimeBoxSieve SourceBoxSieve

lemma card_four_le_interval_energy (Z : Finset ℕ) (a N : ℕ)
    (hZ : ∀ z ∈ Z, a ≤ z ∧ z < a+N) :
    Z.card^4 ≤ 2*N*natAdditiveEnergy Z := by
  have hc : (Z+Z).card ≤ 2*N := by
    have hs : Z+Z ⊆ Ico (2*a) (2*a+2*N) := by
      intro n hn
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hn
      have := hZ x hx
      have := hZ y hy
      apply mem_Ico.mpr
      omega
    have := card_le_card hs
    simpa using this
  have he : Z.card^2*Z.card^2 ≤ (Z+Z).card*natAdditiveEnergy Z := by
    simpa only [Finset.addEnergy_eq_card_filter,natAdditiveEnergy,natEnergyQuadruples] using
      Finset.le_card_add_mul_addEnergy Z Z
  calc
    _ = Z.card^2*Z.card^2 := by ring
    _ ≤ _ := he
    _ ≤ _ := Nat.mul_le_mul_right _ hc

lemma energy_le_goodBox (Z : Finset ℕ) (a N : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hZ : ∀ z ∈ Z, a ≤ z ∧ z < a+N ∧ IsRough y z) :
    natAdditiveEnergy Z ≤ (goodBox ⌊y⌋₊ a N).card := by
  have hd (q : ↥(natEnergyQuadruples Z)) :
      (q.val.1.1 ∈ Z ∧ q.val.1.2 ∈ Z ∧ q.val.2.1 ∈ Z ∧ q.val.2.2 ∈ Z) ∧
      q.val.1.1+q.val.1.2=q.val.2.1+q.val.2.2 := by
    have hq := q.property
    simpa only [natEnergyQuadruples,mem_filter,mem_product,and_assoc] using hq
  let f : ↥(natEnergyQuadruples Z) → ↥(goodBox ⌊y⌋₊ a N) := fun q =>
    ⟨(⟨q.val.1.1-a,by have := hZ _ (hd q).1.1; omega⟩,
      ⟨q.val.1.2-a,by have := hZ _ (hd q).1.2.1; omega⟩,
      ⟨q.val.2.1-a,by have := hZ _ (hd q).1.2.2.1; omega⟩),by
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        intro p
        have h1 := hZ _ (hd q).1.1
        have h2 := hZ _ (hd q).1.2.1
        have h3 := hZ _ (hd q).1.2.2.1
        have h4 := hZ _ (hd q).1.2.2.2
        dsimp only
        rw [Nat.add_sub_of_le h1.1,Nat.add_sub_of_le h2.1,Nat.add_sub_of_le h3.1]
        refine ⟨rough_cast hy h1.2.2 p,rough_cast hy h2.2.2 p,rough_cast hy h3.2.2 p,?_⟩
        have he : (q.val.1.1:ZMod p.val)+q.val.1.2 = (q.val.2.1:ZMod p.val)+q.val.2.2 := by
          have hc := congrArg (fun n : ℕ => (n:ZMod p.val)) (hd q).2
          simpa only [Nat.cast_add] using hc
        have hx : (q.val.1.1:ZMod p.val)+q.val.1.2-q.val.2.1 = (q.val.2.2:ZMod p.val) := by
          linear_combination he
        rw [hx]
        exact rough_cast hy h4.2.2 p⟩
  have hi : Function.Injective f := by
    intro q r he
    have hv := congrArg (fun b : ↥(goodBox ⌊y⌋₊ a N) =>
      (b.val.1.val,b.val.2.1.val,b.val.2.2.val)) he
    have hx := congrArg Prod.fst hv
    have hy := congrArg (fun b : ℕ × ℕ × ℕ => b.2.1) hv
    have hz := congrArg (fun b : ℕ × ℕ × ℕ => b.2.2) hv
    change q.val.1.1-a=r.val.1.1-a at hx
    change q.val.1.2-a=r.val.1.2-a at hy
    change q.val.2.1-a=r.val.2.1-a at hz
    have hq1 := hZ _ (hd q).1.1
    have hq2 := hZ _ (hd q).1.2.1
    have hq3 := hZ _ (hd q).1.2.2.1
    have hr1 := hZ _ (hd r).1.1
    have hr2 := hZ _ (hd r).1.2.1
    have hr3 := hZ _ (hd r).1.2.2.1
    have hqe := (hd q).2
    have hre := (hd r).2
    apply Subtype.ext
    apply Prod.ext <;> apply Prod.ext <;> omega
  simpa only [natAdditiveEnergy,Fintype.card_coe] using Fintype.card_le_of_injective f hi

lemma floor_geometry (D : ℝ) (hD : 2 ≤ D) :
    D ≤ (2*⌊D⌋₊:ℕ) ∧ ((2*⌊D⌋₊:ℕ):ℝ) ≤ 2*D ∧
    ∀ z : ℕ, D ≤ z → z < 2*D → ⌊D⌋₊ ≤ z ∧ z < ⌊D⌋₊+2*⌊D⌋₊ := by
  have hD0 : 0 ≤ D := by linarith
  have ha := Nat.floor_le hD0
  have hb := Nat.lt_floor_add_one D
  have ha2 : 2 ≤ ⌊D⌋₊ := (Nat.le_floor_iff hD0).mpr hD
  have ha2r : (2:ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast ha2
  constructor
  · push_cast
    linarith
  constructor
  · push_cast
    linarith
  intro z hz1 hz2
  constructor
  · exact_mod_cast ha.trans hz1
  · have hzr : (z:ℝ) < (⌊D⌋₊:ℝ)+2*(⌊D⌋₊:ℝ) := by linarith
    exact_mod_cast hzr

lemma eventual_source_D_large : ∀ᶠ L : ℝ in Filter.atTop,
    2 ≤ (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop (16:ℝ)] with L hL
  have hr : (4:ℝ) ≤ L^(199/200:ℝ) := by
    calc
      4 = (16:ℝ)^(1/2:ℝ) := by rw [← Real.sqrt_eq_rpow]; norm_num
      _ ≤ L^(1/2:ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have := Real.add_one_le_exp (L^(199/200:ℝ))
  linarith

theorem eventual_real_energy : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℝ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
      (natAdditiveEnergy Z:ℝ) ≤ C*D^3*L^(-99/25:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_rough_box
  refine ⟨8*C,by positivity,?_⟩
  filter_upwards [h,eventual_source_D_large,Filter.eventually_ge_atTop (1:ℝ)] with L hL hbig hL1
  intro D hD Z hZ
  have hD2 : 2 ≤ D := hbig.trans hD
  obtain ⟨hDN,hND,hgeom⟩ := floor_geometry D hD2
  let a := ⌊D⌋₊
  let N := 2*a
  have hNp : 0 < N := by
    have : (0:ℝ) < N := (by linarith : (0:ℝ) < D).trans_le hDN
    exact_mod_cast this
  have hNz : (N:ℝ) ≠ 0 := by positivity
  have he : (natAdditiveEnergy Z:ℝ) ≤ (goodBox ⌊Real.exp (L^(99/100:ℝ))⌋₊ a N).card := by
    exact_mod_cast energy_le_goodBox Z a N _ (Real.exp_pos _).le
      (fun z hz => ⟨(hgeom z (hZ z hz).1 (hZ z hz).2.1).1,
        (hgeom z (hZ z hz).1 (hZ z hz).2.1).2,(hZ z hz).2.2⟩)
  have hden := hL a N (hD.trans hDN)
  calc
    _ ≤ ((goodBox ⌊Real.exp (L^(99/100:ℝ))⌋₊ a N).card:ℝ) := he
    _ = (N:ℝ)^3*density (fun p : Primes ⌊Real.exp (L^(99/100:ℝ))⌋₊ => p.val) a N := by
      rw [density_eq_card]
      field_simp
    _ ≤ (N:ℝ)^3*(C*L^(-99/25:ℝ)) := mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ (2*D)^3*(C*L^(-99/25:ℝ)) := by gcongr
    _ = _ := by ring

end OrdinaryCorrelations.SourceRoughRealScale

end

end OAI
