import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.RadialOffException
import OAI.Combinatorics.RamseyFive.Geometry.PointStrength

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
theorem row_power_of_tail (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) (H : F)
    (B χ : ℝ) (hB : 0≤B)
    (hm : ∀H:F,mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (htail : ∀a:ℝ,0<a → a≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ a≤ mass (radialWeight x X δ)
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*a^200≤B*Real.exp (2*χ)) :
    (∑H':F,offRow x X δ F H H'^200)≤dyadFactor X.card χ*B := by
  have hh := moment_polynomial_tail (offRow x X δ F H) (fun i:ℕ => (δ:ℝ)*2^i)
    (boundedOverlapDyads x X δ 2) 200 (by norm_num) (B*Real.exp (2*χ))
    (offRow_nonneg x X δ F H) (by intro i _;positivity)
    (offRow_bounded_cover x X δ hδ F hF 2 hm H) (by
      intro i hi
      have ha : 0<(δ:ℝ)*2^i := by positivity
      have he : (Finset.univ.filter fun H':F => (δ:ℝ)*2^i≤offRow x X δ F H H')=
          Finset.univ.filter fun H':F => H≠H' ∧ (δ:ℝ)*2^i≤ mass (radialWeight x X δ)
            (pencilLines x F H∩pencilLines x F H') := by
        apply Finset.filter_congr
        intro H' _
        by_cases h : H=H'
        · simp [offRow,h,not_le.mpr ha]
        · simp [offRow,h]
      rw [he]
      exact htail _ ha (Finset.mem_filter.mp hi).2)
  apply hh.trans
  have hc : ((boundedOverlapDyads x X δ 2).card:ℝ)≤(Nat.clog 2 X.card:ℝ)+1 := by
    exact_mod_cast boundedOverlapDyads_card x X δ 2
  unfold dyadFactor
  calc
    _ ≤ 2^(200:ℕ)*((Nat.clog 2 X.card:ℝ)+1)*(B*Real.exp (2*χ)) := by gcongr
    _ = _ := by ring

theorem low_moment_geometric {d:ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
    (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (B χ b base D₀ : ℝ) (hB : 0<B) (hb : 1≤b) (hD : 0≤D₀)
    (hL : 10000≤(L:ℝ)) (hbase : 23/25≤base)
    (hm : ∀H:F,mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (hlower : ∀H:F,3/4≤ mass (radialWeight x X δ) (pencilLines x F H))
    (hdelta : ∀H:F,|mass (radialWeight x X δ) (pencilLines x F H)-base|≤17/100)
    (hpairs : ∀a:ℝ,0<a → a≤2 →
      ((Finset.univ.filter fun z:DistinctPairs F =>
        a≤ strength (pencilLines x F) (radialWeight x X δ) z).card:ℝ)*a^200≤B^2*Real.exp (2*χ))
    (hrows : ∀H:F,∀a:ℝ,0<a → a≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ a≤ mass (radialWeight x X δ)
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*a^200≤B*Real.exp (2*χ))
    {p : ℕ} (hp : 0<p) (R h : ℕ) (hKR : 200≤R/2) (hh : 0<h)
    (hsize : h≤(R/2)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hdegree : ∀H:F,
      ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ))≤ mass (radialWeight x X δ)
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤B*Real.exp (-3*((L:ℝ)*R)))
    (hdegreeScalar : 2+B*Real.exp (-3*((L:ℝ)*R))≤B*Real.exp (-((L:ℝ)*R)))
    (own : F→Fin R→Bool)
    (hDsum : (∑H:F,|mass (radialWeight x X δ) (pencilLines x F H)-base|^(R/2))≤D₀)
    (hcost : D₀+2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
      (dyadFactor X.card χ*B^2) (dyadFactor X.card χ*B) B b L p R
      (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
      B*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
      (dyadFactor X.card χ*B^2)/(1/(100*(p:ℝ)))^200≤B^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ω,(∑H:F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r e => ω (r,e)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x X δ i.2))≤
      B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  let Q : ℝ := pencilAlphabet (Nat.card K) d
  let M : ℝ := dyadFactor X.card χ*B^2
  let A : ℝ := dyadFactor X.card χ*B
  let C : ℝ := lowMomentBudget Q M A B b L p R
    (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2))
  have hM : 0≤M := by dsimp [M,dyadFactor];positivity
  have hA : 0≤A := by dsimp [A,dyadFactor];positivity
  have hQ : 0≤Q := Nat.cast_nonneg _
  have hC := lowMomentBudget_bounds Q M A B b L p R
    (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2))
    hQ hM hA hB (zero_le_one.trans hb) L.coe_nonneg
  have hQsize : (F.card:ℝ)≤Q := by
    have hh := pencil_size x F hF
    rw [hdim,show d+1-1=d by omega] at hh
    change (F.card:ℝ)≤(pencilAlphabet (Nat.card K) d:ℝ)
    exact_mod_cast hh
  have hPow : (∑z:DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^200)≤M := by
    have hh := score_polynomial_power x X δ hδ F hF 2 (B^2*Real.exp (2*χ)) (by positivity)
      200 (by norm_num) hm (by
        intro i hi
        exact hpairs _ (by positivity) (Finset.mem_filter.mp hi).2)
    simpa only [M,dyadFactor,mul_assoc,mul_left_comm,mul_comm] using hh
  have hRow (H:F) : (∑H':F,offRow x X δ F H H'^200)≤A :=
    row_power_of_tail x X δ hδ F hF H B χ hB.le hm (hrows H)
  have hmassL (H:F) : (∑e∈pencilLines x F H,((L*radialWeight x X δ e:ℝ≥0):ℝ))≤2*(L:ℝ) := by
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using
      mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
  have hN1 (e : RadialLine x) : (Finset.univ.filter fun H:F => e∈pencilLines x F H).card≤
      pencilAlphabet (Nat.card K) (d-1) := by
    have hh := one_anchor_count x F e
    simpa only [hdim,show d+1-2=d-1 by omega,pencilAlphabet] using hh
  have hN2 (e f : RadialLine x) (hef : e≠f) : (Finset.univ.filter fun H:F =>
      e∈pencilLines x F H ∧ f∈pencilLines x F H).card≤pencilAlphabet (Nat.card K) (d-2) := by
    have hh := two_anchor_count x F e f hef
    simpa only [hdim,show d+1-3=d-2 by omega,pencilAlphabet] using hh
  let Δ := ⌈1+B*Real.exp (-3*((L:ℝ)*R))⌉₊
  have hΔ (H:F) : Fintype.card {H':F // AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'}≤Δ := by
    have hc := strong_degree_le x X δ F H (1/(100*(p:ℝ)))
    have hcR : (Fintype.card {H':F // AmbientEnumeration.overlapRelation
        (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'}:ℝ)≤
        1+((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ))≤ mass (radialWeight x X δ)
          (pencilLines x F H∩pencilLines x F H')).card:ℝ) := by exact_mod_cast hc
    exact Nat.cast_le.mp ((hcR.trans (add_le_add (le_refl 1) (hdegree H))).trans
      (show 1+B*Real.exp (-3*((L:ℝ)*R))≤(Δ:ℝ) from Nat.le_ceil _))
  have hΔscale : (Δ:ℝ)≤B*Real.exp (-((L:ℝ)*R)) := by
    have hn := Nat.ceil_lt_add_one (show 0≤1+B*Real.exp (-3*((L:ℝ)*R)) by positivity)
    apply hn.le.trans
    linarith only [hdegreeScalar]
  have hpairs'' : (Fintype.card (ComponentEnumeration.RelatedPair (AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))))):ℝ)≤B^2*Real.exp (((L:ℝ)*R)/10) := by
    apply (strong_pairs_le x X δ F _).trans
    apply le_trans (add_le_add hQsize (power_tail_card _ (fun z => by unfold strength; positivity)
      200 _ M (by positivity) hPow))
    exact hpairScalar
  apply AmbientEnumeration.ambient_untruncated_moment (radialWeight x X δ) (pencilLines x F)
    hp R own L B b (2*(L:ℝ)) C D₀ base B hL hbase hlower hdelta hB hb (by positivity)
    hC.1 hD hB.le hmassL 200 h _ _ (by norm_num) hKR hh hsize herr hN1 hN2 ?_ ?_ ?_
    hDsum hcost hp2 Δ hΔ hΔscale hpairs''
  · exact (score_certificate_majorant x X δ L F p R 200 _ _ Q M B b hB (zero_le_one.trans hb)
      hQsize hM hm hPow).trans hC.2.1
  · intro H
    exact (shift_row_from_power x X δ F H p 200 (by norm_num) A (hRow H)).trans hC.2.2.1
  · exact (shift_pair_from_power x X δ F p 200 M hPow).trans
      ((add_le_add hQsize (le_refl _)).trans hC.2.2.2)

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem actual_low_radial_moment {d : ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
    {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p) (hKR : 200≤R/2)
    (hh : 0<h) (hsize : h≤(R/2)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=d) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1≤cut)
    (hpairs : ∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
        u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
        (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
    (hrows : ∀H:F,∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
        scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/50))
    (hdegree : ∀H:F,
      ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ)) ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
        scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R)))
    (hdegreeScalar : 2+scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R))≤
        scale (K:=K) d S.card*Real.exp (-((L:ℝ)*R)))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (scale (K:=K) d S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (hcost : 40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)+
      2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*(scale (K:=K) d S.card)^2)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*scale (K:=K) d S.card)
        (scale (K:=K) d S.card) cut L p R
        (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
      scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/5)) (own : F→Fin R→Bool) :
    (∫ω,(∑H:F,scoreTerm (pencilLines x F H)
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) (own H)
      (fun r e => ω (r,e)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*
        radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2))≤
      (scale (K:=K) d S.card)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hB : 0<scale (K:=K) d S.card := by
    unfold scale
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hδ : 0<pointStrength (K:=K) S := by
    unfold pointStrength
    have hq : (0:ℝ≥0)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ≥0)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hv := actual_radial_variance x hdim (by omega) S C hS a b c ha hb hc F hF
    (by positivity : 0≤(L:ℝ)/100) hx (hn.trans (by norm_num))
  have hDsum : (∑H:F,|mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H)-(1-ownFraction S (C a) (C b))|^(R/2))≤
      40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100) := by
    apply le_trans _ hv
    apply Finset.sum_le_sum
    intro H _
    exact pow_le_pow_of_le_one (abs_nonneg _) ((hm H).2.1.trans (by norm_num)) (by omega)
  apply low_moment_geometric x hdim hd _ _ L hδ F (fun H hH => (hF H hH).1)
    (scale (K:=K) d S.card) (((L:ℝ)*R)/100) cut (1-ownFraction S (C a) (C b))
    (40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)) hB hcut (by positivity) hL
    (by linarith only [hf]) (fun H => (hm H).2.2.trans (by norm_num))
    (fun H => (hm H).1) (fun H => (hm H).2.1) ?_ ?_ hp R h hKR hh hsize herr
    hdegree hdegreeScalar own hDsum hcost hp2 hpairScalar
  · intro u hu hu2
    simp only [show 2*(((L:ℝ)*R)/100)=((L:ℝ)*R)/50 by ring]
    convert! hpairs u hu hu2 using 1
  · intro H u hu hu2
    simpa only [show 2*(((L:ℝ)*R)/100)=((L:ℝ)*R)/50 by ring] using hrows H u hu hu2

end SharpRamseyFive.ScoreGeometry

end

end OAI
