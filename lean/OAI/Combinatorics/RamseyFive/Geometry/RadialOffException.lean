import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.OutsideCard
import OAI.Combinatorics.RamseyFive.Entropy.LowMomentBudget

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in

lemma radial_lt_off_exception (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a L Q 1) (l : RadialLine x) :
    (radialWeight x (outsideAt x S (O x)) δ l:ℝ)< a := by
  by_contra hn
  have hw : a≤(δ:ℝ)*((RadialLine.trainingOnLine (outsideAt x S (O x)) l).card:ℝ) := by
    simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using le_of_not_gt hn
  have hl : l.val∈localLines S O δ a L x := by
    refine Finset.mem_filter.mpr ⟨hL l,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.property.2
    · change a≤(δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule≤ l.val).card:ℝ) at hw
      rwa [outsideAt_filter_card] at hw
  have hc : (1:ℝ)≤(localLines S O δ a L x).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨l.val,hl⟩
  exact hgood (Finset.mem_filter.mpr ⟨hx,hc⟩)

omit [FiniteDimensional K V] [Finite K] in

lemma strong_degree_le (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (t : ℝ) :
    Fintype.card {H' : F // AmbientEnumeration.overlapRelation (radialWeight x X δ)
      (pencilLines x F) t H H'} ≤
      1+(Finset.univ.filter fun H' : F => H≠H' ∧ t≤
        mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')).card := by
  rw [Fintype.card_subtype]
  apply le_trans (Finset.card_le_card (t := insert H (Finset.univ.filter fun H' : F => H≠H' ∧ t≤
      mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))) ?_) ?_
  · intro H' hH'
    by_cases he : H=H'
    · simpa only [he] using Finset.mem_insert_self H' _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,he,(Finset.mem_filter.mp hH').2.le⟩)
  · simpa only [add_comm] using Finset.card_insert_le H _

omit [FiniteDimensional K V] [Finite K] in

lemma strong_pairs_le (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (t : ℝ) :
    (Fintype.card (ComponentEnumeration.RelatedPair
      (AmbientEnumeration.overlapRelation (radialWeight x X δ) (pencilLines x F) t)):ℝ)≤
      F.card+(Finset.univ.filter fun p : DistinctPairs F =>
        t≤ strength (pencilLines x F) (radialWeight x X δ) p).card := by
  have he : (Fintype.card (ComponentEnumeration.RelatedPair
      (AmbientEnumeration.overlapRelation (radialWeight x X δ) (pencilLines x F) t)):ℝ)=
      ∑ H : F,∑ H' : F,if t< mass (radialWeight x X δ)
        (pencilLines x F H ∩ pencilLines x F H') then (1:ℝ) else 0 := by
    have hsigma {T : Type} [Fintype T] (R : T→T→Prop) :
        (Fintype.card ((h : T) × {h' : T // R h h'}) : ℝ)=
          ∑ h,∑ h',if R h h' then (1:ℝ) else 0 := by
      simp [Fintype.card_sigma,Fintype.card_subtype]
    exact hsigma (T := ↥F) (fun H H' => t < mass (radialWeight x X δ)
      (pencilLines x F H ∩ pencilLines x F H'))
  rw [he,SingletonEnumeration.sum_pairs_split_diagonal]
  apply add_le_add
  · apply (Finset.sum_le_sum (fun H (_ : H∈(Finset.univ : Finset F)) =>
      show (if t< mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H)
        then (1:ℝ) else 0)≤1 by split_ifs <;> norm_num)).trans_eq
    simp
  · calc
      _ ≤ ∑ p : DistinctPairs F,if t≤ strength (pencilLines x F) (radialWeight x X δ) p
          then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p _
        change (if t< strength (pencilLines x F) (radialWeight x X δ) p then (1:ℝ) else 0)≤_
        by_cases hp : t< strength (pencilLines x F) (radialWeight x X δ) p
        · simp [hp,hp.le]
        · simp only [hp,ite_false]; split_ifs <;> norm_num
      _ = _ := by simp

theorem ambient_degree_off_exception (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)≤2)
    (t A : ℝ) (ht : 0< t) (hA : 2≤ A)
    (hscale : 16*((Nat.card K:ℝ)+1)≤ A*t^2)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (t/2) L Q 1) (H : F) :
    (Fintype.card {H' : F // AmbientEnumeration.overlapRelation
      (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F) t H H'}:ℝ)≤ A := by
  let D : ℝ := (Finset.univ.filter fun H' : F => H≠H' ∧ t≤
    mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H ∩ pencilLines x F H')).card
  have hd := score_degree_truncated x hdim (outsideAt x S (O x)) δ hδ F hF H t ht.le
    (radial_lt_off_exception x S O δ (t/2) L hL Q hx hgood)
  have hsq : (mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤4 := by
    calc
      _ ≤ (2:ℝ)^2 := pow_le_pow_left₀ (mass_nonneg _ _) (hm H) 2
      _ = 4 := by norm_num
  have hraw : D*t^2≤8*((Nat.card K:ℝ)+1) := hd.trans (by
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hD : D≤ A/2 := (mul_le_mul_iff_left₀ (sq_pos_of_pos ht)).mp (by nlinarith [hscale])
  have hcard : (Fintype.card {H' : F // AmbientEnumeration.overlapRelation
      (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F) t H H'}:ℝ)≤1+D := by
    dsimp only [D]
    exact_mod_cast strong_degree_le x (outsideAt x S (O x)) δ F H t
  linarith

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def geometryScale (q : ℕ) (n : ℝ) : ℝ := (q:ℝ)^4/n
noncomputable def dyadFactor (m : ℕ) (χ : ℝ) : ℝ := 2^200*(Nat.clog 2 m+1)*Real.exp (2*χ)
def pencilAlphabet (q k : ℕ) : ℕ := ∑ i∈Finset.range k,q^i
noncomputable def pencilLowBudget (q m : ℕ) (n χ b L : ℝ) (p R : ℕ) : ℝ :=
  lowMomentBudget (pencilAlphabet q 4) (dyadFactor m χ*(geometryScale q n)^2)
    (dyadFactor m χ*geometryScale q n) (geometryScale q n) b L p R
      (pencilAlphabet q 3) (pencilAlphabet q 2)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem projective_low_moment (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ L : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n χ b base D₀ : ℝ) (hn : 0 < n) (hb : 1 ≤ b) (hD : 0 ≤ D₀)
    (hL : 10000 ≤ (L:ℝ)) (hbase : (23/25:ℝ) ≤ base)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hcap : n ≤ (Nat.card K:ℝ)^3)
    (hlow : n ≤ (Nat.card K:ℝ)^2*Real.exp (χ/2))
    (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hlower : ∀ H : F,(3/4:ℝ) ≤ mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))
    (hdelta : ∀ H : F,|mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)-base| ≤ 17/100)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    {p : ℕ} (hp : 0 < p) (R h : ℕ) (hKR : 200 ≤ R/2) (hh : 0 < h)
    (hsize : h ≤ (R/2)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1) < 1/2)
    (own : F→Fin R→Bool)
    (hDsum : (∑ H : F,|mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)-base|^(R/2)) ≤ D₀)
    (hcost : D₀+2*((p+1:ℝ)*pencilLowBudget (Nat.card K) (outsideAt x S (O x)).card n χ b L p R) ≤
      geometryScale (Nat.card K) n*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hA : 2 ≤ geometryScale (Nat.card K) n*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1) ≤
      (geometryScale (Nat.card K) n*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S O δ ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) n)^2)/(1/(100*(p:ℝ)))^200 ≤
      (geometryScale (Nat.card K) n)^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ ω, (∑ H : F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S (O x)) δ i.2)) ≤
      (geometryScale (Nat.card K) n)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  let X := outsideAt x S (O x)
  let q := Nat.card K
  let B := geometryScale q n
  let M := dyadFactor X.card χ*B^2
  let A := dyadFactor X.card χ*B
  let C := pencilLowBudget q X.card n χ b L p R
  have hq : 0 < q := Nat.card_pos
  have hB : 0 < B := by dsimp [B,geometryScale]; positivity
  have hM : 0 ≤ M := by dsimp [M,dyadFactor]; positivity
  have hRow : 0 ≤ A := by dsimp [A,dyadFactor]; positivity
  have hQ : 0 ≤ (pencilAlphabet q 4:ℝ) := Nat.cast_nonneg _
  have hC := lowMomentBudget_bounds (pencilAlphabet q 4) M A B b L p R
    (pencilAlphabet q 3) (pencilAlphabet q 2) hQ hM hRow hB (zero_le_one.trans hb) L.coe_nonneg
  have hχ : 0 ≤ χ := by
    by_contra hn
    have he := Real.exp_lt_one_iff.mpr (lt_of_not_ge hn)
    have hnum : (1:ℝ) < 11*2^200 := by norm_num
    linarith
  have hrowlow : n ≤ (q:ℝ)^2*Real.exp χ := hlow.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _))
  have hrowchi : (10*2^200:ℝ) ≤ Real.exp χ := le_trans (by norm_num) hchi
  have hPow : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^200) ≤ M := by
    simpa only [M,B,dyadFactor,geometryScale,mul_assoc,mul_left_comm,mul_comm] using
      score_pair_low_moment x hdim S O δ hδ F hF n χ hn hmass hlow hchi Lines hLines Q hx hm hgood 200 le_rfl
  have hrows (H : F) : (∑ H',offRow x X δ F H H'^200) ≤ A := by
    simpa only [A,B,dyadFactor,geometryScale,mul_assoc,mul_left_comm,mul_comm] using
      score_row_low_moment x hdim X δ hδ F hF H n χ hn hm hcap hrowlow hrowchi
  have hQsize : (F.card:ℝ) ≤ (pencilAlphabet q 4:ℝ) := by
    exact_mod_cast (by simpa only [hdim,Nat.reduceSub,pencilAlphabet] using pencil_size x F hF)
  have hN₁ (d : RadialLine x) : (Finset.univ.filter fun H : F => d∈pencilLines x F H).card ≤ pencilAlphabet q 3 := by
    simpa only [hdim,Nat.reduceSub,pencilAlphabet] using one_anchor_count x F d
  have hN₂ (d e : RadialLine x) (hde : d≠e) :
      (Finset.univ.filter fun H : F => d∈pencilLines x F H ∧ e∈pencilLines x F H).card ≤ pencilAlphabet q 2 := by
    simpa only [hdim,Nat.reduceSub,pencilAlphabet] using two_anchor_count x F d e hde
  have hmassL (H : F) : (∑ d∈pencilLines x F H,((L*radialWeight x X δ d:ℝ≥0):ℝ)) ≤ 2*(L:ℝ) := by
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using
      mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
  have ht : 0 < 1/(100*(p:ℝ)) := by positivity
  let Δ := ⌊B*Real.exp (-((L:ℝ)*R))⌋₊
  have hΔ (H : F) : Fintype.card {H' : F // AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'} ≤ Δ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    exact ambient_degree_off_exception x hdim S O δ hδ F hF hm _ _ ht hA hscale Lines hLines Q hx hstrong H
  have hdeg : (Δ:ℝ) ≤ B*Real.exp (-((L:ℝ)*R)) := Nat.floor_le (by positivity)
  have hRelPairs : (Fintype.card (ComponentEnumeration.RelatedPair (AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))))):ℝ) ≤ B^2*Real.exp (((L:ℝ)*R)/10) := by
    apply (strong_pairs_le x X δ F _).trans
    apply le_trans (add_le_add hQsize (power_tail_card _ (fun z => by unfold strength; positivity) 200 _ M ht hPow))
    exact hpairScalar
  apply AmbientEnumeration.ambient_untruncated_moment (radialWeight x X δ) (pencilLines x F)
    hp R own L B b (2*(L:ℝ)) C D₀ base B hL hbase hlower hdelta hB hb (by positivity)
    hC.1 hD hB.le hmassL 200 h (pencilAlphabet q 3) (pencilAlphabet q 2) (by norm_num)
    hKR hh hsize herr hN₁ hN₂ ?_ ?_ ?_ hDsum hcost hp2 Δ hΔ hdeg hRelPairs
  · exact (score_certificate_majorant x X δ L F p R 200 _ _ _ M B b hB (zero_le_one.trans hb) hQsize hM hm hPow).trans hC.2.1
  · intro H
    exact (shift_row_from_power x X δ F H p 200 (by norm_num) A (hrows H)).trans hC.2.2.1
  · exact (shift_pair_from_power x X δ F p 200 M hPow).trans
      ((add_le_add hQsize (le_refl _)).trans hC.2.2.2)

end SharpRamseyFive.ScoreGeometry

end OAI
