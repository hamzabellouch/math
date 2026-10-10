import Mathlib
import OAI.Probability.ThreeState.Update

namespace OAI

/-! Common-mass couplings and total variation bounds for products and mixtures. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

 

def commonMass {α : Type*} (p q:PMF α) : ℝ := ∑'a,min (mass p a) (mass q a)
lemma commonMass_summable {α : Type*} (p q:PMF α) :
    Summable (fun a=>min (mass p a) (mass q a)) :=
  Summable.of_nonneg_of_le (fun a=>le_min (mass_nonneg p a) (mass_nonneg q a))
    (fun value => min_le_left (mass p value) (mass q value)) (mass_summable p)
lemma commonMass_nonneg {α : Type*} (p q:PMF α) : 0≤commonMass p q :=
  tsum_nonneg (fun a=>le_min (mass_nonneg p a) (mass_nonneg q a))
lemma commonMass_eq {α : Type*} (p q:PMF α) : commonMass p q=1-tvMass p q := by
  have he (a:α) : min (mass p a) (mass q a)=(mass p a+mass q a-|mass p a-mass q a|)/2 := by
    rw [min_def];split_ifs with h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)];ring
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))];ring
  simp_rw [commonMass,he]
  rw [tsum_div_const,((mass_summable p).add (mass_summable q)).tsum_sub (mass_diff_summable p q),
    (mass_summable p).tsum_add (mass_summable q),mass_sum,mass_sum]
  unfold tvMass
  ring
lemma commonMass_le_one {α : Type*} (p q:PMF α) : commonMass p q≤1 := by
  rw [commonMass_eq];linarith [tvMass_nonneg p q]

 

def sharedPMF {α : Type*} (p q:PMF α) (hc:0<commonMass p q) : PMF α := by
  refine ⟨fun a=>ENNReal.ofReal (min (mass p a) (mass q a)/commonMass p q),?_⟩
  have hs : HasSum (fun a=>min (mass p a) (mass q a)/commonMass p q) 1 := by
    convert! (commonMass_summable p q).hasSum.div_const (commonMass p q) using 1
    exact (div_self hc.ne').symm
  apply ENNReal.hasSum_coe.2
  simpa using (hs.toNNReal (fun a=>div_nonneg
    (le_min (mass_nonneg p a) (mass_nonneg q a)) hc.le))
lemma mass_sharedPMF {α : Type*} (p q:PMF α) (hc:0<commonMass p q) (a:α) :
    mass (sharedPMF p q hc) a=min (mass p a) (mass q a)/commonMass p q := by
  change (ENNReal.ofReal _).toReal=_
  exact ENNReal.toReal_ofReal (div_nonneg (le_min (mass_nonneg p a) (mass_nonneg q a)) hc.le)
lemma sharedPMF_scaled {α : Type*} (p q:PMF α) (hc:0<commonMass p q) (a:α) :
    commonMass p q*mass (sharedPMF p q hc) a=min (mass p a) (mass q a) := by
  rw [mass_sharedPMF];field_simp

lemma commonMass_iidVector {α : Type*} (p q:PMF α) (n:ℕ) :
    (commonMass p q)^n≤commonMass (iidVector p n) (iidVector q n) := by
  rcases n with _|n
  · simp only [iidVector,commonMass,min_self,mass_sum,pow_zero,le_refl]
  by_cases hc:commonMass p q=0
  · rw [hc,zero_pow (Nat.succ_ne_zero _)]
    exact commonMass_nonneg _ _
  have hcpos:0<commonMass p q:=lt_of_le_of_ne (commonMass_nonneg p q) (Ne.symm hc)
  let r:=sharedPMF p q hcpos
  have hpoint (v:Fin (n+1)→α) : (commonMass p q)^(n+1)*mass (iidVector r (n+1)) v ≤
      min (mass (iidVector p (n+1)) v) (mass (iidVector q (n+1)) v) := by
    simp only [mass_iidVector]
    have he : (commonMass p q)^(n+1)*∏j:Fin (n+1),mass r (v j)=
        ∏j:Fin (n+1),min (mass p (v j)) (mass q (v j)) := by
      rw [←show (∏j:Fin (n+1),commonMass p q)=(commonMass p q)^(n+1) by simp,
        ←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      exact sharedPMF_scaled p q hcpos (v j)
    rw [he]
    exact le_min
      (Finset.prod_le_prod₀
        (fun index _ => le_min (mass_nonneg p (v index)) (mass_nonneg q (v index)))
        (fun index _ => min_le_left (mass p (v index)) (mass q (v index))))
      (Finset.prod_le_prod₀
        (fun index _ => le_min (mass_nonneg p (v index)) (mass_nonneg q (v index)))
        (fun index _ => min_le_right (mass p (v index)) (mass q (v index))))
  have hh:=(mass_summable (iidVector r (n+1))).mul_left ((commonMass p q)^(n+1))
  have ht:=Summable.tsum_le_tsum hpoint hh (commonMass_summable _ _)
  rw [tsum_mul_left] at ht
  simpa only [mass_sum,mul_one,commonMass] using ht

lemma tvMass_iidVector_le {α : Type*} (p q:PMF α) (n:ℕ) :
    tvMass (iidVector p n) (iidVector q n)≤1-(1-tvMass p q)^n := by
  have hh:=commonMass_iidVector p q n
  rw [commonMass_eq,commonMass_eq] at hh
  linarith
end
end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

lemma tvMass_map_le {α β:Type*} (p q:PMF α) (f:α→β) : tvMass (p.map f) (q.map f)≤tvMass p q :=
  tvMass_bind_le p q (fun a=>PMF.pure (f a))

lemma mass_edge_difference {α:Type*} (law:Spin→PMF α) (lam:ℝ) (h:Admissible lam)
    (i j:Spin) (a:α) :
    mass (edgeLaw law lam h i) a-mass (edgeLaw law lam h j) a=
      lam*(mass (law i) a-mass (law j) a) := by
  rw [mass_edgeLaw,mass_edgeLaw,←weighted_likelihood law a i,←weighted_likelihood law a j]
  change _*(1+lam*(_-1))-_*(1+lam*(_-1))=_
  ring
lemma tvMass_edge {α:Type*} (law:Spin→PMF α) (lam:ℝ) (h:Admissible lam) (i j:Spin) :
    tvMass (edgeLaw law lam h i) (edgeLaw law lam h j)= |lam| *tvMass (law i) (law j) := by
  unfold tvMass
  simp_rw [mass_edge_difference,abs_mul]
  rw [tsum_mul_left]
  ring

lemma tvMass_marginal_le {α:Type*} (law:Spin→PMF α) (i:Spin) :
    tvMass (law i) (marginal law)≤(∑j:Spin,tvMass (law i) (law j))/3 := by
  have he (a:α) : mass (law i) a-mass (marginal law) a=
      (∑j:Spin,(mass (law i) a-mass (law j) a))/3 := by
    rw [mass_marginal,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hp (a:α) : |mass (law i) a-mass (marginal law) a|≤
      (∑j:Spin,|mass (law i) a-mass (law j) a|)/3 := by
    rw [he,abs_div]
    rw [abs_of_nonneg (by norm_num : (0:ℝ)≤3)]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
  have hs : Summable (fun a=>∑j:Spin,|mass (law i) a-mass (law j) a|) :=
    summable_sum (fun j _=>mass_diff_summable _ _)
  have hh:=Summable.tsum_le_tsum hp (mass_diff_summable _ _) (hs.div_const 3)
  rw [tsum_div_const,Summable.tsum_finsetSum (fun j _=>mass_diff_summable (law i) (law j))] at hh
  unfold tvMass
  rw [←Finset.sum_div]
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

lemma advantage_le_pair_bound {α:Type*} (law:Spin→PMF α) (x:ℝ)
    (hx:∀i j,tvMass (law i) (law j)≤x) : advantage law≤x := by
  rw [advantage_eq_tvMass]
  have hb (i:Spin):tvMass (law i) (marginal law)≤x := by
    calc
      _ ≤ (∑j:Spin,tvMass (law i) (law j))/3 := tvMass_marginal_le law i
      _ ≤ (∑j:Spin,x)/3 := div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _=>hx i j)) (by norm_num)
      _ = x := by simp
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hb i)
  have hd:=div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤3)
  simpa using hd

lemma tvMass_sigmaPMF {ι:Type*} {α:ι→Type*} (p:PMF ι) (q r:∀i,PMF (α i)) :
    tvMass (sigmaPMF p q) (sigmaPMF p r)=∑'i,mass p i*tvMass (q i) (r i) := by
  unfold tvMass
  rw [(mass_diff_summable (sigmaPMF p q) (sigmaPMF p r)).tsum_sigma]
  simp_rw [mass_sigmaPMF,←mul_sub,abs_mul,abs_of_nonneg (mass_nonneg p _),tsum_mul_left]
  rw [←tsum_div_const]
  congr 1
  funext i
  ring

lemma summable_weighted_tv {ι:Type*} {α:ι→Type*} (p:PMF ι) (q r:∀i,PMF (α i)) :
    Summable (fun i=>mass p i*tvMass (q i) (r i)) :=
  Summable.of_nonneg_of_le (fun i=>mul_nonneg (mass_nonneg p i) (tvMass_nonneg _ _))
    (fun i=>mul_le_of_le_one_right (mass_nonneg p i) (tvMass_le_one _ _)) (mass_summable p)
end
end ThreeState

end OAI
