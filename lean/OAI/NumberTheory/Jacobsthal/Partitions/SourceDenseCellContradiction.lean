import OAI.NumberTheory.Jacobsthal.Estimates.SourceRichPoints
import OAI.NumberTheory.Jacobsthal.Estimates.SourceRichSetContradiction

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem cofactor_coprime_excluded_bin {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (hP : ∀ i,∀ p ∈ P i,p.Prime)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i : ι) (hi : m i = 0) (q : ℕ) (hq : q ∈ cofactorChoices P m) :
    ∀ p ∈ P i,q.Coprime p := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have hs := (mem_selections P m f).mp hf
  have hz : f i = ∅ := Finset.card_eq_zero.mp ((hs i).2.trans hi)
  have hrec := prime_factor_bin_recovery P m hP hd f hf i
  rw [hz] at hrec
  intro p hp
  apply Nat.Coprime.symm
  apply (hP i p hp).coprime_iff_not_dvd.mpr
  intro hdiv
  have hm : p ∈ (selectionProduct f).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hP i p hp,hdiv,(selectionProduct_pos P hP f (fun j => (hs j).1)).ne'⟩
  have he := Finset.mem_inter.mpr ⟨hm,hp⟩
  rw [hrec] at he
  exact Finset.notMem_empty p he

theorem cofactor_coprime_small {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (hP : ∀ i,∀ p ∈ P i,p.Prime)
    (w : ℝ) (hlarge : ∀ i,∀ p ∈ P i,w < (p : ℝ))
    (q : ℕ) (hq : q ∈ cofactorChoices P m) (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) :
    q.Coprime t := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have hs := (mem_selections P m f).mp hf
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply (Nat.coprime_primes (hP i p ((hs i).1 hp)) ht).mpr
  intro he
  have hh := hlarge i p ((hs i).1 hp)
  subst p
  linarith

theorem distinct_bins_coprime {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i,∀ p ∈ P i,p.Prime)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (i j : ι) (hij : i ≠ j) :
    ∀ p ∈ P i,∀ u ∈ P j,p.Coprime u := by
  intro p hp u hu
  apply (Nat.coprime_primes (hP i p hp) (hP j u hu)).mpr
  intro he
  exact Finset.disjoint_left.mp (hd hij) hp (he.symm ▸ hu)

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement

theorem parent_product_le_of_child_log (Y p q u : ℕ) (w a : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hu : 1 ≤ u) (hw : 1 < w) (ha : 0 < a)
    (hlog : 3*a/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) :
    (p : ℝ)*(q : ℝ) ≤ (Y : ℝ) := by
  have hwlog : 0 < Real.log w := Real.log_pos hw
  have hpositive : 0 < Real.log ((Y : ℝ)/((p : ℝ)*q*u)) := by
    have hh := (le_div_iff₀ hwlog).mp hlog
    have hleft : 0 < (3*a/4)*Real.log w := by positivity
    exact hleft.trans_le hh
  have hden : 0 < (p : ℝ)*q*u := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hp hq) (lt_of_lt_of_le Nat.zero_lt_one hu)
  have hrat0 : 0 ≤ (Y : ℝ)/((p : ℝ)*q*u) := div_nonneg (Nat.cast_nonneg _) hden.le
  have hrat1 : 1 < (Y : ℝ)/((p : ℝ)*q*u) := (Real.log_pos_iff hrat0).mp hpositive
  have hh := (lt_div_iff₀ hden).mp hrat1
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hmul := mul_le_mul_of_nonneg_left huR (show 0 ≤ (p : ℝ)*q by positivity)
  nlinarith

theorem parent_small_coprime_child (p q u : ℕ) (w : ℝ) (hu : u.Prime) (hwu : w < (u : ℝ))
    (hparent : ∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) :
    ∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q*u).Coprime t := by
  intro t ht htw
  apply (hparent t ht htw).mul_left
  apply (Nat.coprime_primes hu ht).mpr
  intro he
  subst u
  linarith

end ErdosInverseRefinement

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseEuler ErdosInverseStructured ErdosInverseBoxHeight ErdosInversePrimeBin

theorem source_no_dense_cell (Clen Cparent aStar K alpha delta beta : ℝ) (h : ℕ)
    (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hh : 12 < aStar*(h : ℝ)/2) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,∀ R thetaP U thetaU Qplus S : ℝ,
        ∀ (C : Finset ℕ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
        z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → sourceW z ≤ U → U ≤ (sourceW z)^K →
        xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
        q0 ∈ C → 0 < q0 →
        S/(q0 : ℝ) ≤ (1+thetaP)^(Clen*Real.log (sourceB z)) →
        (∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S) →
        (∀ q ∈ C,(q : ℝ) ≤ Qplus ∧ Qplus ≤ (1+xi)*(q : ℝ)) →
        (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,p.Coprime u) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,q.Coprime p) →
        (∀ q ∈ C,∀ u ∈ primeBin U thetaU,q.Coprime u) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime →
          (t : ℝ) ≤ sourceW z → (p*q).Coprime t) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        (∀ p ∈ primeBin R thetaP,
          Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q0)) ≤ Cparent) →
        (∀ q ∈ C,Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) ∧
          Int.ModEq (smallModulus (sourceW z) : ℤ) (cofactorHit q a : ℤ) b0) →
        S/sourceZ z ≤ (C.card : ℝ) →
        let P := primeBin R thetaP
        let Uset := primeBin U thetaU
        let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
          (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma beta h/32)
        beta*((P.product C).card : ℝ)*(Uset.card : ℝ) ≤
          ((witnessPairs (P.product C) Uset witness).card : ℝ) → False := by
  have hhpos : 0 < h := by
    by_contra hn
    have hz : h = 0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero,zero_div] at hh
    linarith
  let gamma := sampleGamma beta h
  have hg : 0 < gamma := sampleGamma_pos beta h hb
  obtain ⟨xi0,hxi0,hxi01,hRich⟩ := source_rich_points aStar delta K gamma h ha hd hK hg hhpos
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 : xi ≤ 1 := hxib.trans hxi01
  filter_upwards [source_good_sample aStar K alpha xi delta beta h ha ha1 hK halpha hxi hxi1 hd hb hb1 hh,
    hRich xi hxi hxib,
    uniform_no_rich_nonstructured_set Clen Cparent (xi/4) alpha (gamma/8)
      hClen hCparent (by positivity) halpha (by positivity),
    sourceW_tendsto_atTop.eventually_ge_atTop 2] with z hgood hrich hno hW
  intro R thetaP U thetaU Qplus S C q0 b0 a hRlo hRhi hWU hUtop hPlow hPhigh hUlow hUhigh
    hq0C hq0 hinfl hCsq hCQ hpU hCP hCU hsmall hlog hparentlog hcong hCsize
  dsimp only
  intro hdense
  let P := primeBin R thetaP
  let Uset := primeBin U thetaU
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (gamma/32)
  obtain ⟨s,hPpos,hUpos,_,hreward,hcost⟩ := hgood.2 R thetaP U thetaU Qplus S C q0 b0 a
    hRlo hWU hUtop hPlow hPhigh hUlow hUhigh hq0C hq0 (hCQ q0 hq0C).1 (hCQ q0 hq0C).2
    (hsmall q0 hq0C) (hlog q0 hq0C) hdense
  have hzpos : 0 < z := by linarith [hgood.1]
  have hR : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hRlo
  have hU : 0 ≤ U := by linarith
  have hthetaP : 0 ≤ thetaP := (by positivity : (0 : ℝ) ≤ xi/4).trans hPlow
  have hthetaU : 0 ≤ thetaU := (by positivity : (0 : ℝ) ≤ xi/4).trans hUlow
  have hPprime : ∀ p ∈ P,p.Prime := fun p hp => ((mem_primeBin hR.le hthetaP p).mp hp).1
  have hUprime : ∀ u ∈ Uset,u.Prime := fun u hu => ((mem_primeBin hU hthetaU u).mp hu).1
  have huLarge : ∀ u ∈ Uset,sourceW z < (u : ℝ) :=
    fun u hu => hWU.trans_lt ((mem_primeBin hU hthetaU u).mp hu).2.1
  have hS : 0 < S := (show (0 : ℝ) < q0 by exact_mod_cast hq0).trans_le (hCsq q0 hq0C).2
  have hsmallChild : ∀ q ∈ C,∀ p ∈ P,∀ u ∈ Uset,∀ t : ℕ,t.Prime →
      (t : ℝ) ≤ sourceW z → (p*q*u).Coprime t := by
    intro q hq p hp u hu
    exact parent_small_coprime_child p q u (sourceW z) (hUprime u hu) (huLarge u hu) (hsmall q hq p hp)
  obtain ⟨T,D,hDC,hbox,hinj,hsize,hclass,hinc,hthin⟩ := hrich P C a U thetaU Qplus S R (gamma/32)
    q0 b0 hR hS hWU hUtop hthetaU (hUhigh.trans hxi1) hPpos hPprime hpU hCsq hCP hCU hCQ
    hlog hsmallChild hcong hCsize s hreward hcost
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hPpos
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hUpos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPprime p hp).one_lt.le
  have hq0R : (0 : ℝ) < q0 := by exact_mod_cast hq0
  have hpq := parent_product_le_of_child_log (sourceY z) p q0 u (sourceW z) aStar
    (hPprime p hp).pos hq0 (hUprime u hu).one_lt.le (by linarith) ha (hlog q0 hq0C p hp u hu)
  have hratio : 1 ≤ S/(q0 : ℝ) := (one_le_div hq0R).mpr (hCsq q0 hq0C).2
  have hpR : (p : ℝ) ≤ 2*R := by
    have hh := ((mem_primeBin hR.le hthetaP p).mp hp).2.2
    have ht1 := hPhigh.trans hxi1
    nlinarith
  apply hno.2 S R (p : ℝ) (q0 : ℝ) thetaP hp1 hq0R hpq hratio hinfl
    hRlo hRhi hPlow (hPhigh.trans hxi1) hpR (hparentlog p hp)
    (fun p => (a p : ℤ)) T hthin (cofactorPoints D a) hbox hinj hsize
  · simpa only [Int.cast_natCast] using hclass
  · simpa only [div_div,show (8 : ℝ)*4 = 32 by norm_num] using hinc

end ErdosInverseRefinement

end

end Erdos970

end OAI
