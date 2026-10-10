import OAI.NumberTheory.Ostmann.Supply.RetainedBandScales

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter TensorModes
open scoped BigOperators

theorem retainedBandProducts_conditions {L : ℝ} (_hL : 0≤L)
    (hupper : (2*supplyTruncation L:ℕ)*Real.exp ((9/10:ℝ)*L)≤Real.exp L/2)
    (hlower : (2*supplyTruncation L:ℕ)/Real.exp ((1/20:ℝ)*L)≤1/16)
    (p : ℕ→ℕ) (n : ℕ) (hp : ∀i<n,(p i).Prime)
    (hinj : Set.InjOn p (Finset.range n:Set ℕ))
    (hband : ∀i<n,(1/20:ℝ)*L<Real.log (Real.log (p i:ℝ)) ∧
      Real.log (Real.log (p i:ℝ))≤(9/10:ℝ)*L) :
    ∀t∈retainedProducts p n (2*supplyTruncation L),
      Squarefree t ∧ t≤ supplyRadius L ∧ ∑q∈t.primeFactors,(1:ℝ)/q≤1/16 := by
  classical
  intro t ht
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
  have hsub : s⊆Finset.range n := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
  have hcard : s.card≤2*supplyTruncation L := (Finset.mem_filter.mp hs).2
  have hprime : ∀i∈s,(p i).Prime := fun i hi => hp i (Finset.mem_range.mp (hsub hi))
  have hinjs : Set.InjOn p (s:Set ℕ) := hinj.mono hsub
  have himage : (∏q∈s.image p,q)=∏i∈s,p i :=
    Finset.prod_image (fun i hi j hj hij => hinjs hi hj hij)
  have hprimes : ∀q∈s.image p,q.Prime := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hprime i hi
  have hpf : (∏i∈s,p i).primeFactors=s.image p := by
    rw [←himage]
    exact Nat.primeFactors_prod hprimes
  have hsq : Squarefree (∏i∈s,p i) := by
    rw [←himage]
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun q hq r hr hqr => ?_)
      (fun q hq => (hprimes q hq).squarefree)
    change IsRelPrime q r
    rw [←Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprimes q hq) (hprimes r hr)).mpr hqr
  have hmin (i : ℕ) (hi : i∈s) : Real.exp ((1/20:ℝ)*L)≤(p i:ℝ) := by
    have hp0 : (0:ℝ)<p i := by exact_mod_cast (hprime i hi).pos
    have hlog : 0<Real.log (p i:ℝ) := Real.log_pos (by exact_mod_cast (hprime i hi).one_lt)
    have h := Real.exp_lt_exp.mpr (hband i (Finset.mem_range.mp (hsub hi))).1
    rw [Real.exp_log hlog] at h
    exact h.le.trans (Real.log_le_self hp0.le)
  have hmax (i : ℕ) (hi : i∈s) : (p i:ℝ)≤Real.exp (Real.exp ((9/10:ℝ)*L)) := by
    have hp0 : (0:ℝ)<p i := by exact_mod_cast (hprime i hi).pos
    have hlog : 0<Real.log (p i:ℝ) := Real.log_pos (by exact_mod_cast (hprime i hi).one_lt)
    exact (Real.log_le_iff_le_exp hp0).mp
      ((Real.log_le_iff_le_exp hlog).mp (hband i (Finset.mem_range.mp (hsub hi))).2)
  have hprod : ((∏i∈s,p i:ℕ):ℝ)≤Real.exp ((s.card:ℝ)*Real.exp ((9/10:ℝ)*L)) := by
    rw [Nat.cast_prod,Real.exp_nat_mul,←Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i hi => Nat.cast_nonneg _) hmax
  have hcut : (s.card:ℝ)*Real.exp ((9/10:ℝ)*L)≤Real.exp L/2 := by
    apply le_trans _ hupper
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le
  have htR : (∏i∈s,p i)≤ supplyRadius L := by
    exact_mod_cast (hprod.trans (Real.exp_le_exp.mpr hcut)).trans
      (Nat.le_ceil (Real.exp (Real.exp L/2)))
  refine ⟨hsq,htR,?_⟩
  rw [hpf,Finset.sum_image (fun i hi j hj hij => hinjs hi hj hij)]
  calc
    (∑i∈s,(1:ℝ)/(p i:ℝ))≤∑i∈s,(1:ℝ)/Real.exp ((1/20:ℝ)*L) :=
      Finset.sum_le_sum (fun i hi => one_div_le_one_div_of_le (Real.exp_pos _) (hmin i hi))
    _ = (s.card:ℝ)/Real.exp ((1/20:ℝ)*L) := by simp [div_eq_mul_inv]
    _ ≤ (2*supplyTruncation L:ℕ)/Real.exp ((1/20:ℝ)*L) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le
    _ ≤ 1/16 := hlower

theorem eventually_retainedBandProducts :
    ∀ᶠL:ℝ in atTop, ∀p:ℕ→ℕ,∀n:ℕ,
      (∀i<n,(p i).Prime) → Set.InjOn p (Finset.range n:Set ℕ) →
      (∀i<n,(1/20:ℝ)*L<Real.log (Real.log (p i:ℝ)) ∧
        Real.log (Real.log (p i:ℝ))≤(9/10:ℝ)*L) →
      ∀t∈retainedProducts p n (2*supplyTruncation L),
        Squarefree t ∧ t≤ supplyRadius L ∧ ∑q∈t.primeFactors,(1:ℝ)/q≤1/16 := by
  filter_upwards [eventually_retainedBand_numeric] with L hL
  exact retainedBandProducts_conditions hL.1 hL.2.1 hL.2.2

end Ostmann.Supply

end

end OAI
