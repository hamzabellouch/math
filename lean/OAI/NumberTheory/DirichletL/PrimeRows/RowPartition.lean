import OAI.NumberTheory.DirichletL.PrimeRows.RowCount
import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalLargeTail

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def rowNorm (u : FreeRow) : ℝ := (Ideal.span {u.val}:Ideal O).absNorm

lemma rowNorm_ge_one (u : FreeRow) : 1≤rowNorm u := by
  unfold rowNorm
  have hn : (Ideal.span {u.val}:Ideal O)≠⊥ := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)

lemma finite_bounded_freeRows (H : ℝ) : {u : FreeRow | rowNorm u≤H}.Finite := by
  by_contra hs
  obtain ⟨n,hn⟩ := exists_nat_gt (128*max 1 H)
  have hinf : Set.Infinite {u : FreeRow | rowNorm u≤H} := hs
  obtain ⟨T,hT,hcard⟩ := hinf.exists_subset_card_eq n
  have hc := freeRow_count T (max 1 H) (le_max_left _ _) (fun u hu=>(hT hu).trans (le_max_right _ _))
  rw [hcard] at hc
  exact not_le_of_gt hn hc

def boundedFreeRows (H : ℝ) : Finset FreeRow := (finite_bounded_freeRows H).toFinset

@[simp] lemma mem_boundedFreeRows {H : ℝ} {u : FreeRow} : u∈boundedFreeRows H ↔ rowNorm u≤H :=
  Set.Finite.mem_toFinset _

def rowBand (A B : ℝ) : Finset FreeRow := (boundedFreeRows B).filter (fun u=>u.val≠1 ∧ A≤rowNorm u ∧ rowNorm u<B)

@[simp] lemma mem_rowBand {A B : ℝ} {u : FreeRow} :
    u∈rowBand A B ↔ u.val≠1 ∧ A≤rowNorm u ∧ rowNorm u<B := by
  simp only [rowBand,Finset.mem_filter,mem_boundedFreeRows]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.2.2.le,h⟩

def dyadicRows (A : ℝ) (n : ℕ) : Finset FreeRow := rowBand (A*(2:ℝ)^n) (A*(2:ℝ)^(n+1))

lemma mem_dyadicRows {A : ℝ} {n : ℕ} {u : FreeRow} :
    u∈dyadicRows A n ↔ u.val≠1 ∧ A*(2:ℝ)^n≤rowNorm u ∧ rowNorm u<2*(A*(2:ℝ)^n) := by
  simp only [dyadicRows,mem_rowBand,pow_succ]
  ring_nf

lemma dyadicRows_disjoint (A : ℝ) (hA : 0<A) : Pairwise (fun m n=>Disjoint (dyadicRows A m) (dyadicRows A n)) := by
  intro m n hmn
  apply Finset.disjoint_left.mpr
  intro u hm hn
  rw [mem_dyadicRows] at hm hn
  have hpow (j k : ℕ) (hjk : j<k) : 2*(A*(2:ℝ)^j)≤A*(2:ℝ)^k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.succ_le_iff.mpr hjk)
    have := mul_le_mul_of_nonneg_left hh hA.le
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using this
  rcases lt_or_gt_of_ne hmn with h|h
  · exact not_lt_of_ge ((hpow m n h).trans hn.2.1) hm.2.2
  · exact not_lt_of_ge ((hpow n m h).trans hm.2.1) hn.2.2

lemma exists_dyadicRows (A : ℝ) (hA : 0<A) (u : FreeRow) (hu : u.val≠1) (hU : A≤rowNorm u) :
    ∃n : ℕ,u∈dyadicRows A n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hA).mpr (by simpa using hU)) (by norm_num : (1:ℝ)<2)
  refine ⟨n,mem_dyadicRows.mpr ⟨hu,?_,?_⟩⟩
  · have hh := (le_div_iff₀ hA).mp hn
    simpa only [mul_comm] using hh
  · have hh := (div_lt_iff₀ hA).mp hn'
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

def dyadicRowEquiv (A : ℝ) (hA : 0<A) :
    (Σn : ℕ,dyadicRows A n) ≃ {u : FreeRow // u.val≠1 ∧ A≤rowNorm u} :=
  Equiv.ofBijective (fun p=>⟨p.2.val,(mem_dyadicRows.mp p.2.property).1,
    (le_mul_of_one_le_right hA.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans (mem_dyadicRows.mp p.2.property).2.1⟩) (by
    constructor
    · rintro ⟨m,u⟩ ⟨n,v⟩ heq
      have huv : u.val=v.val := congrArg Subtype.val heq
      have hmn : m=n := by
        by_contra h
        exact (Finset.disjoint_left.mp (dyadicRows_disjoint A hA h)) u.property (huv.symm ▸ v.property)
      subst n
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext huv))
    · intro u
      obtain ⟨n,hn⟩ := exists_dyadicRows A hA u.val u.property.1 u.property.2
      exact ⟨⟨n,⟨u.val,hn⟩⟩,rfl⟩)

theorem tsum_dyadicRows (A : ℝ) (hA : 0<A) (f : FreeRow→ℂ) (hf : Summable f) :
    Summable (fun n=>∑u∈dyadicRows A n,f u) ∧
      (∑'u : FreeRow,if u.val≠1 ∧ A≤rowNorm u then f u else 0)=
        ∑'n : ℕ,∑u∈dyadicRows A n,f u := by
  let e := dyadicRowEquiv A hA
  have hs : Summable (fun p : Σn : ℕ,dyadicRows A n=>f p.2.val) :=
    e.summable_iff.mpr (hf.subtype (fun u=>u.val≠1 ∧ A≤rowNorm u))
  have heq : (fun n : ℕ=>∑'u : dyadicRows A n,f u.val)=(fun n=>∑u∈dyadicRows A n,f u) := by
    funext n
    exact Finset.tsum_subtype _ _
  refine ⟨by simpa only [heq] using hs.sigma,?_⟩
  calc
    _ = ∑'u : {u : FreeRow // u.val≠1 ∧ A≤rowNorm u},f u.val := by
      have hh := (tsum_subtype {u : FreeRow | u.val≠1 ∧ A≤rowNorm u} f).symm
      convert hh using 1
      · apply tsum_congr
        intro u
        by_cases h : u.val≠1 ∧ A≤rowNorm u
        · simp [h]
        · simp [h]
      · rfl
    _ = ∑'p : Σn : ℕ,dyadicRows A n,f p.2.val := (e.tsum_eq (fun u=>f u.val)).symm
    _ = _ := by rw [hs.tsum_sigma];simp_rw [Finset.tsum_subtype]

end SevenEighths.ProbeHighRowFamily

end

end OAI
