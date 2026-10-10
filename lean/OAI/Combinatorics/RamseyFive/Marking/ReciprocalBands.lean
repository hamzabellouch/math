import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BandCoreRanks
import OAI.Combinatorics.RamseyFive.Marking.MarkingEndpoints

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators

def BandCondition (σ K u : ℝ) (i : Fin 7) : Prop :=
  if i.val%2=0 then |u-((i.val/2+1:ℕ):ℝ)*σ|≤K
  else ((i.val/2+1:ℕ):ℝ)*σ+K<u ∧ u<((i.val/2+2:ℕ):ℝ)*σ-K

lemma exists_reciprocal_band {σ K u : ℝ} (hK : 0≤K)
    (hlo : σ≤u) (hhi : u≤4*σ) : ∃ i : Fin 7,BandCondition σ K u i := by
  by_cases h0 : u≤σ+K
  · refine ⟨0,?_⟩
    simp only [BandCondition];norm_num
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  by_cases h1 : u<2*σ-K
  · refine ⟨1,?_⟩
    norm_num [BandCondition]
    exact ⟨by linarith,h1⟩
  by_cases h2 : u≤2*σ+K
  · refine ⟨2,?_⟩
    norm_num [BandCondition]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  by_cases h3 : u<3*σ-K
  · refine ⟨3,?_⟩
    norm_num [BandCondition]
    exact ⟨by linarith,h3⟩
  by_cases h4 : u≤3*σ+K
  · refine ⟨4,?_⟩
    norm_num [BandCondition]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  by_cases h5 : u<4*σ-K
  · refine ⟨5,?_⟩
    norm_num [BandCondition]
    exact ⟨by linarith,h5⟩
  · refine ⟨6,?_⟩
    norm_num [BandCondition]
    exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma popular_reciprocal_caps {q A B : ℝ} {r s : ℕ} (hq : 1≤q)
    (hr : 1≤r) (hr4 : r≤4) (hrs : r+s≤5)
    (hA : A≤32*q^s) (hB : B≤32*q^r) :
    Real.log q≤(r:ℝ)*Real.log q ∧ (r:ℝ)*Real.log q≤4*Real.log q ∧
    A≤32*Real.exp (5*Real.log q-(r:ℝ)*Real.log q) ∧
    B≤32*Real.exp ((r:ℝ)*Real.log q) := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hσ := Real.log_nonneg hq
  have he (n : ℕ) : Real.exp ((n:ℝ)*Real.log q)=q^n := by
    rw [Real.exp_nat_mul,Real.exp_log hq0]
  refine ⟨?_,?_,?_,?_⟩
  · have : (1:ℝ)≤r := by exact_mod_cast hr
    nlinarith
  · have : (r:ℝ)≤4 := by exact_mod_cast hr4
    nlinarith
  · have ht : (s:ℝ)*Real.log q≤5*Real.log q-(r:ℝ)*Real.log q := by
      have : (r:ℝ)+s≤5 := by exact_mod_cast hrs
      nlinarith
    exact hA.trans (mul_le_mul_of_nonneg_left (by rw [←he s];exact Real.exp_le_exp.mpr ht) (by norm_num))
  · simpa only [he] using hB

lemma high_rank_cases (r s : Fin 5) (h : 5<r.val+s.val) :
    (r.val=3 ∧ s.val=3) ∨ r.val=4 ∨ s.val=4 := by
  have := r.isLt
  have := s.isLt
  omega

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance bandsPointDecEq : DecidableEq (ℙ K V) := Classical.decEq _
local instance bandsDualDecEq : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance bandsPairDecEq : DecidableEq (FlagPair K V) := Classical.decEq _

omit [Finite K] [Fintype (ℙ K V)] in
lemma zero_level_memberships (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (b : ℙ K (Dual K V)) : memberships W (levelSet W 0) b=0 := by
  unfold memberships
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hy,hb⟩:=Finset.mem_filter.mp hy
  have hw : finrank K (W y)=0 := (Finset.mem_filter.mp hy).2
  have hz : W y=⊥ := Submodule.finrank_eq_zero.mp hw
  rw [hz] at hb
  have he := b.finrank_submodule
  rw [le_antisymm hb bot_le] at he
  simp at he

lemma typed_popular_rank_pos (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (h : (typedDomain W r true).Nonempty) : 1≤r.val := by
  by_contra hh
  have hr : r.val=0 := by omega
  have hl : chooseLevel W r.val=0 := by have := chooseLevel_le W r.val;omega
  have hn:=typedDomain_level_nonempty W r true h
  obtain ⟨z,hz⟩:=h
  unfold typedDomain at hz
  rw [ite_eq_left hn] at hz
  simp only [ite_true] at hz
  have hb:=((mem_popularDomain _ _ _ _).mp hz).2.1
  rw [hl,zero_level_memberships,Nat.cast_zero] at hb
  have hp : (0:ℝ)<(levelSet W 0).card := by exact_mod_cast (hl ▸ hn).card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  exact (div_pos hp (by positivity)).not_ge hb

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators

lemma closed_band_slack {σ width u s : ℝ} {b : Fin 7}
    (hband : BandCondition σ width u b) (heven : b.val%2=0)
    (hsmall : Real.log 32+width+3*s<σ) :
    Real.log (32*Real.exp (5*σ-u))+3*s<(6-((b.val/2+1:ℕ):ℝ))*σ ∧
    Real.log (32*Real.exp u)+3*s<(6-((5-(b.val/2+1):ℕ):ℝ))*σ := by
  have hr : b.val/2+1≤5 := by have := b.isLt;omega
  have h:=hband
  simp only [BandCondition,heven,ite_true,abs_le] at h
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp,
    Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
  rw [Nat.cast_sub hr]
  norm_num only [Nat.cast_ofNat]
  constructor <;> nlinarith

lemma open_band_slack {σ width u s : ℝ} {b : Fin 7}
    (hband : BandCondition σ width u b) (hodd : b.val%2≠0)
    (hwide : Real.log 32+3*s<width) :
    Real.log (32*Real.exp (5*σ-u))+3*s<(6-((b.val/2+2:ℕ):ℝ))*σ ∧
    Real.log (32*Real.exp u)+3*s<(6-((6-(b.val/2+2):ℕ):ℝ))*σ := by
  have hr : b.val/2+2≤6 := by have := b.isLt;omega
  have h:=hband
  simp only [BandCondition,hodd,ite_false] at h
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp,
    Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
  rw [Nat.cast_sub hr]
  simp only [Nat.cast_add,Nat.cast_ofNat] at h ⊢
  constructor <;> nlinarith

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem closed_reciprocal_ranks (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V)))) (u s width : ℝ) (b : Fin 7)
    (hs : 2 ≤ s) (hband : BandCondition (Real.log (Nat.card K)) width u b)
    (heven : b.val%2=0) (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K)) :
    (∀ a∈goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s,
      b.val/2+1≤finrank K (firstCore p Projectivization.rep a)) ∧
    (∀ y∈goodFirstEndpoints (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4) s,
      5-(b.val/2+1)≤finrank K (secondCore (K:=K) p Projectivization.rep y)) := by
  obtain ⟨ha,hb⟩:=closed_band_slack hband heven hsmall
  exact ⟨fun a h=>goodFirst_integer_rank hdim p _ s (by positivity) hs _ ha a h,
    fun y h=>goodSecond_integer_rank hdim p _ s (by positivity) hs _ hb y h⟩

theorem open_reciprocal_ranks (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V)))) (u s width : ℝ) (b : Fin 7)
    (hs : 2 ≤ s) (hband : BandCondition (Real.log (Nat.card K)) width u b)
    (hodd : b.val%2≠0) (hwide : Real.log 32+3*s<width) :
    (∀ a∈goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s,
      b.val/2+2≤finrank K (firstCore p Projectivization.rep a)) ∧
    (∀ y∈goodFirstEndpoints (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4) s,
      6-(b.val/2+2)≤finrank K (secondCore (K:=K) p Projectivization.rep y)) := by
  obtain ⟨ha,hb⟩:=open_band_slack hband hodd hwide
  exact ⟨fun a h=>goodFirst_integer_rank hdim p _ s (by positivity) hs _ ha a h,
    fun y h=>goodSecond_integer_rank hdim p _ s (by positivity) hs _ hb y h⟩
end SharpRamseyFive.Marking

end

end OAI
