import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SubspacePointsEquiv
import OAI.Combinatorics.RamseyFive.Geometry.Failure

namespace OAI

namespace SharpRamseyFive.CoreGeometry

section
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma rep_mem_iff (a : ℙ K V) (W : Submodule K V) :
    a.rep∈W ↔ a.submodule≤W := by
  rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]

theorem subspace_mass_cap [Finite K] [Fintype (ℙ K V)]
    (p : Law (ℙ K V)) (W : Submodule K V) (B : Finset (ℙ K V))
    (c δ ε : ℝ) (hc : 0≤c)
    (hlight : ∀ a,a∉B → p a≤c)
    (hbad : (∑ a∈B,p a)≤δ)
    (hout : (∑ a,if a.rep∉W then p a else 0)≤ε) :
    1-ε-δ≤c*(∑ i∈Finset.range (finrank K W),(Nat.card K:ℝ)^i) := by
  have hp (a : ℙ K V) : p a≤(if a.rep∈W then c else 0)+
      (if a.rep∉W then p a else 0)+(if a∈B then p a else 0) := by
    by_cases hW : a.rep∈W <;> by_cases hB : a∈B <;> simp only [hW,hB,
      not_true_eq_false,not_false_eq_true,ite_true,ite_false]
    · linarith [p.nonneg a]
    · simpa using hlight a hB
    · linarith [p.nonneg a]
    · simp
  have hs := Finset.sum_le_sum (fun a (_ha : a∈(Finset.univ : Finset (ℙ K V))) => hp a)
  rw [p.sum_one,Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
  have hb : (∑ a,if a∈B then p a else 0)=∑ a∈B,p a := by
    rw [←Finset.sum_filter]; simp only [Finset.filter_univ_mem]
  have hw : (∑ a : ℙ K V,if a.rep∈W then c else 0)=
      c*(∑ i∈Finset.range (finrank K W),(Nat.card K:ℝ)^i) := by
    have hn : (Finset.univ.filter fun a : ℙ K V => a.rep∈W).card=
        ∑ i∈Finset.range (finrank K W),Nat.card K^i := by
      rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card]
      rw [Nat.card_congr (Equiv.subtypeEquivRight fun a => rep_mem_iff a W)]
      exact SharpRamseyFive.ProjectiveIncidence.card_subspacePoints W
    rw [←Finset.sum_filter,Finset.sum_const, nsmul_eq_mul,hn,mul_comm]
    norm_cast
  rw [hb,hw] at hs
  linarith

lemma geometric_card_bound (q : ℝ) (hq : 2≤q) (r : ℕ) :
    (∑ i∈Finset.range r,q^i)≤2*q^(r-1) := by
  cases r with
  | zero => simp
  | succ r =>
    simp only [Nat.add_sub_cancel]
    have h := geom_sum_mul q (r+1)
    rw [pow_succ] at h
    have hp : 0≤q^r := pow_nonneg (by linarith) _
    have hh : q*q^r≤2*q^r*(q-1) := by nlinarith
    have hq' : 0<q-1 := by linarith
    nlinarith

theorem core_dimension_mass [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
    (p : Law (ℙ K V)) (ρ c δ : ℝ) (hρ : 0≤ρ) (hc : 0≤c)
    (B : Finset (ℙ K V)) (hlight : ∀ a,a∉B → p a≤c)
    (hbad : (∑ a∈B,p a)≤δ) :
    1-(finrank K V:ℝ)*ρ-δ≤c*(∑ i∈Finset.range
      (finrank K (core (K := K) p Projectivization.rep ρ)),(Nat.card K:ℝ)^i) := by
  exact subspace_mass_cap p _ B c δ _ hc hlight hbad (core_failure p _ ρ hρ)

end

section
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical

lemma rank_from_light_mass {q A s : ℝ} {r : ℕ} (hq : 2≤q) (hA : 0<A)
    (hs : 2 ≤ s)
    (hmass : (191/200:ℝ)≤(Real.exp (2*s)*A/q^4)*(∑ i∈Finset.range r,q^i)) :
    ⌈5-(Real.log A+3*s)/Real.log q⌉₊≤r := by
  have hq0 : 0<q := by linarith
  have hlogq : 0<Real.log q := Real.log_pos (by linarith)
  have hr : 1≤r := by
    by_contra hn
    have hz : r=0 := by omega
    norm_num [hz] at hmass
  have hc : 0<Real.exp (2*s)*A/q^4 := by positivity
  have he : (191/200:ℝ)≤2*(Real.exp (2*s)*A/q^4)*q^(r-1) := by
    have h := mul_le_mul_of_nonneg_left (geometric_card_bound q hq r) hc.le
    exact hmass.trans (by convert h using 1; ring)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<191/200) he
  have hr0 : q^(r-1)≠0 := ne_of_gt (pow_pos hq0 _)
  rw [Real.log_mul (by positivity : (2:ℝ)*(Real.exp (2*s)*A/q^4)≠0) hr0,
    Real.log_mul (by norm_num : (2:ℝ)≠0) hc.ne',Real.log_div (by positivity)
      (by positivity : q^4≠0),Real.log_mul (Real.exp_ne_zero _) hA.ne',
    Real.log_exp,Real.log_pow,Real.log_pow] at hl
  rw [Nat.cast_sub hr] at hl
  norm_num only [Nat.cast_one,Nat.cast_ofNat] at hl
  have hconstant : Real.log 2-Real.log (191/200:ℝ)≤ s := by
    rw [←Real.log_div (by norm_num : (2:ℝ)≠0) (by norm_num : (191/200:ℝ)≠0)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2/(191/200))
    linarith
  apply Nat.ceil_le.mpr
  apply (mul_le_mul_iff_left₀ hlogq).mp

  have heq : (5-(Real.log A+3*s)/Real.log q)*Real.log q=
      5*Real.log q-(Real.log A+3*s) := by field_simp
  rw [heq]
  nlinarith

theorem core_dimension_lower {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] (hdim : finrank K V=5)
    (p : Law (ℙ K V)) (A s : ℝ) (hA : 0<A) (hs : 2 ≤ s)
    (B : Finset (ℙ K V))
    (hlight : ∀ a,a∉B → p a≤Real.exp (2*s)*A/(Nat.card K:ℝ)^4)
    (hbad : (∑ a∈B,p a)≤1/50) :
    ⌈5-(Real.log A+3*s)/Real.log (Nat.card K)⌉₊≤
      finrank K (core (K := K) p Projectivization.rep (1/200)) := by
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  apply rank_from_light_mass hq hA hs
  have h := core_dimension_mass p (1/200) (Real.exp (2*s)*A/(Nat.card K:ℝ)^4)
    (1/50) (by norm_num) (by positivity) B hlight hbad
  rw [hdim] at h
  norm_num at h ⊢
  exact h
end

section
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def InRectangle (U : Submodule K (Module.Dual K V)) (a : V)
    (b : Module.Dual K V) : Prop := a∈U.dualCoannihilator ∧ b∈U

lemma orthogonal_rank_sum (U : Submodule K (Module.Dual K V)) (W : Submodule K V)
    (horth : U≤W.dualAnnihilator) : finrank K U+finrank K W≤finrank K V := by
  have hm := Submodule.finrank_mono horth
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

theorem open_band_impossible (hdim : finrank K V=5) (r : ℕ)
    (U : Submodule K (Module.Dual K V)) (W : Submodule K V)
    (hU : r≤finrank K U) (hW : 6-r≤finrank K W) (hr : r≤6)
    (horth : U≤W.dualAnnihilator) : False := by
  have h := orthogonal_rank_sum U W horth
  omega

lemma integer_band_complement (hdim : finrank K V=5) (r : ℕ)
    (U : Submodule K (Module.Dual K V)) (W : Submodule K V)
    (hU : r≤finrank K U) (hW : 5-r≤finrank K W) (hr : r≤5)
    (horth : U≤W.dualAnnihilator) : U=W.dualAnnihilator := by
  apply Submodule.eq_of_le_of_finrank_eq horth
  have hm := Submodule.finrank_mono horth
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

theorem integer_band_rectangle (hdim : finrank K V=5) (r : ℕ)
    (U : Submodule K (Module.Dual K V)) (W : Submodule K V)
    (hU : r≤finrank K U) (hW : 5-r≤finrank K W) (hr : r≤5)
    (horth : U≤W.dualAnnihilator) (a c : V) (b y : Module.Dual K V)
    (ha : a∈U.dualCoannihilator) (hb : b∈U) (hc : c∈W)
    (hy : y∈W.dualAnnihilator) : InRectangle U a b ∧ InRectangle U c y := by
  refine ⟨⟨ha,hb⟩,?_,?_⟩
  · apply (Submodule.mem_dualCoannihilator c).mpr
    intro f hf
    exact (Submodule.mem_dualAnnihilator f).mp (horth hf) c hc
  · rw [integer_band_complement hdim r U W hU hW hr horth]
    exact hy

theorem high_band_rectangles (hdim : finrank K V=5)
    (U : Submodule K (Module.Dual K V)) (W : Submodule K V)
    (hU : 2≤finrank K U) (hW : 2≤finrank K W)
    (horth : U≤W.dualAnnihilator) (a c : V) (b y : Module.Dual K V)
    (ha : a∈U.dualCoannihilator) (hb : b∈U) (hc : c∈W)
    (hy : y∈W.dualAnnihilator) (hay : y a=0) :
    (InRectangle U a b ∧ InRectangle U c y) ∨
      (InRectangle W.dualAnnihilator a b ∧ InRectangle W.dualAnnihilator c y) := by
  by_cases hyU : y∈U
  · left
    refine ⟨⟨ha,hb⟩,?_,hyU⟩
    apply (Submodule.mem_dualCoannihilator c).mpr
    intro f hf
    exact (Submodule.mem_dualAnnihilator f).mp (horth hf) c hc
  · right
    let S := U⊔Submodule.span K {y}
    have hUS : U<S := by
      apply lt_of_le_of_ne le_sup_left
      intro he
      apply hyU
      rw [he]
      exact (show Submodule.span K {y}≤S from le_sup_right)
        (Submodule.subset_span (Set.mem_singleton y))
    have hSV : S≤W.dualAnnihilator := by
      apply sup_le horth
      rw [Submodule.span_singleton_le_iff_mem]; exact hy
    have hS : S=W.dualAnnihilator := by
      apply Submodule.eq_of_le_of_finrank_eq hSV
      have ht := Submodule.finrank_lt_finrank_of_lt hUS
      have hm := Submodule.finrank_mono hSV
      have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
      omega
    have haS : a∈S.dualCoannihilator := by
      apply (Submodule.mem_dualCoannihilator a).mpr
      have hle : S≤LinearMap.ker (Module.Dual.eval K V a) := by
        apply sup_le
        · intro f hf
          exact (Submodule.mem_dualCoannihilator a).mp ha f hf
        · rw [Submodule.span_singleton_le_iff_mem]; exact hay
      intro f hf
      exact hle hf
    refine ⟨⟨?_,horth hb⟩,?_,hy⟩
    · rwa [hS] at haS
    · apply (Submodule.mem_dualCoannihilator c).mpr
      intro f hf
      exact (Submodule.mem_dualAnnihilator f).mp hf c hc
end

open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}

def RectangleCharge (U W : Fin n → Submodule K (Module.Dual K V))
    (x : Fin n → V × Module.Dual K V) (i j : Fin n) : Prop :=
  i<j ∧ ((InRectangle (U i) (x i).1 (x i).2 ∧ InRectangle (U i) (x j).1 (x j).2) ∨
    (InRectangle (W j) (x i).1 (x i).2 ∧ InRectangle (W j) (x j).1 (x j).2))

theorem rectangle_charge_count (U W : Fin n → Submodule K (Module.Dual K V))
    (x : Fin n → V × Module.Dual K V) (M : ℝ)
    (hocc : ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (x i).1 (x i).2 then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,if RectangleCharge U W x i j then (1:ℝ) else 0)≤2*n*M := by
  have ht (i j : Fin n) : (if RectangleCharge U W x i j then (1:ℝ) else 0)≤
      (if InRectangle (U i) (x j).1 (x j).2 then 1 else 0)+
      (if InRectangle (W j) (x i).1 (x i).2 then 1 else 0) := by
    by_cases h : RectangleCharge U W x i j
    · simp only [h,ite_true]
      rcases h.2 with h|h
      · simp only [h.2,ite_true]; split_ifs <;> norm_num
      · simp only [h.1,ite_true]; split_ifs <;> norm_num
    · simp only [h,ite_false]; split_ifs <;> norm_num
  calc
    _ ≤ ∑ i,∑ j,((if InRectangle (U i) (x j).1 (x j).2 then (1:ℝ) else 0)+
        (if InRectangle (W j) (x i).1 (x i).2 then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = (∑ i,∑ j,if InRectangle (U i) (x j).1 (x j).2 then (1:ℝ) else 0)+
        ∑ j,∑ i,if InRectangle (W j) (x i).1 (x i).2 then 1 else 0 := by
      simp only [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    _ ≤ (∑ _i : Fin n,M)+(∑ _j : Fin n,M) := add_le_add
      (Finset.sum_le_sum fun i _ => hocc (U i)) (Finset.sum_le_sum fun j _ => hocc (W j))
    _ = _ := by simp; ring

theorem expected_rectangle_charge {Ω : Type*} [Fintype Ω] (p : Law Ω)
    (U W : Ω → Fin n → Submodule K (Module.Dual K V))
    (x : Ω → Fin n → V × Module.Dual K V) (M : ℝ)
    (hocc : ∀ ω,0<p ω → ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (x ω i).1 (x ω i).2 then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,∑ ω,p ω*(if RectangleCharge (U ω) (W ω) (x ω) i j then (1:ℝ) else 0))≤
      2*n*M := by
  have ht (ω : Ω) : p ω*(∑ i,∑ j,if RectangleCharge (U ω) (W ω) (x ω) i j then (1:ℝ) else 0)≤
      p ω*(2*n*M) := by
    by_cases hp : p ω=0
    · simp only [hp,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (rectangle_charge_count _ _ _ M
        (hocc ω (lt_of_le_of_ne (p.nonneg ω) (Ne.symm hp)))) (p.nonneg ω)
  calc
    _ = ∑ ω,p ω*(∑ i,∑ j,if RectangleCharge (U ω) (W ω) (x ω) i j then (1:ℝ) else 0) := by
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset Ω))]
    _ ≤ ∑ ω,p ω*(2*n*M) := Finset.sum_le_sum fun ω _ => ht ω
    _ = _ := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.CoreGeometry

end OAI
