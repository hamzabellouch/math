import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ShellGridScales

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
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinarySparseShell
open Filter Finset OrdinaryNarrowGrid OrdinarySparsePowerScales OrdinarySparseTerminal
  OrdinarySparseNumerics OrdinarySmoothRough OrdinaryCorrelations OrdinarySelbergWeights

lemma explicit_density_cost (J : ℕ) (hJ : 0<J) :
    4/((24*J:ℕ):ℝ)+4*((24*J:ℕ):ℝ)/((576*J^2:ℕ):ℝ)+
      6*((576*J^2:ℕ):ℝ)/(((576*J^2:ℕ):ℝ)*((24*J:ℕ):ℝ)) < 1/(J:ℝ) := by
  have hJ' : (0:ℝ)<J := by exact_mod_cast hJ
  push_cast
  have he : 4/(24*(J:ℝ))+4*(24*J)/(576*(J:ℝ)^2)+
      6*(576*(J:ℝ)^2)/((576*(J:ℝ)^2)*(24*J)) = 7/(12*(J:ℝ)) := by
    field_simp
    ring
  rw [he]
  have hh : 7/(12*(J:ℝ)) < 1/(J:ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) hJ').mpr
    nlinarith
  exact hh

theorem polynomial_sparse_shell (J : ℕ) (hJ : 0<J)
    {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (hNP : UniformlyNonpretentious f) :
    let d := 24*J
    let k := 576*J^2+96*J+4
    ∀ᶠ n : ℕ in atTop, ∀ H : ℕ, 2^(8*k*n) ≤ H → H ≤ 2^(8*k*(n+1)) →
      ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (2^(d*n)) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) → T.card ≤ 2^n →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T < 2120/(J:ℝ) := by
  let d := 24*J
  let s := 576*J^2
  let q := s
  let k := 576*J^2+96*J+4
  let η : ℝ := 2120/(J:ℝ)
  have hJ' : (0:ℝ)<J := by exact_mod_cast hJ
  have hη : 0<η := by dsimp [η]; positivity
  have hd : 0<d := by dsimp [d]; positivity
  have hs : 1≤ s := by
    have hpow : 0<J^2 := by positivity
    dsimp [s]
    omega
  have hq : 0<q := hs
  have hk : s+4*d+4≤k := by dsimp [s,d,k]; omega
  have hcost : 4/(d:ℝ)+4*(d:ℝ)/s+6*(s:ℝ)/((q:ℝ)*d)<η/2120 := by
    have hh := explicit_density_cost J hJ
    have he : η/2120 = 1/(J:ℝ) := by dsimp [η]; ring
    rw [he]
    exact hh
  let C : ℝ := (((s*q:ℕ):ℝ)^2/2*(264/((d:ℝ)/4)+1)*(44/((d:ℝ)/4)+1))
  have hC : 0<C := by
    have hs' : 0<s := hs
    unfold C
    positivity
  let ε := Real.sqrt (η/(4*C))
  have hε : 0<ε := Real.sqrt_pos.2 (by positivity)
  have heq : C*ε^2=η/4 := by
    dsimp [ε]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  change ∀ᶠ n : ℕ in atTop, _
  filter_upwards [shell_grid_bound hf hm hNP d s q k hd hs hq hk hε
    (by positivity : 0<η/2120)] with n hn
  intro H hlo hhi P hP T hsep hT hcard
  apply (hn H hlo hhi P hP T hsep hT hcard).trans_lt
  change C*ε^2+530*(_+η/2120)<η
  rw [heq]
  linarith only [hcost,hη]

lemma all_lengths_of_shell {f : ℕ→ℂ} {η : ℝ} (d k : ℕ) (hk : 0<k)
    (hgood : ∀ᶠ n : ℕ in atTop, ∀ H : ℕ, 2^(8*k*n)≤H → H≤2^(8*k*(n+1)) →
      ∀P : Finset ℕ, P⊆Nat.primesLE (2^(d*n)) →
      ∀T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y=>1≤|x-y|) →
      (∀t∈T, |t|≤(2:ℝ)^(9*k*n)) → T.card≤2^n →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T<η) :
    ∀ᶠ H : ℕ in atTop, ∀ (P : Finset ℕ),
      (∀ p∈P, Nat.Prime p ∧ p^(16*k) ≤ H^d) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (H:ℝ)) → T.card^(16*k) ≤ H →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T < η := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  filter_upwards [eventually_ge_atTop (2^(8*k*max N 8))] with H hH
  have hb : 1 < 2^(8*k) := one_lt_pow₀ (by norm_num) (by positivity)
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < 2^(8*k*max N 8)) hH
  let n := Nat.log (2^(8*k)) H
  have hn : max N 8 ≤ n := by
    apply Nat.le_log_of_pow_le hb
    simpa only [←pow_mul] using hH
  have hn8 : 8 ≤ n := (le_max_right _ _).trans hn
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hlo : 2^(8*k*n) ≤ H := by
    simpa only [←pow_mul] using Nat.pow_log_le_self (2^(8*k)) hHpos.ne'
  have hhi : H ≤ 2^(8*k*(n+1)) := by
    simpa only [←pow_mul] using (Nat.lt_pow_succ_log_self hb H).le
  have hcardpow : H ≤ (2^n)^(16*k) := by
    apply hhi.trans
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    nlinarith
  intro P hP T hsep hT hcard
  have hPS : P ⊆ Nat.primesLE (2^(d*n)) := by
    intro p hp
    refine Nat.mem_primesLE.mpr ⟨?_,(hP p hp).1⟩
    apply (Nat.pow_le_pow_iff_left (by positivity : 16*k ≠ 0)).mp
    apply (hP p hp).2.trans
    calc
      H^d ≤ ((2^n)^(16*k))^d := Nat.pow_le_pow_left hcardpow d
      _ = (2^(d*n))^(16*k) := by
        simp only [←pow_mul]
        congr 1
        ring
  have hcard' : T.card ≤ 2^n :=
    (Nat.pow_le_pow_iff_left (by positivity : 16*k ≠ 0)).mp (hcard.trans hcardpow)
  have hheight : ∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n) := by
    intro t ht
    apply (hT t ht).trans
    have hle : H ≤ 2^(9*k*n) := by
      apply hhi.trans
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith
    exact_mod_cast hle
  exact hN n hNn H hlo hhi P hPS T hsep hheight hcard'

theorem polynomial_sparse_all_lengths (J : ℕ) (hJ : 0<J)
    {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (hNP : UniformlyNonpretentious f) :
    let d := 24*J
    let r := 16*(576*J^2+96*J+4)
    ∀ᶠ H : ℕ in atTop, ∀ (P : Finset ℕ),
      (∀ p∈P, Nat.Prime p ∧ p^r ≤ H^d) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (H:ℝ)) → T.card^r ≤ H →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T < 2120/(J:ℝ) := by
  exact all_lengths_of_shell (24*J) (576*J^2+96*J+4) (by omega)
    (polynomial_sparse_shell J hJ hf hm hNP)

lemma polynomial_exponent_bound (J : ℕ) (hJ : 0<J) :
    16*(576*J^2+96*J+4) ≤ 10816*J^2 := by
  have hJJ : J≤J^2 := Nat.le_self_pow (by decide) J
  have hp : 1≤J^2 := Nat.one_le_pow _ _ hJ
  nlinarith

end OrdinarySparseShell

end

end OAI
