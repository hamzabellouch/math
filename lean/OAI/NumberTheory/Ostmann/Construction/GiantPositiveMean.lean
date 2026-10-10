import OAI.NumberTheory.Ostmann.Construction.FavorableBlock
import OAI.NumberTheory.Ostmann.Construction.GiantWeightedError
import OAI.NumberTheory.Ostmann.Construction.GiantWindowScale
import OAI.NumberTheory.Ostmann.Construction.PrimeLogBlockMass

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_favorable_giant_mean (d : Decomposition) {δ : ℝ} (hδ : 0<δ)
    (r : ℝ) (hr : 4≤r) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ, ∀ P : Finset ℕ,
      Real.exp ((1/20:ℝ)*L)≤G → G≤Real.exp ((9/10:ℝ)*L) →
      P⊆Supply.nonsparsePrimes d δ L →
      (∀p∈P,G≤Real.log p ∧ Real.log p≤G+favorableBlockWidth L) →
      (1/10:ℝ)*favorableBlockWidth L≤primeLogMass P →
      (δ/(20*Real.sqrt 2))*favorableBlockWidth L≤
        ∑p∈P,(Real.log p/(p:ℝ))*giantEmpiricalMean d (giantWindowScale r G L) p := by
  let a := δ/(20*Real.sqrt 2)
  let C := collisionConstant 4
  let D := 1+2*(Real.log 4+4)
  have ha : 0<a := div_pos hδ (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
  have hC : 0<C := collisionConstant_pos 4
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_giant_weighted_error d)
  have hscale := giantWindowScale_eventually r hr M
  have hhlarge := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop D
  have hratio : ∀ᶠ L : ℝ in atTop, 2*C/a^2≤favorableBlockWidth L/L := by
    have h := (tendsto_exp_mul_div_rpow_atTop 1 (1/100) (by norm_num)).eventually_ge_atTop (2*C/a^2)
    simpa only [Real.rpow_one,favorableBlockWidth] using h
  filter_upwards [hscale,hhlarge,hratio,eventually_ge_atTop (1:ℝ)] with L hscale hlarge hratio hL
  intro G P hGlo hGhi hP hwindow hmass
  let X := giantWindowScale r G L
  let h := favorableBlockWidth L
  have hh : 0<h := Real.exp_pos _
  have hL0 : 0<L := by linarith
  obtain ⟨hXM,hlog,hloglog,hcut⟩ := hscale G hGlo hGhi
  have hprimes (p : ℕ) (hp : p∈P) : p.Prime := (Finset.mem_filter.mp (hP hp)).2.1
  have hQ : P⊆(collisionScale 4 X).primesLE := by
    intro p hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_,hprimes p hp⟩
    have hp0 : (0:ℝ)<p := by exact_mod_cast (hprimes p hp).pos
    have he := Real.exp_le_exp.mpr (hwindow p hp).2
    rw [Real.exp_log hp0] at he
    change p≤⌊Real.sqrt (X:ℝ)/(Real.log (X:ℝ))^5⌋₊
    apply (Nat.le_floor_iff (div_nonneg (Real.sqrt_nonneg _) (pow_pos hlog 5).le)).mpr
    exact he.trans hcut
  have herror := hM X hXM P hQ
  have hG1 : 1≤G := by
    have he : 1≤Real.exp ((1/20:ℝ)*L) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by positivity : (0:ℝ)≤(1/20:ℝ)*L)
    exact he.trans hGlo
  have hWupper := primeLogMass_block_le P G h hG1 hh.le
    (fun p hp => ⟨hprimes p hp,(hwindow p hp).1,(hwindow p hp).2⟩)
  have hW2 : primeLogMass P≤2*h := by change D≤h at hlarge; dsimp [D] at hlarge; linarith
  have hW0 : 0≤primeLogMass P := Finset.sum_nonneg
    (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  let err := ∑p∈P,(Real.log p/(p:ℝ))*|giantEmpiricalMean d X p-giantSupportMean d p|
  have hsq : err^2≤(2*h)*(C*L) := by
    calc
      _ ≤ primeLogMass P*(C*Real.log (Real.log (X:ℝ))) := herror
      _ ≤ primeLogMass P*(C*L) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hloglog hC.le) hW0
      _ ≤ _ := mul_le_mul_of_nonneg_right hW2 (mul_pos hC hL0).le
  have hdiv := (le_div_iff₀ hL0).mp hratio
  have hmul := mul_le_mul_of_nonneg_left hdiv (sq_nonneg a)
  have he : a^2*(2*C/a^2*L)=2*C*L := by field_simp
  rw [he] at hmul
  have hsmall : (2*h)*(C*L)≤(a*h)^2 := by
    have hm := mul_le_mul_of_nonneg_left hmul hh.le
    nlinarith
  have herr : err≤a*h := by
    have hp : 0<a*h := mul_pos ha hh
    nlinarith [hsq.trans hsmall]
  have hmean := giant_weighted_mean_lower d X P hδ.le (fun p hp => by
    have ht := (Finset.mem_filter.mp (hP hp)).2
    exact ⟨ht.1,ht.2.2.2.1,ht.2.2.2.2.1,ht.2.2.2.2.2⟩)
  change (δ/Real.sqrt 2)*primeLogMass P-err≤_ at hmean
  have hδsqrt : 0<δ/Real.sqrt 2 := div_pos hδ (Real.sqrt_pos.mpr (by norm_num))
  have hlow := mul_le_mul_of_nonneg_left hmass hδsqrt.le
  have heq : (δ/Real.sqrt 2)*((1/10:ℝ)*h)=2*a*h := by dsimp [a]; ring
  rw [heq] at hlow
  change a*h≤_
  linarith

end Ostmann.Construction

end

end OAI
