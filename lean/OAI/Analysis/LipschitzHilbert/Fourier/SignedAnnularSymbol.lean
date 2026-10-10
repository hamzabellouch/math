import OAI.Analysis.LipschitzHilbert.Packets.AnnularLowerFrame
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! All signed finite annular multipliers have the same Mihlin bounds.
The proof uses only the fixed support annulus and its finite overlap. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem iteratedDeriv_tsupport_subset (q : ℝ → ℂ) (r : ℕ) :
    tsupport (iteratedDeriv r q) ⊆ tsupport q := by
  induction r with
  | zero => simp only [iteratedDeriv_zero,subset_refl]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem reassemblyDifference_tsupport :
    tsupport reassemblyDifference ⊆ {x : ℝ | 9/8≤|x| ∧ |x|≤117/64} := by
  apply closure_minimal
  · intro x hx
    exact ⟨(lt_of_not_ge (fun h => hx (reassemblyDifference_small x h))).le,
      (lt_of_not_ge (fun h => hx (reassemblyDifference_large x h))).le⟩
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)

theorem reassemblyDifference_derivative_support (r : ℕ) (x : ℝ)
    (hx : iteratedDeriv r reassemblyDifference x≠0) :
    9/8≤|x| ∧ |x|≤117/64 :=
  reassemblyDifference_tsupport (iteratedDeriv_tsupport_subset _ r (subset_closure hx))

theorem natural_closed_annulus_count (I : Finset ℕ) (x : ℝ) :
    (I.filter (fun n => 9/8≤|(3/2:ℝ)^n*x| ∧ |(3/2:ℝ)^n*x|≤117/64)).card≤3 := by
  classical
  let A := I.filter (fun n => 9/8≤|(3/2:ℝ)^n*x| ∧ |(3/2:ℝ)^n*x|≤117/64)
  change A.card≤3
  have hsep (j k : ℕ) (hjk : j+2≤k)
      (hj : 9/8≤|(3/2:ℝ)^j*x|) (hk : |(3/2:ℝ)^k*x|≤117/64) : False := by
    have hpow : (3/2:ℝ)^j*(9/4)≤(3/2:ℝ)^k := by
      calc
        _ = (3/2:ℝ)^(j+2) := by rw [pow_add]; norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hjk
    have hscale := mul_le_mul_of_nonneg_right hpow (abs_nonneg x)
    have habs (n : ℕ) : |(3/2:ℝ)^n*x|=(3/2:ℝ)^n*|x| := by
      rw [abs_mul,abs_of_pos (by positivity)]
    rw [habs] at hj hk
    nlinarith only [hj,hk,hscale]
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hjmem := (Finset.mem_filter.mp hj).2
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      have hkmem := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact hsep k j (by omega) hkmem.1 hjmem.2
      · by_contra hn
        exact hsep j k (by omega) hjmem.1 hkmem.2
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

def signedAnnularSymbol (N : ℕ) (s : ℕ → Bool) : SchwartzMap ℝ ℂ :=
  ∑ n∈Finset.range (2*N+1),
    if s n then dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'
    else -dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'

theorem signedAnnularSymbol_derivative (N r : ℕ) (s : ℕ → Bool) (x : ℝ) :
    iteratedDeriv r (signedAnnularSymbol N s) x=
      ∑ n∈Finset.range (2*N+1), if s n then
        (reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)
      else -((reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)) := by
  let q (n : ℕ) : SchwartzMap ℝ ℂ :=
    if s n then dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'
    else -dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'
  have hfun : (signedAnnularSymbol N s : ℝ → ℂ)=fun y => ∑ n∈Finset.range (2*N+1), q n y := by
    funext y
    simp only [signedAnnularSymbol,q,sum_apply]
  rw [hfun,iteratedDeriv_fun_sum (fun n _ => ((q n).smooth r).contDiffAt)]
  apply Finset.sum_congr rfl
  intro n _
  have hd : iteratedDeriv r
      (dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
        (reassemblyScale_pos N n).ne') x=
      (reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x) := by
    change iteratedDeriv r (fun y => reassemblyDifferenceSchwartz (reassemblyScale N n*y)) x=_
    rw [iteratedDeriv_comp_const_smul (reassemblyDifferenceSchwartz.smooth r)]
    rfl
  dsimp only [q]
  split_ifs
  · exact hd
  · change iteratedDeriv r (fun y => -(dilatedSlopeWindow reassemblyDifferenceSchwartz
      (reassemblyScale N n) (reassemblyScale_pos N n).ne' y)) x=_
    rw [iteratedDeriv_fun_neg,hd]

theorem signedAnnularSymbol_mihlin (N r : ℕ) (s : ℕ → Bool) (x : ℝ) :
    |x|^r*‖iteratedDeriv r (signedAnnularSymbol N s) x‖≤
      3*(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz := by
  classical
  let A := (Finset.range (2*N+1)).filter (fun n =>
    9/8≤|reassemblyScale N n*x| ∧ |reassemblyScale N n*x|≤117/64)
  let v (n : ℕ) : ℂ := if s n then
      (reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)
    else -((reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x))
  have hcard : (A.card:ℝ)≤3 := by
    have he (n : ℕ) : reassemblyScale N n*x=(3/2:ℝ)^n*((2/3:ℝ)^N*x) := by
      unfold reassemblyScale
      ring
    exact_mod_cast (show A.card≤3 by
      simpa only [A,he] using natural_closed_annulus_count (Finset.range (2*N+1)) ((2/3:ℝ)^N*x))
  have heq : (∑ n∈Finset.range (2*N+1),v n)=∑ n∈A,v n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,reassemblyDifference_derivative_support r _ h⟩)
    dsimp only [v]
    simp only [hz,smul_zero,neg_zero,ite_self]
  have hS : 0≤SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz := apply_nonneg _ _
  have hterm (n : ℕ) (hn : n∈A) :
      |x|^r*‖v n‖≤(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz := by
    have hb := (Finset.mem_filter.mp hn).2.2
    have hnorm : ‖v n‖=(reassemblyScale N n)^r*
        ‖iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)‖ := by
      dsimp only [v]
      split_ifs <;> simp only [norm_neg,norm_smul,Real.norm_eq_abs,
        abs_of_pos (pow_pos (reassemblyScale_pos N n) r)]
    rw [hnorm,←mul_assoc,←mul_pow]
    have habs : |x| *reassemblyScale N n=|reassemblyScale N n*x| := by
      rw [abs_mul,abs_of_pos (reassemblyScale_pos N n)]
      ring
    rw [habs]
    apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hb r)
      (show ‖iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)‖≤
        SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz by
        have hh := reassemblyDifferenceSchwartz.le_seminorm' ℝ 0 r (reassemblyScale N n*x)
        have he : (reassemblyDifferenceSchwartz : ℝ → ℂ)=reassemblyDifference := rfl
        rw [he] at hh
        simpa only [pow_zero,one_mul] using hh)
      (norm_nonneg _) (by positivity)
  rw [signedAnnularSymbol_derivative]
  change |x|^r*‖∑ n∈Finset.range (2*N+1),v n‖≤_
  rw [heq]
  calc
    _ ≤ |x|^r*(∑ n∈A, ‖v n‖) := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ n∈A, |x|^r*‖v n‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _n∈A, (117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz :=
      Finset.sum_le_sum hterm
    _ = (A.card:ℝ)*((117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz) := by simp
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hcard (show
      0≤(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz by positivity)]

def signedAnnularMihlinConstant : ℝ :=
  ∑ r∈Finset.range 5,
    3*(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz

theorem signedAnnularMihlinConstant_nonneg : 0≤signedAnnularMihlinConstant := by
  exact Finset.sum_nonneg (fun r _ => by positivity)

theorem signedAnnularSymbol_mihlin_four (N r : ℕ) (hr : r≤4) (s : ℕ → Bool) (x : ℝ) :
    |x|^r*‖iteratedDeriv r (signedAnnularSymbol N s) x‖≤signedAnnularMihlinConstant := by
  apply (signedAnnularSymbol_mihlin N r s x).trans
  unfold signedAnnularMihlinConstant
  exact Finset.single_le_sum
    (f:=fun i : ℕ => (3:ℝ)*(117/64:ℝ)^i*SchwartzMap.seminorm ℝ 0 i reassemblyDifferenceSchwartz)
    (fun i _ => by positivity)
    (Finset.mem_range.mpr (show r<5 by omega))

theorem signedAnnularSymbol_norm (N : ℕ) (s : ℕ → Bool) (x : ℝ) :
    ‖signedAnnularSymbol N s x‖≤signedAnnularMihlinConstant := by
  simpa only [pow_zero,one_mul,iteratedDeriv_zero] using
    signedAnnularSymbol_mihlin_four N 0 (by omega) s x

end LipschitzHilbert.PacketRepresentation

end

end OAI
