import OAI.NumberTheory.Jacobsthal.Primes.WeightedPrimeMultiplePairs
import OAI.NumberTheory.Jacobsthal.Sieve.HypotheticalResidues

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosHypotheticalTag
open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts
attribute [local instance] Classical.decEq

theorem hypothetical_small_parameters (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hp : p ∉ small) :
    parameterCandidates Y small (hypotheticalClass a r p) r d = parameterCandidates Y small a r d := by
  ext m
  simp only [parameterCandidates, Finset.mem_filter]
  apply and_congr_right
  intro _hI
  apply and_congr_right
  intro _hdiv
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  have hsp : s ≠ p := by intro h; subst s; exact hp hs
  rw [hypothetical_other a r p s hsp]

theorem hypothetical_count_parameters (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hd : Squarefree d) (hp : p.Prime)
    (hD : r.den.Coprime p) (hsmall : p ∉ small)
    (hother : ∀ s ∈ d.primeFactors, s ≠ p → aligns (fun u => (a u : ℤ)) r s) :
    modulusCount Y small (hypotheticalClass a r p) d = ((parameterCandidates Y small a r d).card : ℤ) := by
  have hall : ∀ s ∈ d.primeFactors, aligns (fun u => (hypotheticalClass a r p u : ℤ)) r s := by
    intro s hs
    by_cases hsp : s = p
    · subst s
      exact hypothetical_aligns a r p hp hD
    · simpa only [aligns, hypothetical_other a r p s hsp] using hother s hs hsp
  rw [modulusCount_eq_parameter_card Y small (hypotheticalClass a r p) r d hd hall,
    hypothetical_small_parameters Y small a r d p hsmall]

end ErdosHypotheticalTag


section

open _root_.Filter
namespace ErdosHypotheticalTag
open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts

theorem source_all_search_units (Cs : ℝ) :
    ∀ᶠ w : ℝ in atTop, 1 < w ∧ ∀ (R : ℝ) (r : ℚ) (p : ℕ),
      0 < R → (r.den : ℝ) ≤ w^Cs → w^((1/4 : ℝ)) ≤ Real.log R/Real.log w →
      R ≤ (p : ℝ) → p.Prime → r.den.Coprime p := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).eventually_gt_atTop Cs
  filter_upwards [hpow, eventually_gt_atTop (1 : ℝ)] with w hCs hw
  refine ⟨hw, ?_⟩
  intro R r p hR hden hsearch hRp hp
  have hw0 : 0 < w := by linarith
  have hL : 0 < Real.log w := Real.log_pos hw
  have hexp : w^(w^((1/4 : ℝ))) ≤ R := by
    have h := (le_div_iff₀ hL).mp hsearch
    rw [Real.rpow_def_of_pos hw0]
    calc
      _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr (by nlinarith [h])
      _ = R := Real.exp_log hR
  have hstrict : w^Cs < w^(w^((1/4 : ℝ))) := Real.rpow_lt_rpow_of_exponent_lt hw hCs
  have hdp : r.den < p := by
    exact_mod_cast hden.trans_lt (hstrict.trans_le (hexp.trans hRp))
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt hdp) (Nat.le_of_dvd r.den_pos hd)

theorem source_hypothetical_count_parameters (Cs : ℝ) :
    ∀ᶠ w : ℝ in atTop, ∀ (R : ℝ) (r : ℚ) (Y : ℕ) (small : Finset ℕ)
      (a : ℕ → ℕ) (d p : ℕ) [NeZero p],
      0 < R → (r.den : ℝ) ≤ w^Cs → w^((1/4 : ℝ)) ≤ Real.log R/Real.log w →
      R ≤ (p : ℝ) → p.Prime → Squarefree d → p ∉ small →
      (∀ s ∈ d.primeFactors, s ≠ p → aligns (fun u => (a u : ℤ)) r s) →
      modulusCount Y small (hypotheticalClass a r p) d =
        ((parameterCandidates Y small a r d).card : ℤ) := by
  filter_upwards [source_all_search_units Cs] with w hw
  intro R r Y small a d p inst hR hden hsearch hRp hp hd hsmall hother
  exact hypothetical_count_parameters Y small a r d p hd hp
    (hw.2 R r p hR hden hsearch hRp hp) hsmall hother

end ErdosHypotheticalTag

end


namespace ErdosStoppedArithmetic
open ErdosAlignedProgression ErdosHypotheticalTag ErdosInverseAlignment ErdosInverseCounts
attribute [local instance] Classical.propDecidable

noncomputable def hypotheticalRowCount (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (p : T) : ℝ :=
  (modulusCount Y small (@hypotheticalClass a r p.val ⟨(hT p.val p.property).ne_zero⟩) (p.val*q) : ℝ)

theorem hypothetical_row_parameters (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (p : T)
    (hsf : Squarefree (p.val*q)) (hD : r.den.Coprime p.val) (hsmall : p.val ∉ small)
    (hother : ∀ t ∈ (p.val*q).primeFactors,t ≠ p.val → aligns (fun u => (a u : ℤ)) r t) :
    hypotheticalRowCount Y small T a r q hT p = ((parameterCandidates Y small a r (p.val*q)).card : ℝ) := by
  let : NeZero p.val := ⟨(hT p.val p.property).ne_zero⟩
  unfold hypotheticalRowCount
  rw [hypothetical_count_parameters Y small a r (p.val*q) p.val hsf (hT p.val p.property) hD hsmall hother,
    Int.cast_natCast]

theorem parameter_value_integer (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ)
    (hI : m ∈ parameterInterval Y r d) (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m) :
    (parameterValue r d m : ℤ)=(r.num+(d : ℤ)*m)/(r.den : ℤ) := by
  have hs := parameterValue_spec Y r d hd m hI hdiv
  have hD : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [← hs.2.2,Int.mul_ediv_cancel_left _ hD]

theorem actual_test_mem_parameters (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ) (hI : m ∈ parameterInterval Y r d)
    (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m)
    (hAvoid : ∀ t ∈ small,¬Int.ModEq (t : ℤ) ((r.num+(d : ℤ)*m)/(r.den : ℤ)) (a t : ℤ)) :
    m ∈ parameterCandidates Y small a r d := by
  apply Finset.mem_filter.mpr
  refine ⟨hI,hdiv,?_⟩
  intro t ht he
  have hNat : Nat.ModEq t (parameterValue r d m) (a t) := he
  have hInt : Int.ModEq (t : ℤ) (parameterValue r d m : ℤ) (a t : ℤ) :=
    (Int.natCast_modEq_iff).mpr hNat
  rw [parameter_value_integer Y r d hd m hI hdiv] at hInt
  exact hAvoid t ht hInt

theorem pair_count_le_hypothetical_sum (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (M : Finset ℤ) (good : ℕ → ℤ → Prop)
    (hGeometry : ∀ p ∈ T,Squarefree (p*q) ∧ r.den.Coprime p ∧ p ∉ small ∧
      ∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t)
    (hCommon : ∀ p ∈ T,∀ m ∈ M,good p m → m ∈ parameterInterval Y r (p*q))
    (hGood : ∀ p ∈ T,∀ m ∈ M,good p m →
      (r.den : ℤ) ∣ r.num+((p*q : ℕ) : ℤ)*m ∧
      ∀ t ∈ small,¬Int.ModEq (t : ℤ) ((r.num+((p*q : ℕ) : ℤ)*m)/(r.den : ℤ)) (a t : ℤ)) :
    ((admissiblePairs T M good).card : ℝ) ≤ ∑ p : T,hypotheticalRowCount Y small T a r q hT p := by
  have hRows : (admissiblePairs T M good).card ≤
      ∑ p ∈ T,(parameterCandidates Y small a r (p*q)).card := by
    rw [admissible_pair_card_rows]
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.card_le_card
    intro m hm
    have hmM := (Finset.mem_filter.mp hm).1
    have hcond := hGood p hp m hmM (Finset.mem_filter.mp hm).2
    exact actual_test_mem_parameters Y small a r (p*q)
      (Nat.pos_of_ne_zero (hGeometry p hp).1.ne_zero) m (hCommon p hp m hmM (Finset.mem_filter.mp hm).2) hcond.1 hcond.2
  calc
    _ ≤ ∑ p ∈ T,((parameterCandidates Y small a r (p*q)).card : ℝ) := by exact_mod_cast hRows
    _ = ∑ p : T,((parameterCandidates Y small a r (p.val*q)).card : ℝ) := (Finset.sum_coe_sort T _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      have hg := hGeometry p.val p.property
      exact (hypothetical_row_parameters Y small T a r q hT p hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).symm

end ErdosStoppedArithmetic


end Erdos970

end OAI
