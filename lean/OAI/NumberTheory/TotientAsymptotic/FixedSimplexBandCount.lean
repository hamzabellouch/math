import OAI.NumberTheory.TotientAsymptotic.FixedSimplexTerminal
import OAI.NumberTheory.TotientAsymptotic.PPTFixedCoordinateValueCount
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.RenewalInput

namespace OAI

/-! For each fixed terminal truncation, count all values having a bad
retained coordinate by the last two strict prime boundaries. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_simplex_bad_band_count (H : ℕ) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ Q : Finset ℕ,∀ n : ℕ→ℕ,
    (∀ v∈Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      fordSimplexCondition x H (n v)) →
    (∀ v∈Q,∃ j∈Finset.Icc 1 (m x-P),
      primeDoubleLog (n v) j < (19/20:ℝ)*fordBandScale x j ∨
      (21/20:ℝ)*fordBandScale x j < primeDoubleLog (n v) j) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-c*(P:ℝ)) := by
  classical
  obtain ⟨A,a,hA,ha,hcountA⟩ := ppt_fixed_bad_coordinate_value_count H
  obtain ⟨D,d,hD,hd,hcountD⟩ := ppt_fixed_bad_coordinate_value_count (H+1)
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  let c := min a d
  refine ⟨A*J^(H+1)+D*J^(H+2),c,by positivity,lt_min ha hd,?_⟩
  filter_upwards [hcountA,hcountD] with P hPA hPD
  filter_upwards [hPA,hPD,hproj,m_tendsto.eventually (eventually_ge_atTop (H+4)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hxA hxD hproj hm hB hx1
  intro Q n hQ hbad
  have hdata (v) (hv : v∈Q) := fixed_simplex_terminal_data (hQ v hv).2.2.2.2
    (show 3 ≤ m x-H by omega)
  choose j hj using hdata
  let U := Q.filter (fun v => ∃ hv : v∈Q,j v hv=m x-H)
  let W := Q\U
  have hUj (v) (hv : v∈U) : ∃ hvQ : v∈Q,j v hvQ=m x-H :=
    (Finset.mem_filter.mp hv).2
  have hWj (v) (hv : v∈W) : ∃ hvQ : v∈Q,j v hvQ=m x-H-1 := by
    obtain ⟨hvQ,hout⟩ := Finset.mem_sdiff.mp hv
    refine ⟨hvQ,?_⟩
    rcases (hj v hvQ).1 with hh|hh
    · exact False.elim (hout (Finset.mem_filter.mpr ⟨hvQ,hvQ,hh⟩))
    · exact hh
  have hU0 := hxA (m x-H-3) (by omega) U n (by
    intro v hv
    obtain ⟨hvQ,hjv⟩ := hUj v hv
    obtain ⟨hn,hphi,hhead,hvx,_⟩ := hQ v hvQ
    have ht := (hj v hvQ).2
    rw [hjv] at ht
    have hi : m x-H-3+3=m x-H := by omega
    refine ⟨hn,hphi,hhead,hvx,?_,?_,?_,?_⟩
    · simpa only [hi] using ht.1
    · simpa only [hi,show m x-H-3+2=m x-H-1 by omega] using ht.2.1
    · simpa only [hi] using ht.2.2.1
    · simpa only [hi] using ht.2.2.2) (by
      intro v hv
      exact hbad v (Finset.mem_filter.mp hv).1)
  have hW0 := hxD (m x-H-4) (by omega) W n (by
    intro v hv
    obtain ⟨hvQ,hjv⟩ := hWj v hv
    obtain ⟨hn,hphi,hhead,hvx,_⟩ := hQ v hvQ
    have ht := (hj v hvQ).2
    rw [hjv] at ht
    have hi : m x-H-4+3=m x-H-1 := by omega
    refine ⟨hn,hphi,hhead,hvx,?_,?_,?_,?_⟩
    · simpa only [hi] using ht.1
    · convert ht.2.1 using 1
      all_goals congr 1
      all_goals omega
    · simpa only [hi] using ht.2.2.1
    · simpa only [hi] using ht.2.2.2) (by
      intro v hv
      exact hbad v (Finset.mem_sdiff.mp hv).1)
  have hU : (U.card:ℝ) ≤ A*(x/Real.log x)*G x (m x-(H+1))*Real.exp (-a*(P:ℝ)) := by
    simpa only [show m x-H-3+2=m x-(H+1) by omega] using hU0
  have hW : (W.card:ℝ) ≤ D*(x/Real.log x)*G x (m x-(H+2))*Real.exp (-d*(P:ℝ)) := by
    simpa only [show m x-H-4+2=m x-(H+2) by omega] using hW0
  have hnorm : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  have hg (R : ℕ) (hR : R ≤ m x) : G x (m x-R) ≤ J^R*G x (m x) := by
    have hh := (div_le_iff₀ (G_pos hB (m x))).mp (hproj R hR)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (pow_nonneg hJ.le R) (pow_le_one₀ rho_pos.le rho_lt_one.le))
      (G_pos hB (m x)).le)
  have heA : Real.exp (-a*(P:ℝ)) ≤ Real.exp (-c*(P:ℝ)) :=
    Real.exp_le_exp.mpr (by
      dsimp only [c]
      simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left a d) (Nat.cast_nonneg P)))
  have heD : Real.exp (-d*(P:ℝ)) ≤ Real.exp (-c*(P:ℝ)) :=
    Real.exp_le_exp.mpr (by
      dsimp only [c]
      simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right a d) (Nat.cast_nonneg P)))
  have hG : 0 ≤ G x (m x) := (G_pos hB _).le
  have hbA := hU.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (hg (H+1) (by omega)) (mul_nonneg hA.le hnorm))
    heA (Real.exp_pos _).le (by positivity))
  have hbD := hW.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (hg (H+2) (by omega)) (mul_nonneg hD.le hnorm))
    heD (Real.exp_pos _).le (by positivity))
  have hcard : (Q.card:ℝ)=(U.card:ℝ)+(W.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show U⊆Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=U.card+W.card by dsimp [W]; omega)
  rw [hcard]
  exact (add_le_add hbA hbD).trans_eq (by ring)

end TotientAsymptotic

end

end OAI
