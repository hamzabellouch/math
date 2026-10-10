import OAI.NumberTheory.TotientAsymptotic.GeometricContractedFamily
import OAI.NumberTheory.TotientAsymptotic.PrefixConcentration

namespace OAI

/-! A fixed upper cutoff for the leading tail coordinate costs vanishing volume. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

lemma renewalSeries_two_thirds_gt_one : 1 < renewalSeries (2/3) := by
  have hs := summable_renewal (r:=2/3) (by norm_num) (by norm_num)
  have hh := hs.sum_le_tsum (Finset.range 3)
    (fun n _ => mul_nonneg (a_pos (by omega)).le (pow_nonneg (by norm_num) _))
  change _ ≤ renewalSeries (2/3) at hh
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  norm_num [Finset.sum_range_succ,a,h4] at hh
  nlinarith [Real.log_two_gt_d9,Real.log_three_gt_d9]

lemma rho_lt_two_thirds : rho < 2/3 := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show (2/3:ℝ) ∈ Set.Ico (0:ℝ) 1 by norm_num)
    (show rho ∈ Set.Ico (0:ℝ) 1 from ⟨rho_pos.le,rho_lt_one⟩) hh
  rw [renewalSeries_rho] at hm
  linarith only [hm,renewalSeries_two_thirds_gt_one]

def headLimitedFamily (m n : ℕ) (B c : ℝ) : Set (Fin n → ℝ) :=
  geometricContractedFamily m n B c ∩ {u | ∀ i,u i ≤ (3/4:ℝ)*B}

lemma measurableSet_headLimitedFamily (m n : ℕ) (B c : ℝ) :
    MeasurableSet (headLimitedFamily m n B c) := by
  apply (measurableSet_geometricContractedFamily _ _ _ _).inter
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i) measurable_const)

lemma geometric_family_subset_prefix {m n : ℕ} {B c : ℝ} (hB : 0 ≤ B) :
    geometricContractedFamily m n B c ⊆ prefixRegion n B 0 0 := by
  intro u hu
  have hp := contractedPrefix_subset_prefixRegion
    (fun i => by linarith only [rowContractionError_nonneg (m-(i.val+1))]) hu.1
  refine ⟨hp.1,?_⟩
  apply hp.2.trans
  simp only [sub_zero]
  exact div_le_self hB (by linarith only [rowContractionError_nonneg m])

lemma head_cap_failure_is_coordinate_bad {N m : ℕ} {B c : ℝ} (hB : 0 < B)
    {u : Fin (N+2) → ℝ} (hu : u ∈ geometricContractedFamily m (N+2) B c)
    (hfail : ¬ ∀ i,u i ≤ (3/4:ℝ)*B) :
    u ∈ fordCoordinateBad N B ⟨0,by omega⟩ := by
  obtain ⟨i,hi⟩ := not_forall.mp hfail
  have hi : (3/4:ℝ)*B < u i := lt_of_not_ge hi
  have hhead : u i ≤ u ⟨0,by omega⟩ := hu.1.2.1.antitone (by simp)
  let T := fordSimplexCenter N B ⟨0,by omega⟩
  have hdim : (0:ℝ) < N+2 := by positivity
  have hfactor : 0 < 1-1/(N+2:ℝ) := by
    have hh : (1:ℝ) < N+2 := by have := Nat.cast_nonneg (α:=ℝ) N; linarith
    exact sub_pos.mpr ((div_lt_one hdim).mpr hh)
  have hT : 0 < T := by
    simpa only [T,fordSimplexCenter,Fin.val_mk,Nat.cast_zero,zero_add,pow_one] using
      mul_pos (mul_pos hB rho_pos) hfactor
  have hTB : T ≤ (2/3:ℝ)*B := by
    dsimp [T,fordSimplexCenter]
    simp only [Nat.cast_zero,zero_add,pow_one]
    calc
      _ ≤ B*rho := mul_le_of_le_one_right (mul_nonneg hB.le rho_pos.le)
        (by
          have hdiv : 0 ≤ 1/(N+2:ℝ) := by positivity
          linarith only [hdiv])
      _ ≤ _ := by nlinarith only [rho_lt_two_thirds.le,hB.le]
  have hratio : (41/40:ℝ) < u ⟨0,by omega⟩/T := by
    apply (lt_div_iff₀ hT).mpr
    nlinarith only [hTB,hB,hi,hhead]
  change (1/40:ℝ) < |u ⟨0,by omega⟩/T-1|
  exact lt_of_lt_of_le (by linarith only [hratio]) (le_abs_self _)

theorem head_limited_volume_lower : ∃ c δ : ℝ,0 < c ∧ 0 < δ ∧
    ∀ H : ℕ,1 ≤ H → ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ volume.real (headLimitedFamily (m x) (N+2) (B x) c) := by
  obtain ⟨c,δ,hc,hδ,hvol⟩ := geometric_contracted_volume_lower
  obtain ⟨C,k,hC,hk,hcap⟩ := prefix_coordinate_concentration_unconditional
  have ht : Tendsto (fun N : ℕ => C*Real.exp (-k*(N+1:ℝ))) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-k)).le
      (Real.exp_lt_one_iff.mpr (by linarith only [hk]))).const_mul (C*Real.exp (-k))
    convert h using 1
    · ext N
      rw [←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
      congr 2
      ring
    · ring_nf
  obtain ⟨L,hL⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (half_pos hδ)))
  refine ⟨c,δ/2,hc,half_pos hδ,?_⟩
  intro H hH
  filter_upwards [hvol H hH,m_tendsto.eventually (eventually_ge_atTop (L+H+3)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hm hB
  intro N hN
  have hNL : L ≤ N := by omega
  have hNpos : 0 < N := by omega
  let S := geometricContractedFamily (m x) (N+2) (B x) c
  let T := headLimitedFamily (m x) (N+2) (B x) c
  let E := prefixRegion (N+2) (B x) 0 0 ∩ fordCoordinateBad N (B x) ⟨0,by omega⟩
  have hsub : S ⊆ T ∪ E := by
    intro u hu
    by_cases h : ∀ i,u i ≤ (3/4:ℝ)*B x
    · exact Or.inl ⟨hu,h⟩
    · exact Or.inr ⟨geometric_family_subset_prefix hB.le hu,
        head_cap_failure_is_coordinate_bad hB hu h⟩
  have hfinite : volume (T ∪ E) ≠ ⊤ := by
    apply measure_ne_top_of_subset (s:=prefixRegion (N+2) (B x) 0 0)
    · intro u hu
      rcases hu with hu|hu
      · exact geometric_family_subset_prefix hB.le hu.1
      · exact hu.1
    · exact prefixRegion_volume_ne_top (by omega) _
  have hm := (measureReal_mono hsub hfinite).trans (measureReal_union_le T E)
  have he := hcap N (B x) hB ⟨0,by omega⟩ (by omega)
  have hG : volume.real (prefixRegion (N+2) (B x) 0 0)=G x (N+2) := prefixRegion_real_eq_G hB.le (by omega)
  have hbad : volume.real E ≤ (δ/2)*G x (N+2) := by
    have hn : N+2-(0+1)=N+1 := by omega
    simp only [hn,Nat.cast_add,Nat.cast_one] at he
    change volume.real E ≤ C*Real.exp (-k*(N+1:ℝ))*
      volume.real (prefixRegion (N+2) (B x) 0 0) at he
    rw [hG] at he
    exact he.trans (mul_le_mul_of_nonneg_right (hL N hNL).le (G_pos hB _).le)
  have hgood := hx N hN
  change δ*G x (N+2) ≤ volume.real S at hgood
  nlinarith only [hm,hbad,hgood]

end TotientAsymptotic

end

end OAI
