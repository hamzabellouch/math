import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Taper

noncomputable def marginal (P d r : ℝ) : ℝ := min 1 (max (1-r*d) 0/P)

theorem marginal_nonneg {P d r : ℝ} (hP : 0 < P) : 0 ≤ marginal P d r :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) hP.le)

theorem marginal_le_one (P d r : ℝ) : marginal P d r ≤ 1 := min_le_left _ _

theorem marginal_antitone {P d : ℝ} (hP : 0 < P) (hd : 0 ≤ d) : Antitone (marginal P d) := by
  intro r s hrs
  apply min_le_min_left
  apply div_le_div_of_nonneg_right _ hP.le
  apply max_le_max_right
  nlinarith only [mul_le_mul_of_nonneg_right hrs hd]

theorem marginal_one {P d r : ℝ} (hP : 0 < P) (h : r*d ≤ 1-P) : marginal P d r=1 := by
  apply min_eq_left
  apply (le_div_iff₀ hP).mpr
  have hh := le_max_left (1-r*d) 0
  linarith only [h, hh]

theorem marginal_zero {P d r : ℝ} (h : 1 ≤ r*d) : marginal P d r=0 := by
  simp only [marginal, max_eq_right (by linarith : 1-r*d ≤ 0), zero_div]
  norm_num

theorem marginal_at_zero_distance {P r : ℝ} (hP : 0 < P) (hP1 : P ≤ 1) : marginal P 0 r=1 := by
  apply marginal_one hP
  simpa only [mul_zero] using sub_nonneg.mpr hP1

theorem lower_comparison {P d r : ℝ} (hP : 0 < P) (h : marginal P d r < 1) :
    1-P*marginal P d r ≤ r*d := by
  have hright : max (1-r*d) 0/P < 1 := by
    by_contra hn
    have heq : marginal P d r=1 := min_eq_left (le_of_not_gt hn)
    rw [heq] at h
    exact lt_irrefl _ h
  have heq : marginal P d r=max (1-r*d) 0/P := min_eq_right hright.le
  rw [heq, mul_div_cancel₀ _ (ne_of_gt hP)]
  have hh := le_max_left (1-r*d) 0
  linarith only [hh]

theorem upper_comparison {P d r : ℝ} (hP : 0 < P) (h : 0 < marginal P d r) :
    r*d ≤ 1-P*marginal P d r := by
  have hrd : r*d < 1 := by
    by_contra hn
    rw [marginal_zero (le_of_not_gt hn)] at h
    exact lt_irrefl _ h
  have hh : marginal P d r ≤ (1-r*d)/P := by
    unfold marginal
    rw [max_eq_left (by linarith only [hrd])]
    exact min_le_right _ _
  have hb := (le_div_iff₀ hP).mp hh
  nlinarith only [hb]

variable {I : Type*} [Fintype I]

noncomputable def mass (g P : ℝ) (d : I → ℝ) (r : ℝ) : ℝ := ∑ i, g*marginal P (d i) r

noncomputable def colocatedMass (g : ℝ) (d : I → ℝ) : ℝ := ∑ i, if d i=0 then g else 0

theorem mass_antitone {g P : ℝ} {d : I → ℝ} (hg : 0 ≤ g) (hP : 0 < P)
    (hd : ∀ i, 0 ≤ d i) : Antitone (mass g P d) := by
  intro r s hrs
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (marginal_antitone hP (hd i) hrs) hg)

theorem continuous_mass {g P : ℝ} {d : I → ℝ} : Continuous (mass g P d) := by
  unfold mass marginal
  fun_prop

theorem exists_full_inverse {P : ℝ} (hP : 0 < P) (hP1 : P ≤ 1/2)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∃ r > 0, ∀ i, marginal P (d i) r=1 := by
  let D := ∑ i, d i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hd i)
  have hden : 0 < 2*(1+D) := by linarith only [hD]
  refine ⟨1/(2*(1+D)), one_div_pos.mpr hden, ?_⟩
  intro i
  apply marginal_one hP
  have hi : d i ≤ D := Finset.single_le_sum (fun t _ => hd t) (Finset.mem_univ i)
  have hh : (1/(2*(1+D)))*d i ≤ 1/2 := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hi]
  linarith only [hh, hP1]

theorem exists_colocated_inverse {P : ℝ} (hP : 0 < P) (hP1 : P ≤ 1)
    (g : ℝ) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∃ r > 0, mass g P d r=colocatedMass g d := by
  let U := 1+∑ i, (d i)⁻¹
  have hsum : 0 ≤ ∑ i, (d i)⁻¹ := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hd i))
  have hU : 0 < U := by dsimp only [U]; linarith only [hsum]
  refine ⟨U, hU, ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : d i=0
  · simp only [hi, marginal_at_zero_distance hP hP1, mul_one, ite_true]
  · have hip : 0 < d i := lt_of_le_of_ne (hd i) (Ne.symm hi)
    have hb : (d i)⁻¹ ≤ ∑ t, (d t)⁻¹ :=
      Finset.single_le_sum (fun t _ => inv_nonneg.mpr (hd t)) (Finset.mem_univ i)
    have hm := mul_le_mul_of_nonneg_right hb hip.le
    rw [inv_mul_cancel₀ hi] at hm
    have hu : 1 ≤ U*d i := by dsimp only [U]; nlinarith only [hm, hip]
    simp only [marginal_zero hu, mul_zero, ite_eq_right hi]

theorem exists_minimal_radius {g P : ℝ} (d : I → ℝ)
    (hg : 0 < g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hd : ∀ i, 0 ≤ d i)
    (htotal : 1 ≤ ∑ _i : I, g) (hcol : colocatedMass g d < 1) :
    ∃ r > 0, mass g P d r=1 ∧ ∀ u, 1 ≤ mass g P d u → u ≤ r := by
  obtain ⟨L, hL, hfull⟩ := exists_full_inverse hP hP1 d hd
  have hmassL : 1 ≤ mass g P d L := by
    simpa only [mass, hfull, mul_one] using htotal
  obtain ⟨U, _hU, hmassU⟩ := exists_colocated_inverse hP (by linarith only [hP1]) g d hd
  have hmassUlt : mass g P d U < 1 := hmassU ▸ hcol
  have hanti := mass_antitone hg.le hP hd
  have hLU : L < U := by
    by_contra hn
    have hh := hanti (le_of_not_gt hn)
    linarith only [hmassL, hmassUlt, hh]
  have hcont : Continuous (mass g P d) := continuous_mass
  have hex : ∃ r ∈ Set.Icc L U, mass g P d r=1 :=
    intermediate_value_Icc' hLU.le hcont.continuousOn ⟨hmassUlt.le, hmassL⟩
  let S := Set.Icc L U ∩ (mass g P d) ⁻¹' {1}
  have hcompact : IsCompact S := isCompact_Icc.inter_right
    (isClosed_singleton.preimage hcont)
  have hne : S.Nonempty := by
    obtain ⟨r, hr, heq⟩ := hex
    exact ⟨r, hr, heq⟩
  obtain ⟨r, hr, hmax⟩ := hcompact.exists_isMaxOn hne continuous_id.continuousOn
  refine ⟨r, hL.trans_le hr.1.1, hr.2, ?_⟩
  intro u hu
  by_contra hn
  have hru : r < u := lt_of_not_ge hn
  have hupper : u ≤ U := by
    by_contra hnu
    have hh := hanti (le_of_lt (lt_of_not_ge hnu))
    linarith only [hu, hmassUlt, hh]
  have heq : mass g P d u=1 := le_antisymm ((hanti hru.le).trans_eq hr.2) hu
  have hus : u ∈ S := ⟨⟨hr.1.1.trans hru.le, hupper⟩, heq⟩
  have hh := hmax hus
  exact (not_le_of_gt hru) hh

end MetricKMedian.Taper
end
end

end OAI
