import Mathlib
import OAI.Combinatorics.HoneycombCorridor.StripDecay
import OAI.Combinatorics.HoneycombCorridor.Reflection

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def reachesRight (t : ℝ) (w : List Bool) : Prop :=
  ∃ v ∈ traced bottomSource w, t ≤ (position v).1

noncomputable def rightDistanceMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact positiveWordMass ((sourceExits D bottomSource).filter (reachesRight t))

noncomputable def tailRate : ℝ := -Real.log rayContraction / 2
noncomputable def tailConstant : ℝ :=
  2 * (Real.cos (3*Real.pi/8))⁻¹ * Real.exp (-Real.log rayContraction)

theorem tailRate_pos : 0 < tailRate := by
  have h := Real.log_neg rayContraction_range.1 rayContraction_range.2
  exact div_pos (neg_pos.mpr h) (by norm_num)

theorem tailConstant_pos : 0 < tailConstant := by
  have hc : 0 < Real.cos (3*Real.pi/8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr hc)) (Real.exp_pos _)

theorem rightDistanceMass_mono (D : Finset Vertex) (s t : ℝ) (hst : s ≤ t) :
    rightDistanceMass D t ≤ rightDistanceMass D s := by
  classical
  apply positiveWordMass_mono
  intro w hw
  obtain ⟨he,v,hv,ht⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨he,v,hv,hst.trans ht⟩

theorem rightDistanceMass_geometric (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (n : ℕ) :
    rightDistanceMass D (2 * n * (h+1)) ≤
      (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero,mul_zero,zero_mul,pow_zero,mul_one]
    apply (positiveWordMass_mono (Finset.filter_subset _ _)).trans
    exact boundary_source_weight_bound D bottomSource hD hg (bottomSource_outside_of_strip h D hstrip)
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    apply le_trans (positiveWordMass_mono ?_) (rightIndexMass_geometric h hh D hD hg hstrip n)
    intro w hw
    obtain ⟨he,v,hv,ht⟩ := Finset.mem_filter.mp hw
    have hvm := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := (strip_index_bounds h v (hstrip v hvm)).2
    have hi' : (boxIndex v 2 : ℝ) ≤ (boxIndex v 1 : ℝ) + h := by exact_mod_cast hi
    have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have hbound : (n : ℝ)*h ≤ (boxIndex v 1 : ℝ) := by
      rw [position_index] at ht
      nlinarith
    exact (mem_lost_upperCut D bottomSource 1 ((n : ℤ)*h) w).mpr
      ⟨he,v,hv,by exact_mod_cast hbound⟩

theorem rightDistanceMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    rightDistanceMass D t ≤ tailConstant / 2 * Real.exp (-tailRate*t/(h+1)) := by
  let n : ℕ := ⌊t / (2 * (h+1 : ℝ))⌋₊
  have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
  have hd : (0 : ℝ) < 2*((h : ℝ)+1) := by positivity
  have hnlo : (n : ℝ) ≤ t/(2*(h+1)) := Nat.floor_le (div_nonneg ht hd.le)
  have hnhi : t/(2*(h+1)) < (n : ℝ)+1 := Nat.lt_floor_add_one _
  have hthreshold : 2*(n : ℝ)*(h+1) ≤ t := by
    have := (le_div_iff₀ hd).mp hnlo
    nlinarith
  have hgeo := (rightDistanceMass_mono D _ _ hthreshold).trans
    (rightDistanceMass_geometric h hh D hD hg hstrip n)
  have hlog := Real.log_neg rayContraction_range.1 rayContraction_range.2
  have he : (n : ℝ)*Real.log rayContraction ≤
      -Real.log rayContraction + -tailRate*t/(h+1) := by
    have hm := mul_le_mul_of_nonpos_right (le_of_lt hnhi) hlog.le
    have heq : -tailRate*t/(h+1) =
        t/(2*(h+1))*Real.log rayContraction := by
      dsimp [tailRate]
      field_simp
    rw [heq]
    nlinarith [hm]
  have hp : rayContraction ^ n ≤
      Real.exp (-Real.log rayContraction) * Real.exp (-tailRate*t/(h+1)) := by
    rw [← Real.exp_add]
    conv_lhs => rw [← Real.exp_log rayContraction_range.1,← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr he
  have hc : 0 ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
    apply inv_nonneg.mpr
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  calc
    _ ≤ (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := hgeo
    _ ≤ (Real.cos (3*Real.pi/8))⁻¹ *
        (Real.exp (-Real.log rayContraction) * Real.exp (-tailRate*t/(h+1))) :=
      mul_le_mul_of_nonneg_left hp hc
    _ = _ := by dsimp [tailConstant]; ring

@[simp] theorem reachesRight_mirror (t : ℝ) (w : List Bool) :
    reachesRight t (mirrorWord w) ↔ ∃ v ∈ traced bottomSource w, t ≤ -(position v).1 := by
  have hm := mirror_traced bottomSource w
  rw [mirror_bottomSource] at hm
  simp only [reachesRight,hm,List.mem_map]
  constructor
  · rintro ⟨v,⟨u,hu,rfl⟩,ht⟩
    exact ⟨u,hu,by simpa using ht⟩
  · rintro ⟨v,hv,ht⟩
    exact ⟨mirrorVertex v,⟨v,hv,rfl⟩,by simpa using ht⟩

theorem lateralMass_le_sides (D : Finset Vertex) (t : ℝ) :
    lateralMass D t ≤ rightDistanceMass D t + rightDistanceMass (mirrorDomain D) t := by
  classical
  simp only [rightDistanceMass,positiveWordMass,Finset.sum_filter,mirror_sourceExits_eq]
  rw [Finset.sum_image (fun a _ b _ hab => mirrorWord_injective hab),← Finset.sum_add_distrib]
  unfold lateralMass
  apply Finset.sum_le_sum
  intro w hw
  simp only [mirrorWord_length]
  by_cases hr : reachesRight t w
  · simp only [hr,ite_true]
    split_ifs <;> nlinarith [pow_nonneg criticalActivity_pos.le w.length]
  · by_cases hl : reachesRight t (mirrorWord w)
    · simp only [hr,hl,ite_false,ite_true,zero_add]
      split_ifs <;> first | exact le_rfl | exact pow_nonneg criticalActivity_pos.le _
    · have hnone : ¬ reachesDistance t w := by
        rintro ⟨v,hv,hv'⟩
        have hab := le_abs.mp hv'
        rcases hab with h | h
        · exact hr ⟨v,hv,h⟩
        · exact hl ((reachesRight_mirror t w).mpr ⟨v,hv,h⟩)
      simp only [hr,hl,hnone,ite_false,zero_add,le_refl]

theorem lateralMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    lateralMass D t ≤ tailConstant * Real.exp (-tailRate*t/(h+1)) := by
  have h1 := rightDistanceMass_exp h hh D hD hg hstrip t ht
  have h2 := rightDistanceMass_exp h hh (mirrorDomain D) (mirrorDomain_convex D hD)
    (by simpa only [mem_mirrorDomain,show mirrorVertex bottomSource.1 = bottomSource.1 from rfl] using hg)
    (mirrorDomain_strip h D hstrip) t ht
  have hs := lateralMass_le_sides D t
  linarith

end PolynomialVacuumBridge.Corridor

end

end OAI
