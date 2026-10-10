import OAI.Geometry.LatticeCovering.Concentration

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι]

lemma square_difference_le {x y δ : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hd : |x-y| ≤ δ) : y^2-x^2 ≤ 2*δ := by
  have hsum : |y+x| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hdiff : |y-x| ≤ δ := by simpa only [abs_sub_comm] using hd
  calc
    _ = (y-x)*(y+x) := by ring
    _ ≤ |(y-x)*(y+x)| := le_abs_self _
    _ = |y-x| * |y+x| := abs_mul _ _
    _ ≤ δ*2 := mul_le_mul hdiff hsum (abs_nonneg _) (le_trans (abs_nonneg _) hdiff)
    _ = _ := by ring

lemma gamma1_rounding_upper (h : ℝ) {x y δ : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hd : |x-y| ≤ δ) : gamma1 (h*x) ≤ exp (h^2*δ)*gamma1 (h*y) := by
  have hs := mul_le_mul_of_nonneg_left (square_difference_le hx hy hd) (sq_nonneg h)
  have he : -(h*x)^2/2 ≤ h^2*δ + -(h*y)^2/2 := by nlinarith
  unfold gamma1
  rw [← mul_div_assoc, ← Real.exp_add]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he) (Real.sqrt_nonneg _)

lemma gamma1_rounding (h : ℝ) {x y δ : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hd : |x-y| ≤ δ) :
    exp (-(h^2*δ))*gamma1 (h*y) ≤ gamma1 (h*x) ∧
      gamma1 (h*x) ≤ exp (h^2*δ)*gamma1 (h*y) := by
  refine ⟨?_, gamma1_rounding_upper h hx hy hd⟩
  have hb := gamma1_rounding_upper h hy hx (by simpa only [abs_sub_comm] using hd)
  calc
    _ ≤ exp (-(h^2*δ)) * (exp (h^2*δ)*gamma1 (h*x)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; simp

lemma abs_sub_bitValue {t : ℝ} (ht : t ∈ Set.Icc 0 1) (e : Bool) :
    |t-bitValue e| ≤ 1 := by
  apply abs_le.mpr
  cases e <;> simp only [bitValue, Bool.false_eq_true, ↓reduceIte, sub_zero] <;>
    constructor <;> linarith [ht.1, ht.2]

lemma density_rounding_upper {h s t δ : ℝ} (hh : 0 < h)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) (hd : |t-s| ≤ δ) :
    density h t ≤ exp (h^2*δ)*density h s := by
  have h0 := gamma1_rounding_upper h (abs_sub_bitValue ht false)
    (abs_sub_bitValue hs false) (show |(t-bitValue false)-(s-bitValue false)| ≤ δ by simpa using hd)
  have h1 := gamma1_rounding_upper h (abs_sub_bitValue ht true)
    (abs_sub_bitValue hs true) (show |(t-bitValue true)-(s-bitValue true)| ≤ δ by
      simpa only [sub_sub_sub_cancel_right] using hd)
  simp only [bitValue, Bool.false_eq_true, ↓reduceIte, sub_zero] at h0 h1
  have h0' := mul_le_mul_of_nonneg_left h0 hh.le
  have h1' := mul_le_mul_of_nonneg_left h1 hh.le
  unfold density
  nlinarith

lemma product_rounding {f g : ι → ℝ} (hf : ∀ j, 0 ≤ f j) (r : ℝ)
    (hfg : ∀ j, f j ≤ exp r*g j) :
    (∏ j, f j) ≤ exp ((Fintype.card ι : ℝ)*r)*(∏ j, g j) := by
  calc
    _ ≤ ∏ j, exp r*g j := Finset.prod_le_prod₀ (fun j _ => hf j) (fun j _ => hfg j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp

lemma folded_rounding_upper {h δ : ℝ} (hh : 0 < h) (s t : ι → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc 0 1) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hd : ∀ j, |t j-s j| ≤ δ) :
    folded h t ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*folded h s := by
  simpa only [folded, mul_assoc] using product_rounding
    (fun j => (density_pos hh (t j)).le) (h^2*δ)
    (fun j => density_rounding_upper hh (hs j) (ht j) (hd j))

lemma atom_eq_product (h : ℝ) (t : ι → ℝ) (e : ι → Bool) :
    atom h t e = ∏ j, h*gamma1 (h*(t j-bitValue (e j))) := by
  simp [atom, gamma, Finset.prod_mul_distrib]

lemma atom_rounding_upper {h δ : ℝ} (hh : 0 < h) (s t : ι → ℝ) (e : ι → Bool)
    (hs : ∀ j, s j ∈ Set.Icc 0 1) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hd : ∀ j, |t j-s j| ≤ δ) :
    atom h t e ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*atom h s e := by
  rw [atom_eq_product, atom_eq_product]
  have hj (j : ι) : h*gamma1 (h*(t j-bitValue (e j))) ≤
      exp (h^2*δ)*(h*gamma1 (h*(s j-bitValue (e j)))) := by
    have hg := gamma1_rounding_upper h (abs_sub_bitValue (ht j) (e j))
      (abs_sub_bitValue (hs j) (e j))
      (show |(t j-bitValue (e j))-(s j-bitValue (e j))| ≤ δ by
        simpa only [sub_sub_sub_cancel_right] using hd j)
    nlinarith [mul_le_mul_of_nonneg_left hg hh.le]
  simpa only [mul_assoc] using product_rounding
    (fun j => mul_nonneg hh.le (gamma1_pos _).le) (h^2*δ) hj

lemma remove_exp_factor {a b η : ℝ} (h : b ≤ exp η*a) : exp (-η)*b ≤ a := by
  calc
    _ ≤ exp (-η)*(exp η*a) := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; simp



theorem rounding {h δ : ℝ} (hh : 0 < h) (s t : ι → ℝ) (e : ι → Bool)
    (hs : ∀ j, s j ∈ Set.Icc 0 1) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hd : ∀ j, |t j-s j| ≤ δ) :
    exp (-((Fintype.card ι : ℝ)*h^2*δ))*folded h s ≤ folded h t ∧
    folded h t ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*folded h s ∧
    exp (-((Fintype.card ι : ℝ)*h^2*δ))*(folded h s*wordMass h s e) ≤ atom h t e ∧
    atom h t e ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*(folded h s*wordMass h s e) := by
  have hd' (j : ι) : |s j-t j| ≤ δ := by simpa only [abs_sub_comm] using hd j
  refine ⟨remove_exp_factor (folded_rounding_upper hh t s ht hs hd'),
    folded_rounding_upper hh s t hs ht hd, ?_, ?_⟩
  · rw [← folded_identity hh]
    exact remove_exp_factor (atom_rounding_upper hh t s e ht hs hd')
  · rw [← folded_identity hh]
    exact atom_rounding_upper hh s t e hs ht hd


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma grid_anchor_mem_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) (j : ι) :
    anchor p z j ∈ Set.Icc 0 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨div_nonneg (Nat.cast_nonneg _) hp0.le, ?_⟩
  apply (div_le_one hp0).mpr
  exact_mod_cast (ZMod.val_lt (z j)).le

lemma grid_distance {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {z : ι → ZMod p} {t : ι → ℝ} (ht : t ∈ gridCell p z) (j : ι) :
    |t j-anchor p z j| ≤ (p : ℝ)⁻¹ := by
  rw [abs_of_nonneg (ht j).1]
  exact (ht j).2.le

lemma grid_folded_integrable (h : ℝ) (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) :
    IntegrableOn (folded h) (gridCell p z) := by
  apply ((continuous_folded h).continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc) : IsCompact (cube : Set (ι → ℝ)))).mono_set
  intro t ht
  exact Set.mem_univ_pi.mpr (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt)

lemma grid_integral_upper {h : ℝ} (hh : 0 < h) (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) :
    (∫ t in gridCell p z, folded h t) ≤
      Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι := by
  have hfin : volume (gridCell p z) ≠ ⊤ := by rw [gridCell_volume]; finiteness
  calc
    _ ≤ ∫ _ in gridCell p z, Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z) := by
      apply setIntegral_mono_on (grid_folded_integrable h p hp z) (integrableOn_const hfin) (gridCell_measurable p z)
      intro t ht
      exact folded_rounding_upper hh _ _ (grid_anchor_mem_cube p hp z)
        (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_distance ht)
    _ = _ := by simp [gridCell_volume_real, mul_comm]

lemma grid_integral_lower {h : ℝ} (hh : 0 < h) (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) :
    Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι ≤
      (∫ t in gridCell p z, folded h t) := by
  have hfin : volume (gridCell p z) ≠ ⊤ := by rw [gridCell_volume]; finiteness
  calc
    _ = ∫ _ in gridCell p z, Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*folded h (anchor p z) := by
      simp [gridCell_volume_real, mul_comm]
    _ ≤ _ := by
      apply setIntegral_mono_on (integrableOn_const hfin) (grid_folded_integrable h p hp z) (gridCell_measurable p z)
      intro t ht
      apply remove_exp_factor
      exact folded_rounding_upper hh _ _
        (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_anchor_mem_cube p hp z)
        (fun j => by rw [abs_sub_comm]; exact grid_distance ht j)


def gridMass (h : ℝ) (p : ℕ) [NeZero p] (E : Finset (ι → ZMod p)) : ℝ :=
  ((p : ℝ)⁻¹)^Fintype.card ι * ∑ z ∈ E, folded h (anchor p z)

lemma grid_integral_total {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p) :
    Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*gridMass (ι := ι) h p Finset.univ ≤ (totalMass h)^Fintype.card ι ∧
    (totalMass h)^Fintype.card ι ≤ Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*gridMass (ι := ι) h p Finset.univ := by
  have he : (totalMass h)^Fintype.card ι =
      ∑ z : ι → ZMod p, ∫ t in gridCell p z, folded h t :=
    (cube_integral (ι := ι) hh).symm.trans (integral_gridCells hp (continuous_folded h))
  simp only [he]
  constructor
  · calc
      _ = ∑ z : ι → ZMod p, Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι := by
        simp only [gridMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ ≤ _ := Finset.sum_le_sum (fun z _ => grid_integral_lower hh p hp z)
  · calc
      _ ≤ ∑ z : ι → ZMod p, Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι :=
        Finset.sum_le_sum (fun z _ => grid_integral_upper hh p hp z)
      _ = _ := by
        simp only [gridMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma halfCube_ae_cube {ι : Type*} [Fintype ι] [DecidableEq ι] : Set.univ.pi (fun _ : ι => Ico (0 : ℝ) 1) =ᵐ[volume] (cube : Set (ι → ℝ)) := by
  rw [volume_pi]
  exact Measure.pi_Ico_ae_eq_pi_Icc

lemma grid_selected_integral {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p)
    (E : Finset (ι → ZMod p)) :
    (∫ t in ⋃ z ∈ E, gridCell p z, folded h t) ≤
      Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*gridMass h p E := by
  rw [integral_biUnion_finset E (fun z _ => gridCell_measurable p z)
    (fun z _ w _ hzw => gridCell_disjoint hp hzw) (fun z _ => grid_folded_integrable h p hp z)]
  calc
    _ ≤ ∑ z ∈ E, Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι :=
      Finset.sum_le_sum (fun z _ => grid_integral_upper hh p hp z)
    _ = _ := by
      simp only [gridMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

lemma grid_integral_event {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p)
    (E : Finset (ι → ZMod p)) (G : Set (ι → ℝ))
    (hG : ∀ t ∈ G, (∀ j, t j ∈ Ico 0 1) → residue p (floorVector p t) ∈ E) :
    (∫ t in G ∩ cube, folded h t) ≤
      Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*gridMass h p E := by
  have hi : IntegrableOn (folded h) (⋃ z ∈ E, gridCell p z) := by
    apply ((continuous_folded h).continuousOn.integrableOn_compact
      (isCompact_univ_pi (fun _ => isCompact_Icc) : IsCompact (cube : Set (ι → ℝ)))).mono_set
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨z,ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨hz,ht⟩
    exact Set.mem_univ_pi.mpr (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt)
  apply (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun t => (folded_pos hh t).le)) ?_).trans
    (grid_selected_integral hh p hp E)
  filter_upwards [halfCube_ae_cube (ι := ι)] with t ht
  intro htg
  have hc : ∀ j, t j ∈ Ico 0 1 := Set.mem_univ_pi.mp (ht.mpr htg.2)
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hG t htg.1 hc, cube_mem_gridCell hp hc⟩⟩

lemma log_folded_grid_distance {h : ℝ} (hh : 0 < h) (p : ℕ) (hp : 0 < p)
    {z : ι → ZMod p} {t : ι → ℝ} (ht : t ∈ gridCell p z) :
    |Real.log (folded h t)-Real.log (folded h (anchor p z))| ≤
      (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹ := by
  have hu := folded_rounding_upper hh (anchor p z) t (grid_anchor_mem_cube p hp z)
    (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_distance ht)
  have hl := folded_rounding_upper hh t (anchor p z)
    (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_anchor_mem_cube p hp z)
    (fun j => by rw [abs_sub_comm]; exact grid_distance ht j)
  have hu' := Real.log_le_log (folded_pos hh t) hu
  have hl' := Real.log_le_log (folded_pos hh (anchor p z)) hl
  rw [Real.log_mul (Real.exp_ne_zero _) (folded_pos hh _).ne', Real.log_exp] at hu' hl'
  exact abs_le.mpr ⟨by linarith,by linarith⟩


def gridEligible (h μ D r : ℝ) (p : ℕ) [NeZero p] : Finset (ι → ZMod p) := by
  classical
  exact Finset.univ.filter (fun z => |Real.log (folded h (anchor p z))-(Fintype.card ι : ℝ)*μ| ≤ D ∧
    r ≤ (Finset.univ.filter fun j => |anchor p z j-1/2| ≤ (h^2)⁻¹).card)

lemma round_into_eligible {h c r : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p)
    (hη : (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹ ≤ c)
    (hw : (p : ℝ)⁻¹ ≤ 1/(2*h^2)) {t : ι → ℝ} (ht : ∀ j, t j ∈ Ico 0 1)
    (hg : |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
      r ≤ ∑ j, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t j)) :
    residue p (floorVector p t) ∈ gridEligible h (logMean h) (2*c) r p := by
  classical
  let z := residue p (floorVector p t)
  have hc := cube_mem_gridCell hp ht
  change z ∈ _
  simp only [gridEligible, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · have hd := log_folded_grid_distance hh p hp hc
    have htr := abs_add_le (Real.log (folded h (anchor p z))-Real.log (folded h t))
      (Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h)
    rw [sub_add_sub_cancel, abs_sub_comm (Real.log (folded h (anchor p z))) (Real.log (folded h t))] at htr
    linarith
  · apply hg.2.trans
    have he : ((Finset.univ.filter fun j => |anchor p z j-1/2| ≤ (h^2)⁻¹).card : ℝ) =
        ∑ j, if |anchor p z j-1/2| ≤ (h^2)⁻¹ then (1 : ℝ) else 0 := by
      simp only [←Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [he]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : t j ∈ centralInterval h
    · have hti : |t j-1/2| ≤ 1/(2*h^2) := abs_le.mpr ⟨by linarith [hj.1],by linarith [hj.2]⟩
      have hd := grid_distance hc j
      have hz : |anchor p z j-1/2| ≤ (h^2)⁻¹ := by
        have ha := abs_add_le (anchor p z j-t j) (t j-1/2)
        rw [sub_add_sub_cancel, abs_sub_comm (anchor p z j) (t j)] at ha
        have he : 1/(2*h^2)+1/(2*h^2) = (h^2)⁻¹ := by field_simp; ring
        linarith
      simp only [Set.indicator_of_mem hj, ite_eq_left hz, le_refl]
    · simp only [Set.indicator_of_notMem hj]
      split_ifs <;> norm_num


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gridMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (E : Finset (ι → ZMod p)) :
    0 ≤ gridMass h p E :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => (folded_pos hh _).le))

lemma gridMass_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p]
    {E F : Finset (ι → ZMod p)} (hEF : E ⊆ F) : gridMass h p E ≤ gridMass h p F := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hEF (fun _ _ _ => (folded_pos hh _).le))
  positivity

lemma exp_small_upper {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1/2) : Real.exp η ≤ 1+2*η := by
  apply (Real.exp_bound_div_one_sub_of_interval hη (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-η)).mpr
  nlinarith

lemma grid_from_continuous {h A B : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p : ℕ) [NeZero p] (hp : 0 < p)
    (E : Finset (ι → ZMod p)) (G : Set (ι → ℝ)) (hG : MeasurableSet G)
    (hRound : ∀ t ∈ G, (∀ j, t j ∈ Ico 0 1) → residue p (floorVector p t) ∈ E)
    (ha : 1-(totalMass h)^Fintype.card ι ≤ A)
    (hg : 1-B ≤ (cubeLaw h : Measure (ι → ℝ)).real G)
    (hη : (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹ ≤ 1/2) :
    |gridMass (ι := ι) h p Finset.univ-1| ≤ A+2*((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹) ∧
    |gridMass h p E-1| ≤ A+B+2*((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹) := by
  let η := (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹
  let a := (totalMass h)^Fintype.card ι
  let q := (cubeLaw h : Measure (ι → ℝ)).real G
  change _ ≤ A+2*η ∧ _ ≤ A+B+2*η
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/2 := hη
  have ha0 : 0 ≤ a := pow_nonneg (totalMass_pos hh).le _
  have ha1 : a ≤ 1 := by simpa using pow_le_pow_left₀ (totalMass_pos hh).le (totalMass_le_one hh) (Fintype.card ι)
  let := cubeLaw_isProbability (ι := ι) hh
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  have haq0 : 0 ≤ a*q := mul_nonneg ha0 hq0
  have haq1 : a*q ≤ 1 := (mul_le_mul_of_nonneg_right ha1 hq0).trans (by simpa using hq1)
  have haq : 1-A-B ≤ a*q := by
    have ht := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hq1)
    change 1-a ≤ A at ha
    change 1-B ≤ q at hg
    nlinarith
  have hexp : 1-η ≤ Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
  have htot := grid_integral_total (ι := ι) hh p hp
  have htu : gridMass (ι := ι) h p Finset.univ ≤ 1+2*η := by
    calc
      _ = Real.exp η*(Real.exp (-η)*gridMass (ι := ι) h p Finset.univ) := by rw [←mul_assoc,←Real.exp_add]; simp
      _ ≤ Real.exp η*a := mul_le_mul_of_nonneg_left htot.1 (Real.exp_pos _).le
      _ ≤ Real.exp η := mul_le_of_le_one_right (Real.exp_pos _).le ha1
      _ ≤ _ := exp_small_upper hη0 hη1
  have htl : 1-A-η ≤ gridMass (ι := ι) h p Finset.univ := by
    have ht := remove_exp_factor htot.2
    have ht' := mul_le_mul_of_nonneg_right hexp ha0
    change 1-a ≤ A at ha
    have hn := mul_nonneg hη0 (sub_nonneg.mpr ha1)
    nlinarith
  have hge : a*q = ∫ t in G ∩ cube, folded h t := by
    dsimp [a,q]
    rw [cubeLaw_real hh hG]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ (totalMass_pos hh).ne')]
  have hgl : 1-A-B-η ≤ gridMass h p E := by
    have ht := remove_exp_factor (grid_integral_event hh p hp E G hRound)
    rw [←hge] at ht
    have ht' := mul_le_mul_of_nonneg_right hexp haq0
    have hn := mul_nonneg hη0 (sub_nonneg.mpr haq1)
    nlinarith
  have hgu := (gridMass_mono hh p (Finset.subset_univ E)).trans htu
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith


def continuousGood (h c r : ℝ) : Set (ι → ℝ) :=
  {t | |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
    r ≤ ∑ j, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t j)}

lemma continuousGood_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] {h c r : ℝ} (hh : 0 < h) :
    MeasurableSet (continuousGood (ι := ι) h c r) := by
  have hc : Measurable (fun t : ι → ℝ => ∑ j, (centralInterval h).indicator
      (fun _ => (1 : ℝ)) (t j)) := by
    exact Finset.measurable_sum _ (fun j _ =>
      (measurable_const.indicator (show MeasurableSet (centralInterval h) from measurableSet_Icc)).comp (measurable_pi_apply j))
  exact (measurableSet_lt (((continuous_folded h).log (fun t => (folded_pos hh t).ne')).sub continuous_const).abs.measurable
    measurable_const).inter (measurableSet_le measurable_const hc)


end SingleLatticeCovering.Folded





noncomputable section
open Real Filter Topology
namespace SingleLatticeCovering.Folded

lemma prime_in_log_interval {s r : ℝ} (hs : 0 ≤ s) (hr : Real.log 4 ≤ r) :
    ∃ p : ℕ, p.Prime ∧ s ≤ Real.log p ∧ Real.log p ≤ s+r := by
  have he : 1 ≤ Real.exp s := Real.one_le_exp_iff.mpr hs
  have hn : 0 < ⌈Real.exp s⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  obtain ⟨p,hp,hpl,hpu⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈Real.exp s⌉₊ hn.ne'
  have hpl' : Real.exp s ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpl.le)
  have hpu' : (p : ℝ) ≤ 4*Real.exp s := by
    have h := Nat.ceil_lt_add_one (Real.exp_pos s).le
    have h' : (p : ℝ) ≤ 2*(⌈Real.exp s⌉₊ : ℝ) := by exact_mod_cast hpu
    linarith
  have h4 : (4 : ℝ) ≤ Real.exp r := (Real.log_le_iff_le_exp (by norm_num)).mp hr
  refine ⟨p,hp,(Real.le_log_iff_exp_le (by exact_mod_cast hp.pos)).mpr hpl',?_⟩
  apply (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr
  calc
    _ ≤ 4*Real.exp s := hpu'
    _ ≤ Real.exp r*Real.exp s := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add, add_comm]


theorem block_prime {b μ : ℝ} (_ : 0 < b)
    (hμ : 4*b^(56/100 : ℝ) ≤ b*μ) (hr : Real.log 4 ≤ b^(56/100 : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ b*μ-4*b^(56/100 : ℝ) ≤ Real.log p ∧
      Real.log p ≤ b*μ-3*b^(56/100 : ℝ) := by
  obtain ⟨p,hp,hl,hu⟩ := prime_in_log_interval (sub_nonneg.mpr hμ) hr
  refine ⟨p,hp,hl,?_⟩
  linarith [hu]



theorem eventually_block_prime {μ : ℝ → ℝ} (hμ : Tendsto μ atTop atTop) :
    ∀ᶠ b : ℝ in atTop, ∃ p : ℕ, p.Prime ∧
      b*μ b-4*b^(56/100 : ℝ) ≤ Real.log p ∧
      Real.log p ≤ b*μ b-3*b^(56/100 : ℝ) := by
  have hpow : ∀ᶠ b : ℝ in atTop, 4*b^(56/100 : ℝ) ≤ b := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 44/100)).const_mul (4 : ℝ)
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (4 : ℝ)*0 < 1)),
      eventually_gt_atTop (0 : ℝ)] with b hb hb0
    have hh : b^(-(44/100 : ℝ)) = b^(56/100 : ℝ)/b := by
      calc
        _ = b^((56/100 : ℝ)-1) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_sub hb0, Real.rpow_one]
    rw [hh] at hb
    have hbb : 4*b^(56/100 : ℝ)/b < 1 := by simpa only [mul_div_assoc] using hb
    exact (by nlinarith [(div_lt_iff₀ hb0).mp hbb])
  filter_upwards [eventually_gt_atTop (0 : ℝ), hμ.eventually (eventually_ge_atTop (1 : ℝ)),
    hpow, (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 56/100)).eventually
      (eventually_ge_atTop (Real.log 4))] with b hb hμb hpb hr
  exact block_prime hb (hpb.trans (by nlinarith)) hr



end SingleLatticeCovering.Folded


namespace SingleLatticeCovering.Folded
open Real Filter Topology Asymptotics

lemma eventually_totalMass_half : ∀ᶠ h : ℝ in atTop, 1/2 ≤ totalMass h := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2*Real.log 4)] with h hh hl
  have hp : 0 < h := by linarith
  have he : Real.exp (-(h^2)/2) ≤ (1/4 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  linarith [totalMass_tail hp]

lemma logMean_tendsto : Tendsto logMean atTop atTop := by
  have hl : Tendsto (fun h : ℝ => Real.log h + (-Real.log (Real.sqrt (2*Real.pi))-1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ Real.tendsto_log_atTop
  apply tendsto_atTop_mono' _ _ hl
  filter_upwards [eventually_totalMass_half, eventually_gt_atTop (0 : ℝ)] with h ha hh
  have hb := logMean_lower_of_half hh ha
  linarith



def heightR (b : ℝ) : ℝ := Real.sqrt ((9/4 : ℝ)*Real.log b)

lemma heightR_tendsto : Tendsto heightR atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 9/4) Real.tendsto_log_atTop)

lemma height_tendsto : Tendsto height atTop atTop :=
  heightR_tendsto.comp tendsto_natCast_atTop_atTop

lemma heightR_sq {b : ℝ} (hb : 1 ≤ b) : heightR b^2 = (9/4 : ℝ)*Real.log b :=
  Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg hb))

lemma heightR_pos {b : ℝ} (hb : 1 < b) : 0 < heightR b :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) (Real.log_pos hb))

lemma heightR_exp {b : ℝ} (hb : 1 ≤ b) (c : ℝ) :
    Real.exp (-(heightR b^2)*c) = b^(-(9/4 : ℝ)*c) := by
  rw [heightR_sq hb, Real.rpow_def_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hb)]
  congr 1
  ring

lemma totalMass_power_loss {h : ℝ} (hh : 0 < h) (b : ℕ) :
    0 ≤ 1-(totalMass h)^b ∧ 1-(totalMass h)^b ≤ 2*(b : ℝ)*Real.exp (-(h^2)/2) := by
  have ha := totalMass_pos hh
  have hu := totalMass_le_one hh
  have hp := pow_le_pow_left₀ ha.le hu b
  have hb := one_add_mul_le_pow (a := totalMass h-1) (by linarith : -2 ≤ totalMass h-1) b
  simp only [add_sub_cancel] at hb
  have ht := mul_le_mul_of_nonneg_left (totalMass_tail hh) (Nat.cast_nonneg b : (0 : ℝ) ≤ _)
  simp only [one_pow] at hp
  constructor <;> nlinarith

lemma height_totalMass_power_loss {b : ℕ} (hb : 2 ≤ b) :
    0 ≤ 1-(totalMass (height b))^b ∧
      1-(totalMass (height b))^b ≤ 2*(b : ℝ)^(-(1/8 : ℝ)) := by
  have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hh : 0 < height b := heightR_pos (by exact_mod_cast (show 1 < b by omega))
  have ht := totalMass_power_loss hh b
  have he : Real.exp (-(height b^2)/2) = (b : ℝ)^(-(9/8 : ℝ)) := by
    calc
      _ = Real.exp (-(heightR (b : ℝ)^2)*(1/2)) := by change Real.exp (-(heightR (b : ℝ)^2)/2) = _; congr 1; ring
      _ = (b : ℝ)^(-(9/4 : ℝ)*(1/2)) := heightR_exp hb1 (1/2)
      _ = _ := by norm_num
  rw [he] at ht
  have hm : (b : ℝ)*(b : ℝ)^(-(9/8 : ℝ)) = (b : ℝ)^(-(1/8 : ℝ)) := by
    calc
      _ = (b : ℝ)^(1 : ℝ)*(b : ℝ)^(-(9/8 : ℝ)) := by rw [Real.rpow_one]
      _ = (b : ℝ)^((1 : ℝ)-(9/8 : ℝ)) := by rw [sub_eq_add_neg, Real.rpow_add hb0]
      _ = _ := by norm_num
  exact ⟨ht.1, by simpa only [mul_assoc, hm] using ht.2⟩

lemma eventually_height_prime : ∀ᶠ b : ℕ in atTop, ∃ p : ℕ, p.Prime ∧
    (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p ∧
    Real.log p ≤ (b : ℝ)*logMean (height b)-3*(b : ℝ)^(56/100 : ℝ) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_block_prime (logMean_tendsto.comp heightR_tendsto))




end SingleLatticeCovering.Folded


namespace SingleLatticeCovering.Folded
open Real Filter Topology Asymptotics

lemma eventually_logpow_bound {s c : ℝ} (r : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, (Real.log b)^r ≤ c*b^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop r hs).bound hc,
    eventually_ge_atTop (1 : ℝ)] with b hb hb1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hb1) _),
    abs_of_nonneg (Real.rpow_nonneg (le_trans (by norm_num) hb1) _)] using hb

lemma eventually_height_bound {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, heightR b ≤ c*b^s := by
  filter_upwards [eventually_logpow_bound (1 : ℝ) hs (div_pos hc (by norm_num : (0 : ℝ) < 3/2)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with b hb hl
  rw [Real.rpow_one] at hb
  have hsqrt : heightR b ≤ (3/2 : ℝ)*Real.log b := by
    unfold heightR
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (Real.log b-1)]
  nlinarith

lemma eventually_height_square_le : ∀ᶠ b : ℝ in atTop, heightR b^2 ≤ b := by
  filter_upwards [eventually_logpow_bound (1 : ℝ) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 4/9), eventually_ge_atTop (1 : ℝ)] with b hb hb1
  rw [Real.rpow_one, Real.rpow_one] at hb
  rw [heightR_sq hb1]
  linarith

lemma eventually_central_mean : ∀ᶠ b : ℝ in atTop,
    2*b^(70/100 : ℝ) ≤ b*Real.exp (-(heightR b^2)/8)/(heightR b*Real.sqrt (2*Real.pi)) := by
  have hc : 0 < 1/(2*Real.sqrt (2*Real.pi)) := by positivity
  filter_upwards [eventually_height_bound (by norm_num : (0 : ℝ) < 3/160) hc,
    eventually_gt_atTop (1 : ℝ)] with b hb hb1
  have hb0 : 0 < b := by linarith
  have hh := heightR_pos hb1
  have hexp : Real.exp (-(heightR b^2)/8) = b^(-(9/32 : ℝ)) := by
    calc
      _ = Real.exp (-(heightR b^2)*(1/8)) := by congr 1; ring
      _ = b^(-(9/4 : ℝ)*(1/8)) := heightR_exp hb1.le (1/8)
      _ = _ := by norm_num
  rw [hexp, le_div_iff₀ (by positivity)]
  have hh' : 2*(heightR b*Real.sqrt (2*Real.pi)) ≤ b^(3/160 : ℝ) := by
    have hs : 0 < Real.sqrt (2*Real.pi) := by positivity
    have ht := (le_div_iff₀ (show (0 : ℝ) < 2*Real.sqrt (2*Real.pi) by positivity)).mp
      (show heightR b ≤ b^(3/160 : ℝ)/(2*Real.sqrt (2*Real.pi)) by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hb)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg hb0.le (70/100 : ℝ))
  have he : b^(70/100 : ℝ)*b^(3/160 : ℝ) = b*b^(-(9/32 : ℝ)) := by
    calc
      _ = b^((70/100 : ℝ)+3/160) := (Real.rpow_add hb0 _ _).symm
      _ = b^((1 : ℝ)+(-(9/32 : ℝ))) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hb0, Real.rpow_one]
  rw [he] at hm
  nlinarith

lemma eventually_log_variance_tail : ∀ᶠ b : ℝ in atTop,
    b*((Real.log 2+heightR b^2/8)/2)^2/((1/2 : ℝ)*b^(56/100 : ℝ))^2 ≤ b^(-(1/20 : ℝ)) := by
  filter_upwards [eventually_logpow_bound (2 : ℝ) (by norm_num : (0 : ℝ) < 7/100)
    (by norm_num : (0 : ℝ) < 1/4), eventually_ge_atTop (2 : ℝ)] with b hb hb2
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hb2
  have hl0 := Real.log_nonneg hb1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.rpow_two] at hb
  have hsq : ((Real.log 2+heightR b^2/8)/2)^2 ≤ (Real.log b)^2 := by
    rw [heightR_sq hb1]
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hr2 : (b^(56/100 : ℝ))^2 = b^(112/100 : ℝ) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hb0.le]
    norm_num
  have he : b^(-(1/20 : ℝ))*((1/2 : ℝ)*b^(56/100 : ℝ))^2 = (1/4 : ℝ)*b*b^(7/100 : ℝ) := by
    rw [mul_pow, hr2]
    have hpow : b^(-(1/20 : ℝ))*b^(112/100 : ℝ) = b*b^(7/100 : ℝ) := by
      calc
        _ = b^(-(1/20 : ℝ)+(112/100 : ℝ)) := (Real.rpow_add hb0 _ _).symm
        _ = b^((1 : ℝ)+(7/100 : ℝ)) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_add hb0, Real.rpow_one]
    nlinarith
  apply (div_le_iff₀ (by positivity)).mpr
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left (hsq.trans hb) hb0.le]



end SingleLatticeCovering.Folded



end
end
end
end
end
end
end

end OAI
