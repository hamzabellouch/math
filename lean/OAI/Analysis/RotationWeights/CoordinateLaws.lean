import OAI.Analysis.RotationWeights.CouplingMoments

namespace OAI

noncomputable section

universe uκ uD

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
namespace CircleCoupling

def roundedWidth (l : ℕ) (w : ℝ) : ℕ := ⌊w*l/2⌋₊
def roundedTag (l : ℕ) (m : ℝ) : ℕ := ⌊(l : ℝ)/m⌋₊
def crossingProbability (κ w m : ℝ) : ℝ := κ*Real.sqrt (w/m)

lemma width_rounding (l : ℕ) (m w : ℝ) (hm : 200 ≤ m)
    (hl : 100*m ≤ l) (hwlo : 1/m ≤ w) (hwhi : w ≤ 1/4) :
    0 < roundedWidth l w ∧ roundedWidth l w < l ∧
      (l:ℝ)*w/3 ≤ roundedWidth l w ∧ (roundedWidth l w:ℝ) ≤ (l:ℝ)*w/2 := by
  have hm0 : 0 < m := by linarith
  have hl0 : (0:ℝ) < l := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hwlo
  have hwl : 100 ≤ w*l := by
    have hh := mul_le_mul_of_nonneg_left hl hw0.le
    have hh' : 1 ≤ w*m := (div_le_iff₀ hm0).mp hwlo
    nlinarith
  have hfloor := Nat.floor_le (show 0 ≤ w*l/2 by positivity)
  have hlow := Nat.lt_floor_add_one (w*l/2)
  change (roundedWidth l w : ℝ)  ≤  w*l/2 at hfloor
  change w*l/2  <  (roundedWidth l w : ℝ)+1 at hlow
  have hthird : (l:ℝ)*w/3 ≤ roundedWidth l w := by nlinarith
  refine ⟨?_,?_,hthird,by nlinarith⟩
  · have : (0:ℝ) < roundedWidth l w := lt_of_lt_of_le (by positivity) hthird
    exact_mod_cast this
  · have : (roundedWidth l w:ℝ) < l := by nlinarith
    exact_mod_cast this

lemma tag_rounding (l : ℕ) (m : ℝ) (hm : 200 ≤ m) (hl : 100*m ≤ l) :
    0 < roundedTag l m ∧ roundedTag l m < l ∧
      (l:ℝ)/(2*m) ≤ roundedTag l m ∧ (roundedTag l m:ℝ) ≤ (l:ℝ)/m := by
  have hm0 : 0 < m := by linarith
  have hl0 : (0:ℝ) < l := by linarith
  have hdiv : 100 ≤ (l:ℝ)/m := (le_div_iff₀ hm0).mpr hl
  have hfloor := Nat.floor_le (show 0 ≤ (l:ℝ)/m by positivity)
  have hlow := Nat.lt_floor_add_one ((l:ℝ)/m)
  change (roundedTag l m : ℝ)  ≤  (l:ℝ)/m at hfloor
  change (l:ℝ)/m  <  (roundedTag l m : ℝ)+1 at hlow
  have hhalf : (l:ℝ)/(2*m) = ((l:ℝ)/m)/2 := by ring
  refine ⟨?_,?_,?_,hfloor⟩
  · have : (0:ℝ) < roundedTag l m := by linarith
    exact_mod_cast this
  · have hlt : (l:ℝ)/m  <  l := (div_lt_iff₀ hm0).mpr (by nlinarith)
    exact_mod_cast hfloor.trans_lt hlt
  · rw [hhalf]; linarith

lemma crossingProbability_nonneg {κ w m : ℝ} (hκ : 0 ≤ κ) :
    0 ≤ crossingProbability κ w m := mul_nonneg hκ (Real.sqrt_nonneg _)

lemma crossingProbability_sq {κ w m : ℝ} (hw : 0 ≤ w) (hm : 0 ≤ m) :
    (crossingProbability κ w m)^2=κ^2*w/m := by
  rw [crossingProbability,mul_pow,Real.sq_sqrt (div_nonneg hw hm)]
  ring

lemma crossingProbability_div_le {κ w m : ℝ} (hκ : 0 ≤ κ) (hm : 0 < m) (hw : 1/m ≤ w) :
    crossingProbability κ w m/w ≤ κ := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hwm : 1 ≤ w*m := (div_le_iff₀ hm).mp hw
  have hroot : Real.sqrt (w/m) ≤ w := by
    apply (Real.sqrt_le_left hw0.le).mpr
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwm hw0.le]
  apply (div_le_iff₀ hw0).mpr
  exact mul_le_mul_of_nonneg_left hroot hκ

lemma crossingProbability_le_kappa {κ w m : ℝ} (hκ : 0 ≤ κ) (hm : 1 ≤ m) (hw : w ≤ 1) :
    crossingProbability κ w m ≤ κ := by
  have hm0 : 0 < m := by linarith
  have hr : Real.sqrt (w/m) ≤ 1 := (Real.sqrt_le_one).mpr ((div_le_one hm0).mpr (hw.trans hm))
  simpa [crossingProbability] using mul_le_mul_of_nonneg_left hr hκ

lemma six_probabilities_le_one (κ a b m : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1/100)
    (hm : 200 ≤ m) (ha : a ≤ 1/4) (hb : b ≤ 1/4)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1/m) :
    2*ENNReal.ofReal (crossingProbability κ a m)+
      2*ENNReal.ofReal (crossingProbability κ b m)+ENNReal.ofReal τ ≤ 1 := by
  have hhρ := crossingProbability_le_kappa hκ0 (by linarith : 1 ≤ m) (by linarith : a ≤ 1)
  have hhσ := crossingProbability_le_kappa hκ0 (by linarith : 1 ≤ m) (by linarith : b ≤ 1)
  have hτ' : τ ≤ 1/200 := hτ.trans ((div_le_div_iff_of_pos_left (by norm_num) (by linarith) (by norm_num)).mpr hm)
  have hρ0 := crossingProbability_nonneg (w := a) (m := m) hκ0
  have hσ0 := crossingProbability_nonneg (w := b) (m := m) hκ0
  rw [← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num),← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) hτ0]
  exact ENNReal.ofReal_le_one.mpr (by linarith)

structure CoordinateParameters where
  l : ℕ
  m : ℕ
  κ : ℝ
  a : ℝ
  b : ℝ
  hm : 200 ≤ m
  hl : 100*m ≤ l
  hκ0 : 0 ≤ κ
  hκ : κ ≤ 1/100
  ha : 1/(m:ℝ) ≤ a ∧ a ≤ 1/4
  hb : 1/(m:ℝ) ≤ b ∧ b ≤ 1/4
namespace CoordinateParameters
variable (P : CoordinateParameters)
instance : NeZero P.l := ⟨by have := P.hm; have := P.hl; omega⟩
lemma m_pos : (0:ℝ)<P.m := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<200) P.hm
lemma a_pos : 0<P.a := lt_of_lt_of_le (by have := P.m_pos; positivity) P.ha.1
lemma b_pos : 0<P.b := lt_of_lt_of_le (by have := P.m_pos; positivity) P.hb.1
lemma width_a : 0 < roundedWidth P.l P.a ∧ roundedWidth P.l P.a < P.l ∧
    (P.l:ℝ)*P.a/3 ≤ roundedWidth P.l P.a ∧ (roundedWidth P.l P.a:ℝ) ≤ (P.l:ℝ)*P.a/2 := width_rounding P.l P.m P.a (by exact_mod_cast P.hm) (by exact_mod_cast P.hl) P.ha.1 P.ha.2
lemma width_b : 0 < roundedWidth P.l P.b ∧ roundedWidth P.l P.b < P.l ∧
    (P.l:ℝ)*P.b/3 ≤ roundedWidth P.l P.b ∧ (roundedWidth P.l P.b:ℝ) ≤ (P.l:ℝ)*P.b/2 := width_rounding P.l P.m P.b (by exact_mod_cast P.hm) (by exact_mod_cast P.hl) P.hb.1 P.hb.2
lemma tag_bounds : 0 < roundedTag P.l P.m ∧ roundedTag P.l P.m < P.l ∧
    (P.l:ℝ)/(2*P.m) ≤ roundedTag P.l P.m ∧ (roundedTag P.l P.m:ℝ) ≤ (P.l:ℝ)/P.m := tag_rounding P.l P.m (by exact_mod_cast P.hm) (by exact_mod_cast P.hl)
def ρ : ℝ := crossingProbability P.κ P.a P.m
def σ : ℝ := crossingProbability P.κ P.b P.m
def τ (tagged : Bool) : ℝ := if tagged then 1/(P.m:ℝ) else 0
lemma ρ_nonneg : 0 ≤ P.ρ := crossingProbability_nonneg P.hκ0
lemma σ_nonneg : 0 ≤ P.σ := crossingProbability_nonneg P.hκ0
lemma τ_nonneg (tagged : Bool) : 0 ≤ P.τ tagged := by unfold τ; split <;> positivity
lemma τ_le (tagged : Bool) : P.τ tagged ≤ 1/(P.m:ℝ) := by unfold τ; split <;> first | rfl | positivity
lemma ρ_le_one : P.ρ ≤ 1 := (crossingProbability_le_kappa P.hκ0 (by exact_mod_cast (by have := P.hm; omega : 1≤P.m)) (by linarith [P.ha.2])).trans (by linarith [P.hκ])
lemma σ_le_one : P.σ ≤ 1 := (crossingProbability_le_kappa P.hκ0 (by exact_mod_cast (by have := P.hm; omega : 1≤P.m)) (by linarith [P.hb.2])).trans (by linarith [P.hκ])
lemma probabilities (tagged : Bool) : 2*ENNReal.ofReal P.ρ+2*ENNReal.ofReal P.σ+ENNReal.ofReal (P.τ tagged) ≤ 1 :=
  six_probabilities_le_one P.κ P.a P.b P.m P.hκ0 P.hκ (by exact_mod_cast P.hm) P.ha.2 P.hb.2
    (P.τ tagged) (P.τ_nonneg tagged) (P.τ_le tagged)

abbrev Sample := Option (Fin 5) × (Fin P.l × Fin P.l)
def law (tagged : Bool) : Measure P.Sample :=
  sixLaw P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m)
    ⟨P.width_a.1,P.width_a.2.1⟩ ⟨P.width_b.1,P.width_b.2.1⟩ ⟨P.tag_bounds.1,P.tag_bounds.2.1⟩
    (ENNReal.ofReal P.ρ) (ENNReal.ofReal P.σ) (ENNReal.ofReal (P.τ tagged))
instance (tagged : Bool) : IsProbabilityMeasure (P.law tagged) :=
  sixLaw_probability _ _ _ _ _ _ _ _ _ _ (P.probabilities tagged)

lemma rounded_width_a_half : (roundedWidth P.l P.a:ℝ) ≤ (P.l:ℝ)/2 := by
  have hl : (0:ℝ) ≤ P.l := Nat.cast_nonneg _
  calc
    _ ≤ (P.l:ℝ)*P.a/2 := P.width_a.2.2.2
    _ ≤ _ := by nlinarith [P.ha.2]
lemma rounded_width_b_half : (roundedWidth P.l P.b:ℝ) ≤ (P.l:ℝ)/2 := by
  have hl : (0:ℝ) ≤ P.l := Nat.cast_nonneg _
  calc
    _ ≤ (P.l:ℝ)*P.b/2 := P.width_b.2.2.2
    _ ≤ _ := by nlinarith [P.hb.2]
lemma rounded_tag_half : (roundedTag P.l P.m:ℝ) ≤ (P.l:ℝ)/2 := by
  apply P.tag_bounds.2.2.2.trans
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by exact_mod_cast (by have := P.hm; omega : 2≤P.m))

lemma law_second_moment (tagged e : Bool) :
    (P.l:ℝ)* ∑ d : Fin P.l, ((P.law tagged).real {ω | digitEndpoint e ω.2=d})^2 ≤
      1+(60*P.κ^2+10*(if tagged then (1:ℝ) else 0))/(P.m:ℝ) := by
  apply sixLaw_second_moment _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.a_pos P.b_pos P.m_pos
    P.ρ_nonneg P.σ_nonneg (P.τ_nonneg tagged) P.width_a.2.2.1 P.rounded_width_a_half
    P.width_b.2.2.1 P.rounded_width_b_half P.tag_bounds.2.2.1 P.rounded_tag_half
    (crossingProbability_sq P.a_pos.le P.m_pos.le) (crossingProbability_sq P.b_pos.le P.m_pos.le) _ (P.probabilities tagged)
  cases tagged <;> simp [τ,one_div,inv_pow]

lemma law_density_ten (tagged e : Bool) (d : Fin P.l) :
    (P.law tagged).real {ω | digitEndpoint e ω.2=d} ≤ 10/(P.l:ℝ) := by
  apply sixLaw_density_ten _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.a_pos P.b_pos P.m_pos
    P.hκ P.ρ_nonneg P.σ_nonneg (P.τ_nonneg tagged) P.width_a.2.2.1 P.rounded_width_a_half
    P.width_b.2.2.1 P.rounded_width_b_half P.tag_bounds.2.2.1 P.rounded_tag_half
    (crossingProbability_div_le P.hκ0 P.m_pos P.ha.1) (crossingProbability_div_le P.hκ0 P.m_pos P.hb.1)
    (P.τ_le tagged) (P.probabilities tagged)
end CoordinateParameters
lemma ae_labelled {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    (a : Option κ) (μ : Measure (D × D)) (P : Option κ × (D × D) → Prop)
    (hP : MeasurableSet {z | P z}) (h : ∀ᵐ z ∂μ, P (a,z)) :
    ∀ᵐ z ∂labelled a μ, P z := by
  exact (ae_map_iff (by fun_prop) hP).mpr h

lemma ae_mixture {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D)) (μ : κ → Measure (D × D))
    (P : Option κ × (D × D) → Prop) (hP : MeasurableSet {z | P z})
    (h₀ : ∀ᵐ z ∂μ₀, P (none,z)) (h : ∀ a, ∀ᵐ z ∂μ a, P (some a,z)) :
    ∀ᵐ z ∂mixture p p₀ μ₀ μ, P z := by
  rw [mixture,ae_add_measure_iff,ae_finsetSum_measure_iff]
  exact ⟨Measure.ae_smul_measure (ae_labelled _ _ _ hP h₀) _,fun a _ =>
    Measure.ae_smul_measure (ae_labelled _ _ _ hP (h a)) _⟩

def supportCondition (l t u r : ℕ) (z : Option (Fin 5) × (Fin l × Fin l)) : Prop :=
  match z.1 with
  | none => z.2.1 = z.2.2
  | some a => if a=0 then z.2.1.val < l-t ∧ l-t ≤ z.2.2.val
    else if a=1 then z.2.1.val < t ∧ t ≤ z.2.2.val
    else if a=2 then z.2.1.val < l-u ∧ l-u ≤ z.2.2.val
    else if a=3 then z.2.1.val < u ∧ u ≤ z.2.2.val
    else z.2.1.val < r ∧ l-r ≤ z.2.2.val

lemma sixLaw_support (l t u r : ℕ) [NeZero l] (ht : 0 < t ∧ t < l)
    (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l) (p q τ : ℝ≥0∞) :
    ∀ᵐ z ∂sixLaw l t u r ht hu hr p q τ, supportCondition l t u r z := by
  apply ae_mixture _ _ _ _ _ (by measurability)
  · unfold diagonal
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    exact ae_of_all _ (fun _ => rfl)
  · intro a
    fin_cases a <;> dsimp [supportCondition,components] <;>
      apply rectangle_ae

namespace CoordinateParameters
variable (P : CoordinateParameters)
lemma law_support (tagged : Bool) :
    ∀ᵐ z ∂P.law tagged, supportCondition P.l (roundedWidth P.l P.a)
      (roundedWidth P.l P.b) (roundedTag P.l P.m) z :=
  sixLaw_support _ _ _ _ _ _ _ _ _ _
lemma law_order (tagged : Bool) : ∀ᵐ z ∂P.law tagged, z.2.1 ≤ z.2.2 := by
  filter_upwards [P.law_support tagged] with z hz
  have htag : 2*roundedTag P.l P.m ≤ P.l := by
    have h := P.rounded_tag_half
    have : (2:ℝ)*(roundedTag P.l P.m:ℝ) ≤ P.l := by linarith
    exact_mod_cast this
  rcases z with ⟨a,x,y⟩
  cases a with
  | none => exact le_of_eq hz
  | some a =>
    fin_cases a <;> simp [supportCondition] at hz <;>
      change x.val ≤ y.val <;> omega

lemma top_a_failure (tagged : Bool) (d : Fin P.l)
    (hd : d.val < P.l-roundedWidth P.l P.a) :
    P.law tagged ({z | z.2.1=d} ∩ {z | z.1=some (0:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.ρ/10)*P.law tagged {z | z.2.1=d} :=
  sixLaw_top_t_failure _ _ _ _ _ _ _ _ _ _ P.ρ_nonneg P.ρ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged false d)
lemma bottom_a_failure (tagged : Bool) (d : Fin P.l)
    (hd : roundedWidth P.l P.a ≤ d.val) :
    P.law tagged ({z | z.2.2=d} ∩ {z | z.1=some (1:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.ρ/10)*P.law tagged {z | z.2.2=d} :=
  sixLaw_bottom_t_failure _ _ _ _ _ _ _ _ _ _ P.ρ_nonneg P.ρ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged true d)
lemma top_b_failure (tagged : Bool) (d : Fin P.l)
    (hd : d.val < P.l-roundedWidth P.l P.b) :
    P.law tagged ({z | z.2.1=d} ∩ {z | z.1=some (2:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.σ/10)*P.law tagged {z | z.2.1=d} :=
  sixLaw_top_u_failure _ _ _ _ _ _ _ _ _ _ P.σ_nonneg P.σ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged false d)
lemma bottom_b_failure (tagged : Bool) (d : Fin P.l)
    (hd : roundedWidth P.l P.b ≤ d.val) :
    P.law tagged ({z | z.2.2=d} ∩ {z | z.1=some (3:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.σ/10)*P.law tagged {z | z.2.2=d} :=
  sixLaw_bottom_u_failure _ _ _ _ _ _ _ _ _ _ P.σ_nonneg P.σ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged true d)
end CoordinateParameters
end CircleCoupling

end

end OAI
