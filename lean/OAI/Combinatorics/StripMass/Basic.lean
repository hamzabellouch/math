import Mathlib

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory

def rho : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)
def c : ℝ := Real.cos (3 * Real.pi / 8)
def lambda : ℝ := Real.pi / 8
def d : ℝ := Real.cos (2 * lambda)
def C : ℝ := Real.cos lambda
def eta : ℝ := 2 * d - 1

abbrev Triangle := ℤ × ℕ × Bool

def up (i : ℤ) (j : ℕ) : Triangle := (i, j, true)
def down (i : ℤ) (j : ℕ) : Triangle := (i, j, false)

def upDownAdjacent (v w : Triangle) : Prop :=
  v.2.2 = true ∧ w.2.2 = false ∧
    ((v.2.1 = w.2.1 ∧ (w.1 = v.1 ∨ w.1 + 1 = v.1)) ∨
      (v.2.1 = w.2.1 + 1 ∧ v.1 = w.1))

def adjacent (v w : Triangle) : Prop := upDownAdjacent v w ∨ upDownAdjacent w v

 
def IsPath (N : ℕ) (finish : Triangle) (p : List Triangle) : Prop :=
  p.head? = some (up 0 0) ∧ p.getLast? = some finish ∧ p.Nodup ∧
  p.IsChain adjacent ∧ ∀ v ∈ p, v.2.1 < N

 
def archWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if k ≠ 0 ∧ IsPath N (up k 0) p then rho ^ p.length else 0

 
def bridgeWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if 0 < N ∧ IsPath N (down k (N - 1)) p then rho ^ p.length else 0

def K (N : ℕ) (k : ℤ) : ℝ := ∑' p, archWeight N k p
def bridgeKernel (N : ℕ) (k : ℤ) : ℝ := ∑' p, bridgeWeight N k p
def archMass (N : ℕ) : ℝ := ∑' k : ℤ, K N k
def bridgeMass (N : ℕ) : ℝ := ∑' k : ℤ, bridgeKernel N k
def moment (N : ℕ) : ℝ := ∑' k : ℕ, (k + 1 : ℝ) * K N (k + 1)

 
def StripSumsFinite (N : ℕ) : Prop :=
  (∀ k : ℤ, Summable (archWeight N k)) ∧
  (∀ k : ℤ, Summable (bridgeWeight N k)) ∧
  Summable (K N) ∧ Summable (bridgeKernel N) ∧
  Summable (fun k : ℕ => (k + 1 : ℝ) * K N (k + 1))

 
def Comparable (f g : ℕ → ℝ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
    ∀ N : ℕ, 1 ≤ N → lo * g N ≤ f N ∧ f N ≤ hi * g N

 
def CriticalStripMass : Prop :=
  (∀ N : ℕ, 1 ≤ N → StripSumsFinite N) ∧
  (∀ N : ℕ, 1 ≤ N → c * archMass N + bridgeMass N = 1) ∧
  Comparable (fun N => moment (N + 1) - moment N) bridgeMass ∧
  Comparable moment (fun N => (N : ℝ) ^ (3 / 4 : ℝ)) ∧
  Comparable bridgeMass (fun N => (N : ℝ) ^ (-(1 / 4) : ℝ)) ∧
  (∀ N : ℕ, 1 ≤ N → bridgeMass (N + 1) ≤ bridgeMass N)

 
def homogeneousQ (N : ℕ) (g : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C C) ^ (2 * N + 1) *
    (Polynomial.X - Polynomial.C c) ^ N * g

def harmonicCoordinate : Polynomial ℝ := Polynomial.X ^ 2 * (1 - Polynomial.X ^ 2)

def HasProjection (N : ℕ) (Q : Polynomial ℝ) : Prop :=
  ∃ P J E : Polynomial ℝ,
    P.natDegree ≤ N ∧ J.natDegree ≤ N ∧ E.degree < (N : WithBot ℕ) ∧
    Q = P.comp harmonicCoordinate + Polynomial.X * J.comp harmonicCoordinate +
      Polynomial.X ^ 2 * E.comp harmonicCoordinate

def MonicProblem (N : ℕ) (g : Polynomial ℝ) : Prop :=
  g.Monic ∧ g.natDegree = N ∧ HasProjection N (homogeneousQ N g)

 
def omega (x : ℝ) : ℝ := (1 / 2) * Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1)

def pairKernel (x y : ℝ) : ℝ := (y - x) ^ 2 / (y + x)

def orderedDomain (N : ℕ) : Set (Fin N → ℝ) :=
  {y | StrictMono y ∧ ∀ i, y i ∈ Ioo 0 1}

def density (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  (∏ i, omega (y i)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (y i) (y j)

def normalizer (N : ℕ) : ℝ := ∫ y in orderedDomain N, density N y

def expectation (N : ℕ) (f : (Fin N → ℝ) → ℝ) : ℝ :=
  (∫ y in orderedDomain N, f y * density N y) / normalizer N

def reflectionProduct (N : ℕ) (x : ℝ) (y : Fin N → ℝ) : ℝ :=
  ∏ i, (y i - x) / (y i + x)

def momentIntegrand (N : ℕ) (x : ℝ) : ℝ :=
  (1 - expectation N (reflectionProduct N x)) * omega x / x

 

def PositiveIntegralCore : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    (∃! g : Polynomial ℝ, MonicProblem N g) ∧
    IntegrableOn (density N) (orderedDomain N) ∧ 0 < normalizer N ∧
    IntegrableOn (momentIntegrand N) (Ioo 0 1) ∧
    moment N = (eta / Real.pi) * ∫ x in Ioo 0 1, momentIntegrand N x

 
theorem omega_nonneg (x : ℝ) : 0 ≤ omega x := by
  unfold omega
  positivity

theorem omega_pos {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < omega x := by
  have hx0 := hx.1
  have hh : 1 < (1 + x) / (2 * x) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * x)).2
    linarith [hx.2]
  have hh' : 1 < Real.sqrt ((1 + x) / (2 * x)) := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hh
  unfold omega
  exact mul_pos (by norm_num) (Real.sqrt_pos.2 (sub_pos.2 hh'))

theorem omega_le_rpow {x : ℝ} (hx : x ∈ Ioo 0 1) :
    omega x ≤ x ^ (-(1 / 4 : ℝ)) := by
  have hx0 := hx.1
  have ha : (1 + x) / (2 * x) ≤ 1 / x := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * x) hx.1).2
    nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)]
  have hb : Real.sqrt ((1 + x) / (2 * x)) - 1 ≤ Real.sqrt (1 / x) :=
    (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.sqrt_le_sqrt ha)
  calc
    omega x ≤ Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1) := by
      unfold omega
      nlinarith [Real.sqrt_nonneg (Real.sqrt ((1 + x) / (2 * x)) - 1)]
    _ ≤ Real.sqrt (Real.sqrt (1 / x)) := Real.sqrt_le_sqrt hb
    _ = x ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by positivity : 0 ≤ 1 / x)]
      norm_num only [one_div, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
      rw [Real.inv_rpow hx.1.le, Real.rpow_neg hx.1.le]

theorem measurable_omega : Measurable omega := by
  unfold omega
  fun_prop

theorem integrableOn_omega : IntegrableOn omega (Ioo 0 1) := by
  have hh : IntegrableOn (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2
      (by norm_num)
  apply hh.mono' measurable_omega.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (omega_nonneg x)] using omega_le_rpow hx

theorem pairKernel_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < pairKernel x y := by
  unfold pairKernel
  exact div_pos (sq_pos_of_pos (sub_pos.2 hxy)) (by linarith)

theorem pairKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ pairKernel x y := by
  unfold pairKernel
  positivity

theorem pairKernel_le_one {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    pairKernel x y ≤ 1 := by
  unfold pairKernel
  apply (div_le_one (by linarith [hx.1, hy.1] : 0 < y + x)).2
  have hxx : x ^ 2 ≤ x := by nlinarith [hx.1, hx.2]
  have hyy : y ^ 2 ≤ y := by nlinarith [hy.1, hy.2]
  nlinarith [mul_pos hx.1 hy.1]

theorem density_pos {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N) :
    0 < density N y := by
  apply mul_pos
  · exact Finset.prod_pos fun i _ => omega_pos (hy.2 i)
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    exact pairKernel_pos (hy.2 i).1 (hy.1 (Finset.mem_Ioi.1 hj))

theorem density_le_product {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N) :
    density N y ≤ ∏ i, omega (y i) := by
  have h0 : 0 ≤ ∏ i : Fin N, omega (y i) :=
    Finset.prod_nonneg fun _ _ => omega_nonneg _
  suffices hh : (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, pairKernel (y i) (y j)) ≤ 1 by
    simpa only [density, mul_one] using mul_le_mul_of_nonneg_left hh h0
  apply Finset.prod_le_one₀
  · intro i _
    exact Finset.prod_nonneg fun j _ => pairKernel_nonneg (hy.2 i).1.le (hy.2 j).1.le
  · intro i _
    exact Finset.prod_le_one₀
      (fun j _ => pairKernel_nonneg (hy.2 i).1.le (hy.2 j).1.le)
      (fun j _ => pairKernel_le_one (hy.2 i) (hy.2 j))

theorem measurable_density (N : ℕ) : Measurable (density N) := by
  unfold density pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ => measurable_omega.comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

theorem isOpen_orderedDomain (N : ℕ) : IsOpen (orderedDomain N) := by
  have heq : orderedDomain N =
      (⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {y | y i < y j}) ∩
      (⋂ i : Fin N, {y | y i ∈ Ioo (0 : ℝ) 1}) := by
    ext y
    simp only [orderedDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictMono]
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

theorem integrableOn_density (N : ℕ) : IntegrableOn (density N) (orderedDomain N) := by
  have hi : IntegrableOn (fun y : Fin N → ℝ => ∏ i, omega (y i))
      (Set.univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1) := by
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun _ => integrableOn_omega
  have his : IntegrableOn (fun y : Fin N → ℝ => ∏ i, omega (y i)) (orderedDomain N) :=
    hi.mono_set (fun _ hy => fun i _ => hy.2 i)
  apply his.mono' (measurable_density N).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  simpa only [Real.norm_eq_abs, abs_of_pos (density_pos hy)] using density_le_product hy

 theorem orderedDomain_nonempty (N : ℕ) : (orderedDomain N).Nonempty := by
  refine ⟨fun i => ((i : ℕ) + 1 : ℝ) / (N + 1 : ℕ), ?_⟩
  constructor
  · intro i j hij
    apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < (N + 1 : ℕ))).2
    exact_mod_cast Nat.add_lt_add_right hij 1
  · intro i
    constructor
    · exact div_pos (by positivity) (by positivity)
    · apply (div_lt_one (by positivity : (0 : ℝ) < (N + 1 : ℕ))).2
      exact_mod_cast Nat.add_lt_add_right i.isLt 1

theorem normalizer_pos (N : ℕ) : 0 < normalizer N := by
  have hpos : 0 ≤ᵐ[volume.restrict (orderedDomain N)] density N := by
    filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
    exact (density_pos hy).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos (integrableOn_density N)).2
  have hs : orderedDomain N ⊆ Function.support (density N) :=
    fun y hy => (density_pos hy).ne'
  have hm := (isOpen_orderedDomain N).measure_pos volume (orderedDomain_nonempty N)
  calc
    0 < volume (orderedDomain N) := hm
    _ = (volume.restrict (orderedDomain N)) (orderedDomain N) :=
      (Measure.restrict_apply_self _ _).symm
    _ ≤ (volume.restrict (orderedDomain N)) (Function.support (density N)) := measure_mono hs

 
theorem integrableOn_power_omega (s : ℝ) (hs : -(3 / 4 : ℝ) < s) :
    IntegrableOn (fun x : ℝ => x ^ s * omega x) (Ioo 0 1) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (s - 1 / 4)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by linarith)
  apply hp.mono' ((measurable_id.pow_const s).mul measurable_omega).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 := hx.1
  change ‖x ^ s * omega x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx.1 s).le (omega_nonneg x))]
  calc
    x ^ s * omega x ≤ x ^ s * x ^ (-(1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (omega_le_rpow hx) (Real.rpow_pos_of_pos hx.1 s).le
    _ = x ^ (s - 1 / 4) := by rw [← Real.rpow_add hx.1]; rfl

theorem integrableOn_coordinate_weight (N : ℕ) (i : Fin N) :
    IntegrableOn (fun y : Fin N → ℝ => (y i) ^ (-(1 / 2 : ℝ)) * density N y)
      (orderedDomain N) := by
  classical
  let f : Fin N → ℝ → ℝ := fun j t => (if j = i then t ^ (-(1 / 2 : ℝ)) else 1) * omega t
  have hf : ∀ j, IntegrableOn (f j) (Ioo 0 1) := by
    intro j
    by_cases hj : j = i
    · simpa only [f, hj, ite_true] using integrableOn_power_omega (-(1 / 2 : ℝ)) (by norm_num)
    · simpa only [f, hj, ite_false, one_mul] using integrableOn_omega
  have hp : IntegrableOn (fun y : Fin N → ℝ => (y i) ^ (-(1 / 2 : ℝ)) * ∏ j, omega (y j))
      (Set.univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1) := by
    have he : (fun y : Fin N → ℝ => (y i) ^ (-(1 / 2 : ℝ)) * ∏ j, omega (y j)) =
        (fun y => ∏ j, f j (y j)) := by
      funext y
      simp only [f, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    rw [he]
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod hf
  have hps := hp.mono_set (show orderedDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1) from
    fun y hy i _ => hy.2 i)
  apply hps.mono' (((measurable_pi_apply i).pow_const _).mul (measurable_density N)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  have hi : 0 ≤ (y i) ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos (hy.2 i).1 _).le
  change ‖(y i) ^ (-(1 / 2 : ℝ)) * density N y‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hi (density_pos hy).le)]
  exact mul_le_mul_of_nonneg_left (density_le_product hy) hi

 
def inverseHalfSum (N : ℕ) (y : Fin N → ℝ) : ℝ := ∑ i, (y i) ^ (-(1 / 2 : ℝ))

theorem integrableOn_inverseHalfSum_density (N : ℕ) :
    IntegrableOn (fun y => inverseHalfSum N y * density N y) (orderedDomain N) := by
  simp only [inverseHalfSum, Finset.sum_mul]
  exact integrable_finsetSum _ fun i _ => integrableOn_coordinate_weight N i

theorem abs_one_sub_prod_le {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, |r i| ≤ 1) : |1 - ∏ i ∈ s, r i| ≤ ∑ i ∈ s, |1 - r i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have his : ∀ j ∈ s, |r j| ≤ 1 := fun j hj => hr j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      |1 - r i * ∏ j ∈ s, r j| = |(1 - r i) + r i * (1 - ∏ j ∈ s, r j)| := by congr 1; ring
      _ ≤ |1 - r i| + |r i * (1 - ∏ j ∈ s, r j)| := abs_add_le _ _
      _ = |1 - r i| + |r i| * |1 - ∏ j ∈ s, r j| := by rw [abs_mul]
      _ ≤ |1 - r i| + 1 * |1 - ∏ j ∈ s, r j| :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (hr i (Finset.mem_insert_self _ _)) (abs_nonneg _))
      _ ≤ |1 - r i| + ∑ j ∈ s, |1 - r j| := by simpa using add_le_add (le_refl |1 - r i|) (ih his)

theorem abs_reflectionFactor_le_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |(y - x) / (y + x)| ≤ 1 := by
  apply abs_le.2
  have hxy : 0 < y + x := by linarith
  constructor
  · apply (le_div_iff₀ hxy).2
    linarith
  · apply (div_le_iff₀ hxy).2
    linarith

theorem abs_one_sub_reflectionFactor_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |1 - (y - x) / (y + x)| ≤ Real.sqrt x * y ^ (-(1 / 2 : ℝ)) := by
  have hxy : 0 < y + x := add_pos hy hx
  have hxS := Real.sq_sqrt hx.le
  have hyS := Real.sq_sqrt hy.le
  have hxsp := Real.sqrt_pos.2 hx
  have hysp := Real.sqrt_pos.2 hy
  have hAM : 2 * Real.sqrt x * Real.sqrt y ≤ x + y := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]
  rw [show 1 - (y - x) / (y + x) = 2 * x / (y + x) by field_simp; ring,
      abs_of_pos (div_pos (by positivity) hxy), Real.rpow_neg hy.le,
      ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hxy hysp).2
  nlinarith [mul_le_mul_of_nonneg_left hAM hxsp.le]

theorem abs_reflectionProduct_le_one {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : 0 ≤ x) : |reflectionProduct N x y| ≤ 1 := by
  rw [reflectionProduct, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ =>
    abs_reflectionFactor_le_one hx (hy.2 i).1)

theorem reflectionProduct_endpoint_bound {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : 0 < x) :
    |1 - reflectionProduct N x y| ≤ Real.sqrt x * inverseHalfSum N y := by
  calc
    |1 - reflectionProduct N x y| ≤ ∑ i : Fin N, |1 - (y i - x) / (y i + x)| :=
      abs_one_sub_prod_le _ _ fun i _ => abs_reflectionFactor_le_one hx.le (hy.2 i).1
    _ ≤ ∑ i : Fin N, Real.sqrt x * (y i) ^ (-(1 / 2 : ℝ)) :=
      Finset.sum_le_sum fun i _ => abs_one_sub_reflectionFactor_le hx (hy.2 i).1
    _ = Real.sqrt x * inverseHalfSum N y := by rw [inverseHalfSum, Finset.mul_sum]

theorem measurable_reflectionProduct (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => reflectionProduct N p.1 p.2) := by
  unfold reflectionProduct
  apply Finset.measurable_prod
  intro i _
  fun_prop

theorem integrableOn_reflectionProduct_density (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun y => reflectionProduct N x y * density N y) (orderedDomain N) := by
  have hm : Measurable (fun y => reflectionProduct N x y * density N y) :=
    ((measurable_reflectionProduct N).comp (measurable_const.prodMk measurable_id)).mul (measurable_density N)
  apply (integrableOn_density N).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (density_pos hy)]
  exact (mul_le_mul_of_nonneg_right (abs_reflectionProduct_le_one hy hx) (density_pos hy).le).trans_eq (one_mul _)

theorem integrableOn_deficit_density (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun y => (1 - reflectionProduct N x y) * density N y) (orderedDomain N) := by
  simpa only [sub_mul, one_mul, Pi.sub_def] using (integrableOn_density N).sub (integrableOn_reflectionProduct_density N hx)

theorem expectation_deficit (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expectation N (fun y => 1 - reflectionProduct N x y) = 1 - expectation N (reflectionProduct N x) := by
  unfold expectation
  simp only [sub_mul, one_mul]
  rw [integral_sub (integrableOn_density N) (integrableOn_reflectionProduct_density N hx)]
  rw [sub_div, show (∫ y in orderedDomain N, density N y) = normalizer N from rfl]
  rw [div_self (normalizer_pos N).ne']

theorem expectation_nonneg (N : ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : ∀ y ∈ orderedDomain N, 0 ≤ f y) : 0 ≤ expectation N f := by
  apply div_nonneg _ (normalizer_pos N).le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  exact mul_nonneg (hf y hy) (density_pos hy).le

end
end CriticalStrip

end OAI
