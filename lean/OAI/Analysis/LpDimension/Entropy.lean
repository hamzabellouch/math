import OAI.Analysis.LpDimension.Model

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Matrix
universe u uE uV uι

namespace SubpolynomialLp

lemma entropy_le_log_card {ι : Type uι} [Fintype ι] (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i) (hsum : ∑ i, μ i = 1) :
    ∑ i, μ i * Real.log (1 / μ i) ≤ Real.log (Fintype.card ι : ℝ) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := μ) (p := fun i => 1 / μ i)
    (fun i _ => (hμ i).le) hsum (fun i _ => show 0 < 1 / μ i from one_div_pos.mpr (hμ i))
  have hn : ∀ i, μ i ≠ 0 := fun i => (hμ i).ne'
  simpa [smul_eq_mul, hn] using h

lemma log_ratio_lower {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  let f : ℝ → ℝ := fun t => Real.log t - 2 * (t - 1) / (t + 1)
  have hd (t : ℝ) (ht : 1 ≤ t) :
      HasDerivAt f ((t - 1) ^ 2 / (t * (t + 1) ^ 2)) t := by
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t + 1 ≠ 0 := by linarith
    convert (Real.hasDerivAt_log ht0).sub
      ((((hasDerivAt_id t).sub_const 1).const_mul 2).div
        ((hasDerivAt_id t).add_const 1) ht1) using 1
    all_goals first | rfl | (simp only [id_eq]; field_simp; ring)
  have hm : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by simpa using (le_of_lt (show 1 < t from by
        simpa only [interior_Ici, Set.mem_Ioi] using ht)))).hasDerivWithinAt)
    intro t ht
    have ht' : 1 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    positivity
  have hh := hm (Set.mem_Ici.mpr le_rfl) hx hx
  dsimp [f] at hh
  norm_num at hh
  linarith

/-- The logarithmic-mean estimate in a division-free form, valid also at a=b. -/
lemma log_mean_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 ≤ (a - b) * (Real.log a - Real.log b) * ((a + b) / 2) := by
  wlog hab : b ≤ a generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    nlinarith
  have hx : 1 ≤ a / b := (le_div_iff₀ hb).mpr (by simpa using hab)
  have hh := log_ratio_lower hx
  rw [Real.log_div ha.ne' hb.ne'] at hh
  have he : 2 * (a / b - 1) / (a / b + 1) = 2 * (a - b) / (a + b) := by
    field_simp
  rw [he] at hh
  have habp : 0 < a + b := by positivity
  have hh' := (div_le_iff₀ habp).mp hh
  have := mul_le_mul_of_nonneg_left hh' (sub_nonneg.mpr hab)
  nlinarith


section ElectricalEnergy
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]

def electricalEnergy (src dst : E → V) (c : E → ℝ) (h : V → ℝ) : ℝ :=
  ∑ e, c e * (h (src e) - h (dst e)) *
    (Real.log (h (src e)) - Real.log (h (dst e)))

lemma sub_mul_log_sub_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (Real.log a - Real.log b) := by
  rcases le_total a b with hab | hab
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab)
      (sub_nonpos.mpr (Real.log_le_log ha hab))
  · exact mul_nonneg (sub_nonneg.mpr hab)
      (sub_nonneg.mpr (Real.log_le_log hb hab))

omit [Fintype V] in
lemma electricalEnergy_nonneg (src dst : E → V) (c : E → ℝ) (h : V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hh : ∀ i, 0 < h i) :
    0 ≤ electricalEnergy src dst c h := by
  apply Finset.sum_nonneg
  intro e _
  rw [mul_assoc]
  exact mul_nonneg (hc e) (sub_mul_log_sub_nonneg (hh _) (hh _))

omit [Fintype V] in
/-- The weighted Cauchy--Schwarz step, before mass normalization. -/
lemma electrical_cauchy_schwarz (src dst : E → V) (c w : E → ℝ) (h : V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hh : ∀ i, 0 < h i) :
    (∑ e, w e * Real.sqrt (c e) * |h (src e) - h (dst e)|) ^ 2 ≤
      electricalEnergy src dst c h *
        ∑ e, (w e) ^ 2 * ((h (src e) + h (dst e)) / 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro e _
    rw [mul_assoc]
    exact mul_nonneg (hc e) (sub_mul_log_sub_nonneg (hh _) (hh _))
  · intro e _
    exact mul_nonneg (sq_nonneg (w e))
      (div_nonneg (add_nonneg (hh _).le (hh _).le) (by norm_num))
  · intro e _
    have he := mul_le_mul_of_nonneg_left (log_mean_sq_le (hh (src e)) (hh (dst e)))
      (mul_nonneg (sq_nonneg (w e)) (hc e))
    calc
      (w e * Real.sqrt (c e) * |h (src e) - h (dst e)|) ^ 2 =
          ((w e) ^ 2 * c e) * (h (src e) - h (dst e)) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt (hc e), sq_abs]
      _ ≤ ((w e) ^ 2 * c e) *
          ((h (src e) - h (dst e)) *
            (Real.log (h (src e)) - Real.log (h (dst e))) *
              ((h (src e) + h (dst e)) / 2)) := he
      _ = _ := by ring

variable [DecidableEq V]

def vertexWeight (src dst : E → V) (w : E → ℝ) (i : V) : ℝ :=
  (∑ e, if src e = i then (w e) ^ 2 else 0) +
  (∑ e, if dst e = i then (w e) ^ 2 else 0)

def vertexMass (src dst : E → V) (w : E → ℝ) (i : V) : ℝ :=
  vertexWeight src dst w i / (2 * ∑ e, (w e) ^ 2)

lemma vertexWeight_pairing (src dst : E → V) (w : E → ℝ) (h : V → ℝ) :
    ∑ i, vertexWeight src dst w i * h i =
      ∑ e, (w e) ^ 2 * (h (src e) + h (dst e)) := by
  simp only [vertexWeight, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  calc
    _ = (∑ e, (w e) ^ 2 * h (src e)) + ∑ e, (w e) ^ 2 * h (dst e) := by
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        simp [ite_mul]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        simp [ite_mul]
    _ = _ := by simp [mul_add, Finset.sum_add_distrib]

lemma vertexMass_pairing (src dst : E → V) (w : E → ℝ) (h : V → ℝ) :
    ∑ i, vertexMass src dst w i * h i =
      (∑ e, (w e) ^ 2 * (h (src e) + h (dst e))) / (2 * ∑ e, (w e) ^ 2) := by
  simp only [vertexMass, div_mul_eq_mul_div, ← Finset.sum_div, vertexWeight_pairing]

lemma vertexMass_sum (src dst : E → V) (w : E → ℝ)
    (hw : 0 < ∑ e, (w e) ^ 2) :
    ∑ i, vertexMass src dst w i = 1 := by
  have h := vertexMass_pairing src dst w (fun _ => 1)
  simp only [mul_one, one_add_one_eq_two, ← Finset.sum_mul] at h
  rw [h, mul_comm (∑ e, (w e) ^ 2) 2]
  exact div_self (mul_ne_zero (by norm_num) hw.ne')

/-- The precise normalized energy inequality used in the heat-entropy proof. -/
lemma heat_cauchy_schwarz (src dst : E → V) (c w : E → ℝ) (h : V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hh : ∀ i, 0 < h i)
    (hw : 0 < ∑ e, (w e) ^ 2)
    (hmass : ∑ i, vertexMass src dst w i * h i = 1) :
    (∑ e, w e * Real.sqrt (c e) * |h (src e) - h (dst e)|) ^ 2 ≤
      electricalEnergy src dst c h * (∑ e, (w e) ^ 2) := by
  have hm := vertexMass_pairing src dst w h
  rw [hmass] at hm
  have hm' := (eq_div_iff (show 2 * ∑ e, (w e) ^ 2 ≠ 0 by positivity)).mp hm
  have hsum : ∑ e, (w e) ^ 2 * ((h (src e) + h (dst e)) / 2) =
      ∑ e, (w e) ^ 2 := by
    simp only [← mul_div_assoc, ← Finset.sum_div]
    rw [← hm']
    ring
  simpa only [hsum] using electrical_cauchy_schwarz src dst c w h hc hh

def graphLaplacian (src dst : E → V) (c : E → ℝ) (h : V → ℝ) (i : V) : ℝ :=
  (∑ e, if src e = i then c e * (h (src e) - h (dst e)) else 0) -
  (∑ e, if dst e = i then c e * (h (src e) - h (dst e)) else 0)

lemma graphLaplacian_pairing (src dst : E → V) (c : E → ℝ) (h g : V → ℝ) :
    ∑ i, graphLaplacian src dst c h i * g i =
      ∑ e, c e * (h (src e) - h (dst e)) * (g (src e) - g (dst e)) := by
  calc
    _ = (∑ e, c e * (h (src e) - h (dst e)) * g (src e)) -
        ∑ e, c e * (h (src e) - h (dst e)) * g (dst e) := by
      simp only [graphLaplacian, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      congr 1 <;> rw [Finset.sum_comm] <;>
        apply Finset.sum_congr rfl <;> intro e _ <;> simp [ite_mul]
    _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]

lemma graphLaplacian_sum (src dst : E → V) (c : E → ℝ) (h : V → ℝ) :
    ∑ i, graphLaplacian src dst c h i = 0 := by
  simpa using graphLaplacian_pairing src dst c h (fun _ => 1)

def heatEntropy (μ : V → ℝ) (h : V → ℝ) : ℝ :=
  ∑ i, μ i * (h i * Real.log (h i))

/-- Entropy dissipation, from the actual weighted graph heat equation. -/
lemma heatEntropy_hasDerivAt (src dst : E → V) (c : E → ℝ) (μ : V → ℝ)
    (h : ℝ → V → ℝ) (s : ℝ) (hμ : ∀ i, 0 < μ i) (hp : ∀ i, 0 < h s i)
    (hd : ∀ i, HasDerivAt (fun t => h t i)
      (-graphLaplacian src dst c (h s) i / μ i) s) :
    HasDerivAt (fun t => heatEntropy μ (h t))
      (-electricalEnergy src dst c (h s)) s := by
  have hh (i : V) := ((hd i).mul ((hd i).log (hp i).ne')).const_mul (μ i)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hh i)
  have he : (∑ i, μ i *
      ((-graphLaplacian src dst c (h s) i / μ i) * Real.log (h s i) +
      h s i * ((-graphLaplacian src dst c (h s) i / μ i) / h s i))) =
      -electricalEnergy src dst c (h s) := by
    calc
      _ = ∑ i, -graphLaplacian src dst c (h s) i * (Real.log (h s i) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(hμ i).ne', (hp i).ne']
        ring
      _ = -∑ i, graphLaplacian src dst c (h s) i * (Real.log (h s i) + 1) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
      _ = _ := by
        rw [graphLaplacian_pairing]
        simp only [add_sub_add_right_eq_sub, electricalEnergy]
  rw [he] at hs
  exact hs

omit [DecidableEq V] in
lemma heatEntropy_continuous (μ : V → ℝ) : Continuous (heatEntropy μ) := by
  unfold heatEntropy
  fun_prop

/-- The entropy identity for the weighted graph heat flow, including the singular
initial point mass. Positivity is only required at strictly positive times. -/
lemma heatEntropy_integral (src dst : E → V) (c : E → ℝ) (μ : V → ℝ)
    (h : ℝ → V → ℝ) (v : V) (hc : ∀ e, 0 ≤ c e) (hμ : ∀ i, 0 < μ i)
    (hcont : Continuous h) (hp : ∀ s : ℝ, 0 < s → ∀ i, 0 < h s i)
    (hd : ∀ s : ℝ, 0 < s → ∀ i, HasDerivAt (fun t => h t i)
      (-graphLaplacian src dst c (h s) i / μ i) s)
    (hzero : h 0 = Pi.single v (1 / μ v))
    (htop : Tendsto h atTop (𝓝 (fun _ => 1))) :
    IntegrableOn (fun s => electricalEnergy src dst c (h s)) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), electricalEnergy src dst c (h s)) = Real.log (1 / μ v) := by
  have hecont : Continuous (fun s => -heatEntropy μ (h s)) :=
    ((heatEntropy_continuous μ).comp hcont).neg
  have hederiv (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      HasDerivAt (fun t => -heatEntropy μ (h t))
        (electricalEnergy src dst c (h s)) s := by
    convert (heatEntropy_hasDerivAt src dst c μ h s hμ
      (hp s hs) (hd s hs)).neg using 1
    first | rfl | simp only [neg_neg]
  have henonneg (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      0 ≤ electricalEnergy src dst c (h s) :=
    electricalEnergy_nonneg src dst c (h s) hc (hp s hs)
  have hetop : Tendsto (fun s => -heatEntropy μ (h s)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (((heatEntropy_continuous μ).tendsto (fun _ => 1)).comp htop).neg
    simpa [heatEntropy] using hh
  have hezero : heatEntropy μ (h 0) = Real.log (1 / μ v) := by
    rw [hzero, heatEntropy]
    simp only [Pi.single_apply]
    rw [Finset.sum_eq_single v]
    · simp [(hμ v).ne']
    · intro i _ hiv
      simp [hiv]
    · simp
  constructor
  · exact integrableOn_Ioi_deriv_of_nonneg hecont.continuousWithinAt hederiv henonneg hetop
  · have hi := integral_Ioi_of_hasDerivAt_of_nonneg hecont.continuousWithinAt
      hederiv henonneg hetop
    simpa [hezero] using hi

variable [DecidableEq E]

def incidence (src dst : E → V) : Matrix E V ℝ :=
  fun e i => (if src e = i then 1 else 0) - (if dst e = i then 1 else 0)

def laplacianMatrix (src dst : E → V) (c : E → ℝ) : Matrix V V ℝ :=
  (incidence src dst).transpose * Matrix.diagonal c * incidence src dst

omit [Fintype E] [DecidableEq E] in
lemma incidence_mulVec (src dst : E → V) (h : V → ℝ) (e : E) :
    (incidence src dst *ᵥ h) e = h (src e) - h (dst e) := by
  simp [Matrix.mulVec, dotProduct, incidence, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma laplacianMatrix_mulVec (src dst : E → V) (c : E → ℝ) (h : V → ℝ) :
    laplacianMatrix src dst c *ᵥ h = graphLaplacian src dst c h := by
  classical
  unfold laplacianMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext i
  change (∑ e, incidence src dst e i * (Matrix.diagonal c *ᵥ (incidence src dst *ᵥ h)) e) = _
  simp only [Matrix.mulVec_diagonal, incidence_mulVec]
  simp only [incidence, sub_mul, Finset.sum_sub_distrib, graphLaplacian]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _ <;> split_ifs <;> simp_all

omit [Fintype V] in
lemma laplacianMatrix_symmetric (src dst : E → V) (c : E → ℝ) :
    (laplacianMatrix src dst c).IsSymm := by
  unfold Matrix.IsSymm laplacianMatrix
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma laplacianMatrix_posSemidef (src dst : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) : (laplacianMatrix src dst c).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (laplacianMatrix_symmetric src dst c), ?_⟩
  intro h
  rw [laplacianMatrix_mulVec]
  have hp := graphLaplacian_pairing src dst c h h
  change 0 ≤ ∑ i, h i * graphLaplacian src dst c h i
  simp only [mul_comm (h _)]
  rw [hp]
  apply Finset.sum_nonneg
  intro e _
  simpa only [sq, mul_assoc] using mul_nonneg (hc e) (sq_nonneg (h (src e) - h (dst e)))

omit [Fintype V] in
lemma laplacianMatrix_apply (src dst : E → V) (c : E → ℝ) (i j : V) :
    laplacianMatrix src dst c i j =
      ∑ e, c e * incidence src dst e i * incidence src dst e j := by
  classical
  unfold laplacianMatrix
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro e _
  ring


omit [Fintype V] in
lemma laplacianMatrix_offdiag_neg (src dst : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) {i j : V} (hij : i ≠ j)
    (hconn : ∃ e, (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    laplacianMatrix src dst c i j < 0 := by
  rw [laplacianMatrix_apply]
  have hnon (e : E) : c e * incidence src dst e i * incidence src dst e j ≤ 0 := by
    have := (hc e).le
    dsimp [incidence]
    split_ifs <;> simp_all
  obtain ⟨e, he⟩ := hconn
  have hneg : c e * incidence src dst e i * incidence src dst e j < 0 := by
    rcases he with ⟨hi, hj⟩ | ⟨hj, hi⟩ <;>
      simp [incidence, hi, hj, hij, hij.symm, (hc e)]
  have hs := Finset.sum_lt_sum (fun e _ => hnon e) ⟨e, Finset.mem_univ e, hneg⟩
  simpa using hs

omit [DecidableEq E] in
lemma graphLaplacian_kernel_constant (src dst : E → V) (c : E → ℝ)
    (hc : ∀ e, 0 < c e)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (h : V → ℝ) (hzero : graphLaplacian src dst c h = 0) (i j : V) : h i = h j := by
  have he : ∑ e, c e * (h (src e) - h (dst e)) ^ 2 = 0 := by
    have hh := graphLaplacian_pairing src dst c h h
    rw [hzero] at hh
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sq, mul_assoc] using hh.symm
  have hn (e : E) : 0 ≤ c e * (h (src e) - h (dst e)) ^ 2 :=
    mul_nonneg (hc e).le (sq_nonneg _)
  have hz (e : E) : h (src e) = h (dst e) := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hn e)).mp he e (Finset.mem_univ e)
    have hs := (mul_eq_zero.mp hz).resolve_left (hc e).ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  by_cases hij : i = j
  · simp [hij]
  · obtain ⟨e, he⟩ := hconn i j hij
    rcases he with ⟨hi, hj⟩ | ⟨hj, hi⟩
    · simpa [hi, hj] using hz e
    · simpa [hi, hj] using (hz e).symm

end ElectricalEnergy

end SubpolynomialLp

end

end OAI
