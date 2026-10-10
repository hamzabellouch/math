import Mathlib
import OAI.Probability.Subsphere.Geometry.Affine

namespace OAI

noncomputable section

namespace SubsphereCurrent.Weighted
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

section
universe v

lemma block_parameters {d n : ℕ} (hd : 128 ≤ d) (hn : (d : ℝ)/2 ≤ n) :
    0 < n-2 ∧ (n-2)+1 ≤ n ∧ (d/16+1)+1 ≤ n-2 ∧
      2*(d/16+1) ≤ n-2 ∧ (d : ℝ)/16 ≤ (d/16+1 : ℕ) ∧
      1 ≤ d/16-1 ∧ (d/16-1)+d/16 ≤ (n-2)-(d/16+1) ∧
      d/16 ≤ n ∧ 0 < n := by
  have hdn : d ≤ 2*n := by exact_mod_cast (by linarith : (d : ℝ) ≤ 2*n)
  have hsmall : (d : ℝ)/16 ≤ (d/16+1 : ℕ) := by
    have hrem := Nat.mod_lt d (by norm_num : 0 < 16)
    have hdiv := Nat.mod_add_div d 16
    have hcast : (d : ℝ) < 16*((d/16 : ℕ)+1) := by exact_mod_cast (by omega : d < 16*(d/16+1))
    push_cast
    linarith
  exact ⟨by omega,by omega,by omega,by omega,hsmall,by omega,by omega,by omega,by omega⟩

lemma weighted_block_test {d n : ℕ} (hd : 128 ≤ d) (hn : (d : ℝ)/2 ≤ n) (hnd : n ≤ d)
    {V : Type v} [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : V → Observation d (d/16) → ℝ≥0∞) (hκ : ∀ v, Measurable (κ v))
    (hκ1 : ∀ obs, ∑ v, κ v obs ≤ 1)
    (g : V → Sphere d → ℝ≥0∞) (hg : ∀ v, Measurable (g v)) (hg1 : ∀ v s, g v s ≤ 1)
    (A : Affine.Test d n) :
    (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
      (∫⁻ s, blockInput κ g (onTest A s) ∂Affine.sphereLaw A.space) ≤
      (32768 : ℝ≥0∞)^n*(Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ))*
        ((2 : ℝ≥0∞)^(n+1)*(⨆ v, norm d (n-2) (g v))) := by
  obtain ⟨hk,hkn,hb0,h2b,hb,hq,hmargin,hm,hn0⟩ := block_parameters hd hn
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hn0)
  let C := (2 : ℝ≥0∞)^(n+1)*(⨆ v, norm d (n-2) (g v))
  have hC : C ≠ ∞ := by
    apply ENNReal.mul_ne_top (by finiteness)
    exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (iSup_le fun v => weighted_norm_le_one hk (hg1 v))
  have hlocal (v : V) : SubsphereRegression.PolynomialMass (sphereDensity (weightedOnTest A (g v)))
      ((n-2)-(d/16+1)) C := by
    intro z t ht
    apply (polynomialMass_weighted A (hg v) hkn hb0 h2b hb z t ht).trans
    exact mul_le_mul' (mul_le_mul' le_rfl (le_iSup (fun v => norm d (n-2) (g v)) v)) le_rfl
  rw [block_reconstruct A κ hκ g hg]
  have he : (((d/16-1 : ℕ) : ℝ)+1) = ((d/16 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d/16),Nat.cast_one]
    ring
  calc
    _ ≤ ∫⁻ _ : Fin (d/16) → A.spaceᗮ,
        (32768 : ℝ≥0∞)^n*(Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ))*C
        ∂Measure.pi (fun _ => stdGaussian A.spaceᗮ) := by
      apply lintegral_mono
      intro w
      have hr := sphere_routing_bound (E := A.space) (fun v => measurable_weightedOnTest A (hg v))
        (fun v => weightedOnTest_le_one A (hg1 v)) hlocal hC
        (by rw [A.dimension]; omega) (by rwa [A.dimension]) hq hmargin
        (fun v obs => κ v (pullObservation A w obs))
        (fun v => (hκ v).comp (measurable_pullObservation A w))
        (fun obs => hκ1 (pullObservation A w obs))
      simpa only [A.dimension,he] using hr
    _ = _ := by simp [C]

lemma weighted_block {d n : ℕ} (hd : 128 ≤ d) (hn : (d : ℝ)/2 ≤ n) (hnd : n ≤ d)
    {W : ℝ} (_hW : 1 ≤ W)
    {V : Type v} [Fintype V] [Nonempty V] (hcard : (Fintype.card V : ℝ) ≤ W)
    (κ : V → Observation d (d/16) → ℝ≥0∞) (hκ : ∀ v, Measurable (κ v))
    (hκ1 : ∀ obs, ∑ v, κ v obs ≤ 1)
    (g : V → Sphere d → ℝ≥0∞) (hg : ∀ v, Measurable (g v)) (hg1 : ∀ v s, g v s ≤ 1) :
    norm d n (blockInput κ g) ≤
      (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ))*ENNReal.ofReal ((131072 : ℝ)^d)*
        (⨆ v, norm d (n-2) (g v)) := by
  classical
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  apply iSup_le
  intro A
  apply (weighted_block_test hd hn hnd κ hκ hκ1 g hg hg1 A).trans
  have hc : (Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ)) ≤
      (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ)) := by
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact_mod_cast ENNReal.ofReal_le_ofReal hcard
  have hp : (32768 : ℝ≥0∞)^n*2^(n+1) ≤ ENNReal.ofReal ((131072 : ℝ)^d) := by
    have hn1 : n+1 ≤ 2*d := by omega
    calc
      _ ≤ (32768 : ℝ≥0∞)^d*2^(2*d) := mul_le_mul'
        (pow_le_pow_right₀ (by norm_num) hnd) (pow_le_pow_right₀ (by norm_num) hn1)
      _ = _ := by rw [pow_mul,← mul_pow,ENNReal.ofReal_pow (by positivity)]; norm_num
  calc
    _ = (Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ))*
        ((32768 : ℝ≥0∞)^n*2^(n+1))*(⨆ v, norm d (n-2) (g v)) := by ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc hp) le_rfl

end

lemma measurable_onTest {d n : ℕ} (A : Affine.Test d n) : Measurable (onTest A) := by
  exact A.measurable_point.subtype_mk

lemma terminal_test {d n : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    (u : Sphere d) {ε : ℝ} (hε : 0 < ε) (hsmall : ε/A.radius ≤ 1)
    {a : ℝ} (ha : a ≤ (n-1 : ℕ)) :
    Affine.sphereLaw A.space {s : Affine.Sphere A.space |
      Real.arccos ⟪u.val,A.point s⟫ ≤ ε} ≤
        ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal (ε/A.radius))^a := by
  have hsub : {s : Affine.Sphere A.space | Real.arccos ⟪u.val,A.point s⟫ ≤ ε} ⊆
      {s : Affine.Sphere A.space | dist s.val (A.project u.val) ≤ ε/A.radius} := by
    intro s hs
    simpa only [Set.mem_ofPred_eq,dist_eq_norm,norm_sub_rev] using
      A.angular_project_error s u.val (mem_sphere_zero_iff_norm.mp u.property) hs
  have hb := SubsphereRegression.sphereLaw_cap_raw (A.project u.val)
    (div_pos hε A.radius_positive) hsmall (Module.finrank_pos (R := ℝ) (M := A.space))
  rw [A.dimension] at hb
  calc
    _ ≤ SubsphereRegression.sphereLaw {s : Affine.Sphere A.space |
        dist s.val (A.project u.val) ≤ ε/A.radius} := measure_mono hsub
    _ ≤ _ := hb.trans (mul_le_mul' le_rfl (by
      rw [ENNReal.ofReal_pow (div_nonneg hε.le A.radius_positive.le),← ENNReal.rpow_natCast]
      exact ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr hsmall) ha))

lemma terminal_average {d n : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε/A.radius ≤ 1)
    {a : ℝ} (ha : a ≤ (n-1 : ℕ)) :
    (∫⁻ s : Affine.Sphere A.space, terminalInput π ε (onTest A s)
      ∂Affine.sphereLaw A.space) ≤
        ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal (ε/A.radius))^a := by
  let : IsProbabilityMeasure (Affine.sphereLaw A.space) := Fixed.sphereLaw_probability
  have he : ∀ s : Affine.Sphere A.space, terminalInput π ε (onTest A s) =
      ∫⁻ u : Sphere d, (if Real.arccos ⟪u.val,A.point s⟫ ≤ ε then (1 : ℝ≥0∞) else 0) ∂π := by
    intro s
    have hm : MeasurableSet {u : Sphere d | Real.arccos ⟪u.val,A.point s⟫ ≤ ε} :=
      measurableSet_le (by fun_prop) measurable_const
    simp only [terminalInput,onTest]
    rw [← one_mul (π _),← lintegral_indicator_const hm 1]
    rfl
  simp_rw [he]
  have hm : Measurable (fun z : Affine.Sphere A.space × Sphere d =>
      if Real.arccos ⟪z.2.val,A.point z.1⟫ ≤ ε then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_le (Real.continuous_arccos.measurable.comp
      ((measurable_subtype_coe.comp measurable_snd).inner
        (A.measurable_point.comp measurable_fst))) measurable_const)
      measurable_const measurable_const
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Sphere d, ENNReal.ofReal ((3 : ℝ)*4^n)*
        (ENNReal.ofReal (ε/A.radius))^a ∂π := by
      apply lintegral_mono
      intro u
      have hs : MeasurableSet {s : Affine.Sphere A.space |
          Real.arccos ⟪u.val,A.point s⟫ ≤ ε} :=
        measurableSet_le (Real.continuous_arccos.measurable.comp
          (measurable_const.inner A.measurable_point)) measurable_const
      have he' : (fun s : Affine.Sphere A.space => if Real.arccos ⟪u.val,A.point s⟫ ≤ ε
          then (1 : ℝ≥0∞) else 0) =
        {s : Affine.Sphere A.space | Real.arccos ⟪u.val,A.point s⟫ ≤ ε}.indicator (fun _ => 1) := rfl
      dsimp only
      rw [he',lintegral_indicator_const hs,one_mul]
      exact terminal_test A u hε hsmall ha
    _ = _ := by simp

lemma weighted_terminal {d n : ℕ} (hd : 4 ≤ d) (hn : (d : ℝ)/2 ≤ n) (hnd : n ≤ d)
    (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    {ε : ℝ} (hε : 0 < ε) :
    norm d n (terminalInput π ε) ≤
      ENNReal.ofReal ((16 : ℝ)^d)*(ENNReal.ofReal ε)^((d : ℝ)/16) := by
  unfold norm
  apply iSup_le
  intro A
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  let : IsProbabilityMeasure (Affine.sphereLaw A.space) := Fixed.sphereLaw_probability
  have ha0 : (0 : ℝ) ≤ d/16 := by positivity
  have ha : (d : ℝ)/16 ≤ (n-1 : ℕ) := by
    rw [Nat.cast_sub hnpos,Nat.cast_one]
    linarith
  have hc : (3 : ℝ)*4^n ≤ 16^d := by
    calc
      (3 : ℝ)*4^n ≤ 4*4^d := mul_le_mul (by norm_num) (pow_le_pow_right₀ (by norm_num) hnd)
        (by positivity) (by positivity)
      _ = 4^(d+1) := by rw [pow_succ]; ring
      _ ≤ 4^(2*d) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by norm_num [pow_mul]
  by_cases hsmall : ε/A.radius ≤ 1
  · calc
      _ ≤ (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
          (ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal (ε/A.radius))^((d : ℝ)/16)) :=
        mul_le_mul' le_rfl (terminal_average A π hε hsmall ha)
      _ = ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal ε)^((d : ℝ)/16) := by
        rw [mul_left_comm,← ENNReal.mul_rpow_of_nonneg _ _ ha0,
          ← ENNReal.ofReal_mul A.radius_positive.le]
        rw [← mul_div_assoc,mul_div_cancel_left₀ ε A.radius_positive.ne']
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl
  · have hr : A.radius ≤ ε := by
      simpa only [one_mul] using le_of_lt ((lt_div_iff₀ A.radius_positive).mp (lt_of_not_ge hsmall))
    calc
      _ ≤ (ENNReal.ofReal A.radius)^((d : ℝ)/16)*1 :=
        mul_le_mul' le_rfl (by simpa using (lintegral_mono (fun _ => prob_le_one) :
          (∫⁻ s : Affine.Sphere A.space, terminalInput π ε (onTest A s)
            ∂Affine.sphereLaw A.space) ≤ ∫⁻ _ : Affine.Sphere A.space, (1 : ℝ≥0∞)
            ∂Affine.sphereLaw A.space))
      _ ≤ (ENNReal.ofReal ε)^((d : ℝ)/16) := by
        rw [mul_one]; exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hr) ha0
      _ ≤ _ := le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr (one_le_pow₀ (by norm_num)))


theorem radius_weighted_estimate : RadiusWeightedEstimate := by
  refine ⟨131072,by norm_num,128,?_⟩
  intro d hd
  constructor
  · intro W hW V _ _ hcard κ hκ hκ1 g hg hg1 n hn hnd
    exact weighted_block hd hn hnd hW hcard κ hκ hκ1 g hg hg1
  · intro n hn hnd π hπ ε hε _
    let := hπ
    apply (weighted_terminal (by omega : 4 ≤ d) hn hnd π hε).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) d

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

theorem radius_weighted_full_estimate : RadiusWeightedFullEstimate := by
  refine ⟨131072,by norm_num,128,?_⟩
  intro d hd
  constructor
  · intro W hW V _ _ hcard κ hκ hκ1 g hg hg1 n hn hnd
    exact weighted_block hd hn hnd hW hcard κ hκ hκ1 g hg hg1
  · intro n hn hnd π hπ ε hε
    let := hπ
    apply (weighted_terminal (by omega : 4 ≤ d) hn hnd π hε).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) d

end SubsphereCurrent.Weighted

end

end OAI
