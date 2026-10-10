import OAI.Analysis.RecursivePotentials.VariableLp

namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

namespace VariableExponent

noncomputable section

lemma holder_mixed {ι : Type uIndex} (S : Finset ι) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (a b : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i) :
    ∑ i ∈ S, a i ^ r * b i ^ (1-r) ≤ (∑ i ∈ S, a i) ^ r * (∑ i ∈ S, b i) ^ (1-r) := by
  have hq : 0 < 1-r := by linarith
  have hpq := Real.HolderConjugate.inv_inv hr hq (by ring : r+(1-r)=1)
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg S hpq
    (fun i hi => Real.rpow_nonneg (ha i hi) r) (fun i hi => Real.rpow_nonneg (hb i hi) (1-r))
  have he₁ : ∀ i ∈ S, (a i ^ r) ^ r⁻¹ = a i := by
    intro i hi; rw [← Real.rpow_mul (ha i hi),mul_inv_cancel₀ hr.ne',Real.rpow_one]
  have he₂ : ∀ i ∈ S, (b i ^ (1-r)) ^ (1-r)⁻¹ = b i := by
    intro i hi; rw [← Real.rpow_mul (hb i hi),mul_inv_cancel₀ hq.ne',Real.rpow_one]
  simp_rw [Finset.sum_congr rfl he₁, Finset.sum_congr rfl he₂] at hh
  simpa only [one_div,inv_inv] using hh

lemma cuberoot_cube {a : ℝ} (ha : 0 ≤ a) : (a ^ 3) ^ (1/3:ℝ) = a := by
  rw [← Real.rpow_natCast,← Real.rpow_mul ha]
  norm_num

lemma cube_cuberoot {a : ℝ} (ha : 0 ≤ a) : (a ^ (1/3:ℝ)) ^ 3 = a := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

lemma cube_two_thirds {a : ℝ} (ha : 0 ≤ a) : (a ^ (2/3:ℝ)) ^ 3 = a ^ 2 := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

lemma square_cuberoot {a : ℝ} (ha : 0 ≤ a) : (a ^ 2) ^ (1/3:ℝ) = a ^ (2/3:ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul ha]
  norm_num

lemma cubic_transport {ι : Type uIndex} (S : Finset ι) {C : ℝ} (hC : 0 ≤ C)
    (a b d : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i)
    (hd : ∀ i ∈ S, 0 ≤ d i) (h : ∀ i ∈ S, C * a i ^ 3 ≤ b i * d i ^ 2) :
    C * (∑ i ∈ S, a i)^3 ≤ (∑ i ∈ S, b i) * (∑ i ∈ S, d i)^2 := by
  have hr (i) (hi : i ∈ S) : C ^ (1/3:ℝ) * a i ≤ b i ^ (1/3:ℝ) * d i ^ (2/3:ℝ) := by
    have hh := Real.rpow_le_rpow (mul_nonneg hC (pow_nonneg (ha i hi) 3)) (h i hi) (by norm_num : (0:ℝ)≤1/3)
    rw [Real.mul_rpow hC (pow_nonneg (ha i hi) 3),cuberoot_cube (ha i hi),
      Real.mul_rpow (hb i hi) (sq_nonneg _),square_cuberoot (hd i hi)] at hh
    exact hh
  have hmixed := holder_mixed S (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<1) b d hb hd
  norm_num only at hmixed
  have hs := (Finset.sum_le_sum hr).trans hmixed
  rw [← Finset.mul_sum] at hs
  norm_num only at hs
  have hB : 0 ≤ ∑ i ∈ S, b i := Finset.sum_nonneg hb
  have hdS : 0 ≤ ∑ i ∈ S, d i := Finset.sum_nonneg hd
  have hh := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hC _) (Finset.sum_nonneg ha)) hs 3
  rw [mul_pow,mul_pow,cube_cuberoot hC,cube_cuberoot hB,cube_two_thirds hdS] at hh
  exact hh

lemma cubic_transport_tsum {ι : Type uIndex} {C : ℝ} (hC : 0 ≤ C)
    (a b d : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, 0 ≤ d i)
    (has : Summable a) (hbs : Summable b) (hds : Summable d)
    (h : ∀ i, C*a i^3 ≤ b i*d i^2) :
    C*(∑' i, a i)^3 ≤ (∑' i, b i)*(∑' i, d i)^2 := by
  classical
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (has.hasSum.pow 3))
    (Filter.Tendsto.mul hbs.hasSum (hds.hasSum.pow 2))
    (Filter.Eventually.of_forall fun S => cubic_transport S hC a b d
      (fun i hi => ha i) (fun i hi => hb i) (fun i hi => hd i) (fun i hi => h i))

lemma energy_of_cubic {C a b B Y : ℝ} (_hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (_hY : 0 ≤ Y) (hBm : B ≤ (a+b)/2)
    (hcubic : C*Y^3 ≤ ((a+b)/2-B)*max a b ^ 2) :
    C*Y^3 ≤ (a^2+b^2-2*B^2)*max a b := by
  let M := max a b
  let D := (a+b)/2-B
  have hM : 0 ≤ M := ha.trans (le_max_left _ _)
  have hD : 0 ≤ D := sub_nonneg.mpr hBm
  have hMsum : M ≤ a+b := max_le (by linarith) (by linarith)
  have hE : D*M ≤ a^2+b^2-2*B^2 := by
    have hh := mul_nonneg hD (show 0 ≤ a+b-M by linarith)
    have hx := mul_nonneg hD hB
    dsimp [D] at *
    nlinarith [sq_nonneg (a-b)]
  exact hcubic.trans (by simpa only [M,pow_two,mul_assoc] using mul_le_mul_of_nonneg_right hE hM)

section Outer

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

abbrev Outer := ↥(lp E 2)

lemma outer_hasSum_square {ι : Type uIndex} [DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] (x : Outer E) :
    HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (by norm_num : (0:ℝ)<(2 : ENNReal).toReal) x

lemma norm_midpoint_average {F : Type uOther} [NormedAddCommGroup F] [NormedSpace ℝ F] (x y : F) :
    ‖x‖ ≤ (‖x+y‖+‖x-y‖)/2 ∧ ‖y‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have hx := norm_add_le (x+y) (x-y)
  have hy := norm_sub_le (x+y) (x-y)
  have h₁ : x+y+(x-y) = (2:ℝ) • x := by module
  have h₂ : x+y-(x-y) = (2:ℝ) • y := by module
  rw [h₁,norm_smul] at hx
  rw [h₂,norm_smul] at hy
  norm_num only [Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at hx hy
  constructor <;> linarith

lemma midpoint_energy_nonneg {F : Type uOther} [NormedAddCommGroup F] [NormedSpace ℝ F] (x y : F) :
    0 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg x) (norm_midpoint_average x y).1 2
  nlinarith [sq_nonneg (‖x+y‖-‖x-y‖)]

theorem outer_sixth_of_components {C : ℝ} (hC : 0 ≤ C) (x y : Outer E)
    (hc : ∀ i, C*‖y i‖^6 ≤ (‖x i+y i‖^2+‖x i-y i‖^2-2*‖x i‖^2)*
      (‖x i+y i‖^2+‖x i-y i‖^2)^2) :
    C*‖y‖^6 ≤ (‖x+y‖^2+‖x-y‖^2-2*‖x‖^2)*(‖x+y‖^2+‖x-y‖^2)^2 := by
  have hp : HasSum (fun i => ‖x i+y i‖^2) (‖x+y‖^2) := outer_hasSum_square E (x+y)
  have hm : HasSum (fun i => ‖x i-y i‖^2) (‖x-y‖^2) := outer_hasSum_square E (x-y)
  have hx := outer_hasSum_square E x
  have hy := outer_hasSum_square E y
  have hS := hp.add hm
  have hD := hS.sub (hx.mul_left 2)
  have hh := cubic_transport_tsum hC (fun i => ‖y i‖^2)
    (fun i => ‖x i+y i‖^2+‖x i-y i‖^2-2*‖x i‖^2)
    (fun i => ‖x i+y i‖^2+‖x i-y i‖^2)
    (fun i => sq_nonneg _) (fun i => midpoint_energy_nonneg (x i) (y i)) (fun i => by positivity)
    hy.summable hD.summable hS.summable (fun i => by convert hc i using 1 ; ring)
  rw [hy.tsum_eq,hD.tsum_eq,hS.tsum_eq] at hh
  convert hh using 1 ; ring

theorem outer_cubic_squared {C : ℝ} (hC : 0 ≤ C) (x y : Outer E)
    (hc : ∀ i, C*‖y i‖^3 ≤ ((‖x i+y i‖+‖x i-y i‖)/2-‖x i‖)*max ‖x i+y i‖ ‖x i-y i‖^2) :
    C^2*‖y‖^6 ≤ (‖x+y‖^2+‖x-y‖^2)*(‖x+y‖^2+‖x-y‖^2-2*‖x‖^2)^2 := by
  let A := fun i => ‖x i+y i‖
  let B := fun i => ‖x i-y i‖
  let M := fun i => max (A i) (B i)
  let D := fun i => A i^2+B i^2-2*‖x i‖^2
  have hM (i) : 0 ≤ M i := (norm_nonneg _).trans (le_max_left _ _)
  have hD (i) : 0 ≤ D i := midpoint_energy_nonneg (x i) (y i)
  have hc' (i) : C*‖y i‖^3 ≤ D i*M i :=
    energy_of_cubic hC (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_midpoint_average (x i) (y i)).1 (hc i)
  have hMi (i) : M i^2 ≤ A i^2+B i^2 := by
    rcases le_total (A i) (B i) with hh | hh
    · dsimp only [M]; rw [max_eq_right hh]; linarith [sq_nonneg (A i)]
    · dsimp only [M]; rw [max_eq_left hh]; linarith [sq_nonneg (B i)]
  have hp : HasSum (fun i => A i^2) (‖x+y‖^2) := outer_hasSum_square E (x+y)
  have hm : HasSum (fun i => B i^2) (‖x-y‖^2) := outer_hasSum_square E (x-y)
  have hx := outer_hasSum_square E x
  have hy := outer_hasSum_square E y
  have hS := hp.add hm
  have hDs : HasSum D (‖x+y‖^2+‖x-y‖^2-2*‖x‖^2) := hS.sub (hx.mul_left 2)
  have hMs : Summable (fun i => M i^2) := Summable.of_nonneg_of_le (fun i => sq_nonneg _) hMi hS.summable
  have hh := cubic_transport_tsum (sq_nonneg C) (fun i => ‖y i‖^2) (fun i => M i^2) D
    (fun i => sq_nonneg _) (fun i => sq_nonneg _) hD hy.summable hMs hDs.summable
    (fun i => by have hh := pow_le_pow_left₀ (mul_nonneg hC (pow_nonneg (norm_nonneg _) 3)) (hc' i) 2; nlinarith [sq_nonneg (C*‖y i‖^3)])
  have hMsum : (∑' i, M i^2) ≤ ‖x+y‖^2+‖x-y‖^2 := by
    rw [← hS.tsum_eq]
    exact Summable.tsum_le_tsum hMi hMs hS.summable
  calc
    C^2*‖y‖^6 = C^2*(∑' i, ‖y i‖^2)^3 := by rw [hy.tsum_eq]; ring
    _ ≤ (∑' i, M i^2)*(∑' i, D i)^2 := hh
    _ ≤ (‖x+y‖^2+‖x-y‖^2)*(∑' i, D i)^2 := mul_le_mul_of_nonneg_right hMsum (sq_nonneg _)
    _ = _ := by rw [hDs.tsum_eq]

theorem outer_cubic_of_components {C : ℝ} (hC : 0 ≤ C) (x y : Outer E)
    (hc : ∀ i, C*‖y i‖^3 ≤ ((‖x i+y i‖+‖x i-y i‖)/2-‖x i‖)*max ‖x i+y i‖ ‖x i-y i‖^2)
    {R : ℝ} (hR : 0 < R) (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖x‖^2 + C/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2 := by
  have hh := outer_cubic_squared E hC x y hc
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hD := midpoint_energy_nonneg x y
  have hx : ‖x‖ ≤ R := by have hx := (norm_midpoint_average x y).1; linarith
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have he : (‖x+y‖^2+‖x-y‖^2-2*‖x‖^2)^2 ≤ (2*(R^2-‖x‖^2))^2 := by
    exact pow_le_pow_left₀ hD (by linarith) 2
  have hh' : C^2*‖y‖^6 ≤ (2*R^2)*(2*(R^2-‖x‖^2))^2 := hh.trans
    (mul_le_mul (by linarith) he (sq_nonneg _) (by positivity))
  have hq : 0 < 2*Real.sqrt 2*R := by positivity
  have hsq : (2*Real.sqrt 2*R*(R^2-‖x‖^2))^2 = (2*R^2)*(2*(R^2-‖x‖^2))^2 := by
    calc
      _ = 4*(Real.sqrt 2)^2*R^2*(R^2-‖x‖^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; ring
  have hfinal : C*‖y‖^3 ≤ 2*Real.sqrt 2*R*(R^2-‖x‖^2) := by
    apply (sq_le_sq₀ (mul_nonneg hC (pow_nonneg (norm_nonneg _) 3)) (mul_nonneg hq.le (sub_nonneg.mpr hx2))).mp
    rw [hsq]
    calc
      (C*‖y‖^3)^2 = C^2*‖y‖^6 := by ring
      _ ≤ _ := hh'
  have hd : C*‖y‖^3/(2*Real.sqrt 2*R) ≤ R^2-‖x‖^2 := (div_le_iff₀ hq).mpr (by simpa only [mul_comm (R^2-‖x‖^2)] using hfinal)
  have heq : C*‖y‖^3/(2*Real.sqrt 2*R) = C/(2*Real.sqrt 2*R)*‖y‖^3 := by ring
  rw [heq] at hd
  linarith

end Outer

end

end VariableExponent

namespace AggregationVector

noncomputable section

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def childLp (s : ι) (f : ι →₀ ℝ) : CoordinateLp ι e :=
  toLpLinear T e (f.filter fun c => c ≠ T.root ∧ T.parent c = s)

@[simp] lemma childLp_apply (s c : ι) (f : ι →₀ ℝ) :
    childLp T e s f c = if c ≠ T.root ∧ T.parent c = s then f c else 0 := by
  exact (toLpLinear_apply T e (f.filter fun c => c ≠ T.root ∧ T.parent c = s) c).trans
    (Finsupp.filter_apply _ _ _)

lemma childLp_norm_le (s : ι) (f : ι →₀ ℝ) (hf : ∀ c, 0 ≤ f c)
    (hU : VariableTree.GlobalUpper T e f) : ‖childLp T e s f‖ ≤ f s := by
  apply lp.norm_le_of_forall_sum_le
    (by simpa only [ENNReal.toReal_ofReal e.pos.le] using e.pos) (hf s)
  intro S
  simp only [ENNReal.toReal_ofReal e.pos.le,Real.norm_eq_abs,childLp_apply]
  have hh := (e.agg_le_iff (S.filter fun c => c ≠ T.root ∧ T.parent c = s) f (hf s)).mp
    (hU s _ (fun c hc => (Finset.mem_filter.mp hc).2))
  simpa [ChildExponent.agg,Finset.sum_filter,apply_ite,Real.zero_rpow e.ne_zero] using hh

lemma childLp_norm_eq (s : ι) (f : ι →₀ ℝ) (H : Finset ι) (hf : f.support ⊆ H) :
    ‖childLp T e s f‖ = e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s) f := by
  apply (Real.rpow_left_inj (norm_nonneg _) (e.agg_nonneg _ _) e.ne_zero).mp
  change ‖toLpLinear T e (show AggregationVector T e from f.filter fun c => c ≠ T.root ∧ T.parent c = s)‖ ^ e.val = _
  rw [toLpLinear_norm_rpow,e.agg_rpow]
  have hs : (f.filter fun c => c ≠ T.root ∧ T.parent c = s).support ⊆
      H.filter (fun c => c ≠ T.root ∧ T.parent c = s) := by
    intro c hc
    rw [Finsupp.support_filter] at hc
    exact Finset.mem_filter.mpr ⟨hf (Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩
  calc
    _ = ∑ c ∈ (f.filter fun c => c ≠ T.root ∧ T.parent c = s).support, |f c| ^ e.val := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finsupp.support_filter] at hc
      simp [(Finset.mem_filter.mp hc).2]
    _ = _ := Finset.sum_subset hs (fun c hc hn => by
      have hfc : f c = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hh
        exact hn (by rw [Finsupp.support_filter]; exact Finset.mem_filter.mpr ⟨hh,(Finset.mem_filter.mp hc).2⟩)
      rw [hfc,abs_zero,Real.zero_rpow e.ne_zero])

def childP (s : ι) (v : AggregationVector T e) :
    CoordinateLp ι e := childLp T e s (VariableTree.P T e v)

def childQ (s : ι) (v : AggregationVector T e) :
    CoordinateLp ι e := childLp T e s (VariableTree.Q T e v)

lemma child_bounds (s : ι) (v : AggregationVector T e) :
    ‖childP T e s v‖ ≤ VariableTree.P T e v s ∧ ‖childQ T e s v‖ ≤ VariableTree.Q T e v s :=
  ⟨childLp_norm_le T e s _ (VariableTree.P_nonneg T e v) (VariableTree.P_upper T e v),
    childLp_norm_le T e s _ (VariableTree.Q_nonneg T e v) (VariableTree.Q_upper T e v)⟩

lemma field_differences (v w : ι →₀ ℝ) (s : ι) :
    |VariableTree.P T e v s-VariableTree.P T e w s| ≤ VariableTree.P T e (v-w) s+VariableTree.Q T e (v-w) s ∧
    |VariableTree.Q T e v s-VariableTree.Q T e w s| ≤ VariableTree.P T e (v-w) s+VariableTree.Q T e (v-w) s := by
  have h₁ := VariableTree.potentials_add_le T e (v-w) w s
  have h₂ := VariableTree.potentials_add_le T e (w-v) v s
  rw [sub_add_cancel] at h₁ h₂
  have hneg := VariableTree.potentials_neg T e (v-w) s
  rw [neg_sub] at hneg
  rw [hneg.1,hneg.2] at h₂
  have hP := VariableTree.P_nonneg T e (v-w) s
  have hQ := VariableTree.Q_nonneg T e (v-w) s
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2]

lemma children_dist_le (s : ι) (v w : AggregationVector T e) :
    ‖childP T e s v-childP T e s w‖ ≤ ‖v-w‖ ∧
    ‖childQ T e s v-childQ T e s w‖ ≤ ‖v-w‖ := by
  have hb : ‖childP T e s (v-w)+childQ T e s (v-w)‖ ≤ ‖v-w‖ := by
    have h := norm_add_le (childP T e s (v-w)) (childQ T e s (v-w))
    have hc := child_bounds T e s (v-w)
    have hp := (VariableTree.P_upper T e (v-w)).le_root T e (VariableTree.P_nonneg T e (v-w)) s
    have hq := (VariableTree.Q_upper T e (v-w)).le_root T e (VariableTree.Q_nonneg T e (v-w)) s
    change _ ≤ VariableTree.P T e (v-w) T.root + VariableTree.Q T e (v-w) T.root
    linarith [hc.1,hc.2]
  have hp0 : ENNReal.ofReal e.val ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr e.pos)
  constructor
  · refine (lp.norm_mono hp0 (y := childP T e s (v-w)+childQ T e s (v-w)) ?_).trans hb
    intro c
    simp only [lp.coeFn_sub,lp.coeFn_add,Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,childP,childQ,childLp_apply]
    split_ifs with hc
    · rw [abs_of_nonneg (add_nonneg (VariableTree.P_nonneg T e (v-w) c) (VariableTree.Q_nonneg T e (v-w) c))]
      exact (field_differences T e v w c).1
    · simp
  · refine (lp.norm_mono hp0 (y := childP T e s (v-w)+childQ T e s (v-w)) ?_).trans hb
    intro c
    simp only [lp.coeFn_sub,lp.coeFn_add,Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,childP,childQ,childLp_apply]
    split_ifs with hc
    · rw [abs_of_nonneg (add_nonneg (VariableTree.P_nonneg T e (v-w) c) (VariableTree.Q_nonneg T e (v-w) c))]
      exact (field_differences T e v w c).2
    · simp

lemma childP_lipschitz (s : ι) : LipschitzWith 1 (childP T e s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (children_dist_le T e s v w).1

lemma childQ_lipschitz (s : ι) : LipschitzWith 1 (childQ T e s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (children_dist_le T e s v w).2

lemma finite_recursion (s : ι) (v : AggregationVector T e) :
    (VariableTree.P T e v s,VariableTree.Q T e v s) =
      leastPair (v s) ‖childP T e s v‖ ‖childQ T e s v‖ := by
  let H := T.head v
  have hH : T.Initial H := T.head_initial v
  have hP : (VariableTree.P T e v).support ⊆ H := by
    intro c hc; by_contra hn
    exact Finsupp.mem_support_iff.mp hc (VariableTree.P_eq_zero_off_head T e v hH (T.support_subset_head v) hn)
  have hQ : (VariableTree.Q T e v).support ⊆ H := by
    intro c hc; by_contra hn
    exact Finsupp.mem_support_iff.mp hc (VariableTree.Q_eq_zero_off_head T e v hH (T.support_subset_head v) hn)
  rw [childP,childQ,childLp_norm_eq T e s _ H hP,childLp_norm_eq T e s _ H hQ]
  by_cases hs : s ∈ H
  · have h := VariableTree.potentials_on_head T e v H hH (T.support_subset_head v) ⟨s,hs⟩
    have hAggP : e.agg ((T.restrict H hH).children ⟨s,hs⟩)
        (fun c => ((T.restrict H hH).pfields e (fun c => v c.1) c).1) =
        e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s) (VariableTree.P T e v) := by
      unfold ChildExponent.agg
      congr 1
      rw [← T.sum_restrict_children H hH ⟨s,hs⟩]
      apply Finset.sum_congr rfl
      intro c hc
      rw [(VariableTree.potentials_on_head T e v H hH (T.support_subset_head v) c).1]
    have hAggQ : e.agg ((T.restrict H hH).children ⟨s,hs⟩)
        (fun c => ((T.restrict H hH).pfields e (fun c => v c.1) c).2) =
        e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s) (VariableTree.Q T e v) := by
      unfold ChildExponent.agg
      congr 1
      rw [← T.sum_restrict_children H hH ⟨s,hs⟩]
      apply Finset.sum_congr rfl
      intro c hc
      rw [(VariableTree.potentials_on_head T e v H hH (T.support_subset_head v) c).2]
    calc
      _ = (T.restrict H hH).pfields e (fun c => v c.1) ⟨s,hs⟩ := Prod.ext h.1 h.2
      _ = _ := by rw [(T.restrict H hH).pfields_eq,hAggP,hAggQ]
  · have hc : H.filter (fun c => c ≠ T.root ∧ T.parent c = s) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      obtain ⟨hcH,hc⟩ := Finset.mem_filter.mp hc
      have hh := hH.2 c hcH
      rw [hc.2] at hh
      exact hs hh
    rw [hc,e.agg_empty,e.agg_empty,
      VariableTree.P_eq_zero_off_head T e v hH (T.support_subset_head v) hs,
      VariableTree.Q_eq_zero_off_head T e v hH (T.support_subset_head v) hs,
      T.zero_off_head v hs]
    norm_num [leastPair]

end

end AggregationVector

namespace AggregationSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def childP (s : ι) : AggregationSpace T e → AggregationVector.CoordinateLp ι e :=
  Completion.extension (AggregationVector.childP T e s)

def childQ (s : ι) : AggregationSpace T e → AggregationVector.CoordinateLp ι e :=
  Completion.extension (AggregationVector.childQ T e s)

@[simp] lemma childP_coe (s : ι) (v : AggregationVector T e) :
    childP T e s (v : AggregationSpace T e) = AggregationVector.childP T e s v :=
  Completion.extension_coe (AggregationVector.childP_lipschitz T e s).uniformContinuous v

@[simp] lemma childQ_coe (s : ι) (v : AggregationVector T e) :
    childQ T e s (v : AggregationSpace T e) = AggregationVector.childQ T e s v :=
  Completion.extension_coe (AggregationVector.childQ_lipschitz T e s).uniformContinuous v

@[continuity,fun_prop] lemma continuous_childP (s : ι) :
    Continuous (childP T e s) := Completion.continuous_extension

@[continuity,fun_prop] lemma continuous_childQ (s : ι) :
    Continuous (childQ T e s) := Completion.continuous_extension

lemma childP_apply (s c : ι) (x : AggregationSpace T e) :
    childP T e s x c = if c ≠ T.root ∧ T.parent c = s then P T e c x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (lp.evalCLM ℝ (fun _ : ι => ℝ) (ENNReal.ofReal e.val) c).continuous.comp (continuous_childP T e s)
      · split_ifs <;> fun_prop
  | ih v => simp only [childP_coe,P_coe,AggregationVector.childP,AggregationVector.childLp_apply]

lemma childQ_apply (s c : ι) (x : AggregationSpace T e) :
    childQ T e s x c = if c ≠ T.root ∧ T.parent c = s then Q T e c x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (lp.evalCLM ℝ (fun _ : ι => ℝ) (ENNReal.ofReal e.val) c).continuous.comp (continuous_childQ T e s)
      · split_ifs <;> fun_prop
  | ih v => simp only [childQ_coe,Q_coe,AggregationVector.childQ,AggregationVector.childLp_apply]

theorem recursion (s : ι) (x : AggregationSpace T e) :
    (P T e s x,Q T e s x) = leastPair (coordinate T e s x) ‖childP T e s x‖ ‖childQ T e s x‖ := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · fun_prop
      · unfold leastPair
        fun_prop
  | ih v => simpa only [P_coe,Q_coe,coordinate_coe,childP_coe,childQ_coe] using
      AggregationVector.finite_recursion T e s v

lemma childP_norm_formula (s : ι) (x : AggregationSpace T e) :
    ‖childP T e s x‖ = (∑' c, if c ≠ T.root ∧ T.parent c = s then P T e c x ^ e.val else 0) ^ (1/e.val) := by
  rw [lp.norm_eq_tsum_rpow (by simpa only [ENNReal.toReal_ofReal e.pos.le] using e.pos)]
  simp only [ENNReal.toReal_ofReal e.pos.le,Real.norm_eq_abs,childP_apply]
  congr 1
  apply tsum_congr
  intro c
  split_ifs <;> simp [abs_of_nonneg (P_nonneg T e c x),Real.zero_rpow e.ne_zero]

lemma childQ_norm_formula (s : ι) (x : AggregationSpace T e) :
    ‖childQ T e s x‖ = (∑' c, if c ≠ T.root ∧ T.parent c = s then Q T e c x ^ e.val else 0) ^ (1/e.val) := by
  rw [lp.norm_eq_tsum_rpow (by simpa only [ENNReal.toReal_ofReal e.pos.le] using e.pos)]
  simp only [ENNReal.toReal_ofReal e.pos.le,Real.norm_eq_abs,childQ_apply]
  congr 1
  apply tsum_congr
  intro c
  split_ifs <;> simp [abs_of_nonneg (Q_nonneg T e c x),Real.zero_rpow e.ne_zero]

end

end AggregationSpace

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

lemma component_comparisons (h : ℕ+) (x : Component h) :
    (h.val+1:ℝ)^(-1/heightExponent h)*‖componentEquiv h x‖ ≤ ‖x‖ ∧
    ‖x‖ ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖componentEquiv h x‖ :=
  AggregationSpace.lp_comparisons (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h) x

lemma component_reflexive (h : ℕ+) : IsReflexive (Component h) :=
  AggregationSpace.finite_height_reflexive (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h)

instance component_dual_separable (h : ℕ+) : SeparableSpace (Component h →L[ℝ] ℝ) :=
  AggregationSpace.finite_height_dual_separable (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h)

theorem reflexive : IsReflexive Xv := SquareSum.isReflexive Component component_reflexive

instance dual_separable : SeparableSpace (Xv →L[ℝ] ℝ) := by
  let : SeparableSpace (SquareSum.Space (SquareSum.DualFamily Component)) :=
    LpSupport.separable (SquareSum.DualFamily Component) 2 (by norm_num)
  have hs : Function.Surjective (SquareSum.pairing Component) :=
    fun f => ⟨SquareSum.restrict Component f,SquareSum.pairing_restrict Component f⟩
  exact hs.denseRange.separableSpace (SquareSum.pairing Component).continuous

lemma componentEquiv_apply (h : ℕ+) (x : Component h) (s : ComponentNode h) :
    componentEquiv h x s = componentCoordinate h s x :=
  AggregationSpace.lpEquiv_apply (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h) x s

lemma component_ext (h : ℕ+) {x y : Component h}
    (he : ∀ s, componentCoordinate h s x = componentCoordinate h s y) : x = y := by
  apply (componentEquiv h).injective
  apply Subtype.ext
  funext s
  exact (componentEquiv_apply h x s).trans ((he s).trans (componentEquiv_apply h y s).symm)

@[simp] lemma coordinate_apply (s : Node) (x : Xv) :
    coordinate s x = componentCoordinate s.1 s.2 (x s.1) := rfl

lemma coordinates_ext {x y : Xv} (h : ∀ s, coordinate s x = coordinate s y) : x = y := by
  apply Subtype.ext
  funext i
  exact component_ext i (fun s => h ⟨i,s⟩)

lemma coordinate_basis (s t : Node) : coordinate s (basis t) = if s = t then 1 else 0 := by
  obtain ⟨h,s⟩ := s
  obtain ⟨k,t⟩ := t
  by_cases he : h = k
  · subst k
    simp only [coordinate_apply,basis,lp.single_apply_self,componentCoordinate,
      AggregationSpace.coordinate_coe,AggregationVector.basisVector_apply]
    congr 1
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,eq_comm]
  · rw [coordinate_apply,basis,lp.single_apply_ne _ _ _ he,map_zero,ite_eq_right]
    intro hh
    exact he (congrArg Sigma.fst hh)

lemma projection_apply (S : Finset Node) (x : Xv) :
    projection S x = ∑ s ∈ S, coordinate s x • basis s := by
  simp [projection]

lemma coordinate_projection (S : Finset Node) (s : Node) (x : Xv) :
    coordinate s (projection S x) = if s ∈ S then coordinate s x else 0 := by
  rw [projection_apply,map_sum]
  simp only [map_smul,coordinate_basis,smul_eq_mul,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq]

lemma projection_finite (S : Finset Node) (x : Xv) : FiniteTotalSupport (projection S x) :=
  ⟨S,fun s hs => by rw [coordinate_projection,ite_eq_right hs]⟩

lemma projection_fixed {S : Finset Node} (x : Xv) (hx : ∀ s ∉ S, coordinate s x = 0) :
    projection S x = x := by
  apply coordinates_ext
  intro s
  rw [coordinate_projection]
  split_ifs with hs
  · rfl
  · exact (hx s hs).symm

lemma projection_idem (S : Finset Node) (x : Xv) :
    projection S (projection S x) = projection S x := by
  apply coordinates_ext
  intro s
  simp only [coordinate_projection]
  split_ifs <;> rfl

lemma component_projection_fixed (h : ℕ+) (H : Finset (ComponentNode h))
    (hH : (componentTree h).Initial H) (x : Component h)
    (hx : ∀ s ∉ H, componentCoordinate h s x = 0) :
    AggregationSpace.projection (componentTree h) (exponent h) H hH x = x := by
  apply component_ext h
  intro s
  rw [componentCoordinate,AggregationSpace.coordinate_projection]
  split_ifs with hs
  · rfl
  · exact (hx s hs).symm

lemma component_mem_tail (h : ℕ+) (H : Finset (ComponentNode h)) (hH : (componentTree h).Initial H)
    (y : Component h) (hy : ∀ s ∈ H, componentCoordinate h s y = 0) :
    y ∈ AggregationSpace.tail (componentTree h) (exponent h) H hH := by
  change AggregationSpace.projection (componentTree h) (exponent h) H hH y = 0
  apply component_ext h
  intro s
  rw [map_zero,componentCoordinate,AggregationSpace.coordinate_projection]
  split_ifs with hs
  · exact hy s hs
  · rfl

lemma component_cubic (x y : Xv) (A : ∀ h, Finset (ComponentNode h)) (hA : AdmissibleHeads x y A)
    (h : ℕ+) :
    cubicConstant*‖y h‖^3 ≤ ((‖x h+y h‖+‖x h-y h‖)/2-‖x h‖)*max ‖x h+y h‖ ‖x h-y h‖^2 := by
  by_cases hx : x h = 0
  · rw [hx]
    exact AggregationSpace.cubic_zero (componentTree h) (exponent h) (y h)
  · obtain ⟨hH,hxH,hyH⟩ := hA h hx
    exact AggregationSpace.cubic_supported (componentTree h) (exponent h) h rfl
      (component_step h) (component_height h) (x h) (y h) hH
      (component_projection_fixed h (A h) hH (x h) hxH) (component_mem_tail h (A h) hH (y h) hyH)

lemma component_sixth (x y : Xv) (A : ∀ h, Finset (ComponentNode h)) (hA : AdmissibleHeads x y A)
    (h : ℕ+) :
    sixthConstant*‖y h‖^6 ≤ (‖x h+y h‖^2+‖x h-y h‖^2-2*‖x h‖^2)*(‖x h+y h‖^2+‖x h-y h‖^2)^2 := by
  have hmid := norm_midpoint_average (x h) (y h)
  exact sixth_of_cubic (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hmid.1 hmid.2 (component_cubic x y A hA h)

theorem cubic_stability (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (hA : AdmissibleHeads x y A) {R : ℝ} (hR : 0 < R) (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖x‖^2+cubicConstant/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2 :=
  outer_cubic_of_components Component cubicConstant_pos.le x y (component_cubic x y A hA) hR hp hm

theorem sixth_stability (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (hA : AdmissibleHeads x y A) :
    sixthConstant*‖y‖^6/(‖x+y‖^2+‖x-y‖^2)^2 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2 := by
  have hh := outer_sixth_of_components Component sixthConstant_pos.le x y (component_sixth x y A hA)
  by_cases hz : ‖x+y‖^2+‖x-y‖^2 = 0
  · rw [hz,zero_pow (by decide : 2 ≠ 0),div_zero]
    have hmid := midpoint_energy_nonneg x y
    rwa [hz] at hmid
  · exact (div_le_iff₀ (sq_pos_of_pos (lt_of_le_of_ne (by positivity) (Ne.symm hz)))).mpr hh

end

end Variable

namespace ScalarLp

noncomputable section

open Filter Topology

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]

lemma coordinate_cofinite {ι : Type uIndex} [DecidableEq ι] (p : PowerExponent) (x : Space ι p) :
    Tendsto (fun i => x i) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := ((lp.memℓp x).summable (by simpa only [ENNReal.toReal_ofReal p.pos.le] using p.pos)).tendsto_cofinite_zero
  simp only [ENNReal.toReal_ofReal p.pos.le] at hh
  have hout := (Real.continuous_rpow_const (one_div_pos.mpr p.pos).le).continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,← Real.rpow_mul (norm_nonneg _),mul_one_div_cancel p.ne_zero,
    Real.rpow_one,Real.zero_rpow (one_div_ne_zero p.ne_zero)] using hout

lemma basis_functionals_tendsto_zero (p : PowerExponent) (s : ℕ → ι) (hs : Function.Injective s)
    (f : Space ι p →L[ℝ] ℝ) :
    Tendsto (fun n => f (lp.single (ENNReal.ofReal p.val) (s n) 1)) atTop (𝓝 0) := by
  have hh := (coordinate_cofinite p.conjugate (restrict p p.conjugate p.holder f)).comp
    (hs.tendsto_cofinite.mono_left Filter.atTop_le_cofinite)
  exact hh

end

end ScalarLp

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

def finiteSubmodule : Submodule ℝ Xv where
  carrier := FiniteTotalSupport
  zero_mem' := ⟨∅, by simp⟩
  add_mem' := by
    rintro x y ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,fun s hs => ?_⟩
    simp only [Finset.mem_union,not_or] at hs
    rw [map_add,hS s hs.1,hT s hs.2,add_zero]
  smul_mem' := by
    rintro a x ⟨S,hS⟩
    exact ⟨S,fun s hs => by rw [map_smul,hS s hs,smul_zero]⟩

lemma finite_single (h : ℕ+) (v : AggregationVector (componentTree h) (exponent h)) :
    FiniteTotalSupport (lp.single 2 h (v : Component h)) := by
  refine ⟨(show ComponentNode h →₀ ℝ from v).support.image (Sigma.mk h),?_⟩
  rintro ⟨k,s⟩ hs
  by_cases he : k = h
  · subst k
    rw [coordinate_apply,lp.single_apply_self,componentCoordinate,AggregationSpace.coordinate_coe]
    apply Finsupp.notMem_support_iff.mp
    intro hh
    exact hs (Finset.mem_image.mpr ⟨s,hh,rfl⟩)
  · rw [coordinate_apply,lp.single_apply_ne _ _ _ he,map_zero]

lemma finite_support_dense : Dense {x : Xv | FiniteTotalSupport x} := by
  change Dense (finiteSubmodule : Set Xv)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply SquareSum.closedSubmodule_eq_top Component _ finiteSubmodule.isClosed_topologicalClosure
  intro h x
  induction x using Completion.induction_on with
  | hp =>
      exact finiteSubmodule.isClosed_topologicalClosure.preimage (lp.singleContinuousLinearMap ℝ Component 2 h).continuous
  | ih v => exact finiteSubmodule.le_topologicalClosure (finite_single h v)

lemma projection_finite_rank (S : Finset Node) : FiniteDimensional ℝ (projection S).range := by
  let V := Submodule.span ℝ (basis '' (S : Set Node))
  let : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (S.finite_toSet.image basis)
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  rintro z ⟨x,rfl⟩
  rw [ContinuousLinearMap.coe_coe,projection_apply]
  exact V.sum_mem fun s hs => V.smul_mem _ (Submodule.subset_span ⟨s,hs,rfl⟩)

lemma projection_weaklyNull {y : ℕ → Xv} (hy : WeaklyNull y) (S : Finset Node) :
    Tendsto (fun j => projection S (y j)) atTop (𝓝 0) := by
  have hh := tendsto_finsetSum S (fun s hs => (hy (coordinate s)).smul_const (basis s))
  simpa only [zero_smul,Finset.sum_const_zero,← projection_apply] using hh

def fiber (S : Finset Node) (h : ℕ+) : Finset (ComponentNode h) :=
  S.preimage (Sigma.mk h) (fun _ _ _ _ hxy => by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hxy)

def ancestralHeads (S : Finset Node) (h : ℕ+) : Finset (ComponentNode h) :=
  (componentTree h).ancestorClosure (fiber S h)

def ancestralUnion (S : Finset Node) : Finset Node := (S.image Sigma.fst).sigma (ancestralHeads S)

lemma fiber_mem (S : Finset Node) (h : ℕ+) (s : ComponentNode h) :
    s ∈ fiber S h ↔ (⟨h,s⟩ : Node) ∈ S := Finset.mem_preimage

lemma ancestralUnion_contains (S : Finset Node) : S ⊆ ancestralUnion S := by
  rintro ⟨h,s⟩ hs
  exact Finset.mem_sigma.mpr ⟨Finset.mem_image.mpr ⟨⟨h,s⟩,hs,rfl⟩,
    (componentTree h).subset_ancestorClosure _ ((fiber_mem S h s).mpr hs)⟩

lemma heads_admissible (w y : Xv) (S : Finset Node) (hw : ∀ s ∉ S, coordinate s w = 0) :
    AdmissibleHeads w (y-projection (ancestralUnion S) y) (ancestralHeads S) := by
  intro h hh
  have hnon : h ∈ S.image Sigma.fst := by
    by_contra hn
    apply hh
    apply component_ext h
    intro s
    rw [map_zero]
    exact hw ⟨h,s⟩ (fun hs => hn (Finset.mem_image.mpr ⟨⟨h,s⟩,hs,rfl⟩))
  refine ⟨(componentTree h).ancestorClosure_initial _,?_,?_⟩
  · intro s hs
    exact hw ⟨h,s⟩ (fun hm => hs ((componentTree h).subset_ancestorClosure _ ((fiber_mem S h s).mpr hm)))
  · intro s hs
    change coordinate ⟨h,s⟩ (y-projection (ancestralUnion S) y) = 0
    have hm : (⟨h,s⟩ : Node) ∈ ancestralUnion S := Finset.mem_sigma.mpr ⟨hnon,hs⟩
    rw [map_sub,coordinate_projection,ite_eq_left hm,sub_self]

lemma weakTailConstant_pos : 0 < weakTailConstant := by
  unfold weakTailConstant
  exact div_pos cubicConstant_pos (by positivity)

lemma cubic_stability_mul (w z : Xv) (hw : FiniteTotalSupport w)
    (A : ∀ h, Finset (ComponentNode h)) (hA : AdmissibleHeads w z A)
    {R : ℝ} (hR : 0 < R) (hp : ‖w+z‖ ≤ R) (hm : ‖w-z‖ ≤ R) :
    ‖w‖^2*R+weakTailConstant*‖z‖^3 ≤ R^3 := by
  have hh := mul_le_mul_of_nonneg_right (cubic_stability w z hw A hA hR hp hm) hR.le
  have he : (‖w‖^2+cubicConstant/(2*Real.sqrt 2*R)*‖z‖^3)*R =
      ‖w‖^2*R+weakTailConstant*‖z‖^3 := by
    unfold weakTailConstant
    field_simp [hR.ne']
  rw [he] at hh
  calc
    _ ≤ R^2*R := hh
    _ = R^3 := by ring

lemma finite_center_weak_bound (x : Xv) {ε : ℝ} (hε : 0 < ε)
    (y : ℕ → Xv) (hy : WeaklyNull y) (hyε : ∀ j, ε ≤ ‖y j‖)
    (hp : ∀ j, ‖x+y j‖ ≤ 1) (hm : ∀ j, ‖x-y j‖ ≤ 1)
    (w : Xv) (hw : FiniteTotalSupport w) :
    ‖w‖^2*(1+‖x-w‖)+weakTailConstant*ε^3 ≤ (1+‖x-w‖)^3 := by
  obtain ⟨S,hS⟩ := hw
  let P := projection (ancestralUnion S)
  let d : ℕ → ℝ := fun j => ‖P (y j)‖
  let z : ℕ → Xv := fun j => y j-P (y j)
  let C : ℝ := 1+‖x-w‖
  let R : ℕ → ℝ := fun j => C+d j
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [norm_zero] using (projection_weaklyNull hy (ancestralUnion S)).norm
  have hR : Tendsto R atTop (𝓝 C) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hpos (j) : 0 < R j := by dsimp [R,C,d]; positivity
  have hplus (j) : ‖w+z j‖ ≤ R j := by
    calc
      ‖w+z j‖ = ‖(x+y j)+(w-x)-P (y j)‖ := by congr 1; dsimp [z]; abel
      _ ≤ ‖x+y j‖+‖w-x‖+‖P (y j)‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1+‖x-w‖+d j := by rw [norm_sub_rev w x]; gcongr; exact hp j
      _ = R j := rfl
  have hminus (j) : ‖w-z j‖ ≤ R j := by
    calc
      ‖w-z j‖ = ‖(x-y j)+(w-x)+P (y j)‖ := by congr 1; dsimp [z]; abel
      _ ≤ ‖x-y j‖+‖w-x‖+‖P (y j)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1+‖x-w‖+d j := by rw [norm_sub_rev w x]; gcongr; exact hm j
      _ = R j := rfl
  have hineq (j) : ‖w‖^2*R j+weakTailConstant*‖z j‖^3 ≤ R j^3 :=
    cubic_stability_mul w (z j) ⟨S,hS⟩ (ancestralHeads S) (heads_admissible w (y j) S hS)
      (hpos j) (hplus j) (hminus j)
  have hlow (j) : ε-d j ≤ ‖z j‖ :=
    (sub_le_sub_right (hyε j) _).trans (norm_sub_norm_le (y j) (P (y j)))
  have hev : ∀ᶠ j in atTop, ‖w‖^2*R j+weakTailConstant*(ε-d j)^3 ≤ R j^3 := by
    filter_upwards [hd.eventually (eventually_lt_nhds hε)] with j hj
    apply le_trans _ (hineq j)
    gcongr
    · exact weakTailConstant_pos.le
    · exact hlow j
  have hl : Tendsto (fun j => ‖w‖^2*R j+weakTailConstant*(ε-d j)^3) atTop
      (𝓝 (‖w‖^2*C+weakTailConstant*(ε-0)^3)) :=
    (tendsto_const_nhds.mul hR).add
      (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hd).pow 3))
  have hh := le_of_tendsto_of_tendsto hl (hR.pow 3) hev
  simpa only [sub_zero] using hh

theorem weak_null_cubic (x : Xv) {ε : ℝ} (hε : 0 < ε)
    (y : ℕ → Xv) (hy : WeaklyNull y) (hyε : ∀ j, ε ≤ ‖y j‖)
    (hp : ∀ j, ‖x+y j‖ ≤ 1) (hm : ∀ j, ‖x-y j‖ ≤ 1) :
    ‖x‖^2+weakTailConstant*ε^3 ≤ 1 := by
  let K : Set Xv := {w | ‖w‖^2*(1+‖x-w‖)+weakTailConstant*ε^3 ≤ (1+‖x-w‖)^3}
  have hc : IsClosed K := isClosed_le (by fun_prop) (by fun_prop)
  have hi : {w : Xv | FiniteTotalSupport w} ⊆ K :=
    fun w hw => finite_center_weak_bound x hε y hy hyε hp hm w hw
  have hx : x ∈ K := closure_minimal hi hc (finite_support_dense x)
  simpa only [K,Set.mem_ofPred_eq,sub_self,norm_zero,add_zero,mul_one,one_pow] using hx

theorem weak_tail (x : Xv) {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (y : ℕ → Xv) (hy : WeaklyNull y) (hyε : ∀ j, ε ≤ ‖y j‖)
    (hp : ∀ j, ‖x+y j‖ ≤ 1) (hm : ∀ j, ‖x-y j‖ ≤ 1) :
    ‖x‖ ≤ theta ε ∧ theta ε < 1 := by
  have hh := weak_null_cubic x hε y hy hyε hp hm
  have hr : 0 ≤ 1-weakTailConstant*ε^3 := by nlinarith [sq_nonneg ‖x‖]
  constructor
  · exact (Real.le_sqrt (norm_nonneg x) hr).mpr (by linarith)
  · apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    have hpos : 0 < weakTailConstant*ε^3 := mul_pos weakTailConstant_pos (pow_pos hε 3)
    norm_num
    linarith

end

end Variable

end RecursivePotentials

end OAI
