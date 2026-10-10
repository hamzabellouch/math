import OAI.Analysis.TreePotential.Moduli

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section WeakNullSequences
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak convergence to zero, expressed by all continuous real linear tests. -/
def WeaklyNull (d : ℕ → E) : Prop :=
  ∀ φ : E →L[ℝ] ℝ, Tendsto (fun n => φ (d n)) atTop (𝓝 0)

lemma WeaklyNull.map {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {d : ℕ → E} (hd : WeaklyNull d) (L : E →L[ℝ] Y) : WeaklyNull (fun n => L (d n)) :=
  fun φ => hd (φ.comp L)

def functionalKernel (φ : E →L[ℝ] ℝ) : ClosedFiniteCodim E where
  space := φ.ker
  closed := φ.isClosed_ker
  finiteCodim := Module.Finite.equiv φ.toLinearMap.quotKerEquivRange.symm

/-- Weak nullity really gives approximation in every closed finite-codimensional
    subspace; the finite-dimensional quotient step is proved explicitly. -/
lemma WeaklyNull.approximable {d : ℕ → E} (hd : WeaklyNull d) (F : ClosedFiniteCodim E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ w : E, w ∈ F.space ∧ ‖d n - w‖ < ε := by
  let : IsClosed (F.space : Set E) := F.closed
  let : Module.Finite ℝ (E ⧸ F.space) := F.finiteCodim
  let e := (Module.finBasis ℝ (E ⧸ F.space)).equivFunL
  have hc : Tendsto (fun n => e (F.space.mkQL (d n))) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hd ((ContinuousLinearMap.proj i).comp (e.toContinuousLinearMap.comp F.space.mkQL))
  have hq : Tendsto (fun n => F.space.mkQL (d n)) atTop (𝓝 0) := by
    have h := (e.symm.continuous.tendsto 0).comp hc
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, map_zero] using h
  have hqn : Tendsto (fun n => ‖F.space.mkQL (d n)‖) atTop (𝓝 0) := by simpa using hq.norm
  have he := hqn.eventually_lt_const (show 0 < ε/2 by positivity)
  filter_upwards [he] with n hn
  obtain ⟨u, hu, hun⟩ := Submodule.Quotient.norm_mk_lt (F.space.mkQL (d n))
    (show 0 < ε/2 by positivity)
  refine ⟨d n - u, (Submodule.Quotient.eq F.space).mp hu.symm, ?_⟩
  have heq : d n - (d n - u) = u := by abel
  rw [heq]
  linarith

lemma hilbert_upper_eval_sq_sum {I : Type*} (v : I → E)
    (hv : ∀ (A : Finset I) (a : I → ℝ),
      ‖∑ n ∈ A, a n • v n‖ ≤ Real.sqrt (∑ n ∈ A, (a n)^2))
    (φ : E →L[ℝ] ℝ) (A : Finset I) :
    ∑ n ∈ A, φ (v n)^2 ≤ ‖φ‖^2 := by
  let S := ∑ n ∈ A, φ (v n)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hscalar : φ (∑ n ∈ A, φ (v n) • v n) = S := by
    simp only [map_sum, map_smul, smul_eq_mul, S, pow_two]
  have hnorm := φ.le_opNorm (∑ n ∈ A, φ (v n) • v n)
  rw [hscalar, Real.norm_eq_abs, abs_of_nonneg hS] at hnorm
  have hprod : S ≤ ‖φ‖ * Real.sqrt S := hnorm.trans
    (mul_le_mul_of_nonneg_left (hv A (fun n => φ (v n))) (norm_nonneg φ))
  have hs : Real.sqrt S ≤ ‖φ‖ := by
    by_cases hzero : Real.sqrt S = 0
    · rw [hzero]; exact norm_nonneg _
    · have hpos : 0 < Real.sqrt S := lt_of_le_of_ne (Real.sqrt_nonneg S) (Ne.symm hzero)
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith [Real.sq_sqrt hS]
  nlinarith [Real.sq_sqrt hS, norm_nonneg φ, Real.sqrt_nonneg S]

lemma weaklyNull_of_hilbert_upper (v : ℕ → E)
    (hv : ∀ (A : Finset ℕ) (a : ℕ → ℝ),
      ‖∑ n ∈ A, a n • v n‖ ≤ Real.sqrt (∑ n ∈ A, (a n)^2)) : WeaklyNull v := by
  intro φ
  have hs : Summable (fun n => φ (v n)^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) (hilbert_upper_eval_sq_sum v hv φ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := hs.tendsto_atTop_zero.sqrt
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using h

lemma oneSidedModulus_nonneg (t : ℝ) : (0 : EReal) ≤ oneSidedModulus E t := by
  apply le_iInf
  intro x
  obtain ⟨φ, hφ, hxφ⟩ := exists_dual_vector'' ℝ x.val
  apply le_iSup_of_le (functionalKernel φ)
  apply le_iInf
  intro y
  have hφy : φ y.val = 0 := y.property.1
  have h := φ.le_of_opNorm_le hφ (x.val + t • y.val)
  rw [map_add, map_smul, hφy, smul_zero, add_zero, hxφ, x.property] at h
  simp only [Real.ringHom_apply, Real.norm_eq_abs, abs_one, one_mul] at h
  exact EReal.coe_le_coe_iff.mpr (by linarith)

lemma oneSided_sphere_tail {t γ : ℝ} (hγ : (γ : EReal) < oneSidedModulus E t)
    (x : E) (hx : ‖x‖ = 1) :
    ∃ F : ClosedFiniteCodim E, ∀ y : E, y ∈ F.space → ‖y‖ = 1 →
      1 + γ ≤ ‖x + t • y‖ := by
  have hxlt := hγ.trans_le (iInf_le _ (⟨x, hx⟩ : {x : E // ‖x‖ = 1}))
  obtain ⟨F, hF⟩ := lt_iSup_iff.mp hxlt
  refine ⟨F, ?_⟩
  intro y hy hyn
  have hylt := hF.trans_le (iInf_le _ (⟨y, hy, hyn⟩ : {y : E // y ∈ F.space ∧ ‖y‖ = 1}))
  have hreal := EReal.coe_lt_coe_iff.mp hylt
  linarith

end WeakNullSequences

section AUCRayGrowth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_bound_extends_to_rays (x : E) (hx : ‖x‖ = 1) (F : Submodule ℝ E)
    {t γ : ℝ} (hγ : 0 ≤ γ)
    (hsphere : ∀ y : E, y ∈ F → ‖y‖ = 1 → 1 + γ ≤ ‖x + t • y‖)
    (y : E) (hy : y ∈ F) (hy1 : 1 ≤ ‖y‖) :
    1 + γ ≤ ‖x + t • y‖ := by
  let a := ‖y‖⁻¹
  have hyn : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy1
  have ha : 0 < a := inv_pos.mpr hyn
  have ha1 : a ≤ 1 := by
    simpa only [a, one_div] using ((div_le_one hyn).mpr hy1 : 1 / ‖y‖ ≤ 1)
  have hay : ‖a • y‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    exact inv_mul_cancel₀ (ne_of_gt hyn)
  have h := hsphere (a • y) (F.smul_mem a hy) hay
  have he : x + t • (a • y) = (1-a) • x + a • (x + t • y) := by module
  rw [he] at h
  have hn := norm_add_le ((1-a) • x) (a • (x + t • y))
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ha1),
    Real.norm_of_nonneg ha.le, hx, mul_one] at hn
  by_contra hh
  have hlong := lt_of_not_ge hh
  have hprod := mul_lt_mul_of_pos_left hlong ha
  have hγa : a * γ ≤ γ := mul_le_of_le_one_left hγ ha1
  nlinarith

lemma oneSided_wide_tail {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (hδ : (γ : EReal) < oneSidedModulus E t) (p : E) (hp : 0 < ‖p‖) :
    ∃ F : ClosedFiniteCodim E, ∀ w : E, w ∈ F.space → t * ‖p‖ ≤ ‖w‖ →
      (1 + γ) * ‖p‖ ≤ ‖p + w‖ := by
  let x := ‖p‖⁻¹ • p
  have hx : ‖x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    exact inv_mul_cancel₀ (ne_of_gt hp)
  obtain ⟨F, hF⟩ := oneSided_sphere_tail hδ x hx
  refine ⟨F, ?_⟩
  intro w hw hwn
  let v := (t * ‖p‖)⁻¹ • w
  have hv : v ∈ F.space := F.space.smul_mem _ hw
  have hc : 0 < t * ‖p‖ := mul_pos ht hp
  have hvn : 1 ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hc).mpr (by simpa using hwn)
  have h := norm_bound_extends_to_rays x hx F.space hγ hF v hv hvn
  have hec : t * (t * ‖p‖)⁻¹ = ‖p‖⁻¹ := by
    field_simp
  have he : x + t • v = ‖p‖⁻¹ • (p + w) := by
    dsimp only [x, v]
    rw [smul_smul, hec, smul_add]
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), mul_comm, ← div_eq_mul_inv] at h
  exact (le_div_iff₀ hp).mp h

/-- One weakly-null child sequence gives a definite AUC increase. -/
lemma oneSided_growth {t γ c : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hc : 0 < c)
    (hδ : (γ : EReal) < oneSidedModulus E t) (p : E) (hp : 0 < ‖p‖)
    (htp : t * ‖p‖ ≤ c/2) (d : ℕ → E) (hd : WeaklyNull d)
    (hdn : ∀ n, c ≤ ‖d n‖) :
    ∃ n, ‖p‖ + γ * ‖p‖ / 2 ≤ ‖p + d n‖ := by
  obtain ⟨F, hF⟩ := oneSided_wide_tail ht hγ.le hδ p hp
  have hε : 0 < min (c/2) (γ * ‖p‖ / 2) := lt_min (by positivity) (by positivity)
  obtain ⟨n, w, hw, he⟩ := (hd.approximable F hε).exists
  have hec : ‖d n - w‖ < c/2 := he.trans_le (min_le_left _ _)
  have heγ : ‖d n - w‖ < γ * ‖p‖ / 2 := he.trans_le (min_le_right _ _)
  have hwn : t * ‖p‖ ≤ ‖w‖ := by
    have h := norm_sub_norm_le (d n) w
    have hd' := hdn n
    linarith
  have hfw := hF w hw hwn
  have hpert := norm_sub_norm_le (p + w) (p + d n)
  have heq : (p + w) - (p + d n) = w - d n := by abel
  rw [heq, norm_sub_rev] at hpert
  exact ⟨n, by linarith⟩

end AUCRayGrowth

section BoundedTrees
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def child {h : ℕ} (s : Tree h) (hs : s.val.length < h) (n : ℕ) : Tree h :=
  ⟨s.val ++ [n], by simp only [List.length_append, List.length_singleton]; omega⟩

@[simp] lemma child_length {h : ℕ} (s : Tree h) (hs : s.val.length < h) (n : ℕ) :
    (child s hs n).val.length = s.val.length + 1 := by simp [child]

lemma exists_pos_real_lt_ereal {b : EReal} (hb : 0 < b) :
    ∃ γ : ℝ, 0 < γ ∧ (γ : EReal) < b := by
  cases b using EReal.rec with
  | bot => exact (not_lt_bot hb).elim
  | coe b =>
    have hb' : 0 < b := EReal.coe_lt_coe_iff.mp hb
    exact ⟨b/2, by positivity, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  | top => exact ⟨1, zero_lt_one, EReal.coe_lt_top 1⟩

/-- The bounded-tree obstruction for arbitrary finite heights. Weak nullity is tested against the whole dual; iteration of the positive per-step gain gives the contradiction. -/


theorem bounded_tree_modulus_eq_zero
    (p : (h : ℕ) → Tree h → E) {m M c : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hc : 0 < c)
    (hbound : ∀ h, 1 ≤ h → ∀ s : Tree h, m ≤ ‖p h s‖ ∧ ‖p h s‖ ≤ M)
    (hweak : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => p h (child s hs n) - p h s))
    (hinc : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      c ≤ ‖p h (child s hs n) - p h s‖) :
    oneSidedModulus E (c / (2 * M)) = 0 := by
  apply le_antisymm ?_ (oneSidedModulus_nonneg _)
  by_contra hnot
  obtain ⟨γ, hγ, hγδ⟩ := exists_pos_real_lt_ereal (lt_of_not_ge hnot)
  have hM : 0 < M := hm.trans_le hmM
  have ht : 0 < c / (2 * M) := by positivity
  let a := γ * m / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (M / a)
  let H := n + 1
  have hH : 1 ≤ H := Nat.le_add_left 1 n
  have hlarge : M < m + (H : ℝ) * a := by
    have hn' : M < (n : ℝ) * a := (div_lt_iff₀ ha).mp hn
    simp only [H, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hpath : ∀ j : ℕ, j ≤ H → ∃ s : Tree H,
      s.val.length = j ∧ m + (j : ℝ) * a ≤ ‖p H s‖ := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨root H, rfl, by simpa using (hbound H hH (root H)).1⟩
    | succ j ih =>
      intro hj
      obtain ⟨s, hsl, hsn⟩ := ih (Nat.le_of_succ_le hj)
      have hs : s.val.length < H := by omega
      have hpb := hbound H hH s
      have hp : 0 < ‖p H s‖ := hm.trans_le hpb.1
      have htp : (c / (2 * M)) * ‖p H s‖ ≤ c/2 := by
        calc
          _ ≤ (c / (2 * M)) * M := mul_le_mul_of_nonneg_left hpb.2 ht.le
          _ = c/2 := by field_simp
      obtain ⟨i, hi⟩ := oneSided_growth ht hγ hc hγδ (p H s) hp htp
        (fun n => p H (child s hs n) - p H s) (hweak H hH s hs) (hinc H hH s hs)
      rw [add_sub_cancel] at hi
      refine ⟨child s hs i, by simp [hsl], ?_⟩
      have hgrowth : a ≤ γ * ‖p H s‖ / 2 := by
        dsimp [a]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpb.1 hγ.le) (by norm_num)
      rw [Nat.cast_succ]
      nlinarith
  obtain ⟨s, hs, hsn⟩ := hpath H le_rfl
  have hb := (hbound H hH s).2
  linarith

/-- Explicit equivalence constants are retained in the obstruction radius.
    Quantification over continuous linear copies is precisely quantification
    over equivalent norms via the identity linear equivalence. -/
theorem bounded_tree_renorming_obstruction
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : (h : ℕ) → Tree h → E) {m M c α β : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hc : 0 < c)
    (hbound : ∀ h, 1 ≤ h → ∀ s : Tree h, m ≤ ‖p h s‖ ∧ ‖p h s‖ ≤ M)
    (hweak : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => p h (child s hs n) - p h s))
    (hinc : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      c ≤ ‖p h (child s hs n) - p h s‖)
    (e : E ≃L[ℝ] Y) (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x : E, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖) :
    oneSidedModulus Y (α * c / (2 * β * M)) = 0 := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hM : 0 < M := hm.trans_le hmM
  have hb' : ∀ h, 1 ≤ h → ∀ s : Tree h,
      α * m ≤ ‖e (p h s)‖ ∧ ‖e (p h s)‖ ≤ β * M := by
    intro h hh s
    exact ⟨(mul_le_mul_of_nonneg_left (hbound h hh s).1 hα.le).trans (he _).1,
      (he _).2.trans (mul_le_mul_of_nonneg_left (hbound h hh s).2 hβ.le)⟩
  have hw' : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => e (p h (child s hs n)) - e (p h s)) := by
    intro h hh s hs
    have hw := (hweak h hh s hs).map e.toContinuousLinearMap
    change WeaklyNull (fun n => e (p h (child s hs n) - p h s)) at hw
    simpa only [map_sub] using hw
  have hi' : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      α*c ≤ ‖e (p h (child s hs n)) - e (p h s)‖ := by
    intro h hh s hs n
    rw [← map_sub]
    exact (mul_le_mul_of_nonneg_left (hinc h hh s hs n) hα.le).trans (he _).1
  have hmM' : α*m ≤ β*M := (mul_le_mul_of_nonneg_left hmM hα.le).trans
    (mul_le_mul_of_nonneg_right hαβ hM.le)
  simpa only [mul_assoc] using bounded_tree_modulus_eq_zero (fun h s => e (p h s))
    (mul_pos hα hm) hmM' (mul_pos hα hc) hb' hw' hi'

end BoundedTrees

end BoundedTreePotentials

end

end OAI
