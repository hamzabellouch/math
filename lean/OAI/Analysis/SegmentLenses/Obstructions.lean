import OAI.Analysis.SegmentLenses.Projections

namespace OAI

/-!
# Equivalent-norm obstructions from weakly null paths
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section OneSidedModulus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def oneSidedOn (x : SphereOne E) (t : ℝ) (F : CofiniteSubspace E) : ℝ :=
  ⨅ y : CofiniteSphere E F, ‖x.val + t • y.val‖ - 1

def oneSidedAt (x : SphereOne E) (t : ℝ) : ℝ :=
  ⨆ F : CofiniteSubspace E, oneSidedOn x t F

def oneSidedModulus (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) : ℝ :=
  ⨅ x : SphereOne E, oneSidedAt x t

def AUC (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ t : ℝ, 0 < t → 0 < oneSidedModulus E t

theorem oneSidedOn_bddBelow (x : SphereOne E) (t : ℝ) (F : CofiniteSubspace E) :
    BddBelow (Set.range (fun y : CofiniteSphere E F => ‖x.val + t • y.val‖ - 1)) := by
  refine ⟨-1, ?_⟩
  rintro _ ⟨y, rfl⟩
  linarith [norm_nonneg (x.val + t • y.val)]

theorem oneSidedAt_bdd (hE : ¬ FiniteDimensional ℝ E) (x : SphereOne E)
    {t : ℝ} (ht : 0 ≤ t) :
    BddAbove (Set.range (fun F : CofiniteSubspace E => oneSidedOn x t F)) := by
  refine ⟨t, ?_⟩
  rintro _ ⟨F, rfl⟩
  let y : CofiniteSphere E F := Classical.choice (F.sphere_nonempty hE)
  have hn := norm_add_le x.val (t • y.val)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, y.property.2, mul_one, x.property] at hn
  exact (ciInf_le (oneSidedOn_bddBelow x t F) y).trans (by linarith)

theorem oneSidedAt_nonneg (hE : ¬ FiniteDimensional ℝ E) (x : SphereOne E)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ oneSidedAt x t := by
  obtain ⟨f, hfn, hfx⟩ := exists_dual_vector ℝ x.val (by rw [x.property]; norm_num)
  let F := CofiniteSubspace.ofMap f
  have := F.sphere_nonempty hE
  have hF : 0 ≤ oneSidedOn x t F := by
    apply le_ciInf
    intro y
    have hy : f y.val = 0 := y.property.1
    have he : f (x.val + t • y.val) = 1 := by
      rw [map_add, map_smul, hy, smul_zero, add_zero, hfx, x.property]; rfl
    have hn := f.le_opNorm (x.val + t • y.val)
    rw [he, norm_one, hfn, one_mul] at hn
    linarith
  exact hF.trans (le_ciSup (oneSidedAt_bdd hE x ht) F)

theorem oneSidedModulus_nonneg (hE : ¬ FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ oneSidedModulus E t := by
  have := sphereOne_nonempty hE
  exact le_ciInf (fun x => oneSidedAt_nonneg hE x ht)

theorem cofinite_gain (hE : ¬ FiniteDimensional ℝ E) {t d : ℝ} (ht : 0 ≤ t)
    (hd : d < oneSidedModulus E t) (x : SphereOne E) :
    ∃ F : CofiniteSubspace E, ∀ y : CofiniteSphere E F,
      1 + d < ‖x.val + t • y.val‖ := by
  have hb : BddBelow (Set.range (fun x : SphereOne E => oneSidedAt x t)) := by
    refine ⟨0, ?_⟩; rintro _ ⟨z, rfl⟩; exact oneSidedAt_nonneg hE z ht
  have hx : d < oneSidedAt x t := hd.trans_le (ciInf_le hb x)
  obtain ⟨F, hF⟩ := exists_lt_of_lt_ciSup hx
  refine ⟨F, fun y => ?_⟩
  have hon := ciInf_le (oneSidedOn_bddBelow x t F) y
  change oneSidedOn x t F ≤ _ at hon
  linarith
end OneSidedModulus

section WeakNullTransfer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def WeaklyNull (u : ℕ → E) : Prop :=
  ∀ L : StrongDual ℝ E, Filter.Tendsto (fun n => L (u n)) Filter.atTop (nhds 0)

theorem WeaklyNull.map {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {u : ℕ → E} (hu : WeaklyNull u) (f : E →L[ℝ] D) : WeaklyNull (fun n => f (u n)) := by
  intro L
  exact hu (L.comp f)

theorem WeaklyNull.finiteDimensional {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] {u : ℕ → D} (hu : WeaklyNull u) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  let e := (Module.finBasis ℝ D).equivFunL
  have hp : Filter.Tendsto (fun n => e (u n)) Filter.atTop (nhds 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hu ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  have h := e.symm.continuous.continuousAt.tendsto.comp hp
  simpa only [Function.comp_def, e.symm_apply_apply, map_zero] using h

theorem WeaklyNull.cofinite_approx {u : ℕ → E} (hu : WeaklyNull u)
    (F : CofiniteSubspace E) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ q ∈ F.space, ‖u n - q‖ < ε := by
  let : IsClosed (F.space : Set E) := F.closed
  have hq := (hu.map F.space.mkQL).finiteDimensional
  have hnorm : Filter.Tendsto (fun n => ‖F.space.mkQL (u n)‖) Filter.atTop (nhds 0) := by
    simpa using hq.norm
  have hev := (tendsto_order.1 hnorm).2 (ε / 2) (by linarith)
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨r, hr, hrn⟩ := Submodule.Quotient.norm_mk_lt (F.space.mkQL (u n)) (half_pos hε)
  refine ⟨n, u n - r, ?_, ?_⟩
  · have he : F.space.mkQ (u n - r) = 0 := by
      rw [map_sub]; change F.space.mkQL (u n) - Submodule.Quotient.mk r = 0
      rw [hr, sub_self]
    exact (Submodule.Quotient.mk_eq_zero F.space).mp he
  · have he : u n - (u n - r) = r := by abel
    rw [he]
    linarith

theorem WeaklyNull.smul_bounded {u : ℕ → E} (hu : WeaklyNull u) (c : ℕ → ℝ)
    {C : ℝ} (hc : ∀ n, |c n| ≤ C) : WeaklyNull (fun n => c n • u n) := by
  intro L
  have ht : Filter.Tendsto (fun n => C * ‖L (u n)‖) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hu L).norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ ht
  intro n
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)


theorem unit_approx_normalize (u q : E) (hu : ‖u‖ = 1) (hq : q ≠ 0) :
    ‖u - ‖q‖⁻¹ • q‖ ≤ 2 * ‖u - q‖ := by
  have hqn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have he : ‖q - ‖q‖⁻¹ • q‖ = |‖q‖ - 1| := by
    rw [show q - ‖q‖⁻¹ • q = (1 - ‖q‖⁻¹) • q by module,
      norm_smul, Real.norm_eq_abs]
    calc
      |1 - ‖q‖⁻¹| * ‖q‖ = |1 - ‖q‖⁻¹| * |‖q‖| := by rw [abs_of_nonneg (norm_nonneg q)]
      _ = |(1 - ‖q‖⁻¹) * ‖q‖| := (abs_mul _ _).symm
      _ = |‖q‖ - 1| := by congr 1; field_simp
  have hd : |‖q‖ - 1| ≤ ‖u - q‖ := by
    rw [← hu, norm_sub_rev u q]
    exact abs_norm_sub_norm_le q u
  have h := norm_add_le (u - q) (q - ‖q‖⁻¹ • q)
  rw [sub_add_sub_cancel] at h
  rw [he] at h
  linarith

theorem WeaklyNull.cofinite_unit_approx {u : ℕ → E} (hu : WeaklyNull u)
    (hn : ∀ n, ‖u n‖ = 1) (F : CofiniteSubspace E) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ w : CofiniteSphere E F, ‖u n - w.val‖ < ε := by
  obtain ⟨n, q, hqF, he⟩ := hu.cofinite_approx F (lt_min (half_pos hε) (by norm_num : (0:ℝ)<1))
  have hq0 : q ≠ 0 := by
    intro hz; rw [hz, sub_zero, hn] at he
    exact (lt_of_lt_of_le he (min_le_right _ _)).false
  refine ⟨n, ⟨‖q‖⁻¹ • q, F.space.smul_mem _ hqF, ?_⟩, ?_⟩
  · simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq0)]
  · exact (unit_approx_normalize (u n) q (hn n) hq0).trans_lt (by
      have := lt_of_lt_of_le he (min_le_left _ _); linarith)
end WeakNullTransfer

section RayAndPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem ray_budget (x v : E) (hx : ‖x‖ = 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    s * (‖x + r • v‖ - 1) ≤ r * (‖x + s • v‖ - 1) := by
  have hs : 0 ≤ s := hr.trans hrs
  have he : s • (x + r • v) = r • (x + s • v) + (s - r) • x := by module
  have hn := norm_add_le (r • (x + s • v)) ((s - r) • x)
  rw [← he, norm_smul, norm_smul, norm_smul, hx, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hs, abs_of_nonneg hr, abs_of_nonneg (sub_nonneg.mpr hrs)] at hn
  nlinarith

theorem ray_strict_gain (x v : E) (hx : ‖x‖ = 1) {r s d : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hd : 0 ≤ d) (hg : 1 + d < ‖x + r • v‖) :
    1 + d < ‖x + s • v‖ := by
  have hb := ray_budget x v hx hr.le hrs
  have hmul := mul_lt_mul_of_pos_left hg (hr.trans_le hrs)
  nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hd]



theorem cofinite_child_growth (hE : ¬ FiniteDimensional ℝ E)
    {a b r d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) (hrab : r ≤ a / b)
    (hd : 0 < d) (hmod : d < oneSidedModulus E r)
    (z : E) (hza : a ≤ ‖z‖) (hzb : ‖z‖ ≤ b)
    (e : ℕ → E) (he : WeaklyNull e) (hea : ∀ n, a ≤ ‖e n‖) :
    ∃ n, (1 + d / 2) * ‖z‖ < ‖z + e n‖ := by
  have hb : 0 < b := ha.trans_le hab
  have hz : 0 < ‖z‖ := ha.trans_le hza
  have hen : ∀ n, 0 < ‖e n‖ := fun n => ha.trans_le (hea n)
  let x : SphereOne E := ⟨‖z‖⁻¹ • z, by
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz.ne']⟩
  let u : ℕ → E := fun n => ‖e n‖⁻¹ • e n
  have hu : WeaklyNull u := he.smul_bounded (fun n => ‖e n‖⁻¹) (C := a⁻¹) (by
    intro n
    rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_anti₀ ha (hea n))
  have hun : ∀ n, ‖u n‖ = 1 := by
    intro n
    simp only [u, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hen n).ne']
  obtain ⟨F, hF⟩ := cofinite_gain hE hr.le hmod x
  obtain ⟨n, w, hw⟩ := hu.cofinite_unit_approx hun F (div_pos hd (by positivity : 0 < 2*r))
  have hwgain := hF w
  have hn := norm_sub_norm_le (x.val + r • w.val) (x.val + r • u n)
  rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, norm_sub_rev w.val (u n)] at hn
  have herr : r * ‖u n - w.val‖ < d / 2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2*r)).mp hw
    nlinarith
  have hfixed : 1 + d / 2 < ‖x.val + r • u n‖ := by linarith
  let s := ‖e n‖ / ‖z‖
  have hrs : r ≤ s := by
    apply (le_div_iff₀ hz).mpr
    have hrb := (le_div_iff₀ hb).mp hrab
    exact (mul_le_mul_of_nonneg_left hzb hr.le).trans (hrb.trans (hea n))
  have hactual := ray_strict_gain x.val (u n) x.property hr hrs (by positivity) hfixed
  have hid : ‖z‖ • (x.val + s • u n) = z + e n := by
    dsimp only [x, s, u]
    simp only [smul_add, smul_smul]
    rw [mul_inv_cancel₀ hz.ne', one_smul]
    congr 1
    rw [show ‖z‖ * (‖e n‖ / ‖z‖ * ‖e n‖⁻¹) = 1 by field_simp [hz.ne', (hen n).ne'], one_smul]
  refine ⟨n, ?_⟩
  have h := mul_lt_mul_of_pos_left hactual hz
  rw [mul_comm (1 + d/2), ← hid, norm_smul, Real.norm_eq_abs, abs_of_pos hz]
  exact h




theorem bounded_finite_paths_modulus_zero (hE : ¬ FiniteDimensional ℝ E)
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) (hrab : r ≤ a / b)
    (paths : ∀ h : ℕ, 1 ≤ h → ∃ z : List ℕ → E,
      (∀ v, v.length ≤ h → a ≤ ‖z v‖ ∧ ‖z v‖ ≤ b) ∧
      (∀ v, v.length < h → WeaklyNull (fun n => z (v ++ [n]) - z v)) ∧
      (∀ v, v.length < h → ∀ n, a ≤ ‖z (v ++ [n]) - z v‖)) :
    oneSidedModulus E r = 0 := by
  apply le_antisymm _ (oneSidedModulus_nonneg hE hr.le)
  by_contra hnot
  have hm : 0 < oneSidedModulus E r := lt_of_not_ge hnot
  let d := oneSidedModulus E r / 2
  have hd : 0 < d := half_pos hm
  have hdmod : d < oneSidedModulus E r := half_lt_self hm
  let c := a * (d / 2)
  have hc : 0 < c := mul_pos ha (half_pos hd)
  obtain ⟨h, hh⟩ := exists_nat_gt (max 1 (b / c))
  have hh1 : 1 ≤ h := by
    have ht : (1:ℝ) < h := (le_max_left _ _).trans_lt hh
    exact_mod_cast ht.le
  have hhc : b < (h : ℝ) * c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hh)
  obtain ⟨z, hz, hw, he⟩ := paths h hh1
  have step : ∀ k : ℕ, k ≤ h → ∃ v : List ℕ,
      v.length = k ∧ a + (k : ℝ) * c ≤ ‖z v‖ := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact ⟨[], rfl, by simpa using (hz [] (by simp)).1⟩
    | succ k ih =>
      intro hk
      obtain ⟨v, hv, hvn⟩ := ih (by omega)
      have hvl : v.length < h := by omega
      obtain ⟨n, hn⟩ := cofinite_child_growth hE ha hab hr hrab hd hdmod
        (z v) (hz v hvl.le).1 (hz v hvl.le).2 _ (hw v hvl) (he v hvl)
      rw [add_sub_cancel] at hn
      refine ⟨v ++ [n], by simp [hv], ?_⟩
      have hza := (hz v hvl.le).1
      have hinc : c ≤ (d / 2) * ‖z v‖ := by
        dsimp only [c]
        nlinarith
      push_cast
      nlinarith
  obtain ⟨v, hv, hvn⟩ := step h le_rfl
  have hvb := (hz v hv.le).2
  linarith
end RayAndPath


section EuclideanWeakNull
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclidean_family_weakly_null (c : I → E)
    (hc : ∀ (s : Finset I) (a : I → ℝ),
      ‖∑ i ∈ s, a i • c i‖ ≤ Real.sqrt (∑ i ∈ s, a i ^ 2))
    (v : ℕ → I) (hv : Function.Injective v) : WeaklyNull (fun n => c (v n)) := by
  intro L
  have hbound : ∀ s : Finset I, ∑ i ∈ s, L (c i) ^ 2 ≤ ‖L‖ ^ 2 := by
    intro s
    let q := ∑ i ∈ s, L (c i) • c i
    let S := ∑ i ∈ s, L (c i) ^ 2
    have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hp : L q = S := by simp only [q, S, map_sum, map_smul, smul_eq_mul, pow_two]
    have hq : ‖q‖ ≤ Real.sqrt S := hc s _
    have h := L.le_opNorm q
    rw [hp, Real.norm_eq_abs, abs_of_nonneg hS] at h
    have h' := h.trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
    have hs := Real.sq_sqrt hS
    nlinarith [Real.sqrt_nonneg S, norm_nonneg L]
  have hs : Summable (fun i => L (c i) ^ 2) := summable_of_sum_le (fun _ => sq_nonneg _) hbound
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp (hs.comp_injective hv).tendsto_atTop_zero
  have hn : Filter.Tendsto (fun n => ‖L (c (v n))‖) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn
end EuclideanWeakNull

section EquivalentPathObstruction
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]



def UnitFinitePaths : Prop := ∀ h : ℕ, 1 ≤ h → ∃ z : List ℕ → E,
  (∀ v, v.length ≤ h → ‖z v‖ = 1) ∧
  (∀ v, v.length < h → WeaklyNull (fun n => z (v ++ [n]) - z v)) ∧
  (∀ v, v.length < h → ∀ n, ‖z (v ++ [n]) - z v‖ = 1)

variable {E} {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]



theorem equivalent_paths_modulus_zero (hE : ¬ FiniteDimensional ℝ E)
    (hpaths : UnitFinitePaths E) (e : E ≃L[ℝ] D)
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ x : E, a * ‖x‖ ≤ ‖e x‖) (hupper : ∀ x : E, ‖e x‖ ≤ b * ‖x‖)
    (hr : 0 < r) (hrab : r ≤ a / b) : oneSidedModulus D r = 0 := by
  have hD : ¬ FiniteDimensional ℝ D := by
    intro hfin
    let := hfin
    exact hE (FiniteDimensional.of_injective e.toLinearMap e.injective)
  apply bounded_finite_paths_modulus_zero hD ha hab hr hrab
  intro h hh
  obtain ⟨z, hz, hw, hn⟩ := hpaths h hh
  refine ⟨fun v => e (z v), ?_, ?_, ?_⟩
  · intro v hv
    have hl := hlower (z v)
    have hu := hupper (z v)
    rw [hz v hv, mul_one] at hl hu
    exact ⟨hl, hu⟩
  · intro v hv
    simpa only [map_sub, ContinuousLinearEquiv.coe_coe] using (hw v hv).map e.toContinuousLinearMap
  · intro v hv n
    simpa only [map_sub, hn v hv n, mul_one] using hlower (z (v ++ [n]) - z v)

theorem equivalent_paths_not_auc (hE : ¬ FiniteDimensional ℝ E)
    (hpaths : UnitFinitePaths E) (e : E ≃L[ℝ] D) : ¬ AUC D := by
  let C := ‖e.symm.toContinuousLinearMap‖ + 1
  let a := C⁻¹
  let b := ‖e.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have ha : 0 < a := inv_pos.mpr hC
  have hb : 0 < b := by dsimp [b]; positivity
  have ha1 : a ≤ 1 := by
    apply (inv_le_one₀ hC).mpr
    dsimp [C]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hb1 : 1 ≤ b := by dsimp [b]; linarith [norm_nonneg e.toContinuousLinearMap]
  have hab : a ≤ b := ha1.trans hb1
  have hl : ∀ x : E, a * ‖x‖ ≤ ‖e x‖ := by
    intro x
    have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    simp only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] at h
    have hh : ‖x‖ ≤ C * ‖e x‖ := by
      dsimp [C]
      nlinarith [norm_nonneg (e x)]
    dsimp only [a]
    exact (inv_mul_le_iff₀ hC).mpr hh
  have hu : ∀ x : E, ‖e x‖ ≤ b * ‖x‖ := by
    intro x
    have h := e.toContinuousLinearMap.le_opNorm x
    simp only [ContinuousLinearEquiv.coe_coe] at h
    dsimp only [b]
    nlinarith [norm_nonneg x]
  have hz := equivalent_paths_modulus_zero hE hpaths e ha hab hl hu (div_pos ha hb) le_rfl
  intro hauc
  have hp := hauc (a/b) (div_pos ha hb)
  rw [hz] at hp
  exact hp.false
end EquivalentPathObstruction

section RootPathCertificates
variable {V : Type*} [DecidableEq V] [SegmentSystem V]


theorem norm_segmentFunctional (S : Finset V) (hS : SegmentSystem.isSegment S)
    (hne : S.Nonempty) : ‖segmentFunctional S‖ = 1 := by
  apply le_antisymm
  · apply dual_norm_le _ (by norm_num)
    intro u
    rw [segmentFunctional_apply, one_mul]
    have hb := indexed_test_bound u.coeff (fun _ : Unit => S)
      (fun _ => Or.inr hS) (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    simp only [Finset.univ_unique, Finset.sum_singleton] at hb
    change (∑ v ∈ S, u.coeff v) ^ 2 ≤ ‖u‖ ^ 2 at hb
    nlinarith [norm_nonneg u, sq_abs (∑ v ∈ S, u.coeff v)]
  · obtain ⟨v, hv⟩ := hne
    have he : segmentFunctional S (unitVector v) = 1 := by
      simp [segmentFunctional, coordinate_unitVector, hv]
    have hn := (segmentFunctional S).le_opNorm (unitVector v)
    simpa [he] using hn

def predualSegment (S : Finset V) : CoordinatePredual V :=
  ⟨segmentFunctional S, Submodule.sum_mem _ (fun v _ => coordinate_mem v)⟩

@[simp] theorem norm_predualSegment (S : Finset V) (hS : SegmentSystem.isSegment S)
    (hne : S.Nonempty) : ‖predualSegment S‖ = 1 := norm_segmentFunctional S hS hne

theorem fullDual_distinct_coordinates_weakly_null (v : ℕ → V) (hv : Function.Injective v) :
    WeaklyNull (fun n => coordinate (v n)) :=
  euclidean_family_weakly_null coordinate norm_coordinate_sum_le v hv

end RootPathCertificates


theorem prefix_append_single_iff (w v : List ℕ) (n : ℕ) :
    w.IsPrefix (v ++ [n]) ↔ w.IsPrefix v ∨ w = v ++ [n] := by
  constructor
  · intro hw
    have hv : v.IsPrefix (v ++ [n]) := ⟨[n], rfl⟩
    rcases List.prefix_or_prefix_of_prefix hw hv with h | h
    · exact Or.inl h
    · by_cases he : w = v ++ [n]
      · exact Or.inr he
      · have hl : w.length ≤ v.length := by
          have hwl := hw.length_le
          have hne : w.length ≠ (v ++ [n]).length := fun heq => he (hw.eq_of_length heq)
          simp only [List.length_append, List.length_singleton] at hwl hne
          omega
        have heq : v = w := h.eq_of_length (Nat.le_antisymm h.length_le hl)
        simpa only [← heq] using (Or.inl (List.prefix_refl v) : v.IsPrefix v ∨ v = v ++ [n])
  · rintro (h | rfl)
    · exact h.trans ⟨[n], rfl⟩
    · exact List.prefix_refl _

section InfinitePaths
local instance : AddCommMonoid BInfinite :=
  (inferInstance : NormedAddCommGroup BInfinite).toAddCommMonoid
local instance : TopologicalSpace BInfinite :=
  (inferInstance : NormedAddCommGroup BInfinite).toUniformSpace.toTopologicalSpace
local instance : Module ℝ BInfinite := (inferInstance : NormedSpace ℝ BInfinite).toModule


def infinitePath (v : InfiniteVertex) : BInfinite := predualSegment (Finset.Iic v)

theorem infinitePath_isSegment (v : InfiniteVertex) :
    SegmentSystem.isSegment (Finset.Iic v) := by
  apply (IntervalSegments.iff_interval _).mpr
  refine ⟨[], v, List.nil_prefix, ?_⟩
  intro w
  simp only [Finset.mem_Iic]
  change w.IsPrefix v ↔ [].IsPrefix w ∧ w.IsPrefix v
  simp

@[simp] theorem norm_infinitePath (v : InfiniteVertex) : ‖infinitePath v‖ = 1 :=
  norm_predualSegment _ (infinitePath_isSegment v) ⟨v, Finset.mem_Iic.mpr le_rfl⟩

theorem infinitePath_child (v : InfiniteVertex) (n : ℕ) :
    infinitePath (v ++ [n]) = infinitePath v + predualCoordinate (v ++ [n]) := by
  classical
  apply Subtype.ext
  change segmentFunctional (Finset.Iic (v ++ [n])) =
    segmentFunctional (Finset.Iic v) + coordinate (v ++ [n])
  have he : Finset.Iic (v ++ [n]) = insert (v ++ [n]) (Finset.Iic v) := by
    ext w
    simp only [Finset.mem_Iic, Finset.mem_insert]
    exact (prefix_append_single_iff w v n).trans (or_comm ..)
  have hn : v ++ [n] ∉ Finset.Iic v := by
    intro h
    have hl := (Finset.mem_Iic.mp h : (v ++ [n]).IsPrefix v).length_le
    simp at hl
  rw [he, segmentFunctional, Finset.sum_insert hn, add_comm]
  rfl

theorem infinitePath_child_sub (v : InfiniteVertex) (n : ℕ) :
    infinitePath (v ++ [n]) - infinitePath v = predualCoordinate (v ++ [n]) := by
  rw [infinitePath_child]
  apply Subtype.ext
  change (infinitePath v).val + coordinate (v ++ [n]) - (infinitePath v).val = coordinate (v ++ [n])
  abel

theorem infinitePath_children_weakly_null (v : InfiniteVertex) :
    WeaklyNull (fun n => infinitePath (v ++ [n]) - infinitePath v) := by
  intro L
  simpa only [infinitePath_child_sub] using distinct_coordinates_weakly_null
    (V := InfiniteVertex) (fun n => v ++ [n]) (by
      intro n m h
      simpa only [List.append_cancel_left_eq, List.singleton_inj] using h) L

end InfinitePaths

section ForestPaths

def forestRoot (h : ℕ) (hh : 1 ≤ h) : ForestVertex := ⟨(h, []), hh, by simp⟩
def forestNode (h : ℕ) (hh : 1 ≤ h) (v : List ℕ) (hv : v.length ≤ h) : ForestVertex :=
  ⟨(h, v), hh, hv⟩

theorem forest_iic_segment (v : ForestVertex) : SegmentSystem.isSegment (Finset.Iic v) := by
  apply (IntervalSegments.iff_interval _).mpr
  refine ⟨forestRoot v.val.1 v.property.1, v, ⟨rfl, List.nil_prefix⟩, ?_⟩
  intro w
  simp only [Finset.mem_Iic]
  constructor
  · intro h
    exact ⟨⟨h.1.symm, List.nil_prefix⟩, h⟩
  · exact And.right



def forestPath (h : ℕ) (hh : 1 ≤ h) (v : List ℕ) : X :=
  if hv : v.length ≤ h then segmentFunctional (Finset.Iic (forestNode h hh v hv)) else 0

@[simp] theorem norm_forestPath (h : ℕ) (hh : 1 ≤ h) (v : List ℕ) (hv : v.length ≤ h) :
    ‖forestPath h hh v‖ = 1 := by
  classical
  rw [forestPath, dite_eq_left hv]
  exact norm_segmentFunctional _ (forest_iic_segment _) ⟨_, Finset.mem_Iic.mpr le_rfl⟩

theorem forestPath_child (h : ℕ) (hh : 1 ≤ h) (v : List ℕ) (hv : v.length < h) (n : ℕ) :
    forestPath h hh (v ++ [n]) = forestPath h hh v +
      coordinate (forestNode h hh (v ++ [n]) (by simp; omega)) := by
  classical
  let a := forestNode h hh v hv.le
  let b := forestNode h hh (v ++ [n]) (by simp; omega)
  have he : Finset.Iic b = insert b (Finset.Iic a) := by
    ext w
    simp only [Finset.mem_Iic, Finset.mem_insert]
    change (w.val.1 = h ∧ w.val.2.IsPrefix (v ++ [n])) ↔
      w = b ∨ (w.val.1 = h ∧ w.val.2.IsPrefix v)
    rw [prefix_append_single_iff]
    constructor
    · rintro ⟨hc, hw | hw⟩
      · exact Or.inr ⟨hc, hw⟩
      · exact Or.inl (Subtype.ext (Prod.ext hc hw))
    · rintro (rfl | ⟨hc, hw⟩)
      · exact ⟨rfl, Or.inr rfl⟩
      · exact ⟨hc, Or.inl hw⟩
  have hn : b ∉ Finset.Iic a := by
    intro hx
    have hl := (Finset.mem_Iic.mp hx).2.length_le
    change (v ++ [n]).length ≤ v.length at hl
    simp at hl
  rw [forestPath, dite_eq_left (by simp; omega), forestPath, dite_eq_left hv.le]
  change segmentFunctional (Finset.Iic b) = segmentFunctional (Finset.Iic a) + coordinate b
  rw [he, segmentFunctional, Finset.sum_insert hn, add_comm]
  rfl

theorem forestPath_children_weakly_null (h : ℕ) (hh : 1 ≤ h) (v : List ℕ) (hv : v.length < h) :
    WeaklyNull (fun n => forestPath h hh (v ++ [n]) - forestPath h hh v) := by
  classical
  have hw := fullDual_distinct_coordinates_weakly_null
    (fun n => forestNode h hh (v ++ [n]) (by simp; omega)) (by
      intro n m hn
      have hlist := congrArg (fun w : ForestVertex => w.val.2) hn
      simpa only [forestNode, List.append_cancel_left_eq, List.singleton_inj] using hlist)
  convert hw using 1
  funext n
  rw [forestPath_child h hh v hv n, add_sub_cancel_left]

end ForestPaths

section FinalObstructions

theorem infinite_unit_finite_paths : UnitFinitePaths BInfinite := by
  intro h hh
  refine ⟨infinitePath, ?_, ?_, ?_⟩
  · intro v hv; exact norm_infinitePath v
  · intro v hv; exact infinitePath_children_weakly_null v
  · intro v hv n
    rw [infinitePath_child_sub, norm_predualCoordinate]

theorem forest_unit_finite_paths : UnitFinitePaths X := by
  classical
  intro h hh
  refine ⟨forestPath h hh, ?_, ?_, ?_⟩
  · exact norm_forestPath h hh
  · exact forestPath_children_weakly_null h hh
  · intro v hv n
    rw [forestPath_child h hh v hv n, add_sub_cancel_left, norm_coordinate]

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]



theorem infinite_equivalent_modulus_zero (e : BInfinite ≃L[ℝ] D)
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ x : BInfinite, a * ‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x : BInfinite, ‖e x‖ ≤ b * ‖x‖)
    (hr : 0 < r) (hrab : r ≤ a / b) : oneSidedModulus D r = 0 := by
  classical
  exact equivalent_paths_modulus_zero predual_not_finite infinite_unit_finite_paths e
    ha hab hlower hupper hr hrab



theorem forest_equivalent_modulus_zero (e : X ≃L[ℝ] D)
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ x : X, a * ‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x : X, ‖e x‖ ≤ b * ‖x‖)
    (hr : 0 < r) (hrab : r ≤ a / b) : oneSidedModulus D r = 0 := by
  classical
  exact equivalent_paths_modulus_zero fullDual_not_finite forest_unit_finite_paths e
    ha hab hlower hupper hr hrab


theorem infinite_no_equivalent_AUC (e : BInfinite ≃L[ℝ] D) : ¬ AUC D := by
  classical
  exact equivalent_paths_not_auc predual_not_finite infinite_unit_finite_paths e


theorem forest_no_equivalent_AUC (e : X ≃L[ℝ] D) : ¬ AUC D := by
  classical
  exact equivalent_paths_not_auc fullDual_not_finite forest_unit_finite_paths e

end FinalObstructions


end SegmentLenses

end

end OAI
