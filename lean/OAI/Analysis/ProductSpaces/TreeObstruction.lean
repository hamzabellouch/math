import OAI.Analysis.ProductSpaces.Model

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts

/-- Natural enumeration of the positive-integer children. -/
def child (v : Vertex) (n : ℕ) : Vertex := v ++ [⟨n + 1, Nat.succ_pos n⟩]

section AbstractObstruction

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Weak convergence to zero, stated directly against continuous real linear functionals. -/
def WeaklyNull (u : ℕ → X) : Prop :=
  ∀ f : X →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 0)

lemma weaklyNull_tendsto_finiteDimensional [FiniteDimensional ℝ X]
    {u : ℕ → X} (hu : WeaklyNull u) : Tendsto u atTop (𝓝 0) := by
  let e := (Module.finBasis ℝ X).equivFunL
  have he : Tendsto (fun n => e (u n)) atTop (𝓝 (e 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa using hu ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  have h := (e.symm.continuous.tendsto (e 0)).comp he
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, map_zero] using h

/-- A weakly null sequence approaches every closed finite-codimensional subspace in norm. -/
lemma weaklyNull_approx_cofinite {u : ℕ → X} (hu : WeaklyNull u)
    (F : Submodule ℝ X) (hF : F ∈ CofiniteSubspaces X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ z ∈ F, ‖u n - z‖ < ε := by
  let : IsClosed (F : Set X) := hF.1
  let : FiniteDimensional ℝ (X ⧸ F) := hF.2
  have hquot : Tendsto (fun n => F.mkQL (u n)) atTop (𝓝 0) :=
    weaklyNull_tendsto_finiteDimensional (fun f => by simpa using hu (f.comp F.mkQL))
  have he : ∀ᶠ n in atTop, ‖F.mkQL (u n)‖ < ε / 2 := by
    have hn := hquot.norm
    simp only [norm_zero] at hn
    exact hn.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [he] with n hn
  obtain ⟨w, hw, hnw⟩ := Submodule.Quotient.norm_mk_lt (F.mkQL (u n))
    (by linarith : (0 : ℝ) < ε / 2)
  refine ⟨u n - w, ?_, ?_⟩
  · apply (Submodule.Quotient.mk_eq_zero F).mp
    change F.mkQ (u n - w) = 0
    rw [map_sub]
    change F.mkQL (u n) - Submodule.Quotient.mk w = 0
    rw [hw, sub_self]
  · simpa only [sub_sub_cancel] using hnw.trans_le (by linarith)

/-- The elementary consequence of positivity of the *actual* inf-sup-inf modulus. -/
lemma oneSided_pos_subspace (N : Seminorm ℝ X) {t : ℝ}
    (hδ : 0 < oneSidedModulus X N t) {x : X} (hx : N x = 1) :
    ∃ F ∈ CofiniteSubspaces X, ∀ y ∈ F, N y = 1 →
      1 + oneSidedModulus X N t / 2 ≤ N (x + t • y) := by
  let directions (F : Submodule ℝ X) :=
    {b : ℝ | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}
  let centers := {r : ℝ | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}}}
  have hbelow : BddBelow centers := by
    by_contra h
    have hz := Real.sInf_of_not_bddBelow h
    change oneSidedModulus X N t = 0 at hz
    linarith
  have hcenter : oneSidedModulus X N t ≤
      sSup {a | ∃ F ∈ CofiniteSubspaces X, a = sInf (directions F)} :=
    csInf_le hbelow ⟨x, hx, rfl⟩
  have hnonempty : {a | ∃ F ∈ CofiniteSubspaces X, a = sInf (directions F)}.Nonempty := by
    refine ⟨_, ⊤, ?_, rfl⟩
    exact ⟨isClosed_univ, inferInstance⟩
  obtain ⟨a, ⟨F, hF, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hnonempty
    (lt_of_lt_of_le (by linarith : oneSidedModulus X N t / 2 < oneSidedModulus X N t)
      hcenter)
  refine ⟨F, hF, ?_⟩
  intro y hy hNy
  have hd : BddBelow (directions F) := by
    refine ⟨-1, ?_⟩
    rintro b ⟨z, hz, hNz, rfl⟩
    linarith [apply_nonneg N (x + t • z)]
  have hle := csInf_le hd (show N (x + t • y) - 1 ∈ directions F from ⟨y, hy, hNy, rfl⟩)
  linarith

end AbstractObstruction
end IndependentProducts

namespace IndependentProducts
section RadialGrowth
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma seminorm_normalize (N : Seminorm ℝ X) {x : X} (hx : 0 < N x) :
    N ((N x)⁻¹ • x) = 1 := by
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
  exact inv_mul_cancel₀ hx.ne'

/-- Convexity extends a positive one-sided gain from one radius to every larger radius. -/
lemma seminorm_radial_growth (N : Seminorm ℝ X) {x w : X} (hx : N x = 1)
    {t r γ : ℝ} (ht : 0 < t) (htr : t ≤ r) (hγ : 0 ≤ γ)
    (hg : 1 + γ ≤ N (x + t • w)) : 1 + γ ≤ N (x + r • w) := by
  have hr : 0 < r := ht.trans_le htr
  have hq : 0 < t / r := div_pos ht hr
  have hq1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  have hcomb : (t / r) • (x + r • w) + (1 - t / r) • x = x + t • w := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hr.ne']
    module
  have hh := map_add_le_add N ((t / r) • (x + r • w)) ((1 - t / r) • x)
  rw [hcomb, map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hq, abs_of_nonneg (sub_nonneg.mpr hq1), hx] at hh
  have hm := mul_nonneg (sub_nonneg.mpr hq1) hγ
  have : (t / r) * (1 + γ) ≤ (t / r) * N (x + r • w) := by nlinarith
  exact (mul_le_mul_iff_right₀ hq).mp this

lemma seminorm_unit_subspace_growth (N : Seminorm ℝ X) {x : X} (hx : N x = 1)
    (F : Submodule ℝ X) {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (hg : ∀ w ∈ F, N w = 1 → 1 + γ ≤ N (x + t • w))
    {z : X} (hz : z ∈ F) (hNz : t ≤ N z) : 1 + γ ≤ N (x + z) := by
  have hzp : 0 < N z := ht.trans_le hNz
  have hw := hg ((N z)⁻¹ • z) (F.smul_mem _ hz) (seminorm_normalize N hzp)
  have hr := seminorm_radial_growth N hx ht hNz hγ hw
  simpa only [smul_smul, mul_inv_cancel₀ hzp.ne', one_smul] using hr

lemma oneSided_pos_local_growth (N : Seminorm ℝ X) {t : ℝ} (ht : 0 < t)
    (hδ : 0 < oneSidedModulus X N t) {x : X} (hx : 0 < N x) :
    ∃ F ∈ CofiniteSubspaces X, ∀ z ∈ F, t * N x ≤ N z →
      (1 + oneSidedModulus X N t / 2) * N x ≤ N (x + z) := by
  obtain ⟨F, hF, hg⟩ := oneSided_pos_subspace N hδ (seminorm_normalize N hx)
  refine ⟨F, hF, ?_⟩
  intro z hz hNz
  have hnz' : t ≤ N ((N x)⁻¹ • z) := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
    exact (le_inv_mul_iff₀ hx).mpr (by simpa [mul_comm] using hNz)
  have hh := seminorm_unit_subspace_growth N (seminorm_normalize N hx) F ht
    (by linarith : 0 ≤ oneSidedModulus X N t / 2) hg (F.smul_mem (N x)⁻¹ hz) hnz'
  have hm := mul_le_mul_of_nonneg_right hh hx.le
  rw [← smul_add, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)] at hm
  simpa only [mul_assoc, mul_left_comm (N x)⁻¹, inv_mul_cancel₀ hx.ne', mul_one] using hm

end RadialGrowth
end IndependentProducts

namespace IndependentProducts
section TreeObstruction
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma not_finiteDimensional_of_weaklyNull_fixed_norm {u : ℕ → X}
    (hu : WeaklyNull u) {ρ : ℝ} (hρ : 0 < ρ) (hsize : ∀ n, ‖u n‖ = ρ) :
    ¬ FiniteDimensional ℝ X := by
  intro hfin
  let := hfin
  have hn := (weaklyNull_tendsto_finiteDimensional hu).norm
  simp only [norm_zero] at hn
  obtain ⟨n, hn⟩ := (hn.eventually (gt_mem_nhds hρ)).exists
  simp only [hsize n, lt_self_iff_false] at hn

/-- The complete deterministic branch-growth obstruction. Its hypotheses concern the tree,
not the existence or nonexistence of any renorming. -/
theorem bounded_tree_no_equivalent_auc (P : Vertex → X) (hP : ∀ v, ‖P v‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsize : ∀ v n, ‖P (child v n) - P v‖ = ρ)
    (hweak : ∀ v, WeaklyNull (fun n => P (child v n) - P v)) :
    ∀ N : Seminorm ℝ X, IsEquivalentNorm X N → ¬ IsAUC X N := by
  intro N hN hauc
  obtain ⟨a, b, ha, hab, hbound⟩ := hN
  have hb : 0 < b := ha.trans_le hab
  have hPa : ∀ v, a ≤ N (P v) := fun v => by
    simpa only [hP, mul_one] using (hbound (P v)).1
  have hPb : ∀ v, N (P v) ≤ b := fun v => by
    simpa only [hP, mul_one] using (hbound (P v)).2
  let t : ℝ := a * ρ / (2 * b)
  have ht : 0 < t := div_pos (mul_pos ha hρ) (by positivity)
  let δ := oneSidedModulus X N t
  have hδ : 0 < δ := hauc t ht
  have hstep : ∀ v, ∃ n, (1 + δ / 4) * N (P v) ≤ N (P (child v n)) := by
    intro v
    have hv : 0 < N (P v) := ha.trans_le (hPa v)
    obtain ⟨F, hF, hg⟩ := oneSided_pos_local_growth N ht hδ hv
    let ε := min (a * ρ / (2 * b)) (δ * N (P v) / (4 * b))
    have hε : 0 < ε := lt_min ht (div_pos (mul_pos hδ hv) (by positivity))
    obtain ⟨n, z, hz, herr⟩ := (weaklyNull_approx_cofinite (hweak v) F hF hε).exists
    let D := P (child v n) - P v
    have herr' : ‖D - z‖ < ε := herr
    have herr₁ : b * ‖D - z‖ < a * ρ / 2 := by
      calc
        b * ‖D - z‖ < b * (a * ρ / (2 * b)) :=
          mul_lt_mul_of_pos_left (herr'.trans_le (min_le_left _ _)) hb
        _ = a * ρ / 2 := by field_simp
    have herr₂ : b * ‖D - z‖ < δ * N (P v) / 4 := by
      calc
        b * ‖D - z‖ < b * (δ * N (P v) / (4 * b)) :=
          mul_lt_mul_of_pos_left (herr'.trans_le (min_le_right _ _)) hb
        _ = δ * N (P v) / 4 := by field_simp
    have hD : a * ρ ≤ N D := by simpa only [D, hsize] using (hbound D).1
    have hNz : a * ρ / 2 ≤ N z := by
      have hh : N D ≤ N (D - z) + N z := by
        simpa only [sub_add_cancel] using map_add_le_add N (D - z) z
      have he := (hbound (D - z)).2
      linarith
    have hrad : t * N (P v) ≤ N z := by
      calc
        t * N (P v) ≤ t * b := mul_le_mul_of_nonneg_left (hPb v) ht.le
        _ = a * ρ / 2 := by dsimp [t]; field_simp
        _ ≤ N z := hNz
    have hgain := hg z hz hrad
    have htri : N (P v + z) ≤ N (P (child v n)) + b * ‖D - z‖ := by
      calc
        N (P v + z) = N (P (child v n) + (z - D)) := by congr 1; dsimp [D]; abel
        _ ≤ N (P (child v n)) + N (z - D) := map_add_le_add N _ _
        _ ≤ N (P (child v n)) + b * ‖D - z‖ := by
          simpa only [norm_sub_rev z D] using add_le_add (le_refl (N (P (child v n)))) (hbound (z - D)).2
    refine ⟨n, ?_⟩
    change (1 + δ / 2) * N (P v) ≤ N (P v + z) at hgain
    nlinarith
  have hq : 1 < 1 + δ / 4 := by linarith
  have hiter : ∀ k : ℕ, ∃ v, a * (1 + δ / 4) ^ k ≤ N (P v) := by
    intro k
    induction k with
    | zero => exact ⟨[], by simpa using hPa []⟩
    | succ k ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨n, hn⟩ := hstep v
      refine ⟨child v n, ?_⟩
      calc
        a * (1 + δ / 4) ^ (k + 1) = (1 + δ / 4) * (a * (1 + δ / 4) ^ k) := by
          rw [pow_succ]; ring
        _ ≤ (1 + δ / 4) * N (P v) := mul_le_mul_of_nonneg_left hv (by linarith)
        _ ≤ N (P (child v n)) := hn
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (b / a) hq
  obtain ⟨v, hv⟩ := hiter k
  have hk' : b < a * (1 + δ / 4) ^ k := by
    have := (div_lt_iff₀ ha).mp hk
    nlinarith
  linarith [hPb v]

end TreeObstruction
end IndependentProducts

end

end OAI
