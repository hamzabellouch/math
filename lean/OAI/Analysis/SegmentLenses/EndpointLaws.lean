import OAI.Analysis.SegmentLenses.Stability

namespace OAI

/-!
# Independent endpoint laws and conditional recovery
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

namespace FiniteLaw
variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

theorem pooled_mean (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (f : Ω → ℝ) (g : Ω' → ℝ) :
    (μ.pooled ν).mean (Sum.elim f g) = (μ.mean f + ν.mean g) / 2 := by
  have h := μ.pooled_expect ν f g
  simp only [expect_scalar, smul_eq_mul] at h
  rw [h]
  ring

end FiniteLaw

section EndpointLaws
open scoped Classical
variable {V ΩP ΩM : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]
  [Fintype ΩP] [Fintype ΩM]




theorem endpoint_laws {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (_hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) {d : ℝ} (hd : 0 ≤ d) (_hd1 : d < 1)
    (hxn : 1 - d ≤ ‖x‖) (_hplus : ‖x + y‖ ≤ 1) (_hminus : ‖x - y‖ ≤ 1)
    (p : Test V) (hpH : p.coeff.support ⊆ H) (hp : ‖p‖ = 1) (hxp : x (p : Primal V) = ‖x‖)
    (μP : FiniteLaw ΩP) (μM : FiniteLaw ΩM)
    (AP : ΩP → Representation V) (AM : ΩM → Representation V)
    (hAP : ∀ ω, (AP ω).energy ≤ 1) (hAM : ∀ ω, (AM ω).energy ≤ 1)
    (_hKP : ∀ ω S, S ∈ (AP ω).family.sets → S ⊆ K)
    (_hKM : ∀ ω S, S ∈ (AM ω).family.sets → S ⊆ K)
    (hmeanP : μP.expect (fun ω => (AP ω).value) = head K (x + y))
    (hmeanM : μM.expect (fun ω => (AM ω).value) = head K (x - y)) :
    let mP := fun g : K.filter (Gate H) => μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|)
    let mM := fun g : K.filter (Gate H) => μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|)
    let m := fun g => (mP g + mM g) / 2
    (lawSlack μP AP p + lawError μP AP p ≤ 4 * d) ∧
    (lawSlack μM AM p + lawError μM AM p ≤ 4 * d) ∧
    μP.mean (fun ω => ‖(AP ω).value - ((AP ω).family.replacement p.coeff).value‖) ≤ 2 * Real.sqrt d ∧
    μM.mean (fun ω => ‖(AM ω).value - ((AM ω).family.replacement p.coeff).value‖) ≤ 2 * Real.sqrt d ∧
    (∀ g, 0 ≤ mP g ∧ 0 ≤ mM g ∧ mP g ≤ 2 * m g ∧ mM g ≤ 2 * m g) ∧
    Real.sqrt (∑ g, m g ^ 2) ≤ Real.sqrt (6 * d) := by
  classical
  dsimp only
  let μ := μP.pooled μM
  let A := Sum.elim AP AM
  have hA : ∀ ω, (A ω).energy ≤ 1 := by intro ω; cases ω with | inl ω => exact hAP ω | inr ω => exact hAM ω
  have hmean : μ.expect (fun ω => (A ω).value) = x := by
    have he : (fun ω => (A ω).value) = Sum.elim (fun ω => (AP ω).value) (fun ω => (AM ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he, μP.pooled_expect μM, hmeanP, hmeanM]
    change (1/2 : ℝ) • headLinear K (x + y) + (1/2 : ℝ) • headLinear K (x - y) = x
    rw [map_add, map_sub, headLinear_apply, head_eq_of_subset hHK x hx]
    module
  have hdef : lawDeficit μ A p = 1 - ‖x‖ := by rw [lawDeficit, hmean, hxp]
  have hdefsum : lawDeficit μP AP p + lawDeficit μM AM p = 2 * (1 - ‖x‖) := by
    have he : μ.mean (fun ω => (A ω).value (p : Primal V)) =
        (μP.mean (fun ω => (AP ω).value (p : Primal V)) +
          μM.mean (fun ω => (AM ω).value (p : Primal V))) / 2 := by
      have hf : (fun ω => (A ω).value (p : Primal V)) =
          Sum.elim (fun ω => (AP ω).value (p : Primal V)) (fun ω => (AM ω).value (p : Primal V)) := by
        funext ω; cases ω <;> rfl
      rw [hf]
      exact μP.pooled_mean μM _ _
    have he' : μ.mean (fun ω => (A ω).value (p : Primal V)) = ‖x‖ := by
      rw [← μ.expect_apply, hmean, hxp]
    simp only [lawDeficit, FiniteLaw.expect_apply]
    linarith
  have hdP := lawDeficit_nonneg μP AP hAP p hp.le
  have hdM := lawDeficit_nonneg μM AM hAM p hp.le
  have hbP : lawDeficit μP AP p ≤ 2 * d := by linarith
  have hbM : lawDeficit μM AM p ≤ 2 * d := by linarith
  have hrootP : Real.sqrt (2 * lawDeficit μP AP p) ≤ 2 * Real.sqrt d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hd]
  have hrootM : Real.sqrt (2 * lawDeficit μM AM p) ≤ 2 * Real.sqrt d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hd]
  refine ⟨?_, ?_, (mean_error_norm_le μP AP hAP p hp.le).trans hrootP,
    (mean_error_norm_le μM AM hAM p hp.le).trans hrootM, ?_, ?_⟩
  · have h := (unit_law_budget μP AP hAP p hp.le).2.2
    linarith
  · have h := (unit_law_budget μM AM hAM p hp.le).2.2
    linarith
  · intro g
    have hpos := μP.mean_nonneg (fun ω => abs_nonneg ((AP ω).family.boundary p.coeff g.val))
    have hneg := μM.mean_nonneg (fun ω => abs_nonneg ((AM ω).family.boundary p.coeff g.val))
    exact ⟨hpos, hneg, by linarith, by linarith⟩
  · apply Real.sqrt_le_sqrt
    have h := law_absolute_mass_bound hH (K.filter (Gate H))
      (fun g hg => (Finset.mem_filter.mp hg).2) μ A hA p hp.le hpH
    have ht : tail H x = 0 := by simp only [tail, hx, sub_self]
    rw [hmean, ht, norm_zero, zero_add, hdef] at h
    have hδ : 0 ≤ 1 - ‖x‖ := hdef ▸ lawDeficit_nonneg μ A hA p hp.le
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hδ)] at h
    have he : ∀ g : K.filter (Gate H), μ.mean (fun ω => |(A ω).family.boundary p.coeff g.val|) =
        (μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|) +
          μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|)) / 2 := by
      intro g
      have hf : (fun ω => |(A ω).family.boundary p.coeff g.val|) =
          Sum.elim (fun ω => |(AP ω).family.boundary p.coeff g.val|)
            (fun ω => |(AM ω).family.boundary p.coeff g.val|) := by
        funext ω; cases ω <;> rfl
      rw [hf]
      exact μP.pooled_mean μM _ _
    simp_rw [he] at h
    linarith

end EndpointLaws

section SymmetricStability
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

theorem finite_symmetric_tail {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (x y : FullDual V) (hx : head K x = x) (hy : head K y = y)
    (hpp : ‖x + y‖ ≤ 1) (hmm : ‖x - y‖ ≤ 1)
    (p : Test V) (hp : ‖p‖ ≤ 1) (hpH : p.coeff.support ⊆ H) :
    ‖tail H y‖ ≤ ‖tail H x‖ + (2 + 2 * Real.sqrt 2) * Real.sqrt (1 - x (p : Primal V)) := by
  have hpK : head K (x + y) = x + y := by
    change headLinear K (x + y) = _
    simp only [map_add, headLinear_apply, hx, hy]
  have hmK : head K (x - y) = x - y := by
    change headLinear K (x - y) = _
    simp only [map_sub, headLinear_apply, hx, hy]
  obtain ⟨μp, Ap, hpE, hpSupp, hpMean⟩ := exists_atomic_law hK (x + y) hpK (by norm_num : (0:ℝ)<1) hpp
  obtain ⟨μm, Am, hmE, hmSupp, hmMean⟩ := exists_atomic_law hK (x - y) hmK (by norm_num : (0:ℝ)<1) hmm
  let μ := μp.pooled μm
  let A := Sum.elim Ap Am
  let σ : Option (LocalFamily K) ⊕ Option (LocalFamily K) → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hσ : ∀ ω, |σ ω| ≤ 1 := by intro ω; cases ω <;> norm_num [σ]
  have henergy : ∀ ω, (A ω).energy ≤ 1 := by
    intro ω
    cases ω with
    | inl ω => simpa only [A, Sum.elim_inl, one_pow] using hpE ω
    | inr ω => simpa only [A, Sum.elim_inr, one_pow] using hmE ω
  have hsupp : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K := by
    intro ω
    cases ω with
    | inl ω => exact hpSupp ω
    | inr ω => exact hmSupp ω
  have hmean : μ.expect (fun ω => (A ω).value) = x := by
    have he : (fun ω => (A ω).value) = Sum.elim (fun ω => (Ap ω).value) (fun ω => (Am ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he, μp.pooled_expect μm, hpMean, hmMean]
    module
  have hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y := by
    have he : (fun ω => σ ω • (A ω).value) = Sum.elim
        (fun ω => (1:ℝ) • (Ap ω).value) (fun ω => (-1:ℝ) • (Am ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he, μp.pooled_expect μm, μp.expect_smul, μm.expect_smul, hpMean, hmMean]
    module
  have hdef : lawDeficit μ A p = 1 - x (p : Primal V) := by rw [lawDeficit, hmean]
  have hδ : 0 ≤ 1 - x (p : Primal V) := hdef ▸ lawDeficit_nonneg μ A henergy p hp
  have h := represented_bounded_multiplier hH μ A henergy hsupp σ hσ p hp hpH
  rw [hsigned, hmean, hdef] at h
  exact h.trans (stable_radical_linear (norm_nonneg _) hδ)



theorem symmetric_tail_bound {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hpp : ‖x + y‖ ≤ 1) (hmm : ‖x - y‖ ≤ 1)
    (p : Test V) (hp : ‖p‖ ≤ 1) (hpH : p.coeff.support ⊆ H) :
    ‖tail H y‖ ≤ ‖tail H x‖ + (2 + 2 * Real.sqrt 2) * Real.sqrt (1 - x (p : Primal V)) := by
  apply dual_norm_le _ (by positivity)
  intro u
  let K := ancestralHull (H ∪ u.coeff.support)
  have hK := ancestralHull_ancestral (H ∪ u.coeff.support)
  have hHK : H ⊆ K := Finset.subset_union_left.trans (subset_ancestralHull _)
  have huK : u.coeff.support ⊆ K := Finset.subset_union_right.trans (subset_ancestralHull _)
  have hppK : ‖head K x + head K y‖ ≤ 1 := by
    have he : head K x + head K y = head K (x + y) := (map_add (headLinear K) x y).symm
    rw [he]
    exact (norm_head_le hK _).trans hpp
  have hmmK : ‖head K x - head K y‖ ≤ 1 := by
    have he : head K x - head K y = head K (x - y) := (map_sub (headLinear K) x y).symm
    rw [he]
    exact (norm_head_le hK _).trans hmm
  have hη : ‖tail H (head K x)‖ ≤ ‖tail H x‖ := by rw [← head_tail_commute]; exact norm_head_le hK _
  have h := finite_symmetric_tail hH hK (head K x) (head K y) (head_head _ _) (head_head _ _)
    hppK hmmK p hp hpH
  rw [head_pairing_of_support K x p (hpH.trans hHK)] at h
  have hb := h.trans (add_le_add hη le_rfl)
  rw [← tail_head_pairing H K y u huK]
  have hop := (tail H (head K y)).le_opNorm (u : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at hop
  exact hop.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg u))

end SymmetricStability



end SegmentLenses

end

end OAI
