import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistory
import OAI.Combinatorics.BalancedRyser.Selection.SelectionPostcheckTail

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Classical

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

def postcheckFailed (q : ℕ) (G : Input I V)
    (before : Option (State I V)) (draw : Option (Noise I V)) : Prop :=
  match before, draw with
  | some S, some r => ¬ Postcheck q G S r.2.1 r.2.2
  | _, _ => False

def postcheckEvent (q : ℕ) (G : Input I V) (t : ℕ) :
    Set (FiniteHistory.Path (Snapshot I V)) :=
  {ω | postcheckFailed q G (ω t).1 (ω (t + 1)).2}

theorem postcheckTail_nonneg (p : Parameters) (q : ℕ) (hP : 0 ≤ p.Pstar) :
    0 ≤ postcheckTail p q := by
  unfold postcheckTail postcheckMean
  have : 0 ≤ max (1 : ℝ) p.C := le_trans (by norm_num) (le_max_left _ _)
  positivity

theorem retained_postcheck_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (before : Option (State I V)) :
    (∑ draw, drawStepWeight p q t G before draw *
      (if postcheckFailed q G before draw then (1 : ℝ) else 0)) ≤
      ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q := by
  have hδ : 0 ≤ ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q :=
    mul_nonneg (by positivity) (postcheckTail_nonneg p q hP)
  cases before with
  | none => simpa [postcheckFailed] using hδ
  | some S =>
      by_cases hp : Precheck p q t G S
      · rw [sum_drawStepWeight_of_precheck p q t G S hp]
        calc
          _ = ∑ draw : Noise I V,
              if ¬ Postcheck q G S draw.2.1 draw.2.2 then noiseWeight p q G S draw else 0 := by
            apply Finset.sum_congr rfl
            intro draw _
            by_cases hpost : Postcheck q G S draw.2.1 draw.2.2 <;>
              simp [postcheckFailed, hpost]
          _ ≤ _ := postcheck_failure_mass_le p q t hq G hG S hp
      · simpa [drawStepWeight, hp, Fintype.sum_option, postcheckFailed] using hδ

theorem measurableSet_postcheckEvent (q : ℕ) (G : Input I V) (t : ℕ) :
    MeasurableSet (postcheckEvent q G t) := by
  let f : FiniteHistory.Prefix (Snapshot I V) t → Snapshot I V → ℝ := fun h out =>
    if postcheckFailed q G (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 out.2 then 1 else 0
  have hm := FiniteHistory.measurable_stepObservable t f
  have heq : postcheckEvent q G t = {ω | (0 : ℝ) < FiniteHistory.stepObservable t f ω} := by
    ext ω
    simp only [postcheckEvent, Set.mem_ofPred_eq, FiniteHistory.stepObservable, f, frestrictLe]
    split <;> simp_all
  rw [heq]
  exact measurableSet_lt measurable_const hm

theorem postcheckEvent_mass_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real (postcheckEvent q G t) ≤
      ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q := by
  let μ := snapshotPathLaw p q G
  let δ := ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q
  let f : FiniteHistory.Prefix (Snapshot I V) t → Option (Noise I V) → ℝ := fun h draw =>
    if postcheckFailed q G (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 draw then 1 else 0
  let X := FiniteHistory.stepObservable t (fun h out => f h out.2)
  have hce := condExp_retained_draw p q G t f
  have hbound : ∀ᵐ ω ∂μ, μ[X | snapshotFiltration t] ω ≤ δ := by
    filter_upwards [hce] with ω hω
    rw [hω]
    exact retained_postcheck_mean_le p q t hq hP G hG (ω t).1
  have hind : X = (postcheckEvent q G t).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rfl
  calc
    μ.real (postcheckEvent q G t) = ∫ ω, X ω ∂μ := by
      rw [hind, integral_indicator_const 1 (measurableSet_postcheckEvent q G t)]
      simp
    _ = ∫ ω, μ[X | snapshotFiltration t] ω ∂μ :=
      (integral_condExp (snapshotFiltration.le t)).symm
    _ ≤ ∫ _ω, δ ∂μ := integral_mono_ae integrable_condExp (integrable_const δ) hbound
    _ = δ := by simp [μ]

theorem postcheck_union_mass_le (p : Parameters) (q T : ℕ) (hq : 0 < q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real (⋃ t ∈ Finset.range T, postcheckEvent q G t) ≤
      (T : ℝ) * (((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q) := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, (snapshotPathLaw p q G).real (postcheckEvent q G t) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Finset.range T,
        ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q :=
      Finset.sum_le_sum (fun t _ => postcheckEvent_mass_le p q t hq hP G hG)
    _ = _ := by simp

theorem graph_card_vertices_le (p : Parameters) (q : ℕ)
    (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    Fintype.card V ≤ Fintype.card I * q := by
  have hpartition : Fintype.card V = ∑ i : I, (slotVertices G i).card := by
    simpa only [Finset.card_univ, slotVertices] using
      (Finset.card_eq_sum_card_fiberwise (f := G.slot)
        (s := Finset.univ) (t := Finset.univ) (by intro v _; exact Finset.mem_univ _))
  rw [hpartition]
  calc
    _ ≤ ∑ _i : I, q := Finset.sum_le_sum (fun i _ => (hG.2.2.1 i).2)
    _ = _ := by simp

theorem graph_time_test_count_le (p : Parameters) (q T : ℕ) (hq : 2 ≤ q)
    (hT : T ≤ 3 * q) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (T : ℝ) * ((Fintype.card I : ℝ) + Fintype.card V) ≤ 18 * (q : ℝ) ^ 3 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hn : (Fintype.card I : ℝ) ≤ 3 * q := by
    exact_mod_cast (show Fintype.card I ≤ 3 * q by rw [hG.1]; omega)
  have hv : (Fintype.card V : ℝ) ≤ (Fintype.card I : ℝ) * q := by
    exact_mod_cast graph_card_vertices_le p q G hG
  have hv' : (Fintype.card V : ℝ) ≤ 3 * (q : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  have hn' : (Fintype.card I : ℝ) ≤ 3 * (q : ℝ) ^ 2 := by nlinarith
  have ht : (T : ℝ) ≤ 3 * q := by exact_mod_cast hT
  calc
    _ ≤ (3 * q) * (6 * (q : ℝ) ^ 2) :=
      mul_le_mul ht (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

theorem postcheck_union_mass_le_source (p : Parameters) (q T : ℕ) (hq : 2 ≤ q)
    (hP : 0 ≤ p.Pstar) (hT : T ≤ 3 * q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real (⋃ t ∈ Finset.range T, postcheckEvent q G t) ≤
      18 * (q : ℝ) ^ 3 * postcheckTail p q := by
  apply (postcheck_union_mass_le p q T (by omega) hP G hG).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (graph_time_test_count_le p q T hq hT G hG)
    (postcheckTail_nonneg p q hP)

theorem main_postcheck_union_mass_le (p : Parameters) (q : ℕ) (hq : 2 ≤ q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real
      (⋃ t ∈ Finset.range (p.lastMainTime q (Fintype.card I)), postcheckEvent q G t) ≤
      18 * (q : ℝ) ^ 3 * postcheckTail p q := by
  apply postcheck_union_mass_le_source p q _ hq hP _ G hG
  exact (Nat.sub_le _ _).trans (by rw [hG.1]; omega)

theorem tendsto_source_postcheck_bound (p : Parameters) (hP : 0 ≤ p.Pstar) :
    Tendsto (fun q : ℕ => 18 * (q : ℝ) ^ 3 * postcheckTail p q)
      atTop (nhds 0) := by
  have hm : 0 ≤ postcheckMean p :=
    mul_nonneg hP (le_trans (by norm_num) (le_max_left (1 : ℝ) p.C))
  have h := (BernoulliTail.tendsto_post_step_abort_bound (postcheckMean p) hm).const_mul 18
  simpa only [postcheckTail, mul_zero, mul_assoc] using h

theorem tendsto_main_postcheck_failure (p : Parameters) (hP : 0 ≤ p.Pstar)
    (I V : ℕ → Type*) [∀ q, Fintype (I q)] [∀ q, Fintype (V q)]
    (G : (q : ℕ) → Input (I q) (V q))
    (hG : ∀ᶠ q : ℕ in atTop, GraphBounds (G q) q p.c p.C) :
    Tendsto (fun q : ℕ => (snapshotPathLaw p q (G q)).real
      (⋃ t ∈ Finset.range (p.lastMainTime q (Fintype.card (I q))),
        postcheckEvent q (G q) t)) atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    _ (tendsto_source_postcheck_bound p hP)
  filter_upwards [eventually_ge_atTop 2, hG] with q hq hg
  exact main_postcheck_union_mass_le p q hq hP (G q) hg

end Balanced.Selection.Process

end

end OAI
