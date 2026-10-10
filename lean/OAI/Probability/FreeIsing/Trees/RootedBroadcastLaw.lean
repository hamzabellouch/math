import OAI.Probability.FreeIsing.Trees.Cardinality
import OAI.Probability.FreeIsing.Trees.RootedBroadcast
import OAI.Probability.FreeIsing.Trees.SpinEncoding

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

def root (d : ℕ) : TreeVertex d := ⟨[], List.isChain_nil⟩

@[simp] lemma root_val (d : ℕ) : (root d).val = [] := rfl

lemma eq_root_iff {d : ℕ} (v : TreeVertex d) : v = root d ↔ v.val = [] := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact h

def eraseRootNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then IsingSpin.pos else noise v

lemma ofNoise_root_decomposition {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v : TreeVertex d) :
    ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have hvroot : v = root d := (eq_root_iff v).mpr hnil
        subst v
        simp [root, ofNoise_root, eraseRootNoise]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise v hnil, ofNoise_nonroot (eraseRootNoise noise) v hnil,
          eraseRootNoise, ite_eq_right hnil, ih _ hlt (parent v) rfl]
        rw [← spinMul_assoc, spinMul_comm (noise v) (noise (root d)), spinMul_assoc]
  exact h _ v rfl

abbrev NonrootVertex (d : ℕ) := {v : TreeVertex d // v ≠ root d}

def nonrootNoise {d : ℕ} (theta : ℝ) (Y : NonrootVertex d → ℝ) (v : TreeVertex d) : IsingSpin :=
  if hv : v = root d then IsingSpin.pos else edgeNoise theta (Y ⟨v, hv⟩)

lemma measurable_nonrootNoise (d : ℕ) (theta : ℝ) : Measurable (@nonrootNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = root d
  · simpa only [nonrootNoise, dite_eq_left hv] using
      (measurable_const : Measurable (fun _ : NonrootVertex d → ℝ => IsingSpin.pos))
  · simpa only [nonrootNoise, dite_eq_right hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp (measurable_pi_apply (X := fun _ : NonrootVertex d => ℝ) ⟨v, hv⟩)

def rootlessFactor {d : ℕ} (theta : ℝ) (Y : NonrootVertex d → ℝ) : TreeVertex d → IsingSpin :=
  ofNoise (nonrootNoise theta Y)

lemma measurable_rootlessFactor (d : ℕ) (theta : ℝ) : Measurable (@rootlessFactor d theta) :=
  (measurable_ofNoise d).comp (measurable_nonrootNoise d theta)

lemma factor_root_decomposition {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v : TreeVertex d) :
    factor theta U v = spinMul (fairSpin (U (root d)))
      (rootlessFactor theta (fun w : NonrootVertex d => U w.val) v) := by
  rw [factor, ofNoise_root_decomposition]
  have heq : eraseRootNoise (inputNoise theta U) =
      nonrootNoise theta (fun w : NonrootVertex d => U w.val) := by
    funext w
    by_cases hw : w = root d
    · subst w
      simp [eraseRootNoise, nonrootNoise]
    · have hnil : w.val ≠ [] := fun h => hw ((eq_root_iff w).mpr h)
      simp [eraseRootNoise, inputNoise, nonrootNoise, hw, hnil]
  rw [heq]
  rfl

lemma factor_edge_agreement {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    {u v : TreeVertex d} (huv : treeAdj u v) (hlt : u.val.length < v.val.length) :
    spinAgreementCode (factor theta U u) (factor theta U v) = edgeNoise theta (U v) := by
  have hp : parent v = u := treeAdj_parent_of_length_lt huv hlt
  have hnil : v.val ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlt
    omega
  change spinMul (factor theta U u) (factor theta U v) = _
  change spinMul (ofNoise (inputNoise theta U) u) (ofNoise (inputNoise theta U) v) = _
  rw [ofNoise_nonroot _ v hnil, hp]
  simp only [inputNoise, ite_eq_right hnil]
  rw [spinMul_comm (edgeNoise theta (U v)), spinMul_cancel]

lemma factor_cylinder_event {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (eta : TreeVertex d → IsingSpin) :
    {U : TreeVertex d → ℝ | ∀ v ∈ D, factor theta U v = eta v} =
      {U | factor theta U r = eta r ∧ ∀ e ∈ inducedEdges D,
        edgeNoise theta (U e.2) = spinAgreementCode (eta e.1) (eta e.2)} := by
  classical
  ext U
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hD.spin_eq_on_iff_root_agreements hr]
  apply and_congr_right
  intro hroot
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have he' := (Finset.mem_filter.mp he).2
  rw [factor_edge_agreement theta U he'.1 he'.2]

def edgeVertex {d : ℕ} (D : Finset (TreeVertex d)) (e : inducedEdges D) : NonrootVertex d := by
  classical
  refine ⟨e.val.2, ?_⟩
  intro heq
  have hlt := (Finset.mem_filter.mp e.property).2.2
  rw [heq, root_val] at hlt
  simp only [List.length_nil] at hlt
  omega

lemma edgeVertex_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (edgeVertex D) := by
  intro a b hab
  apply Subtype.ext
  apply inducedEdges_snd_injOn D a.property b.property
  exact congrArg Subtype.val hab

lemma nonroot_edge_event_mass {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))
      {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
        spinAgreementCode (eta e.val.1) (eta e.val.2)} =
      ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  classical
  let A : Set ((e : inducedEdges D) → ℝ) := Set.pi Set.univ
    (fun e => edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)})
  have hA : MeasurableSet A := MeasurableSet.univ_pi
    (fun e => (measurable_edgeNoise theta) (measurableSet_singleton _))
  have hm : Measurable (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e)) := by
    fun_prop
  calc
    _ = (Measure.map (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e))
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) A := by
      rw [Measure.map_apply hm hA]
      congr 1
      ext Y
      simp [A, Set.mem_pi]
    _ = (Measure.infinitePi (fun _ : inducedEdges D => uniform01)) A := by
      rw [Measure.map_infinitePi_infinitePi_of_inj (edgeVertex_injective D)]
    _ = ∏ e : inducedEdges D, uniform01
        (edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)}) := by
      simpa only [A, Finset.coe_univ] using
        (Measure.infinitePi_pi (fun _ : inducedEdges D => uniform01)
          (s := Finset.univ) (fun e _ => (measurable_edgeNoise theta)
            (measurableSet_singleton (spinAgreementCode (eta e.val.1) (eta e.val.2)))))
    _ = _ := by
      simp only [edgeNoise_mass h0 h1, spinAgreementCode_eq_pos_iff]
      exact Finset.prod_coe_sort (inducedEdges D) (fun e : TreeVertex d × TreeVertex d =>
        ENNReal.ofReal ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

lemma freeCylinderWeight_eq_edge_product {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · norm_num [ENNReal.ofReal_div_of_pos]
  · intro e he
    split_ifs <;> linarith

lemma hasFreeIsingLaw_of_root_nonroot_joint {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (hjoint : ∀ r : TreeVertex d,
      (labelMeasure d).map (fun U => (factor theta U r, fun w : NonrootVertex d => U w.val)) =
        (uniform01.map fairSpin).prod (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) :
    HasFreeIsingLaw theta ((labelMeasure d).map (factor theta)) := by
  classical
  intro D hD eta
  obtain ⟨r, hr⟩ := hD.1
  let A : Set (NonrootVertex d → ℝ) :=
    {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
      spinAgreementCode (eta e.val.1) (eta e.val.2)}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact ((measurable_edgeNoise theta).comp (measurable_pi_apply (edgeVertex D e)))
      (measurableSet_singleton _)
  have hS : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U r, fun w : NonrootVertex d => U w.val)) := by
    exact ((measurable_pi_apply r).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun w => measurable_pi_apply w.val))
  rw [Measure.map_apply (measurable_factor d theta) hS]
  change (labelMeasure d) {U | ∀ v ∈ D, factor theta U v = eta v} = _
  rw [factor_cylinder_event theta D hD r hr eta]
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U r, fun w : NonrootVertex d => U w.val))) ({eta r} ×ˢ A) := by
      rw [Measure.map_apply hm ((measurableSet_singleton _).prod hA)]
      congr 1
      ext U
      simp [A, Set.mem_prod, edgeVertex]
    _ = ((uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) ({eta r} ×ˢ A) := by
      rw [hjoint r]
    _ = (uniform01.map fairSpin) {eta r} *
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A :=
      Measure.prod_prod _ _
    _ = (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
      rw [Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass]
      rw [show (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A = _ from
        nonroot_edge_event_mass h0 h1 D eta]
    _ = freeCylinderWeight theta D eta := (freeCylinderWeight_eq_edge_product h0 h1 D eta).symm

end RootedBroadcast
end Problem367

end

end OAI
