import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.FreeMoments
import OAI.Analysis.Commutator.FreeWordDecomposition

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

abbrev Letter := FreeMoments.Letter S t.functional.toLinearMap

def wordVector (w : List (Letter t S)) : t.functional.GNS :=
  (t.functional.toPreGNS (word w) : t.functional.GNS)

lemma inner_wordVector (w z : List (Letter t S)) :
    inner ℂ (wordVector t S w) (wordVector t S z) =
      t.functional (star (word w) * word z) := by
  rw [wordVector, wordVector, Completion.inner_coe]
  rfl

lemma mul_wordVector (a : A) (w : List (Letter t S)) :
    t.functional.gnsStarAlgHom a (wordVector t S w) =
      (t.functional.toPreGNS (a * word w) : t.functional.GNS) := by
  simp [wordVector, PositiveLinearMap.gnsStarAlgHom]

def CanPrepend (i : ι) (w : List (Letter t S)) : Prop :=
  ∀ a ∈ w.head?, i ≠ a.color

lemma reduced_prepend {i : ι} {w : List (Letter t S)} (hw : Reduced w)
    (hi : CanPrepend t S i w) (a : Letter t S) (ha : a.color = i) :
    Reduced (a :: w) := by
  cases w with
  | nil => exact reduced_singleton a
  | cons b w =>
    exact List.isChain_cons_cons.mpr ⟨by simpa [ha] using hi b (by simp), hw⟩

lemma colors_ne_prepend {i : ι} {w z : List (Letter t S)}
    (hi : CanPrepend t S i w) (a : Letter t S) (ha : a.color = i) :
    w.map FreeMoments.Letter.color ≠ (a :: z).map FreeMoments.Letter.color := by
  cases w with
  | nil => simp
  | cons b w =>
    intro h
    have hc : b.color = a.color := (List.cons.inj h).1
    exact hi b (by simp) (ha ▸ hc.symm)

include hfree in
lemma centered_middle_zero {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    (a : Letter t S) (ha : a.color = i) :
    t.functional (star (word w) * (a.val * word z)) = 0 := by
  change t.functional.toLinearMap (star (word w) * word (a :: z)) = 0
  rw [gram_word (fun a => map_star t.functional a) t.normalized hfree _ _ hw
    (reduced_prepend t S hz hiz a ha)]
  exact gram_zero_of_colors_ne _ _ (colors_ne_prepend t S hiw a ha)

include hfree in
lemma middle_factor {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    {a : A} (ha : a ∈ S i) :
    t.functional (star (word w) * (a * word z)) =
      t.functional a * t.functional (star (word w) * word z) := by
  let a0 : Letter t S :=
    ⟨i, a - t.functional a • (1 : A),
      sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S i))),
      by simp [map_sub, map_smul, t.normalized]⟩
  have h := centered_middle_zero t S hfree hw hz hiw hiz a0 rfl
  change t.functional (star (word w) *
    ((a - t.functional a • (1 : A)) * word z)) = 0 at h
  simp only [sub_mul, smul_mul_assoc, one_mul, mul_sub, mul_smul_comm,
    map_sub, map_smul] at h
  exact sub_eq_zero.mp h

include hfree in
lemma inner_mul_wordVector {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    {a : A} (ha : a ∈ S i) :
    inner ℂ (t.functional.gnsStarAlgHom a (wordVector t S w))
      (t.functional.gnsStarAlgHom a (wordVector t S z)) =
      t.functional (star a * a) * inner ℂ (wordVector t S w) (wordVector t S z) := by
  rw [mul_wordVector, mul_wordVector, Completion.inner_coe, inner_wordVector]
  change t.functional (star (a * word w) * (a * word z)) = _
  simpa only [star_mul, mul_assoc] using
    middle_factor t S hfree hw hz hiw hiz (mul_mem (star_mem ha) ha)

def tailSpan (i : ι) : Submodule ℂ t.functional.GNS :=
  Submodule.span ℂ {x | ∃ w : List (Letter t S),
    Reduced w ∧ CanPrepend t S i w ∧ wordVector t S w = x}

def tailSpace (i : ι) : Submodule ℂ t.functional.GNS :=
  (tailSpan t S i).topologicalClosure

instance (i : ι) : IsClosed ((tailSpace t S i : Submodule ℂ t.functional.GNS) : Set t.functional.GNS) :=
  (tailSpan t S i).isClosed_topologicalClosure

include hfree in
lemma inner_mul_tailSpan (i : ι) {a : A} (ha : a ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpan t S i) (hy : y ∈ tailSpan t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, hiw, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, hiz, rfl⟩ := hy
      exact inner_mul_wordVector t S hfree hw hz hiw hiz ha
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz, mul_add]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]; ring
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz, mul_add]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]; ring

include hfree in
lemma inner_mul_tailSpace (i : ι) {a : A} (ha : a ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpace t S i) (hy : y ∈ tailSpace t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y := by
  apply closure_minimal (s := (tailSpan t S i : Set _))
    (t := {x | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y}) ?_ ?_ hx
  · intro x hx
    apply closure_minimal (s := (tailSpan t S i : Set _))
      (t := {y | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
        t.functional (star a * a) * inner ℂ x y}) ?_ ?_ hy
    · intro y hy
      exact inner_mul_tailSpan t S hfree i ha hx hy
    · apply isClosed_eq <;> fun_prop
  · apply isClosed_eq <;> fun_prop

include hfree in
lemma norm_mul_tailSpace (i : ι) {a : A} (ha : a ∈ S i)
    {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    ‖t.functional.gnsStarAlgHom a x‖ = ‖t.functional.toPreGNS a‖ * ‖x‖ := by
  have h := inner_mul_tailSpace t S hfree i ha hx hx
  have hn := t.functional.preGNS_norm_sq (t.functional.toPreGNS a)
  change (‖t.functional.toPreGNS a‖ : ℂ) ^ 2 = t.functional (star a * a) at hn
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← hn] at h
  have hr : ‖t.functional.gnsStarAlgHom a x‖ ^ 2 =
      ‖t.functional.toPreGNS a‖ ^ 2 * ‖x‖ ^ 2 := by
    have hr := congrArg Complex.re h
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re] using hr
  nlinarith [norm_nonneg (t.functional.gnsStarAlgHom a x),
    mul_nonneg (norm_nonneg (t.functional.toPreGNS a)) (norm_nonneg x)]

def Starts (i : ι) (w : List (Letter t S)) : Prop :=
  ∃ a z, w = a :: z ∧ a.color = i

def headSpan (i : ι) : Submodule ℂ t.functional.GNS :=
  Submodule.span ℂ {x | ∃ w : List (Letter t S),
    Reduced w ∧ Starts t S i w ∧ wordVector t S w = x}

def headSpace (i : ι) : Submodule ℂ t.functional.GNS :=
  (headSpan t S i).topologicalClosure

instance (i : ι) : IsClosed ((headSpace t S i : Submodule ℂ t.functional.GNS) : Set t.functional.GNS) :=
  (headSpan t S i).isClosed_topologicalClosure

include hfree in
lemma headSpace_le_tailSpace_orthogonal (i : ι) :
    headSpace t S i ≤ (tailSpace t S i)ᗮ := by
  apply (headSpan t S i).topologicalClosure_minimal ?_ (Submodule.isClosed_orthogonal _)
  rw [tailSpace, Submodule.orthogonal_closure]
  apply Submodule.span_le.mpr
  rintro x ⟨z, hz, ⟨a, z, rfl, ha⟩, rfl⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, hiw, rfl⟩ := hy
    rw [inner_wordVector]
    change t.functional.toLinearMap (star (word w) * word (a :: z)) = 0
    rw [gram_word (fun a => map_star t.functional a) t.normalized hfree _ _ hw hz]
    exact gram_zero_of_colors_ne _ _ (colors_ne_prepend t S hiw a ha)
  | zero => simp
  | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
  | smul c y _ hy => simp [inner_smul_left, hy]

lemma headSpace_le_other_tailSpace {i j : ι} (hij : i ≠ j) :
    headSpace t S i ≤ tailSpace t S j := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, ⟨a, z, rfl, ha⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨a :: z, hw, ?_, rfl⟩
  intro b hb
  have hb' : b = a := (by simpa using hb : a = b).symm
  subst b
  simpa [ha] using hij.symm

lemma creation_mem_headSpan (i : ι) {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a = 0) {x : t.functional.GNS} (hx : x ∈ tailSpan t S i) :
    t.functional.gnsStarAlgHom a x ∈ headSpan t S i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, hiw, rfl⟩ := hx
    let b : Letter t S := ⟨i, a, ha, ha0⟩
    apply Submodule.subset_span
    refine ⟨b :: w, reduced_prepend t S hw hiw b rfl, ⟨b, w, rfl, rfl⟩, ?_⟩
    rw [mul_wordVector]
    rfl
  | zero => simp
  | add x y _ _ hx hy => simpa using (headSpan t S i).add_mem hx hy
  | smul c x _ hx => simpa using (headSpan t S i).smul_mem c hx

lemma creation_mem_headSpace (i : ι) {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a = 0) {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    t.functional.gnsStarAlgHom a x ∈ headSpace t S i := by
  apply closure_minimal (s := (tailSpan t S i : Set _))
    (t := {x | t.functional.gnsStarAlgHom a x ∈ headSpace t S i}) ?_ ?_ hx
  · intro x hx
    exact (headSpan t S i).le_topologicalClosure
      (creation_mem_headSpan t S i ha ha0 hx)
  · exact (headSpan t S i).isClosed_topologicalClosure.preimage
      (t.functional.gnsStarAlgHom a).continuous

lemma wordVector_mem_head_sup_tail (i : ι) (w : List (Letter t S)) (hw : Reduced w) :
    wordVector t S w ∈ headSpace t S i ⊔ tailSpace t S i := by
  classical
  cases w with
  | nil =>
    apply Submodule.mem_sup_right
    apply (tailSpan t S i).le_topologicalClosure
    exact Submodule.subset_span ⟨[], hw, by simp [CanPrepend], rfl⟩
  | cons a w =>
    by_cases hi : a.color = i
    · apply Submodule.mem_sup_left
      apply (headSpan t S i).le_topologicalClosure
      exact Submodule.subset_span ⟨a :: w, hw, ⟨a, w, rfl, hi⟩, rfl⟩
    · apply Submodule.mem_sup_right
      apply (tailSpan t S i).le_topologicalClosure
      exact Submodule.subset_span ⟨a :: w, hw, by simpa [CanPrepend] using Ne.symm hi, rfl⟩

lemma generated_mem_head_sup_tail (i : ι) {a : A} (ha : a ∈ iSup S) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ headSpace t S i ⊔ tailSpace t S i := by
  have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
    change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
    rw [FreeMoments.reducedAlgebra_eq_iSup]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, hw, rfl⟩ := ha
    exact wordVector_mem_head_sup_tail t S i w hw
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using
      (headSpace t S i ⊔ tailSpace t S i).add_mem ha hb
  | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using
      (headSpace t S i ⊔ tailSpace t S i).smul_mem c ha

lemma total_head_sup_tail (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (headSpace t S i ⊔ tailSpace t S i).topologicalClosure = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using Completion.induction_on with
  | hp => exact (headSpace t S i ⊔ tailSpace t S i).isClosed_topologicalClosure
  | ih x =>
    let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
    have h := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
      (hgen (t.functional.ofPreGNS x)) ξ
    have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS x) ξ =
        (x : t.functional.GNS) := by
      simp [ξ, PositiveLinearMap.gnsStarAlgHom]
    rw [heq] at h
    apply Submodule.topologicalClosure_mono ?_ h
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using generated_mem_head_sup_tail t S i hb

include hfree in
lemma headSpace_eq_tailSpace_orthogonal (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    headSpace t S i = (tailSpace t S i)ᗮ := by
  apply le_antisymm (headSpace_le_tailSpace_orthogonal t S hfree i)
  intro x hx
  let P := headSpace t S i
  have hp : P.starProjection x ∈ P := P.starProjection_apply_mem x
  have hy : x - P.starProjection x ∈ Pᗮ ⊓ (tailSpace t S i)ᗮ :=
    ⟨P.sub_starProjection_mem_orthogonal x,
      (tailSpace t S i)ᗮ.sub_mem hx (headSpace_le_tailSpace_orthogonal t S hfree i hp)⟩
  have hbot : Pᗮ ⊓ (tailSpace t S i)ᗮ = ⊥ := by
    rw [Submodule.inf_orthogonal, ← Submodule.orthogonal_closure,
      total_head_sup_tail t S i hgen, Submodule.top_orthogonal_eq_bot]
  rw [hbot, Submodule.mem_bot] at hy
  rw [sub_eq_zero.mp hy]
  exact hp

end Kadison.FreeCreation
end

end OAI
