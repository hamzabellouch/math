import OAI.Analysis.MatrixScaling.Canonical
import OAI.Geometry.ComplexBundle.Frames
import OAI.Geometry.ComplexBundle.Sections

namespace OAI

noncomputable section

/-! Descent of canonical scaling and Hermitian bundle homomorphisms. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

section
variable {n d r : ℕ} {Y I : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]

theorem canonicalScaling_congr {T S : Fin n → Matrix (Fin r) (Fin d) ℂ}
    (he : T = S) (hT : Expanding T) (hS : Expanding S) :
    canonicalScaling T hT = canonicalScaling S hS := by
  cases he
  rfl

/-- Local normalization with harmless zero values outside a chart. -/
def chartScaling (H : VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I)
    (T : I → Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexp : ∀ a y, y ∈ H.baseSet a → Expanding (T a y)) (a : I) (y : Y) := by
  classical
  exact if hy : y ∈ H.baseSet a then canonicalScaling (T a y) (hexp a y hy) else 0

theorem continuousOn_chartScaling
    (H : VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I)
    (T : I → Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hT : ∀ a, ContinuousOn (T a) (H.baseSet a))
    (hexp : ∀ a y, y ∈ H.baseSet a → Expanding (T a y)) (a : I) :
    ContinuousOn (chartScaling H T hexp a) (H.baseSet a) := by
  classical
  let : LocallyCompactSpace (H.baseSet a) := (H.isOpen_baseSet a).locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := continuous_canonicalScaling_local (fun z : H.baseSet a => T a z.val)
    (continuousOn_iff_continuous_domRestrict.mp (hT a)) (fun z => hexp a z.val z.property)
  apply hc.congr
  intro z
  change canonicalScaling (T a z.val) _ = chartScaling H T hexp a z.val
  rw [chartScaling, dite_eq_left z.property]

theorem exists_scaled_core_section
    (H : VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I)
    (T : I → Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hT : ∀ a, ContinuousOn (T a) (H.baseSet a))
    (hexp : ∀ a y, y ∈ H.baseSet a → Expanding (T a y))
    (U : I → I → Y → Matrix (Fin d) (Fin d) ℂ)
    (V : I → I → Y → Matrix (Fin r) (Fin r) ℂ)
    (hunit : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      (U a b y)ᴴ * U a b y = 1 ∧ U a b y * (U a b y)ᴴ = 1 ∧
      (V a b y)ᴴ * V a b y = 1 ∧ V a b y * (V a b y)ᴴ = 1)
    (hcore : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b → ∀ M,
      H.coordChange a b y M = frameTuple M (U a b y) (V a b y))
    (hcompat : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      T b y = frameTuple (T a y) (U a b y) (V a b y)) :
    ∃ s : ∀ y, H.Fiber y,
      Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)) ∧
      ∀ a y, y ∈ H.baseSet a →
        let X := (H.localTriv a ⟨y,s y⟩).2
        (∑ i, (X i)ᴴ * X i) = 1 ∧
        ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - ∑ i, X i * (X i)ᴴ).PosSemidef := by
  classical
  have hg : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      H.coordChange a b y (chartScaling H T hexp a y) = chartScaling H T hexp b y := by
    intro a b y ha hb
    rw [chartScaling, dite_eq_left ha, chartScaling, dite_eq_left hb, hcore a b y ha hb]
    obtain ⟨hu,hu',hv,hv'⟩ := hunit a b y ha hb
    have ht := hcompat a b y ha hb
    have he := canonicalScaling_frame (T a y) (U a b y) (V a b y) hu hu' hv hv'
      (hexp a y ha) (ht ▸ hexp b y hb)
    exact he.symm.trans (canonicalScaling_congr ht.symm _ _)
  obtain ⟨s,hs,he⟩ := glue_core_section H (chartScaling H T hexp)
    (continuousOn_chartScaling H T hT hexp) hg
  refine ⟨s,hs,?_⟩
  intro a y hy
  rw [he a y hy]
  simpa only [chartScaling, dite_eq_left hy] using canonicalScaling_relations (T a y) (hexp a y hy)

end

variable {n d r : ℕ}

def frameTupleLinear (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ) :
    (Fin n → Matrix (Fin r) (Fin d) ℂ) →ₗ[ℂ] (Fin n → Matrix (Fin r) (Fin d) ℂ) where
  toFun T := frameTuple T U V
  map_add' T S := by ext i; simp [frameTuple, Matrix.mul_add, Matrix.add_mul]
  map_smul' z T := by ext i; simp [frameTuple, Matrix.mul_smul, Matrix.smul_mul]

def frameTupleCLM (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ) :
    (Fin n → Matrix (Fin r) (Fin d) ℂ) →L[ℂ] (Fin n → Matrix (Fin r) (Fin d) ℂ) :=
  ⟨frameTupleLinear U V, (frameTupleLinear U V).continuous_of_finiteDimensional⟩

theorem frameTupleCLM_apply (U : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin r) (Fin r) ℂ) (T : Fin n → Matrix (Fin r) (Fin d) ℂ) :
    frameTupleCLM U V T = frameTuple T U V := rfl

theorem frameTuple_comp (U₁ U₂ : Matrix (Fin d) (Fin d) ℂ)
    (V₁ V₂ : Matrix (Fin r) (Fin r) ℂ) (T : Fin n → Matrix (Fin r) (Fin d) ℂ) :
    frameTuple (frameTuple T U₁ V₁) U₂ V₂ = frameTuple T (U₂ * U₁) (V₂ * V₁) := by
  funext i
  simp only [frameTuple, conjTranspose_mul, Matrix.mul_assoc]

theorem continuousOn_frameTupleCLM {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (U : Y → Matrix (Fin d) (Fin d) ℂ) (V : Y → Matrix (Fin r) (Fin r) ℂ)
    (hU : ContinuousOn U s) (hV : ContinuousOn V s) :
    ContinuousOn (fun y => frameTupleCLM (n := n) (U y) (V y)) s := by
  apply continuousOn_clm_apply.mpr
  intro T
  apply continuousOn_pi.mpr
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  have hu := continuousOn_iff_continuous_domRestrict.mp hU
  have hv := continuousOn_iff_continuous_domRestrict.mp hV
  exact (hv.matrix_mul continuous_const).matrix_mul hu.matrix_conjTranspose

/-- Construct the actual Hom-tuple vector bundle from transition matrices
and their verified cocycle. There is no bundle-realization hypothesis. -/
def matrixHomCore {Y I : Type*} [TopologicalSpace Y]
    (O : I → Set Y) (hO : ∀ i, IsOpen (O i)) (idx : Y → I) (hat : ∀ y, y ∈ O (idx y))
    (U : I → I → Y → Matrix (Fin d) (Fin d) ℂ)
    (V : I → I → Y → Matrix (Fin r) (Fin r) ℂ)
    (hUc : ∀ i j, ContinuousOn (U i j) (O i ∩ O j))
    (hVc : ∀ i j, ContinuousOn (V i j) (O i ∩ O j))
    (hUs : ∀ i y, y ∈ O i → U i i y = 1)
    (hVs : ∀ i y, y ∈ O i → V i i y = 1)
    (hUm : ∀ i j k y, y ∈ O i → y ∈ O j → y ∈ O k → U j k y * U i j y = U i k y)
    (hVm : ∀ i j k y, y ∈ O i → y ∈ O j → y ∈ O k → V j k y * V i j y = V i k y) :
    VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I where
  baseSet := O
  isOpen_baseSet := hO
  indexAt := idx
  mem_baseSet_at := hat
  coordChange i j y := frameTupleCLM (U i j y) (V i j y)
  coordChange_self i y hy T := by
    change frameTuple T (U i i y) (V i i y) = T
    rw [hUs i y hy, hVs i y hy]
    funext k
    simp [frameTuple]
  continuousOn_coordChange i j := continuousOn_frameTupleCLM _ _ (hUc i j) (hVc i j)
  coordChange_comp i j k y hy T := by
    simp only [frameTupleCLM_apply, frameTuple_comp, hUm i j k y hy.1.1 hy.1.2 hy.2,
      hVm i j k y hy.1.1 hy.1.2 hy.2]

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

def hermitianChartSet (a : Y) : Set Y :=
  (trivializationAt (Fin d → ℂ) E a).baseSet ∩ (trivializationAt (Fin r → ℂ) F a).baseSet

def hermitianSourceTransition (a b : Y) :=
  bundleUnitaryTransition (trivializationAt (Fin d → ℂ) E a) (trivializationAt (Fin d → ℂ) E b)

def hermitianTargetTransition (a b : Y) :=
  bundleUnitaryTransition (trivializationAt (Fin r → ℂ) F a) (trivializationAt (Fin r → ℂ) F b)

/-- The Hom-tuple core is constructed from ordinary Hermitian bundles.
The charts, orthonormalizations, transition matrices, and cocycle proofs
are derived here; no unitary core is an input. -/
def hermitianHomCore
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F)) :
    VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) Y :=
  matrixHomCore (hermitianChartSet (d := d) (r := r) (E := E) (F := F))
    (fun a => (trivializationAt (Fin d → ℂ) E a).open_baseSet.inter
      (trivializationAt (Fin r → ℂ) F a).open_baseSet)
    id (fun y => ⟨mem_baseSet_trivializationAt (Fin d → ℂ) E y,
      mem_baseSet_trivializationAt (Fin r → ℂ) F y⟩)
    (hermitianSourceTransition (d := d) (E := E)) (hermitianTargetTransition (r := r) (F := F))
    (fun _ _ => (continuousOn_bundleUnitaryTransition hE _ _).mono
      (fun _ h => ⟨h.1.1,h.2.1⟩))
    (fun _ _ => (continuousOn_bundleUnitaryTransition hF _ _).mono
      (fun _ h => ⟨h.1.2,h.2.2⟩))
    (fun _ y h => bundleUnitaryTransition_self _ y h.1)
    (fun _ y h => bundleUnitaryTransition_self _ y h.2)
    (fun _ _ _ y ha hb hc => bundleUnitaryTransition_comp _ _ _ y ha.1 hb.1 hc.1)
    (fun _ _ _ y ha hb hc => bundleUnitaryTransition_comp _ _ _ y ha.2 hb.2 hc.2)

theorem hermitianHomCore_coordChange
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F)) (a b y : Y)
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ) :
    (hermitianHomCore hE hF).coordChange a b y T =
      frameTuple T (hermitianSourceTransition (d := d) (E := E) a b y)
        (hermitianTargetTransition (r := r) (F := F) a b y) := rfl

theorem hermitianHomCore_unitary (a b y : Y)
    (ha : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (hb : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) b) :
    let U := hermitianSourceTransition (d := d) (E := E) a b y
    let V := hermitianTargetTransition (r := r) (F := F) a b y
    Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ Vᴴ * V = 1 ∧ V * Vᴴ = 1 := by
  obtain ⟨hu,hu'⟩ := bundleUnitaryTransition_unitary
    (trivializationAt (Fin d → ℂ) E a) (trivializationAt (Fin d → ℂ) E b) y ha.1 hb.1
  obtain ⟨hv,hv'⟩ := bundleUnitaryTransition_unitary
    (trivializationAt (Fin r → ℂ) F a) (trivializationAt (Fin r → ℂ) F b) y ha.2 hb.2
  exact ⟨hu,hu',hv,hv'⟩

end Kaplansky

end

end OAI
