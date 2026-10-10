import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.LocalUnitaryFrame
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Bilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

lemma skew (B : Bilinear E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v) (u v : E) :
    B (J u) v = -B u (J v) := by
  have h := hBJ u (J v)
  rw [hJ, map_neg] at h
  linarith

lemma orthogonal_J (B : Bilinear E) (J : E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v) (u : E) :
    B u (J u) = 0 := by
  have h := skew B J hJ hBJ u u
  rw [hB (J u) u] at h
  linarith

def normalize (B : Bilinear E) (u : E) : E := (Real.sqrt (B u u))⁻¹ • u

lemma normalize_unit (B : Bilinear E) (u : E) (h : 0 < B u u) :
    B (normalize B u) (normalize B u) = 1 := by
  have hp : (Real.sqrt (B u u)) ^ 2 = B u u := Real.sq_sqrt h.le
  have hn : Real.sqrt (B u u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
  simp only [normalize, map_smul, _root_.smul_apply, smul_eq_mul]
  field_simp
  exact hp.symm

lemma normalize_eq_of_unit (B : Bilinear E) (u : E) (h : B u u = 1) :
    normalize B u = u := by simp [normalize, h]

def transverse (B : Bilinear E) (J : E →L[ℝ] E) (u w : E) : E :=
  w - B u w • u - B (J u) w • J u

lemma transverse_orthogonal (B : Bilinear E) (J : E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v)
    (u w : E) (hu : B u u = 1) :
    B u (transverse B J u w) = 0 ∧ B (J u) (transverse B J u w) = 0 := by
  have hz := orthogonal_J B J hB hJ hBJ u
  have hz' : B (J u) u = 0 := by rw [hB, hz]
  have hj : B (J u) (J u) = 1 := (hBJ u u).trans hu
  constructor <;> simp [transverse, map_sub, map_smul, hu, hz, hz', hj]

lemma transverse_eq (B : Bilinear E) (J : E →L[ℝ] E) (u w : E)
    (hw : B u w = 0) (hjw : B (J u) w = 0) : transverse B J u w = w := by
  simp [transverse, hw, hjw]

def frame (J : E →L[ℝ] E) (u w : E) : Fin 4 → E := ![u,J u,w,J w]

lemma frame_gram (B : Bilinear E) (J : E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v)
    (u w : E) (hu : B u u = 1) (hw : B w w = 1)
    (huw : B u w = 0) (hjuw : B (J u) w = 0) :
    ∀ i j : Fin 4, B (frame J u w i) (frame J u w j) = if i = j then 1 else 0 := by
  have huz := orthogonal_J B J hB hJ hBJ u
  have hwz := orthogonal_J B J hB hJ hBJ w
  have huw' : B u (J w) = 0 := by have h := skew B J hJ hBJ u w; linarith
  have hwu : B w u = 0 := by rw [hB, huw]
  have hwju : B w (J u) = 0 := by rw [hB, hjuw]
  have hjwu : B (J w) u = 0 := by rw [hB, huw']
  have hjuu : B (J u) u = 0 := by rw [hB, huz]
  have hjww : B (J w) w = 0 := by rw [hB, hwz]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, hu, hw, hBJ, huz, hwz, huw, hjuw, huw', hwu, hwju, hjwu, hjuu, hjww]

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {B : D → Bilinear E} {v w : D → E} {J : D → E →L[ℝ] E}
variable {U : Set D}

lemma contDiffOn_evaluate (hB : ContDiffOn ℝ ∞ B U)
    (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun x => B x (v x) (w x)) U := (hB.clm_apply hv).clm_apply hw

lemma contDiffOn_normalize (hB : ContDiffOn ℝ ∞ B U) (hv : ContDiffOn ℝ ∞ v U)
    (hp : ∀ x ∈ U, 0 < B x (v x) (v x)) :
    ContDiffOn ℝ ∞ (fun x => normalize (B x) (v x)) U := by
  apply ContDiffOn.smul _ hv
  apply ContDiffOn.inv
  · exact (contDiffOn_evaluate hB hv hv).sqrt (fun x hx => ne_of_gt (hp x hx))
  · intro x hx
    exact ne_of_gt (Real.sqrt_pos.mpr (hp x hx))

lemma contDiffOn_transverse (hB : ContDiffOn ℝ ∞ B U)
    (hJ : ContDiffOn ℝ ∞ J U) (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun x => transverse (B x) (J x) (v x) (w x)) U :=
  (hw.sub ((contDiffOn_evaluate hB hv hw).smul hv)).sub
    ((contDiffOn_evaluate hB (hJ.clm_apply hv) hw).smul (hJ.clm_apply hv))

lemma exists_smooth_frame_near (x₀ : D) (hU : IsOpen U) (hx : x₀ ∈ U)
    (hB : ContDiffOn ℝ ∞ B U) (hJ : ContDiffOn ℝ ∞ J U)
    (hBs : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hBJ : ∀ x ∈ U, ∀ u v, B x (J x u) (J x v) = B x u v)
    (u₀ w₀ : E) (hu₀ : B x₀ u₀ u₀ = 1) (hw₀ : B x₀ w₀ w₀ = 1)
    (huw : B x₀ u₀ w₀ = 0) (hjuw : B x₀ (J x₀ u₀) w₀ = 0) :
    ∃ V : Set D, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ∃ u w : D → E, ContDiffOn ℝ ∞ u V ∧ ContDiffOn ℝ ∞ w V ∧
        u x₀ = u₀ ∧ w x₀ = w₀ ∧
        ∀ x ∈ V, ∀ i j : Fin 4,
          B x (frame (J x) (u x) (w x) i) (frame (J x) (u x) (w x) j) =
            if i = j then 1 else 0 := by
  let u : D → E := fun x => normalize (B x) u₀
  have hc : ContinuousOn (fun x => B x u₀ u₀) U :=
    (contDiffOn_evaluate hB contDiffOn_const contDiffOn_const).continuousOn
  let U₁ := {x ∈ U | 0 < B x u₀ u₀}
  have hopen : IsOpen U₁ := hc.isOpen_inter_preimage hU isOpen_Ioi
  have hx₁ : x₀ ∈ U₁ := ⟨hx, by simp [hu₀]⟩
  have hsub : U₁ ⊆ U := fun _ hx => hx.1
  have hu : ContDiffOn ℝ ∞ u U₁ :=
    contDiffOn_normalize (hB.mono hsub) contDiffOn_const (fun _ hx => hx.2)
  have hueq : u x₀ = u₀ := normalize_eq_of_unit _ _ hu₀
  let t : D → E := fun x => transverse (B x) (J x) (u x) w₀
  have ht : ContDiffOn ℝ ∞ t U₁ :=
    contDiffOn_transverse (hB.mono hsub) (hJ.mono hsub) hu contDiffOn_const
  have hteq : t x₀ = w₀ := by
    dsimp only [t]
    rw [hueq]
    exact transverse_eq _ _ _ _ huw hjuw
  have htc : ContinuousOn (fun x => B x (t x) (t x)) U₁ :=
    (contDiffOn_evaluate (hB.mono hsub) ht ht).continuousOn
  let V := {x ∈ U₁ | 0 < B x (t x) (t x)}
  have hV : IsOpen V := htc.isOpen_inter_preimage hopen isOpen_Ioi
  have hxV : x₀ ∈ V := ⟨hx₁, by rw [hteq, hw₀]; norm_num⟩
  have hVU : V ⊆ U₁ := fun _ hx => hx.1
  let w : D → E := fun x => normalize (B x) (t x)
  have hw : ContDiffOn ℝ ∞ w V :=
    contDiffOn_normalize (hB.mono (fun _ hx => hsub (hVU hx))) (ht.mono hVU) (fun _ hx => hx.2)
  refine ⟨V,hV,hxV,(fun _ hx => hsub (hVU hx)),u,w,hu.mono hVU,hw,hueq,?_,?_⟩
  · dsimp only [w]
    rw [hteq]
    exact normalize_eq_of_unit _ _ hw₀
  · intro x hxV
    have hxU : x ∈ U := hsub (hVU hxV)
    have hun : B x (u x) (u x) = 1 := normalize_unit _ _ hxV.1.2
    have hwn : B x (w x) (w x) = 1 := normalize_unit _ _ hxV.2
    have horth := transverse_orthogonal (B x) (J x) (hBs x hxU)
      (hJs x hxU) (hBJ x hxU) (u x) w₀ hun
    apply frame_gram (B x) (J x) (hBs x hxU) (hJs x hxU) (hBJ x hxU)
      (u x) (w x) hun hwn
    · change B x (u x) ((Real.sqrt (B x (t x) (t x)))⁻¹ • t x) = 0
      simp only [map_smul, smul_eq_mul]
      exact mul_eq_zero.mpr (Or.inr horth.1)
    · change B x (J x (u x)) ((Real.sqrt (B x (t x) (t x)))⁻¹ • t x) = 0
      simp only [map_smul, smul_eq_mul]
      exact mul_eq_zero.mpr (Or.inr horth.2)

end TamingCompatibility.LocalUnitaryFrame

end

end OAI
