import Mathlib
import OAI.Analysis.Conductivity.Branching.ParentEndPartition
import OAI.Analysis.Conductivity.Variational.FiniteEndPhysicalDescent
import OAI.Analysis.Conductivity.Sources.FacePasting

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

theorem compact_localLip_H1_pi {u : Coord3 → ℝ}
    (hu : ∀ x,LocalLipAt u x) {R : ℝ} (hR : R<3)
    (hs : ∀ x,R<‖WithLp.toLp 2 x‖ → u x=0) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=u (WithLp.ofLp x) ∧ ∀ i,
        weakGradient w x i=lineDeriv ℝ u (WithLp.ofLp x) (Pi.single i 1)) := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hh (x : R3) : LocalLipAt (u ∘ E) x :=
    (hu (E x)).comp (E.toContinuousLinearMap.lipschitzWith.locallyLipschitz x)
  have hz (x : R3) (hx : R<‖x‖) : (u ∘ E) x=0 := hs (E x) hx
  obtain ⟨K,hK⟩ := compact_locallyLipschitz hh (bounded_support_compact hz)
  obtain ⟨w,hw,he⟩ := compact_lipschitz_H1 hK hR hz
  refine ⟨w,hw,?_⟩
  filter_upwards [he] with x hx
  refine ⟨hx.1,fun i => (hx.2 i).trans ?_⟩
  unfold lineDeriv
  congr 1

theorem cut_physicalPeriodicField_H10 {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {χ : Coord3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (_ : HasCompactSupport χ)
    (hs : tsupport χ⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=χ (WithLp.ofLp x)*physicalPeriodicField f (WithLp.ofLp x) ∧ ∀ i,
        weakGradient w x i=lineDeriv ℝ (fun y => χ y*physicalPeriodicField f y)
          (WithLp.ofLp x) (Pi.single i 1)) := by
  refine compact_localLip_H1_pi (u:=fun y => χ y*physicalPeriodicField f y) (R:=5/2) ?_ (by norm_num) ?_
  · intro x
    by_cases hx : x∈tsupport χ
    · exact (localLipAt_of_contDiffAt (hχ.of_le (by simp)).contDiffAt).mul
        (physicalPeriodicField_localLip hp hf (sourceDirections_ne_zero_on_band (hs hx)))
    · apply (localLipAt_of_contDiffAt (contDiffAt_const (c:=(0:ℝ)))).congr
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change χ y=0 at hy
      simp [hy]
  · intro x hx
    have hn : x∉tsupport χ := fun h => hx.not_ge (sourceBand_euclidean_bound (hs h))
    simp [image_eq_zero_of_notMem_tsupport hn]

lemma cut_physicalPeriodicField_lineDeriv {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    {χ : Coord3 → ℝ} (hχ : Differentiable ℝ χ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) (k : Fin 3) :
    lineDeriv ℝ (fun y => χ y*physicalPeriodicField f y)
        (sourceCollarPiece i j x) (Pi.single k 1)=
      fderiv ℝ χ (sourceCollarPiece i j x) (Pi.single k 1)*f (sourceFaceAngles i j x)+
        χ (sourceCollarPiece i j x)*
          ((sourceCartesianGradientMatrix i j x)*ᵥ
            (fun l => direction (Pi.single l 1) f (sourceFaceAngles i j x))) k := by
  have hd := physicalPeriodicField_hasFDeriv hp hf i j hx
  have hh := (hχ _).hasFDerivAt.mul hd
  change lineDeriv ℝ (χ * physicalPeriodicField f) _ _ = _
  rw [hh.differentiableAt.lineDeriv_eq_fderiv,hh.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  have he := physicalPeriodicField_fderiv hp hf i j hx (Pi.single k 1)
  rw [hd.fderiv] at he
  rw [he,physicalPeriodicField_piece hp i j (sourceCollarOpenBox_subset hx)]
  simp only [dotProduct_single_one]
  ring

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_shift (a b T : ℝ) (n : Fin 2 → ℤ) (x : Coord3) :
    flatEndCoordinates a b (x+angularShift T n)=flatEndCoordinates a b x+angularShift T n := by
  ext i
  fin_cases i <;> simp [flatEndCoordinates,angularShift]

lemma AngularPeriodic.flatEnd {E : Type*} {f : Coord3 → E} {T : ℝ}
    (hp : AngularPeriodic T f) (a b : ℝ) :
    AngularPeriodic T (fun x => f (flatEndCoordinates a b x)) := by
  intro n x
  change f (flatEndCoordinates a b (x+angularShift T n))=f (flatEndCoordinates a b x)
  rw [flatEndCoordinates_shift,hp n (flatEndCoordinates a b x)]

def attachedPeriodicField (f : Coord3 → ℝ) (a b : ℝ) : Coord3 → ℝ :=
  physicalPeriodicField (fun x => f (flatEndCoordinates a b x))

lemma attachedPeriodicField_zero_nhds {f : Coord3 → ℝ} {τ a b : ℝ} (hτ : 0<τ)
    (hz : ∀ x,x 0<τ → f x=0) {y : Coord3}
    (hy : a*(sourceCollarTime y-b)≤0) :
    attachedPeriodicField f a b=ᶠ[𝓝 y] (fun _ => 0) := by
  have hc : Continuous (fun y : Coord3 => a*(sourceCollarTime y-b)) :=
    continuous_const.mul (locallyLipschitz_sourceCollarTime.continuous.sub continuous_const)
  filter_upwards [(isOpen_lt hc continuous_const).mem_nhds (hy.trans_lt hτ)] with z hz'
  exact hz _ hz'

theorem attachedPeriodicCorrection_H10 {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {τ a b l₀ l r r₀ : ℝ} (hτ : 0<τ) (hz : ∀ x,x 0<τ → f x=0)
    (hl : l₀<l) (hr : r<r₀) (hl₀ : -(1:ℝ)/100≤l₀) (hr₀ : r₀≤1/100) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure,a*(sourceCollarTime (WithLp.ofLp x)-b)≤0 →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand l r →
        weakValue d x=attachedPeriodicField f a b (WithLp.ofLp x) ∧ ∀ i,
          weakGradient d x i=lineDeriv ℝ (attachedPeriodicField f a b)
            (WithLp.ofLp x) (Pi.single i 1)) := by
  obtain ⟨χ,hχ,hχc,hχb,hχs,hχ1⟩ := exists_nonneg_band_cutoff hl hr hl₀ hr₀
  have hc : ContDiff ℝ 1 (fun x => f (flatEndCoordinates a b x)) :=
    hf.comp ((contDiff_flatEndCoordinates a b).of_le (WithTop.coe_le_coe.mpr le_top))
  have hs : tsupport χ⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := by
    intro x hx
    exact ⟨hl₀.trans (hχs hx).1,(hχs hx).2.trans hr₀⟩
  obtain ⟨d,hd,hde⟩ := cut_physicalPeriodicField_H10 (hp.flatEnd a b) hc hχ hχc hs
  refine ⟨d,hd,?_,?_⟩
  · filter_upwards [hde] with x hx hy
    have he := attachedPeriodicField_zero_nhds hτ hz hy
    have he' : (fun y => χ y*attachedPeriodicField f a b y)=ᶠ[𝓝 (WithLp.ofLp x)]
        (fun _ => 0) := by
      filter_upwards [he] with y hy
      rw [hy,mul_zero]
    refine ⟨hx.1.trans ?_,fun i => (hx.2 i).trans ?_⟩
    · exact he'.eq_of_nhds
    · change lineDeriv ℝ (fun y => χ y*attachedPeriodicField f a b y) _ _=0
      rw [he'.lineDeriv_eq (𝕜:=ℝ)]
      simp [lineDeriv]
  · filter_upwards [hde] with x hx hy
    have he : (fun y => χ y*attachedPeriodicField f a b y)=ᶠ[𝓝 (WithLp.ofLp x)]
        attachedPeriodicField f a b := by
      filter_upwards [hχ1 _ hy] with y hy
      rw [hy,one_mul]
    exact ⟨hx.1.trans he.eq_of_nhds,fun i => (hx.2 i).trans he.lineDeriv_eq⟩

end ScalarConductivity

end
end

end OAI
