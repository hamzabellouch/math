import OAI.Geometry.Immersion.ClosedSurface.NormalJets
import OAI.Geometry.Immersion.ClosedSurface.SecondForms

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes



lemma gramDet_ne_zero_of_injective (A : Base →L[ℝ] RVec 4) (hA : Function.Injective A) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 := by
  let X := A dx
  let Y := A dy
  have hX : X ≠ 0 := by
    intro hx
    have he : dx = 0 := hA (by simpa [X] using hx)
    exact one_ne_zero (congrArg Prod.fst he)
  have hXX : X ⬝ᵥ X ≠ 0 := (dotProduct_self_eq_zero).not.mpr hX
  intro hD
  let v : Base := -(X ⬝ᵥ Y) • dx + (X ⬝ᵥ X) • dy
  have hv : A v = -(X ⬝ᵥ Y) • X + (X ⬝ᵥ X) • Y := by simp [v,X,Y]
  have hsq : A v ⬝ᵥ A v = (X ⬝ᵥ X) * NormalFrame.gramDet X Y := by
    rw [hv]
    simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hz : A v = 0 := dotProduct_self_eq_zero.mp (by rw [hsq]; change _ * NormalFrame.gramDet (A dx) (A dy) = 0; rw [hD,mul_zero])
  have hv0 : v = 0 := hA (by simpa using hz)
  have hy0 := congrArg Prod.snd hv0
  exact hXX (by simpa [v,dx,dy] using hy0)

lemma injective_of_gramDet_ne_zero (A : Base →L[ℝ] RVec 4)
    (hD : NormalFrame.gramDet (A dx) (A dy) ≠ 0) : Function.Injective A := by
  have hz : ∀ v : Base, A v = 0 → v = 0 := by
    intro v hv
    have hb : A v = v.1 • A dx + v.2 • A dy := by
      calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
           _ = _ := by simp
    have hx := congrArg (fun W => A dx ⬝ᵥ W) hv
    have hy := congrArg (fun W => A dy ⬝ᵥ W) hv
    rw [hb] at hx hy
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      dotProduct_comm (A dy) (A dx)] at hx hy
    have hvx : v.1 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.1 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dy ⬝ᵥ A dy) * hx - (A dx ⬝ᵥ A dy) * hy)).resolve_left hD
    have hvy : v.2 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.2 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dx ⬝ᵥ A dx) * hy - (A dx ⬝ᵥ A dy) * hx)).resolve_left hD
    exact Prod.ext hvx hvy
  intro p q hpq
  exact sub_eq_zero.mp (hz (p-q) (by simpa using sub_eq_zero.mpr hpq))

lemma gramDet_ne_zero_iff_injective (A : Base →L[ℝ] RVec 4) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 ↔ Function.Injective A :=
  ⟨injective_of_gramDet_ne_zero A, gramDet_ne_zero_of_injective A⟩

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma contDiffAt_realSecondTensor {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    ContDiffAt ℝ ∞ (realSecondTensor F) p := by
  have hx := (contDiff_real_coordDeriv hF dx).contDiffAt (x := p)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffAt (x := p)
  have hb (v w : Base) : ContDiffAt ℝ ∞ (fun q => realSecondForm F v w q) p :=
    contDiffAt_realNormalPart hx hy
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hb dx dx
  · exact hb dx dy
  · exact hb dy dy

lemma continuous_gramDet_field {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p => NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p)) := by
  have hx := (contDiff_real_coordDeriv hF dx).continuous
  have hy := (contDiff_real_coordDeriv hF dy).continuous
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma good_eventually {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} {p : X}
    (hB : ContinuousAt B p) (hξ : ContinuousAt ξ p) (hg : Good (B p) (ξ p)) :
    ∀ᶠ q in 𝓝 p, Good (B q) (ξ q) := by
  have ho : IsOpen {z : (Fin 3 → RVec n) × Base | Good z.1 z.2} :=
    isOpen_good continuous_fst continuous_snd
  exact (hB.prodMk hξ).preimage_mem_nhds (ho.mem_nhds hg)




theorem actual_local_phase_data {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {H : Base → PhaseMean.Tensor} {p : Base} (hH : ContinuousAt H p)
    (hImm : Function.Injective (fderiv ℝ F p))
    (hB : ∃ v w : Base, realSecondForm F v w p ≠ 0)
    (hH0 : 0 < H p 0) (hHdet : 0 < H p 0 * H p 2 - (H p 1)^2) :
    ∃ (ξ : Fin 3 → Base) (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ) (U : Set Base),
      IsOpen U ∧ p ∈ U ∧
      (∀ A, ∑ i, Q i A • covectorSquare (ξ i) = A) ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ F x) ∧
        (∀ i, 0 < Q i (H x)) ∧ (∀ i, Good (realSecondTensor F x) (ξ i)) ∧
        (∀ i j, i ≠ j → Good (realSecondTensor F x) (ξ i + ξ j) ∧
          Good (realSecondTensor F x) (ξ i - ξ j))) := by
  obtain ⟨ξ,Q,hdec,hpos,hgood,hcross⟩ := actual_positive_phase_data hF p hB (H p) hH0 hHdet
  have hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0 :=
    gramDet_ne_zero_of_injective (fderiv ℝ F p) hImm
  have hbc := (contDiffAt_realSecondTensor hF p hD).continuousAt
  have hde : ∀ᶠ x in 𝓝 p, NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0 :=
    (continuous_gramDet_field hF).continuousAt.eventually_ne hD
  have hpe : ∀ᶠ x in 𝓝 p, ∀ i, 0 < Q i (H x) := by
    rw [Filter.eventually_all]
    intro i
    exact (show ContinuousAt (fun x => Q i (H x)) p from
      (Q i).continuous.continuousAt.comp hH).eventually_const_lt (hpos i)
  have hge : ∀ᶠ x in 𝓝 p, ∀ i, Good (realSecondTensor F x) (ξ i) := by
    rw [Filter.eventually_all]
    intro i
    exact good_eventually hbc continuousAt_const (hgood i)
  have hce : ∀ᶠ x in 𝓝 p, ∀ i j, i ≠ j → Good (realSecondTensor F x) (ξ i + ξ j) ∧
      Good (realSecondTensor F x) (ξ i - ξ j) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro hij
    exact (good_eventually hbc continuousAt_const (hcross i j hij).1).and
      (good_eventually hbc continuousAt_const (hcross i j hij).2)
  have he := hde.and (hpe.and (hge.and hce))
  obtain ⟨U,hUs,hU,hpU⟩ := mem_nhds_iff.mp he
  refine ⟨ξ, Q, U, hU, hpU, hdec, fun x hx => ?_⟩
  obtain ⟨hd,hp,hg,hc⟩ := hUs hx
  exact ⟨injective_of_gramDet_ne_zero (fderiv ℝ F x) hd, hp, hg, hc⟩

end ClosedSurfaceR4.RealModes

end

end OAI
