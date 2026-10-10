import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothPolynomialFamilyImage
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-! # A noncritical limit supplies the minor bound for all late parameters -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem continuous_det_clm {P : Type*} [TopologicalSpace P] {n : ℕ}
    {d : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hd : Continuous d) :
    Continuous (fun p => (d p).det) := by
  have hm : Continuous (fun p => LinearMap.toMatrix' (d p).toLinearMap) := by
    apply continuous_matrix
    intro i j
    simp only [LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp (hd.clm_apply continuous_const)
  simpa only [LinearMap.det_toMatrix'] using hm.matrix_det

theorem converging_smooth_polynomial_family_image
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℝ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : Fin.append v₀ z₀ ∈ closedBall 0 R)
    (hdet : (fderiv ℝ (fun v => f (b₀, Fin.append v z₀)) v₀).det ≠ 0)
    (E : ℝ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBound (fun r => (volume (E r)).toReal)) :
    ∃ C : ℝ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBound (fun r => (volume (C r)).toReal) := by
  classical
  let d := fun a => fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀
  have hd : Continuous d := by
    have hg : ContDiff ℝ 2 (fun p : P × (Fin n → ℝ) => f (p.1, Fin.append p.2 z₀)) :=
      hf.comp (contDiff_fst.prodMk
        ((contDiff_finAppend n k).comp (contDiff_snd.prodMk contDiff_const)))
    have hh : ContDiff ℝ 1 d := ContDiff.fderiv hg (contDiff_const (c := v₀)) (by norm_num)
    exact hh.continuous
  let D := fun a => |(d a).det|
  have hD : Continuous D := (continuous_det_clm hd).abs
  have hDpos : 0 < D b₀ := abs_pos.mpr hdet
  let c := D b₀ / 2
  have hc : 0 < c := half_pos hDpos
  let T := S ∩ {a | c ≤ D a}
  have hT : IsCompact T := hS.inter_right (isClosed_le continuous_const hD)
  have hb₀T : b₀ ∈ T := ⟨hb₀, (half_le_self hDpos.le)⟩
  have hlate : ∀ᶠ r in atTop, b r ∈ T := by
    have hh := (hD.continuousAt.tendsto.comp hlim).eventually
      (Ioi_mem_nhds (show c < D b₀ from half_lt_self hDpos))
    filter_upwards [hh] with r hr
    exact ⟨hb r, hr.le⟩
  let b' := fun r => if b r ∈ T then b r else b₀
  have hb' : ∀ r, b' r ∈ T := by
    intro r
    dsimp [b']
    split_ifs with h
    · exact h
    · exact hb₀T
  obtain ⟨C, hC, hCE, hClower⟩ := compact_smooth_polynomial_family_image
    rem n k hn f hf hpoly T hT b' hb' R c hR hc v₀ z₀ hanchor
    (fun a ha => ha.2) E hE hER hm hmlower
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hlate] with r hr
  simpa only [b', ite_eq_left hr] using hCE r

end PolycyclicRecognition

end

end OAI
