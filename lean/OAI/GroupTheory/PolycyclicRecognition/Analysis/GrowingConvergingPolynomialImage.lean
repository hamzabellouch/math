import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConvergingPolynomialImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GrowingPolynomialImage

namespace OAI

/-! # Converging polynomial image volume on growing cubes -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_polynomial_family_image_growing_sequence
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : ∀ r, Fin.append v₀ z₀ ∈ closedBall 0 (R r))
    (hdet : (fderiv ℝ (fun v => f (b₀, Fin.append v z₀)) v₀).det ≠ 0)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
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
  obtain ⟨C, hC, hCE, hClower⟩ := compact_polynomial_family_image_growing_sequence
    scale hscale rem n k hn f hf.continuous hpoly T hT b' hb' R hR hRupper c hc v₀ z₀ hanchor
    (fun a ha => ha.2) E hE hER hm hmlower
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hlate] with r hr
  simpa only [b', ite_eq_left hr] using hCE r

end PolycyclicRecognition

end

end OAI
