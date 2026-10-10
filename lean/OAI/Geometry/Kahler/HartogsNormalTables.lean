import OAI.Geometry.Kahler.HartogsNormalJets

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def verticalDelta (i : Fin 3) : ℂ := if i = 2 then 1 else 0

def liftedHessian (f : Base → ℝ) (q : Ambient) : CMatrix :=
  complexHessian (fun q : Ambient => f q.1) q

def liftedThird (f : Base → ℝ) (q : Ambient) (a c d : Fin 3) : ℂ :=
  dz (fun r => liftedHessian f r c d) q a

def liftedBarThird (f : Base → ℝ) (q : Ambient) (b c d : Fin 3) : ℂ :=
  dbar (fun r => liftedHessian f r c d) q b

def liftedFourth (f : Base → ℝ) (q : Ambient) (a b c d : Fin 3) : ℂ :=
  dbar (fun r => liftedThird f r a c d) q b

lemma dz_dbar_congr {f g : Ambient → ℂ} {p : Ambient} (h : f =ᶠ[𝓝 p] g) (i j : Fin 3) :
    dz (fun q => dbar f q j) p i = dz (fun q => dbar g q j) p i := by
  apply dz_congr
  filter_upwards [h.eventuallyEq_nhds] with q hq
  exact dbar_congr hq j

lemma dbar_dz_congr {f g : Ambient → ℂ} {p : Ambient} (h : f =ᶠ[𝓝 p] g) (i j : Fin 3) :
    dbar (fun q => dz f q i) p j = dbar (fun q => dz g q i) p j := by
  apply dbar_congr
  filter_upwards [h.eventuallyEq_nhds] with q hq
  exact dz_congr hq i

lemma normalLogWeight_third {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (a c d : Fin 3) :
    dz (fun q => complexHessian (normalLogWeight f w) q c d) (0,w) a =
      liftedThird f (0,w) a c d := by
  apply dz_congr
  filter_upwards [normalLogWeight_hessian_eventually hf w] with q hq
  exact congrFun (congrFun hq c) d

lemma normalLogWeight_barThird {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (b c d : Fin 3) :
    dbar (fun q => complexHessian (normalLogWeight f w) q c d) (0,w) b =
      liftedBarThird f (0,w) b c d := by
  apply dbar_congr
  filter_upwards [normalLogWeight_hessian_eventually hf w] with q hq
  exact congrFun (congrFun hq c) d

lemma normalLogWeight_fourth {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (normalLogWeight f w) r c d) q a) (0,w) b =
      liftedFourth f (0,w) a b c d := by
  apply dbar_dz_congr
  filter_upwards [normalLogWeight_hessian_eventually hf w] with q hq
  exact congrFun (congrFun hq c) d

lemma normalBarrier_hessian {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (i j : Fin 3) :
    complexHessian (logarithmicBarrier ∘ normalLogWeight f w) (0,w) i j =
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) i j +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta i * verticalDelta j := by
  rw [complexHessian_barrier (normalLogWeight_contDiffAt (q := (0,w)) hf w) hn,
    normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_barFirst hf,
    normalLogWeight_hessian (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  rfl

lemma normalBarrier_third {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a c d : Fin 3) :
    dz (fun q => complexHessian (logarithmicBarrier ∘ normalLogWeight f w) q c d) (0,w) a =
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedThird f (0,w) a c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta c * liftedHessian f (0,w) a d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * verticalDelta c * verticalDelta d := by
  rw [dz_complexHessian_barrier ((normalLogWeight_contDiffAt (q := (0,w)) hf w).of_le (WithTop.coe_le_coe.mpr le_top)) hn]
  simp only [normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_barFirst hf,
    normalLogWeight_pureSecond (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    normalLogWeight_hessian (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_third hf,
    mul_zero, zero_mul, add_zero]
  rfl

lemma normalBarrier_fourth {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ normalLogWeight f w) r c d) q a) (0,w) b =
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * liftedThird f (0,w) a c d +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedFourth f (0,w) a b c d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * verticalDelta a * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) a b * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedBarThird f (0,w) b c d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * verticalDelta c * liftedHessian f (0,w) a d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) c b * liftedHessian f (0,w) a d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta c * liftedBarThird f (0,w) b a d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * liftedThird f (0,w) a c b * verticalDelta d +
      (barrierFourth (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * verticalDelta a * verticalDelta c * verticalDelta d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) a b * verticalDelta c * verticalDelta d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedHessian f (0,w) c b * verticalDelta d := by
  have hs := normalLogWeight_contDiffAt (q := (0,w)) hf w
  rw [dbar_dz_complexHessian_barrier (hs.of_le (WithTop.coe_le_coe.mpr le_top)) hn]
  simp only [normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_barFirst hf,
    normalLogWeight_pureSecond (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_pureBarSecond hf,
    dbar_dz_real_eq_hessian (hs.of_le (WithTop.coe_le_coe.mpr le_top)),
    dbar_dz_dz_real (hs.of_le (WithTop.coe_le_coe.mpr le_top)),
    normalLogWeight_hessian (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_third hf,
    normalLogWeight_barThird hf, normalLogWeight_fourth hf, mul_zero, zero_mul, add_zero]
  rfl

end PinchedHartogs

end

end OAI
