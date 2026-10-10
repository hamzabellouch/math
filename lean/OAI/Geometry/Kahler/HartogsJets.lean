import OAI.Geometry.Kahler.HartogsCurvature

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def logarithmicBarrier (s : ℝ) : ℝ := -Real.log (1 - Real.exp s)
def barrierX (s : ℝ) : ℝ := Real.exp s / (1 - Real.exp s)
def barrierQ (s : ℝ) : ℝ := barrierX s * (1 + barrierX s)
def barrierThird (s : ℝ) : ℝ := barrierQ s * (1 + 2 * barrierX s)
def barrierFourth (s : ℝ) : ℝ := barrierQ s * (1 + 6 * barrierX s + 6 * barrierX s ^ 2)

lemma barrier_den_ne_zero {s : ℝ} (hs : s < 0) : 1 - Real.exp s ≠ 0 :=
  ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr hs))

lemma logarithmicBarrier_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt logarithmicBarrier (barrierX s) s := by
  have hh := ((hasDerivAt_const s (1 : ℝ)).sub (Real.hasDerivAt_exp s)).log
    (barrier_den_ne_zero hs)
  convert hh.neg using 1 <;> try rfl
  dsimp [barrierX]
  ring

lemma barrierX_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt barrierX (barrierQ s) s := by
  convert (Real.hasDerivAt_exp s).div
    ((hasDerivAt_const s (1 : ℝ)).sub (Real.hasDerivAt_exp s)) (barrier_den_ne_zero hs) using 1 <;> try rfl
  dsimp [barrierQ, barrierX]
  field_simp [barrier_den_ne_zero hs]
  ; ring

lemma barrierQ_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt barrierQ (barrierThird s) s := by
  convert (barrierX_hasDerivAt hs).mul
    ((hasDerivAt_const s (1 : ℝ)).add (barrierX_hasDerivAt hs)) using 1 <;> try rfl
  dsimp [barrierQ, barrierThird]
  ring

lemma barrierThird_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt barrierThird (barrierFourth s) s := by
  convert (barrierQ_hasDerivAt hs).mul
    ((hasDerivAt_const s (1 : ℝ)).add ((barrierX_hasDerivAt hs).const_mul 2)) using 1 <;> try rfl
  dsimp [barrierFourth, barrierThird, barrierQ]
  ring

lemma barrierX_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ barrierX s :=
  Real.contDiff_exp.contDiffAt.div (contDiffAt_const.sub Real.contDiff_exp.contDiffAt)
    (barrier_den_ne_zero hs)
lemma barrierQ_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ barrierQ s :=
  (barrierX_contDiffAt hs).mul (contDiffAt_const.add (barrierX_contDiffAt hs))
lemma barrierThird_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ barrierThird s :=
  (barrierQ_contDiffAt hs).mul (contDiffAt_const.add (contDiffAt_const.mul (barrierX_contDiffAt hs)))
lemma logarithmicBarrier_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ logarithmicBarrier s :=
  ((contDiffAt_const.sub Real.contDiff_exp.contDiffAt).log (barrier_den_ne_zero hs)).neg

lemma complexHessian_barrier {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ ∞ s p) (hn : s p < 0) (i j : Fin 3) :
    complexHessian (logarithmicBarrier ∘ s) p i j =
      (barrierX (s p) : ℂ) * complexHessian s p i j +
        (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p i * dbar (fun q => (s q : ℂ)) p j := by
  apply complexHessian_real_comp (hs.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  · filter_upwards [Iio_mem_nhds hn] with y hy
    exact logarithmicBarrier_hasDerivAt hy
  · exact barrierX_hasDerivAt hn

lemma dz_complexHessian_real_comp {s : Ambient → ℝ} {p : Ambient}
    {ρ₀ ρ₁ ρ₂ ρ₃ : ℝ → ℝ} {V : Set ℝ}
    (hs : ContDiffAt ℝ 3 s p) (hV : IsOpen V) (hp : s p ∈ V)
    (h₀ : ∀ y ∈ V, HasDerivAt ρ₀ (ρ₁ y) y)
    (h₁ : ∀ y ∈ V, HasDerivAt ρ₁ (ρ₂ y) y)
    (h₂ : ∀ y ∈ V, HasDerivAt ρ₂ (ρ₃ y) y) (a c d : Fin 3) :
    dz (fun q => complexHessian (ρ₀ ∘ s) q c d) p a =
      (ρ₁ (s p) : ℂ) * dz (fun q => complexHessian s q c d) p a +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (ρ₂ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a *
        dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a *
        dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d := by
  have he : (fun q => complexHessian (ρ₀ ∘ s) q c d) =ᶠ[𝓝 p]
      (fun q => (ρ₁ (s q) : ℂ) * complexHessian s q c d +
       (ρ₂ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (hV.mem_nhds hp)] with q hq hnq
    apply complexHessian_real_comp (hq.of_le (by norm_num))
    · filter_upwards [hV.mem_nhds hnq] with y hy
      exact h₀ y hy
    · exact h₁ (s q) hnq
  have hx : DifferentiableAt ℝ (fun q => (ρ₁ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₁ (s p) hp).differentiableAt.comp p (hs.differentiableAt (by norm_num)))
  have hq : DifferentiableAt ℝ (fun q => (ρ₂ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₂ (s p) hp).differentiableAt.comp p (hs.differentiableAt (by norm_num)))
  have hh : DifferentiableAt ℝ (fun q => complexHessian s q c d) p :=
    ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c) :
      ContDiffAt ℝ 1 _ p).differentiableAt (by norm_num)
  have hz : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q c) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  have hb : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q d) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) d).differentiableAt (by norm_num)
  erw [dz_congr he, dz_add (hx.mul hh) ((hq.mul hz).mul hb), dz_mul hx hh,
    dz_mul (hq.mul hz) hb, dz_mul hq hz,
    dz_real_comp (hs.differentiableAt (by norm_num)) (h₁ (s p) hp),
    dz_real_comp (hs.differentiableAt (by norm_num)) (h₂ (s p) hp)]
  dsimp [complexHessian]
  ring

lemma dbar_dz_complexHessian_real_comp {s : Ambient → ℝ} {p : Ambient}
    {ρ₀ ρ₁ ρ₂ ρ₃ ρ₄ : ℝ → ℝ} {V : Set ℝ}
    (hs : ContDiffAt ℝ 4 s p) (hV : IsOpen V) (hp : s p ∈ V)
    (h₀ : ∀ y ∈ V, HasDerivAt ρ₀ (ρ₁ y) y)
    (h₁ : ∀ y ∈ V, HasDerivAt ρ₁ (ρ₂ y) y)
    (h₂ : ∀ y ∈ V, HasDerivAt ρ₂ (ρ₃ y) y)
    (h₃ : ∀ y ∈ V, HasDerivAt ρ₃ (ρ₄ y) y) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (ρ₀ ∘ s) r c d) q a) p b =
      (ρ₂ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => complexHessian s q c d) p a +
      (ρ₁ (s p) : ℂ) * dbar (fun q => dz (fun r => complexHessian s r c d) q a) p b +
      (ρ₃ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (ρ₂ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * complexHessian s p c d +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => complexHessian s q c d) p b +
      (ρ₃ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (ρ₂ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * complexHessian s p a d +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * dbar (fun q => complexHessian s q a d) p b +
      (ρ₃ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => (s q : ℂ)) p d +
      (ρ₂ (s p) : ℂ) * dbar (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r c) q a) p b * dbar (fun q => (s q : ℂ)) p d +
      (ρ₂ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b +
      (ρ₄ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b := by
  have he : (fun q => dz (fun r => complexHessian (ρ₀ ∘ s) r c d) q a) =ᶠ[𝓝 p]
      (fun q =>
        (ρ₁ (s q) : ℂ) * dz (fun r => complexHessian s r c d) q a +
        (ρ₂ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * complexHessian s q c d +
        (ρ₂ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * complexHessian s q a d +
        (ρ₂ (s q) : ℂ) * dz (fun r => dz (fun w => (s w : ℂ)) r c) q a * dbar (fun r => (s r : ℂ)) q d +
        (ρ₃ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (hV.mem_nhds hp)] with q hq hnq
    exact dz_complexHessian_real_comp (hq.of_le (by norm_num)) hV hnq h₀ h₁ h₂ a c d
  have hd := hs.differentiableAt (by norm_num)
  have hx : DifferentiableAt ℝ (fun q => (ρ₁ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₁ (s p) hp).differentiableAt.comp p hd)
  have hq : DifferentiableAt ℝ (fun q => (ρ₂ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₂ (s p) hp).differentiableAt.comp p hd)
  have ht : DifferentiableAt ℝ (fun q => (ρ₃ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₃ (s p) hp).differentiableAt.comp p hd)
  have hz (i : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hb (i : Fin 3) : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hh (i j : Fin 3) : DifferentiableAt ℝ (fun q => complexHessian s q i j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) j) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hzz (i j : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r i) q j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) i) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  have hhz (i j k : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => complexHessian s r i j) q k) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 3) (by norm_num) j) (m := 2) (by norm_num) i) (m := 1) (by norm_num) k).differentiableAt (by norm_num)
  rw [dbar_congr he]
  simp (disch := fun_prop) only [dbar_add, dbar_mul]
  rw [dbar_real_comp hd (h₁ (s p) hp),
    dbar_real_comp hd (h₂ (s p) hp), dbar_real_comp hd (h₃ (s p) hp)]
  ring

lemma dz_complexHessian_barrier {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 3 s p) (hn : s p < 0) (a c d : Fin 3) :
    dz (fun q => complexHessian (logarithmicBarrier ∘ s) q c d) p a =
      (barrierX (s p) : ℂ) * dz (fun q => complexHessian s q c d) p a +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (barrierQ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a *
        dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a *
        dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d := by
  have he : (fun q => complexHessian (logarithmicBarrier ∘ s) q c d) =ᶠ[𝓝 p]
      (fun q => (barrierX (s q) : ℂ) * complexHessian s q c d +
       (barrierQ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (Iio_mem_nhds hn)] with q hq hnq
    apply complexHessian_real_comp (hq.of_le (by norm_num))
    · filter_upwards [Iio_mem_nhds hnq] with y hy
      exact logarithmicBarrier_hasDerivAt hy
    · exact barrierX_hasDerivAt hnq
  have hx := (_root_.OAI.ContDiffAt.hartogs_real_cast (((barrierX_contDiffAt hn).of_le (show (3 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp p hs)).differentiableAt (by norm_num)
  have hq := (_root_.OAI.ContDiffAt.hartogs_real_cast (((barrierQ_contDiffAt hn).of_le (show (3 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp p hs)).differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ (fun q => complexHessian s q c d) p :=
    ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c) :
      ContDiffAt ℝ 1 _ p).differentiableAt (by norm_num)
  have hz : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q c) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  have hb : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q d) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) d).differentiableAt (by norm_num)
  erw [dz_congr he, dz_add (hx.mul hh) ((hq.mul hz).mul hb), dz_mul hx hh,
    dz_mul (hq.mul hz) hb, dz_mul hq hz,
    dz_real_comp (hs.differentiableAt (by norm_num)) (barrierX_hasDerivAt hn),
    dz_real_comp (hs.differentiableAt (by norm_num)) (barrierQ_hasDerivAt hn)]
  dsimp [complexHessian]
  ring

lemma dbar_dz_complexHessian_barrier {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 4 s p) (hn : s p < 0) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ s) r c d) q a) p b =
      (barrierQ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => complexHessian s q c d) p a +
      (barrierX (s p) : ℂ) * dbar (fun q => dz (fun r => complexHessian s r c d) q a) p b +
      (barrierThird (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (barrierQ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * complexHessian s p c d +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => complexHessian s q c d) p b +
      (barrierThird (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (barrierQ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * complexHessian s p a d +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * dbar (fun q => complexHessian s q a d) p b +
      (barrierThird (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => (s q : ℂ)) p d +
      (barrierQ (s p) : ℂ) * dbar (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r c) q a) p b * dbar (fun q => (s q : ℂ)) p d +
      (barrierQ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b +
      (barrierFourth (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b := by
  have he : (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ s) r c d) q a) =ᶠ[𝓝 p]
      (fun q =>
        (barrierX (s q) : ℂ) * dz (fun r => complexHessian s r c d) q a +
        (barrierQ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * complexHessian s q c d +
        (barrierQ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * complexHessian s q a d +
        (barrierQ (s q) : ℂ) * dz (fun r => dz (fun w => (s w : ℂ)) r c) q a * dbar (fun r => (s r : ℂ)) q d +
        (barrierThird (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (Iio_mem_nhds hn)] with q hq hnq
    exact dz_complexHessian_barrier (hq.of_le (by norm_num)) hnq a c d
  have hd := hs.differentiableAt (by norm_num)
  have hx : DifferentiableAt ℝ (fun q => (barrierX (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((barrierX_hasDerivAt hn).differentiableAt.comp p hd)
  have hq : DifferentiableAt ℝ (fun q => (barrierQ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((barrierQ_hasDerivAt hn).differentiableAt.comp p hd)
  have ht : DifferentiableAt ℝ (fun q => (barrierThird (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((barrierThird_hasDerivAt hn).differentiableAt.comp p hd)
  have hz (i : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hb (i : Fin 3) : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hh (i j : Fin 3) : DifferentiableAt ℝ (fun q => complexHessian s q i j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) j) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hzz (i j : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r i) q j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) i) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  have hhz (i j k : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => complexHessian s r i j) q k) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 3) (by norm_num) j) (m := 2) (by norm_num) i) (m := 1) (by norm_num) k).differentiableAt (by norm_num)
  rw [dbar_congr he]
  simp (disch := fun_prop) only [dbar_add, dbar_mul]
  rw [dbar_real_comp hd (barrierX_hasDerivAt hn),
    dbar_real_comp hd (barrierQ_hasDerivAt hn), dbar_real_comp hd (barrierThird_hasDerivAt hn)]
  ring

lemma dbar_dz_real_eq_hessian {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 2 s p) (a b : Fin 3) :
    dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b = complexHessian s p a b :=
  (dz_dbar_comm (_root_.OAI.ContDiffAt.hartogs_real_cast hs) a b).symm

lemma dz_dz_base_norm_sq (p : Ambient) (a c : Fin 3) :
    dz (fun q => dz (fun r : Ambient => (‖r.1‖ ^ 2 : ℝ)) q c) p a = 0 := by
  have he (q : Ambient) : dz (fun r : Ambient => (‖r.1‖ ^ 2 : ℝ)) q c =
      star (q.1 0 * (if c = 0 then 1 else 0) + q.1 1 * (if c = 1 then 1 else 0)) := by
    rw [dz_base_norm_sq]
    simp only [star_add, star_mul']
    split_ifs <;> simp
  simp only [he]
  have hd : DifferentiableAt ℂ (fun q : Ambient => q.1 0 * (if c = 0 then 1 else 0) +
      q.1 1 * (if c = 1 then 1 else 0)) p := by fun_prop
  rw [dz_conj (hd.restrictScalars ℝ) a, dbar_holomorphic hd, star_zero]

def horizontalIdentity (i j : Fin 3) : ℂ :=
  (if i = 0 then 1 else 0) * (if j = 0 then 1 else 0) +
  (if i = 1 then 1 else 0) * (if j = 1 then 1 else 0)

def inverseCube (s : ℝ) : ℝ := 2 / (1 - s) ^ 3
def inverseFourth (s : ℝ) : ℝ := 6 / (1 - s) ^ 4

lemma inverseSquare_hasDerivAt {s : ℝ} (hs : 1 - s ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - y)⁻¹ ^ 2) (inverseCube s) s := by
  convert (invOneSub_hasDerivAt hs).pow 2 using 1 ; try rfl
  dsimp [inverseCube]
  field_simp
lemma inverseCube_hasDerivAt {s : ℝ} (hs : 1 - s ≠ 0) :
    HasDerivAt inverseCube (inverseFourth s) s := by
  have hh := ((invOneSub_hasDerivAt hs).pow 3).const_mul 2
  have he : inverseCube = fun y : ℝ => 2 * ((1 - y)⁻¹ ^ 3) := by
    funext y
    simp [inverseCube, div_eq_mul_inv, inv_pow]
  rw [he]
  convert hh using 1 ; try rfl
  dsimp [inverseFourth]
  field_simp
  ; ring

lemma psi_hessian_center (w : ℂ) (i j : Fin 3) :
    complexHessian (fun q : Ambient => psi q.1) (0,w) i j = horizontalIdentity i j := by
  rw [show (fun q : Ambient => psi q.1) =
    (fun q : Ambient => -Real.log (1 - ‖q.1‖ ^ 2)) by rfl]
  rw [complexHessian_negLogOneSub]
  · simp only [complexHessian_base_norm_sq, dz_base_norm_sq, dbar_base_norm_sq]
    simp [horizontalIdentity]
  · exact (contDiff_norm_sq ℂ).contDiffAt.comp _ contDiffAt_fst
  · simp

lemma psi_third_center (w : ℂ) (a c d : Fin 3) :
    dz (fun q => complexHessian (fun r : Ambient => psi r.1) q c d) (0,w) a = 0 := by
  have hh := dz_complexHessian_real_comp
    (s := fun q : Ambient => ‖q.1‖ ^ 2)
    (ρ₀ := fun y => -Real.log (1-y)) (ρ₁ := fun y => (1-y)⁻¹)
    (ρ₂ := fun y => (1-y)⁻¹ ^ 2) (ρ₃ := inverseCube)
    ((contDiff_norm_sq ℂ).contDiffAt.comp (0,w) contDiffAt_fst)
    (V := Iio 1) isOpen_Iio (by simp)
    (fun y hy => negLogOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => by simpa only [inv_pow] using invOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => inverseSquare_hasDerivAt (ne_of_gt (sub_pos.mpr hy))) a c d
  change dz (fun q => complexHessian (fun r : Ambient => -Real.log (1-‖r.1‖^2)) q c d) (0,w) a = _
  erw [hh]
  simp only [dz_dz_base_norm_sq]
  simp only [complexHessian_base_norm_sq, dz_base_norm_sq, dbar_base_norm_sq]
  simp [dz]

lemma psi_fourth_center (w : ℂ) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (fun v : Ambient => psi v.1) r c d) q a) (0,w) b =
      horizontalIdentity a b * horizontalIdentity c d + horizontalIdentity c b * horizontalIdentity a d := by
  have hs : ContDiffAt ℝ 4 (fun q : Ambient => ‖q.1‖ ^ 2) (0,w) :=
    (contDiff_norm_sq ℂ).contDiffAt.comp (0,w) contDiffAt_fst
  have hh := dbar_dz_complexHessian_real_comp
    (s := fun q : Ambient => ‖q.1‖ ^ 2)
    (ρ₀ := fun y => -Real.log (1-y)) (ρ₁ := fun y => (1-y)⁻¹)
    (ρ₂ := fun y => (1-y)⁻¹ ^ 2) (ρ₃ := inverseCube) (ρ₄ := inverseFourth)
    hs (V := Iio 1) isOpen_Iio (by simp)
    (fun y hy => negLogOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => by simpa only [inv_pow] using invOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => inverseSquare_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => inverseCube_hasDerivAt (ne_of_gt (sub_pos.mpr hy))) a b c d
  change dbar (fun q => dz (fun r => complexHessian (fun v : Ambient => -Real.log (1-‖v.1‖^2)) r c d) q a) (0,w) b = _
  erw [hh]
  erw [dbar_dz_real_eq_hessian (hs.of_le (by norm_num)) a b,
    dbar_dz_real_eq_hessian (hs.of_le (by norm_num)) c b]
  simp only [dz_dz_base_norm_sq]
  simp only [complexHessian_base_norm_sq, dz_base_norm_sq, dbar_base_norm_sq]
  simp [horizontalIdentity, dz, dbar]

end PinchedHartogs

end

end OAI
