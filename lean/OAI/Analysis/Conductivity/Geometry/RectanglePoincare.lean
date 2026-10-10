import Mathlib
import OAI.Analysis.Conductivity.Geometry.BoxEnergyPoincare

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma RectFootprint.prism_volume (Q : RectFootprint) (lo hi : ℝ) :
    volume (Q.prism lo hi)=ENNReal.ofReal (Q.xu-Q.xl)*ENNReal.ofReal (Q.yu-Q.yl)*
      ENNReal.ofReal (hi-lo) := by
  simp only [RectFootprint.prism,RectFootprint.carrier,Measure.volume_eq_prod,
    Measure.prod_prod,Real.volume_Icc]

lemma RectFootprint.prism_volume_pos (Q : RectFootprint) (lo hi : ℝ) :
    0 < volume (Q.prism lo hi) ↔ Q.xl<Q.xu ∧ Q.yl<Q.yu ∧ lo<hi := by
  rw [Q.prism_volume]
  simp only [ENNReal.mul_pos_iff,ENNReal.ofReal_pos,sub_pos]
  tauto

lemma RectFootprint.prism_real_pos (Q : RectFootprint) (lo hi : ℝ)
    (hx : Q.xl<Q.xu) (hy : Q.yl<Q.yu) (hz : lo<hi) :
    0 < volume.real (Q.prism lo hi) := by
  exact ENNReal.toReal_pos ((Q.prism_volume_pos lo hi).mpr ⟨hx,hy,hz⟩).ne'
    (Q.prism_compact lo hi).measure_ne_top

def RectFootprint.poincareConstant (Q : RectFootprint) (lo hi : ℝ) : ℝ :=
  4*((Q.xu-Q.xl)^2+(Q.yu-Q.yl)^2+(hi-lo)^2)

def RectFootprint.average (Q : RectFootprint) (lo hi : ℝ) (f : Box3 → ℝ) : ℝ :=
  boxAverage ((Q.xl,Q.yl),lo) ((Q.xu-Q.xl,Q.yu-Q.yl),hi-lo) f

lemma RectFootprint.poincareConstant_nonneg (Q : RectFootprint) (lo hi : ℝ) :
    0 ≤ Q.poincareConstant lo hi := by unfold RectFootprint.poincareConstant; positivity

theorem RectFootprint.poincare (Q : RectFootprint) (lo hi : ℝ) {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume (Q.prism lo hi) f (Q.average lo hi f) ≤
      Q.poincareConstant lo hi*(∫ z in Q.prism lo hi,cubeEnergyDensity f z) := by
  by_cases h : Q.xl<Q.xu ∧ Q.yl<Q.yu ∧ lo<hi
  · rw [Q.prism_closedBox]
    exact smooth_box_volume_poincare hf _ _ (sub_pos.mpr h.1) (sub_pos.mpr h.2.1) (sub_pos.mpr h.2.2)
  · have hz : volume (Q.prism lo hi)=0 := by
      exact nonpos_iff_eq_zero.mp (le_of_not_gt (fun hp => h ((Q.prism_volume_pos lo hi).mp hp)))
    simp [localVariance,Measure.restrict_eq_zero.mpr hz]

lemma rectangle_energy_mono {Q R : Set Box3} {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hR : IsCompact R) (hQR : Q⊆R) :
    (∫ z in Q,cubeEnergyDensity f z) ≤ ∫ z in R,cubeEnergyDensity f z := by
  exact setIntegral_mono_set ((continuous_cubeEnergyDensity hf).continuousOn.integrableOn_compact hR)
    (Filter.Eventually.of_forall (fun _ => cubeEnergyDensity_nonneg f _))
    (Filter.Eventually.of_forall (fun _ hx => hQR hx))

theorem RectFootprint.poincare_in (Q : RectFootprint) (lo hi : ℝ) {R : Set Box3}
    (hR : IsCompact R) (hQR : Q.prism lo hi⊆R) {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume (Q.prism lo hi) f (Q.average lo hi f) ≤
      Q.poincareConstant lo hi*(∫ z in R,cubeEnergyDensity f z) := by
  exact (Q.poincare lo hi hf).trans (mul_le_mul_of_nonneg_left (rectangle_energy_mono hf hR hQR)
    (Q.poincareConstant_nonneg lo hi))

open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X]

def patchCluster (Q : ℕ → Set X) : ℕ → Set X
  | 0 => Q 0
  | n+1 => patchCluster Q n ∪ Q (n+1)

omit [MeasurableSpace X] in
lemma patchCluster_mono (Q : ℕ → Set X) {n m : ℕ} (h : n ≤ m) :
    patchCluster Q n ⊆ patchCluster Q m := by
  induction h with
  | refl => exact Subset.rfl
  | @step m h ih => exact ih.trans (subset_union_left (t := Q (m+1)))

omit [MeasurableSpace X] in
lemma subset_patchCluster (Q : ℕ → Set X) (n : ℕ) : Q n ⊆ patchCluster Q n := by
  cases n with
  | zero => exact Subset.rfl
  | succ n => exact subset_union_right

def patchPoincareConstant (μ : Measure X) (Q : ℕ → Set X) (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => A 0
  | n+1 => patchPoincareConstant μ Q A n+2*A (n+1)+
    4*μ.real (Q (n+1))/μ.real (patchCluster Q n ∩ Q (n+1))*
      (patchPoincareConstant μ Q A n+A (n+1))

lemma patchPoincareConstant_nonneg (μ : Measure X) (Q : ℕ → Set X) (A : ℕ → ℝ)
    (hA : ∀ n, 0≤A n) (n : ℕ) : 0≤patchPoincareConstant μ Q A n := by
  induction n with
  | zero => exact hA 0
  | succ n ih =>
    dsimp [patchPoincareConstant]
    have hQ : 0≤μ.real (Q (n+1)) := ENNReal.toReal_nonneg
    have hO : 0≤μ.real (patchCluster Q n ∩ Q (n+1)) := ENNReal.toReal_nonneg
    have hn := hA (n+1)
    positivity

theorem connected_patch_poincare (μ : Measure X) (Q : ℕ → Set X) (A : ℕ → ℝ)
    (hA : ∀ n, 0≤A n) {f : X → ℝ} (m : ℕ → ℝ) (E : ℝ) (hE : 0≤E) (N : ℕ)
    (hfin : ∀ n≤N, μ (Q n)≠⊤)
    (hover : ∀ n<N, 0<μ.real (patchCluster Q n ∩ Q (n+1)))
    (hint : ∀ n≤N, ∀ c : ℝ, IntegrableOn (fun x => (f x-c)^2) (Q n) μ)
    (hloc : ∀ n≤N, localVariance μ (Q n) f (m n) ≤ A n*E) :
    localVariance μ (patchCluster Q N) f (m 0) ≤ patchPoincareConstant μ Q A N*E := by
  have hi : ∀ n≤N, ∀ c : ℝ, IntegrableOn (fun x => (f x-c)^2) (patchCluster Q n) μ := by
    intro n hn
    induction n with
    | zero => exact hint 0 (by omega)
    | succ n ih =>
      intro c
      exact (ih (by omega) c).union (hint (n+1) hn c)
  have hfinite : ∀ n≤N, μ (patchCluster Q n)≠⊤ := by
    intro n hn
    induction n with
    | zero => exact hfin 0 (by omega)
    | succ n ih =>
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ih (by omega),hfin (n+1) hn⟩)
        (measure_union_le _ _)
  have hall : ∀ n≤N, localVariance μ (patchCluster Q n) f (m 0) ≤ patchPoincareConstant μ Q A n*E := by
    intro n hn
    induction n with
    | zero => exact hloc 0 (by omega)
    | succ n ih =>
      exact overlap_poincare_glue μ hE (patchPoincareConstant_nonneg μ Q A hA n) (hA (n+1))
        (hfinite n (by omega)) (hfin (n+1) hn) (hover n (by omega))
        (hi n (by omega) (m 0)) (hint (n+1) hn (m (n+1))) (hint (n+1) hn (m 0))
        (ih (by omega)) (hloc (n+1) hn)
  exact hall N le_rfl

end ScalarConductivity

end

end OAI
