import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialSlices
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceContDiffPartialDInfty
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpace

namespace OAI

noncomputable section
namespace VelocityDetection.TimeBlocks
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Family where
  term : ℕ → ℝ → Coord n → E
  smooth : ∀ k, ContDiff ℝ ∞ (uncurry (term k))
  before : ∀ (k : ℕ) (t : ℝ), t ≤ (k:ℝ)+1 → term k t = 0
  after : ∀ (k : ℕ) (t : ℝ), (k:ℝ)+2 ≤ t → term k t = 0

end VelocityDetection.TimeBlocks
end

noncomputable section
namespace VelocityDetection.TimeBlocks
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : Family (n := n) (E := E))

def total (t : ℝ) (X : Coord n) : E := ∑' k : ℕ, F.term k t X

def finiteSum (L : ℕ) (t : ℝ) (X : Coord n) : E := ∑ k ∈ Finset.range L, F.term k t X

theorem eq_finite {L : ℕ} {t : ℝ} (ht : t ≤ (L:ℝ)+1) : total F t = finiteSum F L t := by
  funext X
  apply tsum_eq_sum
  intro k hk
  have hh : L ≤ k := by simpa using hk
  have hh' : (L:ℝ) ≤ k := by exact_mod_cast hh
  exact congrFun (F.before k t (by linarith)) X

@[fun_prop] theorem contDiff_total : ContDiff ℝ ∞ (uncurry (total F)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨L,hL⟩ := exists_nat_gt p.1
  have hh : ContDiff ℝ ∞ (uncurry (finiteSum F L)) := by
    change ContDiff ℝ ∞ (fun q : ℝ × Coord n => ∑ k ∈ Finset.range L, F.term k q.1 q.2)
    exact ContDiff.sum (fun k _ => F.smooth k)
  apply hh.contDiffAt.congr_of_eventuallyEq
  have hv : ∀ᶠ q : ℝ × Coord n in 𝓝 p, q.1 < L :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hL
  exact hv.mono (fun q hq => congrFun (eq_finite F (by linarith : q.1 ≤ (L:ℝ)+1)) q.2)

theorem at_rest {t : ℝ} (ht : t ≤ 1) : total F t = 0 := by
  rw [eq_finite F (L := 0) (by simpa using ht)]
  funext X
  change (∑ k ∈ Finset.range 0, F.term k t X) = 0
  simp only [Finset.range_zero,Finset.sum_empty]

theorem eq_term (k : ℕ) {t : ℝ} (ht : t ∈ Icc ((k:ℝ)+1) ((k:ℝ)+2)) :
    total F t = F.term k t := by
  funext X
  apply tsum_eq_single k
  intro j hj
  rcases lt_or_gt_of_ne hj with h | h
  · have hh : (j:ℝ)+1 ≤ k := by exact_mod_cast h
    exact congrFun (F.after j t (by linarith [ht.1])) X
  · have hh : (k:ℝ)+1 ≤ j := by exact_mod_cast h
    exact congrFun (F.before j t (by linarith [ht.2])) X

theorem support {K : Set (Coord n)} (hs : ∀ k t X, F.term k t X ≠ 0 → X ∈ K) :
    ∀ t X, total F t X ≠ 0 → X ∈ K := by
  intro t X h
  obtain ⟨L,hL⟩ := exists_nat_gt t
  rw [congrFun (eq_finite F (by linarith : t ≤ (L:ℝ)+1)) X] at h
  obtain ⟨k,_,hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact hs k t X hk

theorem periodic (hp : ∀ k t, FactorsThrough (F.term k t) PeriodicSpace.cover) (t : ℝ) :
    FactorsThrough (total F t) PeriodicSpace.cover := by
  intro X Y hXY
  exact tsum_congr (fun k => hp k t hXY)

end VelocityDetection.TimeBlocks
end

noncomputable section
namespace VelocityDetection.TimeBlocks
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SpatialCalculus

theorem slice_derivative_congr {n : ℕ} {f g : ScalarField n} {t : ℝ} (h : f t = g t)
    (i : Fin n) : spatialD i f t = spatialD i g t := by
  funext X
  change partialD i (f t) X = partialD i (g t) X
  rw [h]

theorem slice_advection_congr {n : ℕ} (a : VectorField n) {f g : ScalarField n} {t : ℝ}
    (h : f t = g t) : advection a f t = advection a g t := by
  funext X
  simp only [advection,slice_derivative_congr h]

theorem advection_zero {n : ℕ} (a : VectorField n) {f : ScalarField n} {t : ℝ}
    (h : f t = 0) : advection a f t = 0 := by
  rw [slice_advection_congr a (g := fun _ _ => 0) h]
  funext X
  simp only [advection,spatialD,deriv_const,mul_zero,Finset.sum_const_zero,Pi.zero_apply]

theorem spatialD_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ScalarField n)
    (hf : ∀ k ∈ s, ∀ t, Differentiable ℝ (f k t)) (i : Fin n) :
    spatialD i (fun t X => ∑ k ∈ s, f k t X) = fun t X => ∑ k ∈ s, spatialD i (f k) t X := by
  funext t X
  exact partialD_sum s (fun k => f k t) (fun k hk => hf k hk t) i X

theorem laplacian_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ScalarField n)
    (hf : ∀ k ∈ s, ContDiff ℝ ∞ (uncurry (f k))) :
    laplacian (fun t X => ∑ k ∈ s, f k t X) = fun t X => ∑ k ∈ s, laplacian (f k) t X := by
  have hs : ∀ k ∈ s, ∀ t, Differentiable ℝ (f k t) :=
    fun k hk t => ((hf k hk).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hd (i : Fin n) : ∀ k ∈ s, ∀ t, Differentiable ℝ ((spatialD i (f k)) t) :=
    fun k hk t => ((TailSpace.Jets.contDiff_uncurry_spatialD (hf k hk) i).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  funext t X
  simp only [laplacian,spatialD_sum s f hs]
  simp only [spatialD_sum s (fun k => spatialD _ (f k)) (hd _)]
  exact Finset.sum_comm

theorem advection_sum {n : ℕ} {ι : Type*} (a : VectorField n) (s : Finset ι) (f : ι → ScalarField n)
    (hf : ∀ k ∈ s, ∀ t, Differentiable ℝ (f k t)) :
    advection a (fun t X => ∑ k ∈ s, f k t X) = fun t X => ∑ k ∈ s, advection a (f k) t X := by
  funext t X
  simp only [advection,spatialD_sum s f hf,Finset.mul_sum]
  exact Finset.sum_comm

end VelocityDetection.TimeBlocks
end

end OAI
