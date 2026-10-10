import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ComplexMollification

namespace OAI

/-! The whole-space H=W specialization required by the two continuum
reductions. The approximation is constructed by normalized smooth convolution,
with no published density hypothesis remaining. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem complexMollification_error_tendsto {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) :
    Tendsto (fun k => ∫ x, ‖u x-complexMollification u k x‖^2) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun k => ha.trans_le (integral_nonneg (fun x => sq_nonneg _)))
  · intro a ha
    exact complexMollification_error hu ha

def mollifiedH1 {n : ℕ} (u : Coulomb.H1Vector n) (k : ℕ) : Coulomb.H1Vector n :=
  classicalH1State (fun s => complexMollification (u.value s) k)
    (fun s => (complexMollification_smooth (u.value_L2 s) k).of_le (by simp))
    (fun s => complexMollification_memLp (u.value_L2 s) k)
    (fun s a => by
      have he := complexMollification_partial (u.value_L2 s) (u.partial_L2 s a)
        (EuclideanSpace.single a 1) (u.weak_partial s a) k
      simp_rw [he]
      exact complexMollification_memLp (u.partial_L2 s a) k)

theorem mollifiedH1_gradient {n : ℕ} (u : Coulomb.H1Vector n) (k : ℕ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (mollifiedH1 u k).gradient s a x = complexMollification (u.gradient s a) k x :=
  complexMollification_partial (u.value_L2 s) (u.partial_L2 s a)
    (EuclideanSpace.single a 1) (u.weak_partial s a) k x

theorem mollifiedH1_error_tendsto {n : ℕ} (u : Coulomb.H1Vector n) :
    Tendsto (fun k => h1GraphError u (mollifiedH1 u k)) atTop (𝓝 0) := by
  have hv := tendsto_finsetSum Finset.univ (fun s _ =>
    complexMollification_error_tendsto (u.value_L2 s))
  have hg := tendsto_finsetSum Finset.univ (fun s _ =>
    tendsto_finsetSum Finset.univ (fun a _ =>
      complexMollification_error_tendsto (u.partial_L2 s a)))
  unfold h1GraphError
  simp_rw [mollifiedH1_gradient]
  simpa only [mollifiedH1,classicalH1State,Finset.sum_const_zero,add_zero] using hv.add hg

/-- Meyers–Serrin, H=W, specialized to the full Euclidean weak-H1 space,
proved here by the explicit convolution sequence. -/
theorem publishedSobolevSmoothDensity : PublishedSobolevSmoothDensity := by
  intro n u ε hε
  have he := (tendsto_order.mp (mollifiedH1_error_tendsto u)).2 ε hε
  obtain ⟨k,hk⟩ := he.exists
  refine ⟨fun s => complexMollification (u.value s) k,
    fun s => complexMollification_smooth (u.value_L2 s) k,
    fun s => complexMollification_memLp (u.value_L2 s) k,?_,hk⟩
  intro s a
  have heq := complexMollification_partial (u.value_L2 s) (u.partial_L2 s a)
    (EuclideanSpace.single a 1) (u.weak_partial s a) k
  simp_rw [heq]
  exact complexMollification_memLp (u.partial_L2 s a) k

end ContinuumCoulomb

end

end OAI
