import OAI.NumberTheory.DirichletL.Descent.DescentProfiles
import OAI.NumberTheory.DirichletL.Descent.Marks

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapFourier
open InverseMoment
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def density (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ℂ := (𝓕 g) t*logPhase t xj

theorem density_norm (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ‖density g xj t‖=‖(𝓕 g) t‖ := by
  simp only [density,norm_mul,logPhase_norm,mul_one]

theorem density_moment (g : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃C:ℝ,0≤C ∧ ∀xj,
      Integrable (fun t:ℝ=>(1+‖t‖)^J*‖density g xj t‖) ∧
      (∫t:ℝ,(1+‖t‖)^J*‖density g xj t‖)≤C := by
  refine ⟨∫t:ℝ,(1+‖t‖)^J*‖(𝓕 g) t‖,integral_nonneg (fun t=>by positivity),?_⟩
  intro xj
  simp only [density_norm]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable g J,le_rfl⟩

lemma phase_neg (t x : ℝ) : logPhase (-t) x=logPhase t (-x) := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma phase_sub (t xj xc y : ℝ) :
    logPhase t xj*logPhase t xc*logPhase (-t) y=logPhase t (xj+xc-y) := by
  rw [phase_neg,←logPhase_add,←logPhase_add]
  rfl

lemma fourier_phase_integrable (g : 𝓢(ℝ,ℂ)) (x : ℝ) (a : ℂ) :
    Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x*a) := by
  have h : Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x) (volume:Measure ℝ) :=
    (𝓕 g).integrable.mul_bdd (c:=1)
    (logPhase_continuous_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>le_of_eq (logPhase_norm t x)))
  exact h.mul_const a

theorem tuple_mark_phase (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (A : Finset ι) (t : ℝ) :
    primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A =
      ∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
        logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property)) := by
  rw [primeMark_eq_tuple_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logPhase_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem overlap_tuple_separation (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  have he (p : ∀i∈I,ι) (t:ℝ) :
      (𝓕 g) t*logPhase t xj*logPhase t xc*
        ((∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
          logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property))) =
      (𝓕 g) t*logPhase t (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))*
        (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) := by
    rw [←phase_sub]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun p hp=>fourier_phase_integrable g _ _)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_mul_const]
  have hinv := schwartz_logPhase_inversion g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
  rw [mul_comm (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)]
  congr 1
  rw [hinv]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem overlap_mode_integrable (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A) := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  apply integrable_finsetSum
  intro p hp
  convert fourier_phase_integrable g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
    (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) using 1
  funext t
  rw [←phase_sub]
  ring

theorem actual_overlap_separation
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (hy : ∀i∈I,∀p∈L i,0<y i p) (A : Finset ι)
    (yj yc : ℝ) (hj : 0<yj) (hc : 0<yc) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      W (yj*yc/(∏i∈I.attach,y i.val (p i.val i.property)))) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        logPhase t (Real.log yc)*
        primeMark I L (fun i p=>a i p*logPhase (-t) (Real.log (y i p))) A := by
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  simp only [CubicReflectionKernel.logSchwartz_apply,Real.exp_sub,Real.exp_add,
    Real.exp_log hj,Real.exp_log hc,Real.exp_sum]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (hy i.val i.property (p i.val i.property)
    ((Finset.mem_pi.mp hp) i.val i.property))).symm

end SevenEighths.InverseInitialOverlapFourier

end

end OAI
