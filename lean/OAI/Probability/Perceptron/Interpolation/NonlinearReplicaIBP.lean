import Mathlib
import OAI.Probability.Perceptron.Variational.BoundedGibbsDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma bounded_gaussian_replica_coordinate_ibp {m n : ℕ} (i : Fin (m+1))
    {H H' : (Fin (m+1) → ℝ) → S → ℝ}
    {F F' : (Fin (m+1) → ℝ) → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ g x, |H g x| ≤ A) (hHB : ∀ g x, |H' g x| ≤ B)
    (hFC : ∀ g x, |F g x| ≤ C) (hFD : ∀ g x, |F' g x| ≤ D)
    (hdH : ∀ g t x, HasDerivAt (fun u => H (i.insertNth u g) x) (H' (i.insertNth t g) x) t)
    (hdF : ∀ g t x, HasDerivAt (fun u => F (i.insertNth u g) x) (F' (i.insertNth t g) x) t) :
    (∫ g, g i * gibbsReplicaMean μ (H g) n (F g)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
        (fun x => replicaPotential (H' g) n x*F g x+F' g x) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => H' g (x 0)*F g (fun j => x j.succ))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hr (J : (Fin (m+1) → ℝ) → S → ℝ)
      (hJ : Measurable (Function.uncurry J)) :
      Measurable (Function.uncurry (fun g => replicaPotential (J g) n)) := by
    change Measurable (fun p : (Fin (m+1) → ℝ)×(Fin n → S) => ∑ j : Fin n, J p.1 (p.2 j))
    exact Finset.measurable_sum _ fun j _ => hJ.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have he := bounded_gaussian_gibbs_coordinate_ibp (Measure.pi (fun _ : Fin n => μ)) i
    (hr H hH) (hr H' hH') hF hF' (by positivity) (by positivity) hC hD
    (fun g => replicaPotential_bound (hHA g) n)
    (fun g => replicaPotential_bound (hHB g) n) hFC hFD
    (fun g t x => HasDerivAt.fun_sum fun j _ => hdH g t (x j)) hdF
  refine he.trans ?_
  apply integral_congr_ae
  filter_upwards [] with g
  have hm : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  have hm' : Measurable (H' g) := hH'.comp (measurable_const.prodMk measurable_id)
  have fm : Measurable (F g) := hF.comp (measurable_const.prodMk measurable_id)
  rw [tilt_replica_sum μ hm hm' hA (hHA g) (hHB g) n 1]
  simp only [gibbsReplicaMean]
  rw [tilt_replica_new_product μ hm hm' fm hA (hHA g) (hHB g) (hFC g) 1]
  change _ - _ * ((n:ℝ)*_) = _ - (n:ℝ)*(_*_)
  ring

lemma nonlinear_pattern_replica_coordinate_ibp {m n : ℕ} (i : Fin (m+1)) (j : Fin n)
    (f : Jet3) {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {U : (Fin n → S) → ℝ}
    (hv : ∀ l, Measurable (v l)) (hh : Measurable h) (hU : Measurable U)
    {A C D : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhA : ∀ x, |h x| ≤ A) (hvC : ∀ l x, |v l x| ≤ C) (hUD : ∀ x, |U x| ≤ D) :
    let b := gaussianField (m+1) v
    let H := fun g x => h x+f.f (b g x)
    (∫ g, g i*gibbsReplicaMean μ (H g) n (fun x => f.d1 (b g (x j))*U x)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
        (fun x => ((∑ l, f.d1 (b g (x l))*v i (x l))*f.d1 (b g (x j))+
          f.d2 (b g (x j))*v i (x j))*U x) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => f.d1 (b g (x 0))*v i (x 0)*
          (f.d1 (b g (x j.succ))*U (fun l => x l.succ)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let b := gaussianField (m+1) v
  let H := fun g x => h x+f.f (b g x)
  let H' := fun g x => f.d1 (b g x)*v i x
  let F := fun g (x : Fin n → S) => f.d1 (b g (x j))*U x
  let F' := fun g (x : Fin n → S) => f.d2 (b g (x j))*v i (x j)*U x
  have hb : Measurable (Function.uncurry b) := gaussianField_measurable hv
  have hb' : Measurable (fun p : (Fin (m+1) → ℝ)×(Fin n → S) => b p.1 (p.2 j)) :=
    hb.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hHm : Measurable (Function.uncurry H) :=
    (hh.comp measurable_snd).add (f.f.continuous.measurable.comp hb)
  have hH'm : Measurable (Function.uncurry H') :=
    (f.d1.continuous.measurable.comp hb).mul ((hv i).comp measurable_snd)
  have hFm : Measurable (Function.uncurry F) :=
    (f.d1.continuous.measurable.comp hb').mul (hU.comp measurable_snd)
  have hF'm : Measurable (Function.uncurry F') :=
    ((f.d2.continuous.measurable.comp hb').mul
      ((hv i).comp ((measurable_pi_apply j).comp measurable_snd))).mul (hU.comp measurable_snd)
  have hHA (g x) : |H g x| ≤ A+‖f.f‖ :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (f.f.norm_coe_le_norm _))
  have hHB (g x) : |H' g x| ≤ ‖f.d1‖*C := by
    dsimp only [H']
    rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i x) (abs_nonneg _) (norm_nonneg _)
  have hFC (g x) : |F g x| ≤ ‖f.d1‖*D := by
    dsimp only [F]
    rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hUD x) (abs_nonneg _) (norm_nonneg _)
  have hFD (g x) : |F' g x| ≤ ‖f.d2‖*C*D := by
    dsimp only [F']
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (f.d2.norm_coe_le_norm _) (hvC i _)
      (abs_nonneg _) (norm_nonneg _)) (hUD _) (abs_nonneg _) (by positivity)
  have hdH (g t x) : HasDerivAt (fun s => H (i.insertNth s g) x)
      (H' (i.insertNth t g) x) t := by
    dsimp [H,H',b]
    simp_rw [gaussianField_insertNth]
    convert! ((f.has1 _).comp t (((hasDerivAt_id t).mul_const (v i x)).add_const
      (gaussianField m (fun l => v (i.succAbove l)) g x))).const_add (h x) using 1
    simp only [one_mul,id_eq]
  have hdF (g t x) : HasDerivAt (fun s => F (i.insertNth s g) x)
      (F' (i.insertNth t g) x) t := by
    dsimp [F,F',b]
    simp_rw [gaussianField_insertNth]
    convert! (((f.has2 _).comp t (((hasDerivAt_id t).mul_const (v i (x j))).add_const
      (gaussianField m (fun l => v (i.succAbove l)) g (x j)))).mul_const (U x)) using 1
    simp only [one_mul,id_eq]
  have he := bounded_gaussian_replica_coordinate_ibp μ i hHm hH'm hFm hF'm
    (by positivity) (by positivity) (by positivity) (by positivity) hHA hHB hFC hFD hdH hdF
  convert! he using 1
  apply integral_congr_ae
  filter_upwards [] with g
  congr 2
  funext x
  dsimp only [H', F, F', replicaPotential, b]
  ring
end SphericalPerceptronFreeEnergy
end

end OAI
