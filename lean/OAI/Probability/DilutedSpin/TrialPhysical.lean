import OAI.Probability.DilutedSpin.FiniteHierarchyDense

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped Topology BigOperators NNReal
local instance trialPhysicalMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance trialPhysicalBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma trial_edge_lipschitz {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith 1 (fun θ : Interaction p => trialLog r ζ m (fun x => Real.log (edge θ x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ θ'
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using trial_edge_stability r θ θ' m hm ζ

lemma trial_site_lipschitz {p k : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith (k+1) (fun z : (Fin k → InteractionSample p) × ℝ => trialLog r ζ m (siteLog z.1 z.2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq]
  have h1 : |z.2-w.2|≤dist z w := by
    change |z.2-w.2|≤ max (dist z.1 w.1) (dist z.2 w.2)
    simpa only [Real.dist_eq] using le_max_right (dist z.1 w.1) (dist z.2 w.2)
  have h2 : ∑ j,‖(z.1 j).1-(w.1 j).1‖≤(k:ℝ)*dist z w := by
    calc
      _ ≤ ∑ j : Fin k,dist z w := Finset.sum_le_sum (fun j _ => by
        rw [← dist_eq_norm]
        exact (show dist (z.1 j).1 (w.1 j).1≤dist (z.1 j) (w.1 j) from le_max_left _ _).trans
          ((dist_le_pi_dist z.1 w.1 j).trans (show dist z.1 w.1≤dist z w from le_max_left _ _)))
      _ = _ := by simp
  have h := trial_site_stability r z.1 w.1 z.2 w.2 m hm ζ
  push_cast
  nlinarith

lemma trial_edge_bound {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (θ : Interaction p) :
    |trialLog r ζ m (fun x => Real.log (edge θ x))|≤‖θ‖ :=
  (trialLog_continuous_bound r _ (continuous_log_edge θ) (log_edge_bound θ) m hm).2 ζ

lemma trial_site_bound {p k : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) (h : ℝ) :
    |trialLog r ζ m (siteLog θ h)|≤|h|+∑ j,‖(θ j).1‖ :=
  (trialLog_continuous_bound r _ (continuous_siteLog θ h) (siteLog_bound θ h) m hm).2 ζ

end DilutedSpinGlass

end

end OAI
