import OAI.Probability.SLE.Stochastic.PlanarCutoffStop
import OAI.Probability.SLE.Loewner.SmoothDomainExhaustion

namespace OAI

/-! A nested sequence of actual stopping times exhausts each finite exit
of a continuous planar Wiener path from an open domain. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Function
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target
namespace SmoothDomainExhaustion
variable {U : Set (ℝ×ℝ)} (e : SmoothDomainExhaustion U 0)

def stop (T : ℝ≥0) (n : ℕ) : Driver×Driver → ℝ≥0 := planarCutoffStop (e.cutoff n) T

lemma stop_stopping (T : ℝ≥0) (n : ℕ) :
    IsStoppingTime planarWienerFiltration (fun b => (e.stop T n b : WithTop ℝ≥0)) :=
  planarCutoffStop_stopping _ (e.smooth n).continuous T

lemma stop_le (T : ℝ≥0) (n : ℕ) (b : Driver×Driver) : e.stop T n b ≤ T :=
  planarCutoffStop_le _ _ _

lemma stop_mem_support (T : ℝ≥0) (n : ℕ) (b : Driver×Driver) (t : ℝ≥0)
    (ht : t ≤ e.stop T n b) : planarWiener t b∈tsupport (e.cutoff n) :=
  planarCutoffStop_in_support _ (by rw [e.based n]; exact one_ne_zero) _ _ _ ht

lemma stop_mem_domain (T : ℝ≥0) (n : ℕ) (b : Driver×Driver) (t : ℝ≥0)
    (ht : t ≤ e.stop T n b) : planarWiener t b∈U :=
  e.supported n (e.stop_mem_support T n b t ht)

lemma stop_monotone (T : ℝ≥0) (b : Driver×Driver) : Monotone (fun n => e.stop T n b) := by
  intro n m hnm
  have hh : planarCutoffHit (e.cutoff n) b ≤ planarCutoffHit (e.cutoff m) b := by
    change hittingAfter planarWiener {z | e.cutoff n z=0} 0 b ≤
      hittingAfter planarWiener {z | e.cutoff m z=0} 0 b
    apply hittingAfter_anti planarWiener 0
    intro z hz
    by_contra hn
    exact (e.increasing hnm hn) hz
  apply WithTop.coe_le_coe.mp
  change (cutoffStop _ _ _ : WithTop ℝ≥0) ≤ (cutoffStop _ _ _ : WithTop ℝ≥0)
  rw [cutoffStop_coe,cutoffStop_coe]
  exact min_le_min_right _ hh

lemma eventually_le_stop (T t : ℝ≥0) (ht : t ≤ T) (b : Driver×Driver)
    (hpath : ∀ s ≤ t, planarWiener s b∈U) : ∀ᶠ n in atTop, t ≤ e.stop T n b := by
  let K := (fun s => planarWiener s b) '' Icc 0 t
  have hK : IsCompact K := isCompact_Icc.image (planarWiener_continuous b)
  have hKU : K ⊆ U := by
    rintro z ⟨s,hs,rfl⟩
    exact hpath s hs.2
  filter_upwards [e.exhausts K hK hKU] with n hn
  apply planarCutoffStop_ge_of_nonzero _ (e.smooth n).continuous T t ht b
  intro s hs
  exact hn ⟨s,⟨zero_le,hs⟩,rfl⟩

lemma stop_tendsto_finite_exit (T τ : ℝ≥0) (hτT : τ ≤ T) (b : Driver×Driver)
    (hpath : ∀ s < τ, planarWiener s b∈U) (hexit : planarWiener τ b∉U) :
    Tendsto (fun n => e.stop T n b) atTop (𝓝 τ) := by
  have hb (n) : e.stop T n b ≤ τ := by
    have hz : e.cutoff n (planarWiener τ b)=0 := by
      by_contra hn
      exact hexit (e.supported n (subset_tsupport _ hn))
    have hh : planarCutoffHit (e.cutoff n) b ≤ (τ : WithTop ℝ≥0) :=
      hittingAfter_le_of_mem (zero_le : (0:ℝ≥0) ≤ τ) hz
    apply WithTop.coe_le_coe.mp
    change (cutoffStop _ _ _ : WithTop ℝ≥0) ≤ _
    rw [cutoffStop_coe]
    exact (min_le_left _ _).trans hh
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨t,hat,htτ⟩ := exists_between ha
    filter_upwards [e.eventually_le_stop T t (htτ.le.trans hτT) b
      (fun s hs => hpath s (hs.trans_lt htτ))] with n hn
    exact hat.trans_le hn
  · intro a ha
    exact Eventually.of_forall fun n => (hb n).trans_lt ha

end SmoothDomainExhaustion
end SLEExactGauge

end

end OAI
