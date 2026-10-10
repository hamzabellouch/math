import OAI.Probability.FreeIsing.Cavity.Homeomorph
import OAI.Probability.FreeIsing.Energy.CoupledAttenuation
import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

def field (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) : ℝ :=
  (cavityFromSites h0 h1 (H v, H w)).1

theorem continuous_field (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Continuous (field (d := d) h0 h1) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro w
  exact continuous_fst.comp ((continuous_cavityFromSites h0 h1).comp
    ((continuous_apply v).prodMk (continuous_apply w)))

theorem measurable_field (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Measurable (field (d := d) h0 h1) :=
  (continuous_field h0 h1).measurable

theorem measurable_field_apply (h0 : 0 ≤ theta) (h1 : theta < 1)
    (v w : TreeVertex d) : Measurable (fun H => field h0 h1 H v w) :=
  (measurable_pi_apply w).comp ((measurable_pi_apply v).comp
    (measurable_field h0 h1))

theorem field_reverse (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H w v = (cavityFromSites h0 h1 (H v, H w)).2 := by
  exact congrArg Prod.fst (cavityFromSites_swap h0 h1 (H v, H w))

theorem field_spec (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H v w + cavityMessage theta (field h0 h1 H w v) = H v := by
  rw [field_reverse h0 h1 H v w]
  exact (cavityFromSites_spec h0 h1 (H v, H w)).1

theorem field_relabel (h0 : 0 ≤ theta) (h1 : theta < 1)
    (g : TreeAut d) (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 (relabel g H) v w =
      field h0 h1 H (g.toEquiv.symm v) (g.toEquiv.symm w) := rfl

theorem field_neg (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 (-H) v w = -field h0 h1 H v w := by
  exact congrArg Prod.fst (cavityFromSites_neg h0 h1 (H v, H w))

theorem field_zero (h0 : 0 ≤ theta) (h1 : theta < 1)
    (v w : TreeVertex d) : field h0 h1 0 v w = 0 := by
  have h := cavityFromSites_eq h0 h1 (z := (0, 0)) (p := (0, 0))
    (by simp)
  exact congrArg Prod.fst h

theorem field_site_bound (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    |field h0 h1 H v w - H v| ≤ Real.artanh theta :=
  (cavityFromSites_bound h0 h1 (H v, H w)).1

theorem field_sub_abs_le (h0 : 0 ≤ theta) (h1 : theta < 1)
    {H H' : TreeVertex d → ℝ} {M : ℝ} (v w : TreeVertex d)
    (hv : |H v - H' v| ≤ M) (hw : |H w - H' w| ≤ M) :
    |field h0 h1 H v w - field h0 h1 H' v w| ≤ M / (1 - theta) :=
  cavity_pair_sub_abs_le h0 h1
    (field_spec h0 h1 H v w) (field_spec h0 h1 H w v)
    (field_spec h0 h1 H' v w) (field_spec h0 h1 H' w v) hv hw

section Joining

abbrev SitePair (d : ℕ) := (TreeVertex d → ℝ) × (TreeVertex d → ℝ)

def pairRelabel (g : TreeAut d) : SitePair d → SitePair d :=
  Prod.map (relabel g) (relabel g)

theorem measurable_pairRelabel (g : TreeAut d) : Measurable (pairRelabel g) :=
  (measurable_relabel g).prodMap (measurable_relabel g)

theorem site_sub_identDistrib {ν : Measure (SitePair d)}
    (hinv : ∀ g : TreeAut d, MeasurePreserving (pairRelabel g) ν ν)
    (u v : TreeVertex d) :
    IdentDistrib (fun p : SitePair d => p.1 u - p.2 u)
      (fun p : SitePair d => p.1 v - p.2 v) ν ν := by
  obtain ⟨g, hg⟩ := exists_treeAut_map u v
  have hm (w : TreeVertex d) : Measurable (fun p : SitePair d => p.1 w - p.2 w) :=
    ((measurable_pi_apply w).comp measurable_fst).sub
      ((measurable_pi_apply w).comp measurable_snd)
  refine ⟨(hm u).aemeasurable, (hm v).aemeasurable, ?_⟩
  calc
    ν.map (fun p : SitePair d => p.1 u - p.2 u) =
        ν.map ((fun p : SitePair d => p.1 v - p.2 v) ∘ pairRelabel g) := by
      congr 1
      funext p
      simp [pairRelabel, relabel, ← hg]
    _ = (ν.map (pairRelabel g)).map (fun p : SitePair d => p.1 v - p.2 v) :=
      (Measure.map_map (hm v) (measurable_pairRelabel g)).symm
    _ = ν.map (fun p : SitePair d => p.1 v - p.2 v) := by rw [(hinv g).map_eq]

theorem integral_field_sub_sq_le {ν : Measure (SitePair d)}
    (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hinv : ∀ g : TreeAut d, MeasurePreserving (pairRelabel g) ν ν)
    (o v w : TreeVertex d)
    (hInt : Integrable (fun p : SitePair d => (p.1 o - p.2 o) ^ 2) ν) :
    (∫ p, (field h0 h1 p.1 v w - field h0 h1 p.2 v w) ^ 2 ∂ν) ≤
      (∫ p : SitePair d, (p.1 o - p.2 o) ^ 2 ∂ν) / (1 - theta) ^ 2 := by
  have hv := (site_sub_identDistrib hinv o v).sq
  have hw := (site_sub_identDistrib hinv o w).sq
  exact integral_cavity_pair_sub_sq_le h0 h1
    ((measurable_field_apply h0 h1 v w).comp measurable_fst)
    ((measurable_field_apply h0 h1 v w).comp measurable_snd)
    (hv.integrable_snd hInt) (hw.integrable_snd hInt)
    (Filter.Eventually.of_forall (fun p =>
      ⟨field_spec h0 h1 p.1 v w, field_spec h0 h1 p.1 w v,
        field_spec h0 h1 p.2 v w, field_spec h0 h1 p.2 w v⟩))
    hv.integral_eq.symm.le hw.integral_eq.symm.le

end Joining

end Problem367.CavityArray

end

end OAI
