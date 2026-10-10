import OAI.Probability.SpanningForest.GraphTreePosterior
import OAI.Probability.SpanningForest.CanonicalDrift

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.GraphTreePosterior

def innerMean (G : GraphCode)
    (e : EdgeCode) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) : ℝ :=
  CanonicalDrift.outerLimit
    (fun m (q : ℝ × (EdgeCode → ℝ)) => finiteBallMean G e n m q.1 q.2) (t, y)

def drift (G : GraphCode)
    (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) : ℝ :=
  CanonicalDrift.outerLimit
    (fun n (q : ℝ × (EdgeCode → ℝ)) => innerMean G e n q.1 q.2) (t, y)

theorem innerMean_mem_Icc (G : GraphCode)
    (e : EdgeCode) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    innerMean G e n t y ∈ Set.Icc (0 : ℝ) 1 :=
  CanonicalDrift.outerLimit_mem_Icc
    (b := fun m (q : ℝ × (EdgeCode → ℝ)) => finiteBallMean G e n m q.1 q.2)
    (fun m q => finiteBallMean_mem_Icc G e n m q.1 q.2) (t, y)

theorem drift_mem_Icc (G : GraphCode)
    (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) :
    drift G t y e ∈ Set.Icc (0 : ℝ) 1 :=
  CanonicalDrift.outerLimit_mem_Icc
    (b := fun n (q : ℝ × (EdgeCode → ℝ)) => innerMean G e n q.1 q.2)
    (fun n q => innerMean_mem_Icc G e n q.1 q.2) (t, y)

theorem measurable_innerMean (e : EdgeCode) (n : ℕ) :
    Measurable (fun q : GraphCode ×
        (ℝ × (EdgeCode → ℝ)) => innerMean q.1 e n q.2.1 q.2.2) := by
  exact CanonicalDrift.measurable_outerLimit (fun m => measurable_finiteBallMean e n m)

theorem measurable_drift (e : EdgeCode) :
    Measurable (fun q : GraphCode ×
        (ℝ × (EdgeCode → ℝ)) => drift q.1 q.2.1 q.2.2 e) := by
  exact CanonicalDrift.measurable_outerLimit (fun n => measurable_innerMean e n)

theorem innerMean_eq_of_tendsto {G : GraphCode}
    (e : EdgeCode) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) {a : ℝ}
    (h : Tendsto (fun m => finiteBallMean G e n m t y) atTop (nhds a)) :
    innerMean G e n t y = a := CanonicalDrift.outerLimit_eq_of_tendsto h

theorem drift_response_of_finite {G : GraphCode}
    (e : EdgeCode) (t : ℝ) (y z : EdgeCode → ℝ) {d : ℝ}
    (h : ∀ n m, |finiteBallMean G e n m t y - finiteBallMean G e n m t z| ≤ d) :
    |drift G t y e - drift G t z e| ≤ d := by
  apply CanonicalDrift.abs_outerLimit_sub_le
    (b := fun n (q : ℝ × (EdgeCode → ℝ)) => innerMean G e n q.1 q.2)
    (x := (t, y)) (y := (t, z))
    (fun n q => innerMean_mem_Icc G e n q.1 q.2)
  intro n
  exact CanonicalDrift.abs_outerLimit_sub_le
    (b := fun m (q : ℝ × (EdgeCode → ℝ)) => finiteBallMean G e n m q.1 q.2)
    (x := (t, y)) (y := (t, z))
    (fun m q => finiteBallMean_mem_Icc G e n m q.1 q.2) (h n)

theorem finiteBallMean_of_not_adj {G : GraphCode}
    (e : EdgeCode) (he : ¬ Adj G e.1.1 e.1.2) (n m : ℕ)
    (t : ℝ) (y : EdgeCode → ℝ) : finiteBallMean G e n m t y = 0 := by
  apply mean_of_not_mem
  intro hmem
  exact he ((mem_inducedCode_edges G (edgeBallCode G m e) e.1).mp hmem).2.2.2

theorem drift_of_not_adj {G : GraphCode}
    (e : EdgeCode) (he : ¬ Adj G e.1.1 e.1.2) (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e = 0 := by
  simp only [drift, innerMean, CanonicalDrift.outerLimit,
    finiteBallMean_of_not_adj e he, limsup_const]

theorem measurable_drift_joint :
    Measurable (fun q : (GraphCode × (ℝ × (EdgeCode → ℝ))) × EdgeCode =>
      drift q.1.1 q.1.2.1 q.1.2.2 q.2) :=
  measurable_from_prod_countable_left (fun e => measurable_drift e)

theorem measurable_drift_fixed (G : GraphCode) (e : EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => drift G q.1 q.2 e) := by
  apply CanonicalDrift.measurable_outerLimit
    (b := fun n (q : ℝ × (EdgeCode → ℝ)) => innerMean G e n q.1 q.2)
  intro n
  apply CanonicalDrift.measurable_outerLimit
    (b := fun m (q : ℝ × (EdgeCode → ℝ)) => finiteBallMean G e n m q.1 q.2)
  intro m
  exact measurable_mean (Intrinsic.exhaustion G e m) e (edgeCodes (Intrinsic.exhaustion G e n))

theorem abs_drift_le_one (G : GraphCode) (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) :
    |drift G t y e| ≤ 1 := by
  obtain ⟨h0, h1⟩ := drift_mem_Icc G t y e
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem finiteBallMean_congr_on_edges {G : GraphCode} (y z : EdgeCode → ℝ)
    (h : ∀ f, Adj G f.1.1 f.1.2 → y f = z f) (e : EdgeCode) (n m : ℕ) (t : ℝ) :
    finiteBallMean G e n m t y = finiteBallMean G e n m t z := by
  apply mean_congr_field
  intro f hf
  apply h f
  exact ((mem_inducedCode_edges G (edgeBallCode G n e) f.1).mp
    ((mem_edgeCodes (Intrinsic.exhaustion G e n) f).mp hf)).2.2.2

theorem drift_congr_on_edges {G : GraphCode} (y z : EdgeCode → ℝ)
    (h : ∀ f, Adj G f.1.1 f.1.2 → y f = z f) (e : EdgeCode) (t : ℝ) :
    drift G t y e = drift G t z e := by
  simp only [drift, innerMean, CanonicalDrift.outerLimit,
    finiteBallMean_congr_on_edges y z h]

end Problem336.GraphTreePosterior

end

end OAI
