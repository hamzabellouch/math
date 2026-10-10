import OAI.Probability.FreeIsing.Trees.PathResponse

namespace OAI

noncomputable section

namespace Problem367.TreePathResponse

theorem expectation_update_field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D)
    (f : (D → IsingSpin) → ℝ) (t : ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta (Function.update h v (h v + t)) D
        (extendFiniteSpin D eta)) f =
    FinitePosterior.mean
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (extendFiniteSpin D eta v)) f t := by
  classical
  simp only [LeafGibbs.expectation, GibbsLeaf.energy_update_field beta h D hv,
    FinitePosterior.mean, FinitePosterior.weight, FinitePosterior.partition]

theorem hasDerivAt_mean_coordinate {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (u : TreeVertex d) {v : TreeVertex d}
    (hv : v ∈ D) (t : ℝ) :
    HasDerivAt (fun s => mean beta (Function.update h v (h v + s)) D u)
      (covariance beta (Function.update h v (h v + t)) D u v) t := by
  classical
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .pos⟩
  simpa only [mean, covariance, LeafGibbs.covariance,
    expectation_update_field beta h hv] using
    FinitePosterior.hasDerivAt_mean
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (extendFiniteSpin D eta v))
      (fun eta => spinSign (extendFiniteSpin D eta u)) t

def field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (u : TreeVertex d) : ℝ :=
  Real.artanh (mean beta h D u)

theorem hasDerivAt_field_coordinate {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {u v : TreeVertex d}
    (hu : u ∈ D) (hv : v ∈ D) (t : ℝ) :
    HasDerivAt (fun s => field beta (Function.update h v (h v + s)) D u)
      (response beta (Function.update h v (h v + t)) D u v) t := by
  have ha := hasDerivAt_artanh_interval
    (mean_mem_Ioo beta (Function.update h v (h v + t)) hu)
  have hd := ha.comp t (hasDerivAt_mean_coordinate beta h u hv t)
  convert! hd using 1
  unfold response
  ring

theorem lipschitzWith_root_field_coordinate {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    LipschitzWith
      ⟨Real.tanh beta ^ v.1.length, pow_nonneg (tanh_nonneg_of_beta_nonneg hbeta) _⟩
      (fun t => field beta (Function.update h v (h v + t)) D (ConnectedHull.root d)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro t
    exact (hasDerivAt_field_coordinate beta h hr hv t).differentiableAt
  · intro t
    rw [(hasDerivAt_field_coordinate beta h hr hv t).deriv]
    have hb := root_response_mem_Icc hbeta (Function.update h v (h v + t)) hD hr hv
    change |response beta (Function.update h v (h v + t)) D (ConnectedHull.root d) v| ≤ _
    rw [abs_of_nonneg hb.1]
    exact hb.2

end Problem367.TreePathResponse

end

end OAI
