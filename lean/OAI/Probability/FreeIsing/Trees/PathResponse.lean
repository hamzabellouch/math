import OAI.Probability.FreeIsing.Trees.GibbsMarginal
import OAI.Probability.FreeIsing.Trees.PathGibbs

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathResponse

def mean {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (v : TreeVertex d) : ℝ :=
  LeafGibbs.expectation
    (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
    (fun eta => spinSign (extendFiniteSpin D eta v))

def covariance {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (u v : TreeVertex d) : ℝ :=
  LeafGibbs.covariance
    (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
    (fun eta => spinSign (extendFiniteSpin D eta u))
    (fun eta => spinSign (extendFiniteSpin D eta v))

theorem path_subset {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hr : ConnectedHull.root d ∈ D)
    {v : TreeVertex d} (hv : v ∈ D) : ConnectedHull.vertices v ⊆ D := by
  intro u hu
  obtain ⟨n, hn, rfl⟩ := ConnectedHull.mem_vertices.mp hu
  apply hD.prefix_mem_of_min_length_le hr (fun x _ => Nat.zero_le _) hv
  · exact List.take_prefix n v.1
  · exact Nat.zero_le _

theorem exists_path_fields {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    ∃ y : Fin (v.1.length + 1) → ℝ, ∀ f : (Fin (v.1.length + 1) → IsingSpin) → ℝ,
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
        (fun eta => f (fun i => extendFiniteSpin D eta (ConnectedHull.path v i))) =
      FinitePathGibbs.mean beta (y 0) (PathPosterior.childFields y) v.1.length f := by
  classical
  have hsub := path_subset hD hr hv
  have hrpath : ConnectedHull.root d ∈ ConnectedHull.vertices v := by
    simpa using ConnectedHull.prefix_mem_vertices v (Nat.zero_le v.1.length)
  obtain ⟨h', hh'⟩ := tree_gibbs_marginal_of_shared_min beta
    (ConnectedHull.connected_vertices v) hD hsub hrpath
    (fun x _ => Nat.zero_le _) h
  refine ⟨fun i => h' (ConnectedHull.path v i), fun f => ?_⟩
  have hrest (eta : D → IsingSpin) :
      TreePathGibbs.assignmentEquiv v (Finset.restrict₂ (π := fun _ => IsingSpin) hsub eta) =
        (fun i => extendFiniteSpin D eta (ConnectedHull.path v i)) := by
    funext i
    exact (extendFiniteSpin_apply D eta
      ⟨ConnectedHull.path v i, hsub (TreePathGibbs.vertexEquiv v i).property⟩).symm
  calc
    _ = LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h' (ConnectedHull.vertices v)
          (extendFiniteSpin (ConnectedHull.vertices v) eta))
        (fun eta => f (TreePathGibbs.assignmentEquiv v eta)) := by
      simpa only [hrest] using hh' (fun eta => f (TreePathGibbs.assignmentEquiv v eta))
    _ = _ := TreePathGibbs.expectation_eq_path v beta h' f

theorem exists_root_covariance_product {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    ∃ z : ℕ → ℝ,
      covariance beta h D (ConnectedHull.root d) v =
        (1 - mean beta h D (ConnectedHull.root d) ^ 2) * Real.tanh beta ^ v.1.length *
          ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i) := by
  obtain ⟨y, hy⟩ := exists_path_fields beta h hD hr hv
  refine ⟨FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length, ?_⟩
  have hm := hy (fun s => spinSign (s 0))
  have hn := hy (fun s => spinSign (s (Fin.last v.1.length)))
  have hp := hy (fun s => spinSign (s 0) * spinSign (s (Fin.last v.1.length)))
  simp only [ConnectedHull.path_zero, ConnectedHull.path_last] at hm hn hp
  unfold covariance LeafGibbs.covariance mean
  rw [hp, hm, hn]
  exact FinitePathGibbs.endpointCovariance_eq beta (y 0) (PathPosterior.childFields y) v.1.length

theorem mean_mem_Ioo {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D) :
    mean beta h D v ∈ Set.Ioo (-1 : ℝ) 1 := by
  classical
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .pos⟩
  rw [mean, LeafGibbs.expectation_eq_mean_zero]
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro eta
    cases extendFiniteSpin D eta v <;> simp [spinSign]
  · refine ⟨fun _ => .neg, ?_⟩
    rw [extendFiniteSpin_apply D (fun _ => .neg) ⟨v, hv⟩]
    rfl
  · refine ⟨fun _ => .pos, ?_⟩
    rw [extendFiniteSpin_apply D (fun _ => .pos) ⟨v, hv⟩]
    rfl

theorem variance_pos {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D) :
    0 < 1 - mean beta h D v ^ 2 := by
  have hm := mean_mem_Ioo beta h hv
  have hp : 0 < (1 - mean beta h D v) * (1 + mean beta h D v) :=
    mul_pos (by linarith [hm.2]) (by linarith [hm.1])
  nlinarith

def response {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (u v : TreeVertex d) : ℝ :=
  covariance beta h D u v / (1 - mean beta h D u ^ 2)

theorem exists_root_response_product {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    ∃ z : ℕ → ℝ, response beta h D (ConnectedHull.root d) v =
      Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i) := by
  obtain ⟨z, hz⟩ := exists_root_covariance_product beta h hD hr hv
  refine ⟨z, ?_⟩
  rw [response, hz]
  have hp := (variance_pos beta h hr).ne'
  field_simp

theorem root_response_mem_Icc {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    response beta h D (ConnectedHull.root d) v ∈ Set.Icc 0 (Real.tanh beta ^ v.1.length) := by
  obtain ⟨z, hz⟩ := exists_root_response_product beta h hD hr hv
  rw [hz]
  have ht := pow_nonneg (tanh_nonneg_of_beta_nonneg hbeta) v.1.length
  have ha0 : 0 ≤ ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i) :=
    Finset.prod_nonneg fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
  have ha1 : (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)
  exact ⟨mul_nonneg ht ha0, mul_le_of_le_one_right ht ha1⟩

end Problem367.TreePathResponse

end

end OAI
