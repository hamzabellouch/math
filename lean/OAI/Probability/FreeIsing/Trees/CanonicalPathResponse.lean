import OAI.Probability.FreeIsing.Cavity.BinaryMixture
import OAI.Probability.FreeIsing.Cavity.Homeomorph
import OAI.Probability.FreeIsing.Estimates.ChainMarginals
import OAI.Probability.FreeIsing.Trees.CoordinateResponse

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.FinitePathGibbs

theorem mean_eq_posterior_mean (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) :
    mean beta root h n f =
      FinitePosterior.mean (energy beta root h n) (fun _ => 0) f 0 := by
  unfold mean FinitePosterior.mean FinitePosterior.partition
  simp only [FinitePosterior.weight, zero_mul, add_zero]
  simp_rw [mass_eq_exp_energy, partition_eq_sum_exp, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem coordinate_mean_mem_Ioo (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (i : Fin (n + 1)) :
    mean beta root h n (fun x => spinSign (x i)) ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [mean_eq_posterior_mean]
  let : Nonempty (Fin (n + 1) → IsingSpin) := ⟨fun _ => .pos⟩
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro x
    cases x i <;> simp [spinSign]
  · exact ⟨fun _ => .neg, rfl⟩
  · exact ⟨fun _ => .pos, rfl⟩

theorem coordinate_mean_affine (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (i : Fin n) :
    mean beta root h n (fun x => spinSign (x i.succ)) =
      PosteriorChain.intercept beta (backwardField beta h n i) +
        PosteriorChain.slope beta (backwardField beta h n i) *
          mean beta root h n (fun x => spinSign (x i.castSucc)) := by
  have hh := InhomogeneousChain.coordinateMean_affine
    (fun j => PosteriorChain.transition beta (backwardField beta h n j))
    (rootLaw beta root h n) spinSign
    (fun j => PosteriorChain.intercept beta (backwardField beta h n j))
    (fun j => PosteriorChain.slope beta (backwardField beta h n j))
    (sum_rootLaw beta root h n)
    (fun j => PosteriorChain.transition_sum beta (backwardField beta h n j))
    (fun j => PosteriorChain.transition_spinMean_affine beta (backwardField beta h n j)) n i
  simpa only [InhomogeneousChain.coordinateMean, ← mass_eq_jointWeight, mean] using hh

theorem backwardField_eq_cavityFromSites {beta : ℝ} (hbeta : 0 ≤ beta)
    (root : ℝ) (h : ℕ → ℝ) (n : ℕ) (i : Fin n) :
    backwardField beta h n i =
      (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
        (Real.artanh (mean beta root h n (fun x => spinSign (x i.castSucc))),
          Real.artanh (mean beta root h n (fun x => spinSign (x i.succ))))).2 := by
  have hh := PosteriorChain.cavityFromSites_affine_mean_snd hbeta
    (backwardField beta h n i)
    (Real.artanh (mean beta root h n (fun x => spinSign (x i.castSucc))))
  rw [Real.tanh_artanh (coordinate_mean_mem_Ioo beta root h n i.castSucc),
    ← coordinate_mean_affine beta root h n i] at hh
  exact hh.symm

end Problem367.FinitePathGibbs

namespace Problem367.TreePathResponse

theorem measurable_mean {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (u : TreeVertex d) :
    Measurable (fun h : TreeVertex d → ℝ => mean beta h D u) := by
  unfold mean LeafGibbs.expectation GibbsLeaf.energy
  fun_prop

theorem measurable_field {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (u : TreeVertex d) :
    Measurable (fun h : TreeVertex d → ℝ => field beta h D u) := by
  have ha : Measurable Real.artanh := by
    unfold Real.artanh
    fun_prop
  exact ha.comp (measurable_mean beta D u)

def orientedCavity {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) (D : Finset (TreeVertex d))
    (u v : TreeVertex d) : ℝ :=
  (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (field beta h D u, field beta h D v)).2

theorem measurable_orientedCavity {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (u v : TreeVertex d) :
    Measurable (fun h : TreeVertex d → ℝ => orientedCavity hbeta h D u v) := by
  exact (measurable_cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta)
    (Real.tanh_lt_one beta)).snd.comp
      ((measurable_field beta D u).prodMk (measurable_field beta D v))

theorem root_response_eq_canonical_product {d : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    response beta h D (ConnectedHull.root d) v =
      Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
            (ConnectedHull.takeVertex v (i + 1))) := by
  obtain ⟨y, hy⟩ := exists_path_fields beta h hD hr hv
  have hmean (i : Fin (v.1.length + 1)) :
      mean beta h D (ConnectedHull.path v i) =
        FinitePathGibbs.mean beta (y 0) (PathPosterior.childFields y) v.1.length
          (fun x => spinSign (x i)) :=
    hy (fun x => spinSign (x i))
  have hback (i : ℕ) (hi : i < v.1.length) :
      FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length i =
        orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
          (ConnectedHull.takeVertex v (i + 1)) := by
    have hh := FinitePathGibbs.backwardField_eq_cavityFromSites hbeta
      (y 0) (PathPosterior.childFields y) v.1.length ⟨i, hi⟩
    rw [← hmean (Fin.castSucc ⟨i, hi⟩), ← hmean (Fin.succ ⟨i, hi⟩)] at hh
    exact hh
  have hprod :
      (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
        (FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length i)) =
      ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
        (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
          (ConnectedHull.takeVertex v (i + 1))) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hback i (Finset.mem_range.mp hi)]
  have hcov : covariance beta h D (ConnectedHull.root d) v =
      (1 - mean beta h D (ConnectedHull.root d) ^ 2) * Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
            (ConnectedHull.takeVertex v (i + 1))) := by
    rw [← hprod]
    have hm := hy (fun x => spinSign (x 0))
    have hn := hy (fun x => spinSign (x (Fin.last v.1.length)))
    have hp := hy (fun x => spinSign (x 0) * spinSign (x (Fin.last v.1.length)))
    simp only [ConnectedHull.path_zero, ConnectedHull.path_last] at hm hn hp
    unfold covariance LeafGibbs.covariance mean
    rw [hp, hm, hn]
    exact FinitePathGibbs.endpointCovariance_eq beta (y 0)
      (PathPosterior.childFields y) v.1.length
  rw [response, hcov]
  have hp := (variance_pos beta h hr).ne'
  field_simp

end Problem367.TreePathResponse

end

end OAI
