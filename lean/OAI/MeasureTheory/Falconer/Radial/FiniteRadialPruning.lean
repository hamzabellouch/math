import OAI.MeasureTheory.Falconer.Radial.MultilevelRadialPruning
import OAI.MeasureTheory.Falconer.Angular.MultiscaleCapMass
import OAI.MeasureTheory.Falconer.Measures.PairCorePruning

namespace OAI

/-! # Finite radial pruning from actual parent-cell tests -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem finite_radial_pruning (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℕ) (hJ : 0 < J) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d))
    (parent : ℕ → ι → ι) (c : ℕ → ι → Space d)
    (r D W diam : ℕ → ℝ) (Bs Bp capRadius : ℝ) (F K t : ℕ → ℝ≥0∞)
    (P S : Set (Space d)) (hP : MeasurableSet P) (hS : MeasurableSet S)
    (hPfull : ν Pᶜ = 0) (hSfull : μ Sᶜ = 0)
    (hPb : ∀ x ∈ P, ‖x‖ ≤ Bp) (hSb : ∀ z ∈ S, ‖z‖ ≤ Bs)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hcover : ∀ j ≤ J, ∀ z ∈ S, ∃ i ∈ I j, z ∈ Q j i)
    (hgeom : ∀ j < J, ∀ i ∈ I j, ∀ z ∈ Q j i, ‖z-c j i‖ ≤ D j ∧ ‖z‖ ≤ Bs)
    (hfar : ∀ j < J, D j < r j)
    (hparent : ∀ j < J, ∀ i ∈ I (j+1), parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ diam j)
    (hwidth : ∀ j < J, diam j+2*(Bs+Bp)*capRadius ≤ W j)
    (hball : ∀ j < J, ∀ i ∈ I j, ν (ball (c j i) (r j)) ≤ K j)
    (htrouble : ∀ j < J, ∀ i ∈ I j,
      ((ProbabilityTheory.cond μ (Q j i)).prod ν)
        (troublesomePair (ProbabilityTheory.cond μ (Q j i)) (c j i) (r j) (D j) Bs (W j) (F j)) ≤ t j)
    (θ : ℝ≥0∞) (hθ : 0 < θ) (hθtop : θ ≠ ∞) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (ν.prod μ) Gᶜ ≤ (∑ j ∈ Finset.range J, (K j+t j))+(J+1:ℝ≥0∞)*θ ∧
      ∀ x u : Space d,
        μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ capRadius} ≤
          ∏ j ∈ Finset.range J, θ⁻¹*F j := by
  let G₀ := radialGoodPairs μ J I Q c r D W Bs F ∩ (P ×ˢ S)
  have hG₀ : MeasurableSet G₀ :=
    (radialGoodPairs_measurable μ J I Q c r D W Bs F (fun j hj => hQ j hj.le)).inter (hP.prod hS)
  let G := G₀ \ multiscaleFiberBad μ G₀ Q I θ J
  have hG : MeasurableSet G := hG₀.diff
    (multiscaleFiberBad_measurable μ G₀ hG₀ Q I θ J hQ)
  refine ⟨G,hG,?_,?_⟩
  · have hb := radial_good_pairs_cost μ ν J I Q c r D W Bs F K t
      (fun j hj => hQ j hj.le) hpos (fun j hj => hdisj j hj.le) hball htrouble
    have hc := pair_core_restriction_cost ν μ (radialGoodPairs μ J I Q c r D W Bs F)
      P S hPfull hSfull
    have hd := density_pruned_pair_cost ν μ G₀ hG₀ Q I J θ hQ hdisj
    simp only [measure_univ,mul_one] at hb hd
    exact hd.trans (add_le_add (hc.trans hb) le_rfl)
  · intro x u
    have hbound : ∀ z, (x,z) ∈ G₀ → ‖z-x‖ ≤ Bs+Bp := by
      intro z hz
      exact (norm_sub_le z x).trans (add_le_add (hSb z hz.2.2) (hPb x hz.2.1))
    have hne : ∀ z, (x,z) ∈ G₀ → z ≠ x := by
      intro z hz he
      obtain ⟨i,hi,hzi⟩ := hcover 0 (Nat.zero_le _) z hz.2.2
      have hbad : (z,x) ∉ levelRadialBad μ (I 0) (Q 0) (c 0) (r 0) (D 0) Bs (W 0) (F 0) := by
        intro hh
        exact hz.1 (mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨Finset.mem_range.mpr hJ,hh⟩⟩)
      have hn : (z,x) ∉ nearPinPairs (I 0) (Q 0) (c 0) (r 0) := fun h => hbad (Or.inl h)
      have hs := distance_of_not_nearPinPairs (I 0) (Q 0) (c 0) (r 0) hn hi hzi
      have hh := (hgeom 0 hJ i hi z hzi).1
      rw [he] at hh
      have hs' : r 0 ≤ ‖x-c 0 i‖ := by simpa only [dist_eq_norm] using hs
      exact (not_le_of_gt (hfar 0 hJ)) (hs'.trans hh)
    have hlocal : ∀ j < J, ∀ p ∈ I j, ∀ q ∈ Q j p, (x,q) ∈ G₀ → q ≠ x →
        μ (Q j p ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤
          diam j+2*(Bs+Bp)*capRadius}) ≤ F j*μ (Q j p) := by
      intro j hj p hp q hqp hq _
      have ht := original_tube_test_of_radial_good μ J I Q c r D W Bs F hq.1 hj (hfar j hj) hp
        (hQ j hj.le) hqp (hgeom j hj p hp q hqp).1 (hgeom j hj p hp q hqp).2
      apply (measure_mono ?_).trans ht
      intro y hy
      exact ⟨hy.1,hy.2.trans (hwidth j hj)⟩
    have hm := multiscale_physical_cap_mass μ G₀ hG₀ Q I parent J x u capRadius (Bs+Bp) diam θ F
      hθ hθtop hQ hdisj hparent hdiam hbound hne hlocal
      (fun z hz => hcover J le_rfl z hz.1.1.2.2)
    simpa only [retainedRadialCap, G, measure_univ,mul_one] using hm

end Falconer

end OAI
