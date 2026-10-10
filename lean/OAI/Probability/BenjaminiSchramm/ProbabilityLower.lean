import OAI.Probability.BenjaminiSchramm.InputReduction

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_finite_ae_of_finite_mass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V)
    (hf : (∑' y, law p {ω | Conn G ω x y}) ≠ ⊤) :
    ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
  have hi : (∫⁻ ω, clusterMass G ω x ∂law p) ≠ ⊤ := by
    rwa [lintegral_clusterMass]
  filter_upwards [ae_lt_top (measurable_clusterMass G x) hi] with ω hω
  by_contra hinf
  have hinf : (cluster G ω x).Infinite := hinf
  obtain ⟨n,hn⟩ := exists_nat_gt (clusterMass G ω x).toReal
  have hvol : ω ∈ volumeEvent G x n := by
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    rw [Set.encard_eq_top hinf]
    exact le_top
  have hb := ENNReal.toReal_mono hω.ne (volume_threshold_le_clusterMass G ω x n hvol)
  rw [ENNReal.toReal_natCast] at hb
  exact (not_lt_of_ge hb) hn

theorem uniform_testSets_of_good_cost [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval)
    (hgood : ∀ x, ∃ S : Finset V, x ∈ S ∧ boundaryCost G hloc S x (p : ℝ) < 1) :
    ∃ (L : ℕ) (a : ℝ), a < 1 ∧ ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p : ℝ) ≤ a := by
  obtain ⟨O,hO⟩ := hqt
  choose S hmem hcost using hgood
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.ofNonempty : V)
    exact ⟨o,ho⟩
  let L := O.sup (fun x => (S x).card)
  let a := O.sup' hOn (fun x => boundaryCost G hloc (S x) x (p : ℝ))
  refine ⟨L,a,(Finset.sup'_lt_iff hOn).mpr (fun x _ => hcost x),?_⟩
  intro x
  obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO x
  refine ⟨(S o).map α.toEmbedding,?_,?_,?_⟩
  · simp only [Finset.mem_map,Equiv.toEmbedding_apply]
    exact ⟨o,hmem o,rfl⟩
  · simpa only [Finset.card_map] using Finset.le_sup (f := fun x => (S x).card) ho
  · rw [boundaryCost_aut G hloc hαβ]
    exact Finset.le_sup' (f := fun x => boundaryCost G hloc (S x) x (p : ℝ)) ho

theorem finite_mass_of_uniform_testSets [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (L : ℕ) (a : ℝ) (ha : a < 1)
    (htest : ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p : ℝ) ≤ a) (x : V) :
    (∑' y, law p {ω | Conn G ω x y}) ≠ ⊤ := by
  let : Encodable V := Encodable.ofCountable V
  have hrow (F : Finset V) : ∑ y ∈ F, twoPoint G p x y ≤ (L : ℝ) / (1 - a) := by
    apply le_of_tendsto (tendsto_finsetSum F (fun y _ => tendsto_domainTwoPoint G p x y))
    obtain ⟨N,hN⟩ := subset_vertexExhaustion F
    filter_upwards [eventually_ge_atTop N] with n hn
    have hFn : F ⊆ vertexExhaustion n := hN.trans (vertexExhaustion_mono hn)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hFn (fun _ _ _ => measureReal_nonneg)).trans
      (domainRow_uniform_bound G hloc p L a ha htest (vertexExhaustion n) x)
  have hs := summable_of_sum_le (twoPoint_nonneg G p x) hrow
  have he : ENNReal.ofReal (susceptibility G p x) =
      ∑' y, law p {ω | Conn G ω x y} := by
    rw [susceptibility,ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G p x) hs]
    apply tsum_congr
    intro y
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [←he]
  exact ENNReal.ofReal_ne_top

theorem exists_bad_cost_of_pc_lt [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : pc G < p) :
    ∃ x, ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (p : ℝ) := by
  by_contra! hgood
  obtain ⟨L,a,ha,htest⟩ := uniform_testSets_of_good_cost G hloc hqt p hgood
  have hfin (x : V) : ∀ᵐ ω ∂law p, (cluster G ω x).Finite :=
    cluster_finite_ae_of_finite_mass G p x
      (finite_mass_of_uniform_testSets G hloc p L a ha htest x)
  have hz : law p {ω | (infiniteClusters G ω).Nonempty} = 0 := by
    have he : {ω | (infiniteClusters G ω).Nonempty} =
        ⋃ x, {ω | (cluster G ω x).Infinite} := by
      ext ω
      simp only [infiniteClusters_nonempty_iff,Set.mem_iUnion,Set.mem_ofPred_eq]
    rw [he]
    exact measure_iUnion_null (fun x => ae_iff.mp (hfin x))
  obtain ⟨q,hq,hqp⟩ := sInf_lt_iff.mp hp
  have hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty} :=
    hq.trans_le (exists_infinite_cluster_probability_mono G hqp.le)
  rw [hz] at hpos
  exact hpos.false

theorem percolationProbability_mul_twoPoint_le [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    percolationProbability G p x * twoPoint G p x y ≤ percolationProbability G p y := by
  apply (association_infinite_conn G p x x y).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro ω ⟨hi,hc⟩
  change (cluster G ω y).Infinite
  rwa [←cluster_eq_of_conn G ω hc]

theorem percolationProbability_lower_of_bad_cost [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (r p : unitInterval)
    (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (r : ℝ)) :
    1 - Real.exp ((r : ℝ) - p) ≤ percolationProbability G p x := by
  apply infinite_cluster_probability_ge_of_escape G hloc x p
  intro Λ
  rw [←finite_escape_eq_law G hloc Λ x p]
  apply (finite_escape_probability_lower G Λ x (incidentSupport G hloc Λ)
    r p hr hrp hp ?_).2
  intro S hS hx
  rw [boundaryExpectation_eq_of_incident_subset G hloc S x _
    (incidentSupport_mono G hloc hS)]
  exact hcost S hx

theorem one_sub_exp_neg_linear (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-1) * s ≤ 1 - Real.exp (-s) := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp s) (Real.exp_pos (-s)).le
  rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  have he : Real.exp (-1) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have hl := mul_le_mul_of_nonneg_right he hs0
  nlinarith

theorem percolationProbability_linear_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (x : V) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : unitInterval, pc G < p → p < 1 →
      c * ((p : ℝ) - pc G) ≤ percolationProbability G p x := by
  obtain ⟨O,hO⟩ := hqt
  have hqt : QuasiTransitive G := ⟨O,hO⟩
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO x
    exact ⟨o,ho⟩
  have hpc0 : 0 < pc G := pc_pos G hloc hqt
  let a : ℝ := O.inf' hOn (fun o => twoPoint G (pc G) o x)
  have ha : 0 < a := (Finset.lt_inf'_iff hOn).mpr
    (fun o _ => twoPoint_pos G hconn (pc G) hpc0 o x)
  refine ⟨a * Real.exp (-1) / 2,by positivity,fun p hp hp1 => ?_⟩
  have hpR : (pc G : ℝ) < (p : ℝ) := hp
  let r : unitInterval := ⟨((p : ℝ) + pc G) / 2,
    ⟨by linarith [p.2.1,(pc G).2.1],by linarith [p.2.2,(pc G).2.2]⟩⟩
  have hrc : pc G < r := by change (pc G : ℝ) < ((p : ℝ) + pc G) / 2; linarith only [hpR]
  have hrp : r < p := by change ((p : ℝ) + pc G) / 2 < (p : ℝ); linarith only [hpR]
  obtain ⟨z,hcost⟩ := exists_bad_cost_of_pc_lt G hloc hqt r hrc
  have hb := percolationProbability_lower_of_bad_cost G hloc z r p (hpc0.trans hrc) hrp hp1 hcost
  obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO z
  have hθ : 1 - Real.exp ((r : ℝ) - p) ≤ percolationProbability G p o := by
    change 1 - Real.exp ((r : ℝ) - p) ≤ (law p).real {ω | (cluster G ω (α o)).Infinite} at hb
    rw [infinite_cluster_aut G p hαβ] at hb
    exact hb
  have hτ : a ≤ twoPoint G p o x :=
    (Finset.inf'_le (f := fun o => twoPoint G (pc G) o x) ho).trans
      (twoPoint_mono G o x hp.le)
  have ht := (mul_le_mul_of_nonneg_left hτ
    (show 0 ≤ percolationProbability G p o from ENNReal.toReal_nonneg)).trans
      (percolationProbability_mul_twoPoint_le G p o x)
  let s : ℝ := (p : ℝ) - r
  have hs0 : 0 ≤ s := sub_nonneg.mpr hrp.le
  have hs1 : s ≤ 1 := by dsimp [s]; linarith [p.2.2,r.2.1]
  have hl := one_sub_exp_neg_linear s hs0 hs1
  have he : (r : ℝ) - p = -s := by dsimp [s]; ring
  rw [he] at hθ
  have hm := mul_le_mul_of_nonneg_right (hl.trans hθ) ha.le
  have hid : (Real.exp (-1) * s) * a =
      (a * Real.exp (-1) / 2) * ((p : ℝ) - pc G) := by dsimp [s,r]; ring
  rw [hid] at hm
  exact hm.trans ht

end Percolation.BenjaminiSchramm

end OAI
