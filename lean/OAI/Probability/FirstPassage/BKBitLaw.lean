import OAI.Probability.FirstPassage.BKBinaryRanks
import OAI.Probability.FirstPassage.BKExponentialQuantiles

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

def dyadicRankCell (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    (x : Finset (Edge × Fin t)) : Set Ω :=
  {ω | ∀ e ∈ S, ⌊(2:ℝ)^t*Real.exp (-τ e ω)⌋₊ = dyadicRank t x e}

lemma measurableSet_dyadicRankCell (hτ : ∀ e, Measurable (τ e))
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    MeasurableSet (dyadicRankCell τ S t x) := by
  simp only [dyadicRankCell,ofPred_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro _
  apply measurableSet_eq_fun _ measurable_const
  fun_prop

omit [MeasurableSpace Ω] in
lemma dyadicRankCell_disjoint (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    {x y : Finset (Edge × Fin t)} (hx : x ⊆ S ×ˢ Finset.univ) (hy : y ⊆ S ×ˢ Finset.univ) (hxy : x ≠ y) :
    Disjoint (dyadicRankCell τ S t x) (dyadicRankCell τ S t y) := by
  apply Set.disjoint_left.mpr
  intro ω hωx hωy
  apply hxy
  exact dyadicRanks_injective S t hx hy (fun e he => (hωx e he).symm.trans (hωy e he))

lemma ExponentialEnvironment.dyadicRankCell_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    P.real (dyadicRankCell τ S t x) = 1/(2:ℝ)^((S ×ˢ (Finset.univ : Finset (Fin t))).card) := by
  have hh := h.survival_ranks_joint_real S (2^t) (by positivity) (dyadicRank t x)
    (fun e _ => dyadicRank_lt t x e)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  change P.real (dyadicRankCell τ S t x) = _ at hh
  rw [hh,one_div_pow,← pow_mul,card_product,card_univ,Fintype.card_fin]
  rw [Nat.mul_comm]

theorem ExponentialEnvironment.dyadicRankCells_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (A : Finset (Finset (Edge × Fin t)))
    (hA : A ⊆ (S ×ˢ Finset.univ).powerset) :
    P.real (⋃ x ∈ A, dyadicRankCell τ S t x) = fairFamilyMass (S ×ˢ Finset.univ) A := by
  classical
  let _ := h.probability
  have hd : Set.PairwiseDisjoint (↑A : Set (Finset (Edge × Fin t))) (dyadicRankCell τ S t) := by
    intro x hx y hy hxy
    exact dyadicRankCell_disjoint τ S t (mem_powerset.mp (hA hx)) (mem_powerset.mp (hA hy)) hxy
  have he := measure_biUnion_finset (μ := P) hd (fun x _ => measurableSet_dyadicRankCell h.measurable S t x)
  have hr := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at hr
  change P.real (⋃ x ∈ A, dyadicRankCell τ S t x) = ∑ x ∈ A, P.real (dyadicRankCell τ S t x) at hr
  rw [hr]
  simp only [h.dyadicRankCell_real,sum_const,nsmul_eq_mul,fairFamilyMass,div_eq_mul_inv,one_mul]

theorem ExponentialEnvironment.ae_dyadicRankCell (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) :
    ∀ᵐ ω ∂P, ∃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, ω ∈ dyadicRankCell τ S t x := by
  let _ := h.probability
  let U : Set Ω := ⋃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, dyadicRankCell τ S t x
  have hm : MeasurableSet U := MeasurableSet.biUnion (Finset.countable_toSet _)
    (fun x _ => measurableSet_dyadicRankCell h.measurable S t x)
  have hp : P.real U = 1 := by
    rw [h.dyadicRankCells_real S t _ (Finset.Subset.rfl),fairFamilyMass_powerset]
  have hP : P U = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
    change P.real U = (1 : ℝ≥0∞).toReal
    simpa using hp
  have hz : P (Uᶜ) = 0 := by
    rw [measure_compl hm (measure_ne_top _ _),hP]
    simp
  have hh : ∀ᵐ ω ∂P, ω ∈ U := by
    rw [ae_iff]
    exact hz
  filter_upwards [hh] with ω hω
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx,hcell⟩ := Set.mem_iUnion.mp hx
  exact ⟨x,hx,hcell⟩

omit [MeasurableSpace Ω] in
lemma dyadicRankCell_survival {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (h : ω ∈ dyadicRankCell τ S t x) {e : Edge} (he : e ∈ S) :
    roundedSurvival t (τ e ω) = dyadicSurvival t x e := by
  rw [roundedSurvival,h e he,dyadicSurvival_eq_rank]

omit [MeasurableSpace Ω] in
lemma dyadicRankCell_path_iff {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (h : ω ∈ dyadicRankCell τ S t x) (p : StrictPathWitness) (hp : p.edges ⊆ S) :
    RoundedPathGood t (fun e => τ e ω) p ↔ DyadicPathGood t x p := by
  have hs : ∀ e ∈ p.edges, roundedSurvival t (τ e ω) = dyadicSurvival t x e :=
    fun e he => dyadicRankCell_survival h (hp he)
  have hc := pathCost_eq_of_agree (fun e => roundedEdgeCost t (τ e ω))
    (fun e => -Real.log (dyadicSurvival t x e)) p.start p.steps
    (fun e he => congrArg (fun a => -Real.log a) (hs e he))
  unfold RoundedPathGood DyadicPathGood
  rw [hc]
  apply and_congr_left
  intro _
  exact forall_congr' (fun e => forall_congr' (fun he => by rw [hs e he]))

end PlanarFPP

end OAI
