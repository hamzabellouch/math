import OAI.Probability.GammaPassage.DyadicRanks
import OAI.Probability.GammaPassage.SurvivalRank
import OAI.Probability.GammaPassage.BKRepeated

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Finset Filter PlanarFPP
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

def gammaDyadicRankCell (shape rate : ℝ) (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    (x : Finset (Edge × Fin t)) : Set Ω :=
  {ω | ∀ e ∈ S, ⌊(2:ℝ)^t*gammaSurvival shape rate (τ e ω)⌋₊ = dyadicRank t x e}

lemma measurableSet_gammaDyadicRankCell (hs : 0 < shape) (hr : 0 < rate) (hτ : ∀ e, Measurable (τ e))
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    MeasurableSet (gammaDyadicRankCell shape rate τ S t x) := by
  simp only [gammaDyadicRankCell,ofPred_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro _
  apply measurableSet_eq_fun _ measurable_const
  exact (measurable_const.mul ((gammaSurvival_measurable hs hr).comp (hτ e))).nat_floor

omit [MeasurableSpace Ω] in
lemma gammaDyadicRankCell_disjoint (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    {x y : Finset (Edge × Fin t)} (hx : x ⊆ S ×ˢ Finset.univ) (hy : y ⊆ S ×ˢ Finset.univ) (hxy : x ≠ y) :
    Disjoint (gammaDyadicRankCell shape rate τ S t x) (gammaDyadicRankCell shape rate τ S t y) := by
  apply Set.disjoint_left.mpr
  intro ω hωx hωy
  apply hxy
  exact dyadicRanks_injective S t hx hy (fun e he => (hωx e he).symm.trans (hωy e he))

lemma GammaEnvironment.gammaDyadicRankCell_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    P.real (gammaDyadicRankCell shape rate τ S t x) = 1/(2:ℝ)^((S ×ˢ (Finset.univ : Finset (Fin t))).card) := by
  have hh := h.survival_ranks_joint_real hs hr S (2^t) (by positivity) (dyadicRank t x)
    (fun e _ => dyadicRank_lt t x e)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  change P.real (gammaDyadicRankCell shape rate τ S t x) = _ at hh
  rw [hh,one_div_pow,← pow_mul,card_product,card_univ,Fintype.card_fin]
  rw [Nat.mul_comm]

/-- Uniform bit-cube probabilities, obtained from the actual Gamma
edge law through an exact disjoint partition into dyadic rank cells. -/
theorem GammaEnvironment.gammaDyadicRankCells_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (A : Finset (Finset (Edge × Fin t)))
    (hA : A ⊆ (S ×ˢ Finset.univ).powerset) :
    P.real (⋃ x ∈ A, gammaDyadicRankCell shape rate τ S t x) = fairFamilyMass (S ×ˢ Finset.univ) A := by
  classical
  let _ := h.probability
  have hd : Set.PairwiseDisjoint (↑A : Set (Finset (Edge × Fin t))) (gammaDyadicRankCell shape rate τ S t) := by
    intro x hx y hy hxy
    exact gammaDyadicRankCell_disjoint τ S t (mem_powerset.mp (hA hx)) (mem_powerset.mp (hA hy)) hxy
  have he := measure_biUnion_finset (μ := P) hd (fun x _ => measurableSet_gammaDyadicRankCell hs hr h.measurable S t x)
  have hreal := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at hreal
  change P.real (⋃ x ∈ A, gammaDyadicRankCell shape rate τ S t x) = ∑ x ∈ A, P.real (gammaDyadicRankCell shape rate τ S t x) at hreal
  rw [hreal]
  simp only [h.gammaDyadicRankCell_real hs hr,sum_const,nsmul_eq_mul,fairFamilyMass,div_eq_mul_inv,one_mul]

/-- Every original environment lies in one of the bit cells almost surely.
Coverage follows from exact mass one, so no choice of a binary expansion on
null endpoint configurations is needed. -/
theorem GammaEnvironment.ae_gammaDyadicRankCell (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) :
    ∀ᵐ ω ∂P, ∃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, ω ∈ gammaDyadicRankCell shape rate τ S t x := by
  let _ := h.probability
  let U : Set Ω := ⋃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, gammaDyadicRankCell shape rate τ S t x
  have hm : MeasurableSet U := MeasurableSet.biUnion (Finset.countable_toSet _)
    (fun x _ => measurableSet_gammaDyadicRankCell hs hr h.measurable S t x)
  have hp : P.real U = 1 := by
    rw [h.gammaDyadicRankCells_real hs hr S t _ (Finset.Subset.rfl),fairFamilyMass_powerset]
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

end GammaFPP

end OAI
