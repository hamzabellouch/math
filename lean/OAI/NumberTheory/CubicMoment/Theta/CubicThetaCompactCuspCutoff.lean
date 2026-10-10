import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarCuspSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCusps

namespace OAI

/-! A finite disjoint cusp cover gives smooth compact cutoffs on the
actual quotient by subtracting its scalar incoming cusp cutoffs. -/
noncomputable section
open Set
open scoped MatrixGroups ContDiff BigOperators
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_mono (δ : SL(2,Eisenstein)) {H K : ℝ} (h : H≤K) :
    cubicThetaCuspNeighborhood δ K⊆cubicThetaCuspNeighborhood δ H := by
  intro q hq
  obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ K q).mp hq
  exact (cubicThetaCuspNeighborhood_mem_iff δ H q).mpr ⟨p,h.trans_lt hp,hpq⟩

lemma cubicThetaDisjointCuspCover :
    ∃ S T : Finset SL(2,Eisenstein),
      (∀ V, cubicThetaQuotientCore S V ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ V=univ) ∧
      (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1) := by
  classical
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  obtain ⟨T,_,hT,hd⟩ := cubicThetaFiniteCusps_disjoint (S.image Inv.inv)
  refine ⟨S,T,?_,hd 1 le_rfl⟩
  intro V
  have him : (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ V)=
      ⋃ δ∈S.image Inv.inv,cubicThetaCuspNeighborhood δ V := by
    ext q
    simp
  rw [← hT V,← him]
  exact hS V

def cubicThetaCompactCuspCutoff (T : Finset SL(2,Eisenstein)) (N : ℝ)
    (q : CubicThetaQuotient) : ℂ :=
  1-∑ δ∈T,cubicThetaScalarCuspQuotient δ N q

lemma cubicThetaCompactCuspCutoff_continuous (T : Finset SL(2,Eisenstein))
    {N : ℝ} (hN : 1≤N) : Continuous (cubicThetaCompactCuspCutoff T N) :=
  continuous_const.sub (continuous_finsetSum T (fun δ _ => cubicThetaScalarCuspQuotient_continuous δ hN))

lemma cubicThetaCompactCuspCutoff_smooth (T : Finset SL(2,Eisenstein))
    {N : ℝ} (hN : 1≤N) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaCompactCuspCutoff T N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} :=
  contDiffOn_const.sub (ContDiffOn.sum (fun δ _ => cubicThetaScalarCuspQuotient_smooth δ hN))

lemma cubicThetaCompactCuspCutoff_high (T : Finset SL(2,Eisenstein))
    (hd : (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1))
    {N : ℝ} (hN : 1≤N) {δ : SL(2,Eisenstein)} (hδ : δ∈T)
    {q : CubicThetaQuotient} (hq : q∈cubicThetaCuspNeighborhood δ (2*N)) :
    cubicThetaCompactCuspCutoff T N q=0 := by
  classical
  have hqδ := cubicThetaCuspNeighborhood_mono δ (by linarith : (1:ℝ)≤2*N) hq
  have hz (ε : SL(2,Eisenstein)) (hε : ε∈T) (hne : ε≠δ) :
      cubicThetaScalarCuspQuotient ε N q=0 := by
    by_contra h
    have hqε := cubicThetaCuspNeighborhood_mono ε hN (cubicThetaScalarCuspQuotient_support ε hN h)
    exact Set.disjoint_left.mp (hd hε hδ hne) hqε hqδ
  have hsum : (∑ ε∈T,cubicThetaScalarCuspQuotient ε N q)=cubicThetaScalarCuspQuotient δ N q :=
    Finset.sum_eq_single δ hz (fun h => False.elim (h hδ))
  rw [cubicThetaCompactCuspCutoff,hsum,cubicThetaScalarCuspQuotient_high δ hN hq,sub_self]

lemma cubicThetaCompactCuspCutoff_compact (S T : Finset SL(2,Eisenstein))
    (hc : ∀ V, cubicThetaQuotientCore S V ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ V=univ)
    (hd : (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1))
    {N : ℝ} (hN : 1≤N) : HasCompactSupport (cubicThetaCompactCuspCutoff T N) := by
  have hK := cubicThetaQuotientCore_compact S (2*N)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro q hq
  by_contra hn
  have hcover : q∈cubicThetaQuotientCore S (2*N) ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ (2*N) := by
    rw [hc]
    trivial
  obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp (hcover.resolve_left hn)
  exact hq (cubicThetaCompactCuspCutoff_high T hd hN hδ hqδ)

end CubicFirstMoment

end

end OAI
