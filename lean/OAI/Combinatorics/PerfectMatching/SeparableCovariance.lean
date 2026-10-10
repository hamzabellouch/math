import OAI.Combinatorics.PerfectMatching.WeightedSpectrum

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators Topology
open Matrix Filter
namespace MatchingEntropy
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separableDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope,
      separableLower y-maxMatchingEntropy G y ≤ separableLower x-maxMatchingEntropy G x := by
  have hs : UpperSemicontinuousOn (fun y => separableLower y-maxMatchingEntropy G y)
      G.polytope := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      continuous_separableLower.continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

theorem matching_covariance_rank_face (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by
  let W := weightedDirectionSpace p (matchingNormalized G x)
  let L : G.faceSpace x →ₗ[ℝ] W :=
    ((normalizeLinear x).comp (G.faceSpace x).subtype).codRestrict W
      (fun u => normalized_face_mem G heven hp hopt u.property)
  have hi : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    funext e
    have hh := congrFun (congrArg Subtype.val huv) e
    change u.val e/Real.sqrt (x e.val)=v.val e/Real.sqrt (x e.val) at hh
    exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr e.property))).mp hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hq := (G.faceSpace x).finrank_quotient_add_finrank
  rw [covariance_rank hp.1.1]
  have hq' : G.faceCodimension x+Module.finrank ℝ (G.faceSpace x)=Fintype.card {e // 0 < x e} := by
    simpa only [LooplessGraph.faceCodimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using hq
  change Module.finrank ℝ (G.faceSpace x) ≤ Module.finrank ℝ W at hdim
  dsimp only [W] at hdim
  omega

theorem faceCodimension_strict (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope) :
    G.faceCodimension x < 2*Fintype.card V := by
  by_cases hn4 : 4 ≤ Fintype.card V
  · have hb := LooplessGraph.faceCodimension_strong_aux (Fintype.card V) G rfl heven hn4 x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_covariance (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : {e // 0 < x e} → ℝ) :
    u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤
      ∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  let v := G.mean (fun M => p M*a M)
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_separable_second_variation G hp hopt hmax w c hcenter
  have hzero : ∀ e, ¬0 < x e → v e=0 := by
    intro e he
    have he0 : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
    exact mean_score_support G hp.1 a e (by rw [hp.2,he0])
  have hnorm : (∑ e, (v e)^2/x e) =
      ∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
  have hbar : (∑ e, (v e)^2/(1-x e)) =
      ∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
    change (v e.val)^2/(1-x e.val)=x e.val/(1-x e.val)*((v e.val)^2/x e.val)
    field_simp [ne_of_gt e.property]
  have hquad : (∑ M, p M*(a M)^2)=u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change -(∑ e, (v e)^2/x e)+3*(∑ e, (v e)^2/(1-x e))+(∑ M,p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hbar,hquad] at hh
  have heq : (∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) =
      (∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2)-
      3*(∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) := by
    simp_rw [sub_mul,one_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq]
  linarith

omit [Fintype V] [DecidableEq V] in
theorem matching_covariance_diagonal (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e : {e // 0<x e}) :
    covariance p (matchingNormalized G x) e e=1-x e.val := by
  rw [covariance_entry hp.1.1]
  have hh := normalizedCentered_variance hp.1.2
    (fun M (e : {e // 0<x e}) => G.indicator M e.val)
    (by intro M e; simp only [LooplessGraph.indicator]; split <;> norm_num)
    (fun e => x e.val) (fun e => congrFun hp.2 e.val) (fun e => e.property) e
  convert hh using 1
  apply Finset.sum_congr rfl
  intro M _
  change p M*matchingNormalized G x M e*matchingNormalized G x M e=
    p M*(matchingNormalized G x M e)^2
  ring

theorem separable_max_has_forced (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x) : ∃ e, x e=1 := by
  by_contra hforced
  push Not at hforced
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  have hsecond := covariance_weighted_rank (covariance_posSemidef p (matchingNormalized G x))
    (fun e => 1-3*x e.val/(1-x e.val)) (matching_separable_covariance G hp hopt hmax)
  have htrace : (∑ e : {e // 0<x e}, (1-3*x e.val/(1-x e.val))*
      covariance p (matchingNormalized G x) e e) = Fintype.card {e // 0<x e}-2*(Fintype.card V:ℝ) := by
    have he (e : {e // 0<x e}) : (1-3*x e.val/(1-x e.val))*
        covariance p (matchingNormalized G x) e e=1-4*x e.val := by
      rw [matching_covariance_diagonal G hp]
      have hh : 1-x e.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (hforced e.val))
      field_simp
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    obtain ⟨r,hr⟩ := heven
    have hv : Fintype.card V=2*r := by omega
    have hs : (∑ e : {e // 0<x e}, x e.val)=(r:ℝ) := by
      rw [← G.marginal_sum hv hx]
      exact (sum_positive_support x x (fun e he =>
        le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
    rw [hs,hv]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [htrace] at hsecond
  have hrank := matching_covariance_rank_face G heven hp hopt
  have hstrict := faceCodimension_strict G heven hn hx
  have hrankR : (Fintype.card {e // 0<x e}:ℝ) ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by exact_mod_cast hrank
  have hstrictR : (G.faceCodimension x:ℝ)<2*(Fintype.card V:ℝ) := by exact_mod_cast hstrict
  linarith

end MatchingEntropy
end
end

end OAI
