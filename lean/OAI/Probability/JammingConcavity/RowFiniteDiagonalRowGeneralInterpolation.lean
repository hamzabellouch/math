import Mathlib
import OAI.Probability.JammingConcavity.RowFiniteDiagonalRowDirectionPairingTendsto

namespace OAI

/-! Row Finite Diagonal Row General Interpolation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
 

structure RowExtensionData (u : ℝ → ℝ) (L Q : ℝ) where
  value : RowProfile Q → ℝ
  derivative : RowProfile Q → SphericalProfile
  bound : ∀ q s, s ∈ Set.Icc (0:ℝ) 1 → (derivative q).val s ≤ L^2
  finite_value_limit : ∀ (q : RowProfile Q) (P : ℕ → RowFiniteProfile Q),
    Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0) →
    Tendsto (fun n => (P n).functional u) atTop (𝓝 (value q))
  finite_derivative_limit : ∀ (q : RowProfile Q) (P : ℕ → RowFiniteProfile Q),
    Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0) →
    Tendsto (fun n => sphericalProfileDistance ((P n).derivative u) (derivative q).val) atTop (𝓝 0)
  value_continuous : ∀ (q : RowProfile Q) (qn : ℕ → RowProfile Q),
    Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0) →
    Tendsto (fun n => value (qn n)) atTop (𝓝 (value q))
  derivative_continuous : ∀ (q : RowProfile Q) (qn : ℕ → RowProfile Q),
    Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0) →
    Tendsto (fun n => sphericalProfileDistance (derivative (qn n)).val (derivative q).val) atTop (𝓝 0)

lemma rowExtension_exists {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (Q : ℝ) : Nonempty (RowExtensionData u L Q) := by
  obtain ⟨Phi,hPhi,hPhiCont⟩ := rowGeneralFunctional hu hL hH hb Q
  obtain ⟨D,hD,hDlim,hDcont⟩ := rowGeneralDerivative u L H hu hL hH hb Q
  exact ⟨⟨Phi,D,hD,hPhi,hDlim,hPhiCont,hDcont⟩⟩

lemma RowExtensionData.finite_value {u : ℝ → ℝ} {L Q : ℝ} (E : RowExtensionData u L Q)
    (P : RowFiniteProfile Q) : P.functional u = E.value P.asProfile := by
  apply tendsto_nhds_unique (tendsto_const_nhds (f := atTop (α := ℕ)))
  apply E.finite_value_limit P.asProfile (fun _ => P)
  simpa only [RowFiniteProfile.asProfile,sphericalProfileDistance_self] using (tendsto_const_nhds (x := (0:ℝ)) (f := atTop (α := ℕ)))

lemma RowExtensionData.finite_derivative {u : ℝ → ℝ} {L Q : ℝ} (E : RowExtensionData u L Q)
    (P : RowFiniteProfile Q) : sphericalProfileDistance (P.derivative u) (E.derivative P.asProfile).val=0 := by
  apply tendsto_nhds_unique (tendsto_const_nhds (f := atTop (α := ℕ)))
  apply E.finite_derivative_limit P.asProfile (fun _ => P)
  simpa only [RowFiniteProfile.asProfile,sphericalProfileDistance_self] using (tendsto_const_nhds (x := (0:ℝ)) (f := atTop (α := ℕ)))

lemma RowExtensionData.pairing_continuous {u : ℝ → ℝ} {L Q : ℝ} (E : RowExtensionData u L Q)
    (q r : RowProfile Q) : Continuous (fun t => rowDirectionPairing q.1 r.1 (E.derivative (rowProfileMix q r t))) := by
  rw [continuous_iff_seqContinuous]
  intro t ts ht
  apply rowDirectionPairing_tendsto q r _ (fun _ => q) (fun _ => r) _ (fun n => E.bound _)
  · simpa only [sphericalProfileDistance_self] using (tendsto_const_nhds (x := (0:ℝ)) (f := atTop (α := ℕ)))
  · simpa only [sphericalProfileDistance_self] using (tendsto_const_nhds (x := (0:ℝ)) (f := atTop (α := ℕ)))
  · exact E.derivative_continuous _ _ (rowProfileMix_parameter_tendsto q r ht)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

def rowGaussianPairBlocks : List ℝ → (ℕ → ℝ≥0) → (ℕ → ℝ≥0) → List (ℝ × ℝ × ℝ)
  | [],_,_ => []
  | m::ms,d,e => (m,(d 0:ℝ),(e 0:ℝ))::rowGaussianPairBlocks ms (fun j => d (j+1)) (fun j => e (j+1))

lemma rowGaussianPairBlocks_left (ms : List ℝ) (d e : ℕ → ℝ≥0) :
    (rowGaussianPairBlocks ms d e).map (fun c => (c.1,c.2.1)) = rowGaussianBlocks ms d := by
  induction ms generalizing d e with
  | nil => rfl
  | cons m ms ih => simp [rowGaussianPairBlocks,rowGaussianBlocks,ih]
lemma rowGaussianPairBlocks_right (ms : List ℝ) (d e : ℕ → ℝ≥0) :
    (rowGaussianPairBlocks ms d e).map (fun c => (c.1,c.2.2)) = rowGaussianBlocks ms e := by
  induction ms generalizing d e with
  | nil => rfl
  | cons m ms ih => simp [rowGaussianPairBlocks,rowGaussianBlocks,ih]
lemma rowGaussianPairBlocks_ranks (ms : List ℝ) (d e : ℕ → ℝ≥0) :
    (rowGaussianPairBlocks ms d e).map Prod.fst = ms := by
  have h := congrArg (List.map Prod.fst) (rowGaussianPairBlocks_left ms d e)
  simpa only [List.map_map,Function.comp_def,rowGaussianBlocks_ranks] using h
lemma rowGaussianBlocks_total (ms : List ℝ) (d : ℕ → ℝ≥0) :
    ((rowGaussianBlocks ms d).map Prod.snd).sum = ∑ j : Fin ms.length, (d j:ℝ) := by
  induction ms generalizing d with
  | nil => simp [rowGaussianBlocks]
  | cons m ms ih => simp [rowGaussianBlocks,Fin.sum_univ_succ,ih]

lemma rowGaussianPairBlocks_valid (ms : List ℝ) (d e : ℕ → ℝ≥0)
    (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    ∀ c ∈ rowGaussianPairBlocks ms d e, 0 ≤ c.1 ∧ c.1 ≤ 1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2 := by
  intro c hc
  have hl : (c.1,c.2.1) ∈ rowGaussianBlocks ms d := by
    rw [←rowGaussianPairBlocks_left ms d e]
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  have hr : (c.1,c.2.2) ∈ rowGaussianBlocks ms e := by
    rw [←rowGaussianPairBlocks_right ms d e]
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  have h1 := rowGaussianBlocks_mem ms d _ hl
  have h2 := rowGaussianBlocks_mem ms e _ hr
  exact ⟨(hm _ h1.1).1.le,(hm _ h1.1).2.le,h1.2,h2.2⟩

def rowNNMix (t : ℝ) (a b : ℝ≥0) : ℝ≥0 :=
  (1-rowUnitClip t).toNNReal*a+(rowUnitClip t).toNNReal*b
lemma rowNNMix_coe (t : ℝ) (a b : ℝ≥0) :
    (rowNNMix t a b:ℝ) = (1-rowUnitClip t)*(a:ℝ)+rowUnitClip t*(b:ℝ) := by
  simp [rowNNMix,Real.coe_toNNReal _ (sub_nonneg.mpr (rowUnitClip_mem t).2),
    Real.coe_toNNReal _ (rowUnitClip_mem t).1]

lemma rowGaussianPairBlocks_interpolated (ms : List ℝ) (d e : ℕ → ℝ≥0) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    rowInterpolatedBlocks (rowGaussianPairBlocks ms d e) t = rowGaussianBlocks ms (fun j => rowNNMix t (d j) (e j)) := by
  induction ms generalizing d e with
  | nil => rfl
  | cons m ms ih =>
    simp only [rowGaussianPairBlocks,rowInterpolatedBlocks,List.map_cons,rowGaussianBlocks]
    congr 1
    · simp [rowNNMix_coe,rowUnitClip_eq ht]
    · exact ih _ _

lemma rowGaussianBlocks_mix_cumulative (ms : List ℝ) (d e : ℕ → ℝ≥0) (t s : ℝ) :
    gaussianRankProfile (rowGaussianBlocks ms (fun j => rowNNMix t (d j) (e j))) s =
      (1-rowUnitClip t)*gaussianRankProfile (rowGaussianBlocks ms d) s+
        rowUnitClip t*gaussianRankProfile (rowGaussianBlocks ms e) s := by
  induction ms generalizing d e with
  | nil => simp [gaussianRankProfile,rowGaussianBlocks]
  | cons m ms ih =>
    simp only [gaussianRankProfile,rowGaussianBlocks,List.map_cons,List.sum_cons]
    split_ifs <;> try simp only [rowNNMix_coe]
    · have h := ih (fun j => d (j+1)) (fun j => e (j+1))
      dsimp [gaussianRankProfile] at h
      rw [h]; ring
    · have h := ih (fun j => d (j+1)) (fun j => e (j+1))
      simpa only [zero_add,gaussianRankProfile] using h
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

def RowFiniteProfile.mix {Q : ℝ} (P R : RowFiniteProfile Q) (hr : P.ranks=R.ranks) (t : ℝ) : RowFiniteProfile Q where
  ranks := P.ranks
  ordered := P.ordered
  valid := P.valid
  increment := fun j => rowNNMix t (P.increment j) (R.increment j)
  root := rowNNMix t P.root R.root
  residual := rowNNMix t P.residual R.residual
  diagonal := by
    have hp := P.diagonal
    have hq := R.diagonal
    simp only [rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum] at hp hq ⊢
    rw [Fin.sum_univ_eq_sum_range (fun j => (P.increment j:ℝ))] at hp
    rw [Fin.sum_univ_eq_sum_range (fun j => (R.increment j:ℝ))] at hq
    rw [←hr] at hq
    rw [Fin.sum_univ_eq_sum_range (fun j => (rowNNMix t (P.increment j) (R.increment j):ℝ))]
    simp_rw [rowNNMix_coe]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    linear_combination (1-rowUnitClip t)*hp+rowUnitClip t*hq

lemma RowFiniteProfile.mix_profile {Q : ℝ} (P R : RowFiniteProfile Q) (hr : P.ranks=R.ranks) (t : ℝ) :
    (P.mix R hr t).asProfile = rowProfileMix P.asProfile R.asProfile t := by
  apply Subtype.ext
  apply sphericalProfile_ext
  funext s
  change (rowCascadeProfile P.ranks (fun j => rowNNMix t (P.increment j) (R.increment j)) (rowNNMix t P.root R.root)).val s =
    (1-rowUnitClip t)*P.profile.val s+rowUnitClip t*R.profile.val s
  rw [rowCascadeProfile_sum _ P.ordered]
  change (rowNNMix t P.root R.root:ℝ)+gaussianRankProfile (rowGaussianBlocks P.ranks (fun j => rowNNMix t (P.increment j) (R.increment j))) s = _
  rw [rowNNMix_coe,rowGaussianBlocks_mix_cumulative]
  rw [RowFiniteProfile.profile,rowCascadeProfile_sum _ P.ordered,RowFiniteProfile.profile,rowCascadeProfile_sum _ R.ordered]
  rw [hr]
  dsimp [gaussianRankProfile]
  ring

def RowFiniteProfile.pairBlocks {Q : ℝ} (P R : RowFiniteProfile Q) : List (ℝ × ℝ × ℝ) :=
  (0,(P.root:ℝ),(R.root:ℝ))::(rowGaussianPairBlocks P.ranks P.increment R.increment ++ [(1,(P.residual:ℝ),(R.residual:ℝ))])

lemma RowFiniteProfile.pairBlocks_left {Q : ℝ} (P R : RowFiniteProfile Q) :
    (P.pairBlocks R).map (fun c => (c.1,c.2.1)) =
      (0,(P.root:ℝ))::(rowGaussianBlocks P.ranks P.increment ++ [(1,(P.residual:ℝ))]) := by
  simp [pairBlocks,rowGaussianPairBlocks_left]
lemma RowFiniteProfile.pairBlocks_right {Q : ℝ} (P R : RowFiniteProfile Q) (hr : P.ranks=R.ranks) :
    (P.pairBlocks R).map (fun c => (c.1,c.2.2)) =
      (0,(R.root:ℝ))::(rowGaussianBlocks R.ranks R.increment ++ [(1,(R.residual:ℝ))]) := by
  simp [pairBlocks,rowGaussianPairBlocks_right,hr]
lemma RowFiniteProfile.pairBlocks_valid {Q : ℝ} (P R : RowFiniteProfile Q) :
    ∀ c ∈ P.pairBlocks R, 0 ≤ c.1 ∧ c.1 ≤ 1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2 := by
  intro c hc
  simp only [pairBlocks,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | hc | rfl
  · exact ⟨le_rfl,zero_le_one,P.root.coe_nonneg,R.root.coe_nonneg⟩
  · exact rowGaussianPairBlocks_valid _ _ _ P.valid c hc
  · exact ⟨zero_le_one,le_rfl,P.residual.coe_nonneg,R.residual.coe_nonneg⟩
lemma RowFiniteProfile.pairBlocks_sorted {Q : ℝ} (P R : RowFiniteProfile Q) :
    (P.pairBlocks R).Pairwise (fun c d => c.1 ≤ d.1) := by
  have h := rowRootResidual_sorted P.ranks P.increment P.root P.residual P.ordered P.valid
  rw [←P.pairBlocks_left R] at h
  simpa only [List.pairwise_map] using h
lemma RowFiniteProfile.pairBlocks_total {Q : ℝ} (P R : RowFiniteProfile Q) (hr : P.ranks=R.ranks) :
    rowVarianceTotal (P.pairBlocks R)=0 := by
  have he : rowVarianceTotal (P.pairBlocks R) =
      (((P.pairBlocks R).map (fun c => (c.1,c.2.2))).map Prod.snd).sum-
      (((P.pairBlocks R).map (fun c => (c.1,c.2.1))).map Prod.snd).sum := by
    simp only [rowVarianceTotal,List.map_map,Function.comp_def]
    generalize P.pairBlocks R = bs
    induction bs with
    | nil => simp
    | cons b bs ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring
  rw [he,P.pairBlocks_left R,P.pairBlocks_right R hr]
  simp only [List.map_cons,List.map_append,List.sum_cons,List.sum_append,rowGaussianBlocks_total]
  have hp := P.diagonal
  have hq := R.diagonal
  simp only [rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum] at hp hq
  linarith
lemma RowFiniteProfile.pairBlocks_interpolated {Q : ℝ} (P R : RowFiniteProfile Q) (hr : P.ranks=R.ranks) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    rowInterpolatedBlocks (P.pairBlocks R) t =
      (0,((P.mix R hr t).root:ℝ))::(rowGaussianBlocks (P.mix R hr t).ranks (P.mix R hr t).increment ++ [(1,((P.mix R hr t).residual:ℝ))]) := by
  simp only [pairBlocks,rowInterpolatedBlocks,List.map_cons,List.map_append]
  simp only [mix,rowNNMix_coe,rowUnitClip_eq ht]
  congr 2
  exact rowGaussianPairBlocks_interpolated _ _ _ ht
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowDerivativeRankMoment_append_terminal (bs : List (ℝ × ℝ)) (a T : ℝ) (u : ℝ → ℝ)
    {s : ℝ} (hs : s<a) (x : ℝ) :
    rowDerivativeRankMoment (bs++[(a,T)]) u s x =
      rowDerivativeRankMoment bs (gaussianRowOperator a T u) s x := by
  induction bs generalizing x with
  | nil => simp only [List.nil_append,rowDerivativeRankMoment_cons,ite_eq_left hs]; rfl
  | cons b bs ih =>
    rw [List.cons_append,rowDerivativeRankMoment_cons,rowDerivativeRankMoment_cons]
    split_ifs
    · rw [←List.cons_append,gaussianRowComposition_append_eq]
      rfl
    · rw [gaussianRowComposition_append_eq]
      congr 1
      exact funext ih

lemma rowFullBlocks_profile {Q : ℝ} (P : RowFiniteProfile Q) {s : ℝ} (hs : s ∈ Set.Ico (0:ℝ) 1) :
    gaussianRankProfile ((0,(P.root:ℝ))::(rowGaussianBlocks P.ranks P.increment ++ [(1,(P.residual:ℝ))])) s = P.profile.val s := by
  simp only [gaussianRankProfile,List.map_cons,List.map_append,List.sum_cons,List.sum_append,
    ite_eq_left hs.1,ite_eq_right (not_le.mpr hs.2),List.map_nil,List.sum_nil,add_zero]
  exact (rowCascadeProfile_sum _ P.ordered _ _ s).symm

lemma rowFullBlocks_derivative {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    {Q : ℝ} (P : RowFiniteProfile Q) {s : ℝ} (hs : s ∈ Set.Ico (0:ℝ) 1) :
    rowDerivativeRankMoment ((0,(P.root:ℝ))::(rowGaussianBlocks P.ranks P.increment ++ [(1,(P.residual:ℝ))])) u s 0 = P.derivative u s := by
  rw [rowDerivativeRankMoment_cons,ite_eq_right (not_lt.mpr hs.1)]
  simp_rw [rowDerivativeRankMoment_append_terminal _ _ _ _ hs.2,rowRankMoment_blocks _ P.ordered]
  simp only [rowTiltStep,zero_mul,Real.exp_zero,mul_one,integral_const,probReal_univ,smul_eq_mul,div_one,zero_add]
  have hv := rowBoundedOperator_terminal hu (show (0:ℝ)≤1 by norm_num) le_rfl (P.residual:ℝ)
  have hm := measurable_rowDerivativeDepthMoment hv (rowGaussianBlocks P.ranks P.increment)
    (rowGaussianBlocks_valid P.ranks (fun a ha => ⟨(P.valid a ha).1.le,(P.valid a ha).2.le⟩) P.increment) (rpcStepLevel P.ranks s)
  exact (rowGaussian_integral P.root hm).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma rowFiniteSubFTC {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (bs : List (ℝ × ℝ × ℝ))
    (hbs : ∀ c ∈ bs, 0 ≤ c.1 ∧ c.1 ≤ 1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2)
    (hord : bs.Pairwise (fun c d => c.1 ≤ d.1)) (htotal : rowVarianceTotal bs=0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a≤b) (hb1 : b≤1) (x : ℝ) :
    gaussianRowComposition (rowInterpolatedBlocks bs b) u x-
      gaussianRowComposition (rowInterpolatedBlocks bs a) u x =
      ∫ t in a..b, -(1/2:ℝ)*(∫ s in (0:ℝ)..1,
        (gaussianRankProfile (bs.map (fun c => (c.1,c.2.2))) s-
          gaussianRankProfile (bs.map (fun c => (c.1,c.2.1))) s)*
          rowDerivativeRankMoment (rowInterpolatedBlocks bs t) u s x) := by
  have hbu := rowTerminal_of_C2 hu hL hH hb
  let F := fun t => gaussianRowComposition (rowInterpolatedBlocks bs t) u x
  let F' := fun t => -(1/2:ℝ)*(∫ s in (0:ℝ)..1,
    (gaussianRankProfile (bs.map (fun c => (c.1,c.2.2))) s-
      gaussianRankProfile (bs.map (fun c => (c.1,c.2.1))) s)*
      rowDerivativeRankMoment (rowInterpolatedBlocks bs t) u s x)
  have hd : ∀ t ∈ Set.Ioo a b, HasDerivAt F (F' t) t :=
    fun t ht => rowFiniteIntegral u L H hu hL hH hb bs hbs hord htotal t ⟨ha.trans_lt ht.1,ht.2.trans_le hb1⟩ x
  obtain ⟨K,C,hC,hf,hm,hbound⟩ := rowVarianceFamily_bounds hbu bs (fun c hc => ⟨(hbs c hc).1,(hbs c hc).2.1⟩)
  have he : F' =ᵐ[volume.restrict (Set.Ioo a b)] deriv F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hd t ht).deriv.symm
  have hi : IntervalIntegrable F' volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
    apply (integrable_const C).mono' ((aestronglyMeasurable_deriv F _).congr he.symm)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hv := rowFiniteVariance u L H hu hL hH hb bs hbs t ⟨ha.trans_lt ht.1,ht.2.trans_le hb1⟩ x
    have heq : F' t = rowFiniteVarianceResponse bs u t x := (hd t ht).deriv.symm.trans hv.deriv
    rw [Real.norm_eq_abs,heq]
    exact hbound t x
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (rowVarianceComposition_continuous hbu bs (fun c hc => ⟨(hbs c hc).1,(hbs c hc).2.1⟩) x).continuousOn hd hi).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma RowExtensionData.finite_pairing {u : ℝ → ℝ} {L H Q : ℝ} (E : RowExtensionData u L Q)
    (hu : RowBoundedTerminal u L H) (q r : RowProfile Q) (P : RowFiniteProfile Q) :
    rowDirectionPairing q.1 r.1 (P.derivativeProfile hu) = rowDirectionPairing q.1 r.1 (E.derivative P.asProfile) := by
  have h := rowDirectionPairing_difference_bound q.1 r.1 q.1 r.1 (P.derivativeProfile hu) (E.derivative P.asProfile)
    (fun s _ => (P.derivative_bounds hu s).2) (fun s hs => rowProfile_difference_bound q r hs)
  simp only [sphericalProfileDistance_self,zero_add,mul_zero,zero_add,RowFiniteProfile.derivativeProfile,
    E.finite_derivative P,mul_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

lemma rowFiniteProfileFTC {u : ℝ → ℝ} {L H Q : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (E : RowExtensionData u L Q) (P R : RowFiniteProfile Q) (hr : P.ranks=R.ranks)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a≤b) (hb1 : b≤1) :
    E.value (rowProfileMix P.asProfile R.asProfile b)-E.value (rowProfileMix P.asProfile R.asProfile a) =
      ∫ t in a..b, -(1/2:ℝ)*rowDirectionPairing P.profile R.profile (E.derivative (rowProfileMix P.asProfile R.asProfile t)) := by
  have he := rowFiniteSubFTC hu hL hH hb (P.pairBlocks R) (P.pairBlocks_valid R)
    (P.pairBlocks_sorted R) (P.pairBlocks_total R hr) ha hab hb1 0
  have ha' : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha,hab.trans hb1⟩
  have hb' : b ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans hab,hb1⟩
  rw [P.pairBlocks_interpolated R hr ha',P.pairBlocks_interpolated R hr hb'] at he
  change (P.mix R hr b).functional u-(P.mix R hr a).functional u = _ at he
  rw [E.finite_value,E.finite_value,P.mix_profile R hr a,P.mix_profile R hr b] at he
  refine he.trans ?_
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.le.trans hb1⟩
  dsimp only
  congr 1
  rw [P.pairBlocks_right R hr,P.pairBlocks_left R,P.pairBlocks_interpolated R hr ht']
  calc
    _ = rowDirectionPairing P.profile R.profile ((P.mix R hr t).derivativeProfile (rowTerminal_of_C2 hu hL hH hb)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro s hs
      dsimp only
      rw [rowFullBlocks_profile R ⟨hs.1.le,hs.2⟩,rowFullBlocks_profile P ⟨hs.1.le,hs.2⟩,
        rowFullBlocks_derivative (rowTerminal_of_C2 hu hL hH hb) (P.mix R hr t) ⟨hs.1.le,hs.2⟩]
      rfl
    _ = _ := by
      have hh := E.finite_pairing (rowTerminal_of_C2 hu hL hH hb) P.asProfile R.asProfile (P.mix R hr t)
      rw [P.mix_profile R hr t] at hh
      exact hh
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowProfileMix_tendsto {Q : ℝ} (q r : RowProfile Q) (qn rn : ℕ → RowProfile Q) (t : ℝ)
    (hq : Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0))
    (hr : Tendsto (fun n => sphericalProfileDistance (rn n).1.val r.1.val) atTop (𝓝 0)) :
    Tendsto (fun n => sphericalProfileDistance (rowProfileMix (qn n) (rn n) t).1.val (rowProfileMix q r t).1.val) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _)
    (fun n => rowProfileMix_distance (qn n) (rn n) q r t)
  simpa using (hq.const_mul (1-rowUnitClip t)).add (hr.const_mul (rowUnitClip t))

lemma rowProfile_distance_le {Q : ℝ} (q r : RowProfile Q) : sphericalProfileDistance r.1.val q.1.val ≤ Q := by
  unfold sphericalProfileDistance
  calc
    _ ≤ ∫ _ in (0:ℝ)..1, Q := intervalIntegral.integral_mono_on (by norm_num)
      (r.1.integrable.sub q.1.integrable).abs (intervalIntegrable_const) (fun s hs => rowProfile_difference_bound q r hs)
    _ = Q := by simp
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowGeneralFTC {u : ℝ → ℝ} {L H Q : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (E : RowExtensionData u L Q) (q r : RowProfile Q) {b : ℝ} (hb' : b ∈ Set.Icc (0:ℝ) 1) :
    E.value (rowProfileMix q r b)-E.value q =
      ∫ t in (0:ℝ)..b, -(1/2:ℝ)*rowDirectionPairing q.1 r.1 (E.derivative (rowProfileMix q r t)) := by
  let P : ℕ → RowFiniteProfile Q := q.1.rowGrid q.2
  let R : ℕ → RowFiniteProfile Q := r.1.rowGrid r.2
  let qn := fun n => (P n).asProfile
  let rn := fun n => (R n).asProfile
  have hqn : Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0) := rowGrid_distance_tendsto q.1 q.2
  have hrn : Tendsto (fun n => sphericalProfileDistance (rn n).1.val r.1.val) atTop (𝓝 0) := rowGrid_distance_tendsto r.1 r.2
  let g := fun t => -(1/2:ℝ)*rowDirectionPairing q.1 r.1 (E.derivative (rowProfileMix q r t))
  let gn := fun n t => -(1/2:ℝ)*rowDirectionPairing (qn n).1 (rn n).1 (E.derivative (rowProfileMix (qn n) (rn n) t))
  have hc (n : ℕ) : Continuous (gn n) := continuous_const.mul (E.pairing_continuous (qn n) (rn n))
  have hg : Continuous g := continuous_const.mul (E.pairing_continuous q r)
  have hlim (t : ℝ) : Tendsto (fun n => gn n t) atTop (𝓝 (g t)) := by
    apply Tendsto.const_mul
    apply rowDirectionPairing_tendsto q r _ qn rn _ (fun n => E.bound _) hqn hrn
    exact E.derivative_continuous _ _ (rowProfileMix_tendsto q r qn rn t hqn hrn)
  have hbound (n : ℕ) (t : ℝ) : ‖gn n t‖ ≤ (1/2:ℝ)*L^2*Q := by
    rw [Real.norm_eq_abs]
    change |-(1/2:ℝ)*rowDirectionPairing (qn n).1 (rn n).1 (E.derivative (rowProfileMix (qn n) (rn n) t))| ≤ _
    rw [abs_mul]
    norm_num only [abs_neg,abs_div,abs_one]
    calc
      _ ≤ (1/2:ℝ)*(L^2*sphericalProfileDistance (rn n).1.val (qn n).1.val) :=
        mul_le_mul_of_nonneg_left (rowDirectionPairing_bound _ _ _ (E.bound _)) (by norm_num)
      _ ≤ (1/2:ℝ)*(L^2*Q) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (rowProfile_distance_le (qn n) (rn n)) (sq_nonneg L)) (by norm_num)
      _ = _ := by ring
  have hi : Tendsto (fun n => ∫ t in (0:ℝ)..b, gn n t) atTop (𝓝 (∫ t in (0:ℝ)..b, g t)) := by
    simp only [intervalIntegral.integral_of_le hb'.1]
    exact tendsto_integral_of_dominated_convergence (fun _ => (1/2:ℝ)*L^2*Q)
      (fun n => (hc n).aestronglyMeasurable) (integrable_const _) (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  have he (n : ℕ) : E.value (rowProfileMix (qn n) (rn n) b)-E.value (qn n) = ∫ t in (0:ℝ)..b, gn n t := by
    have hh := rowFiniteProfileFTC hu hL hH hb E (P n) (R n) (show (P n).ranks=(R n).ranks from rfl) (a := 0) (b := b) le_rfl hb'.1 hb'.2
    simpa [gn,qn,rn,RowFiniteProfile.asProfile,rowProfileMix_zero] using hh
  have hv : Tendsto (fun n => E.value (rowProfileMix (qn n) (rn n) b)-E.value (qn n)) atTop (𝓝 (E.value (rowProfileMix q r b)-E.value q)) :=
    (E.value_continuous _ _ (rowProfileMix_tendsto q r qn rn b hqn hrn)).sub (E.value_continuous q qn hqn)
  exact tendsto_nhds_unique hv (by simpa only [he] using hi)

lemma rowGeneral_hasDerivWithinAt {u : ℝ → ℝ} {L H Q : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (E : RowExtensionData u L Q) (q r : RowProfile Q) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun v => E.value (rowProfileMix q r v))
      (-(1/2:ℝ)*rowDirectionPairing q.1 r.1 (E.derivative (rowProfileMix q r t))) (Set.Icc (0:ℝ) 1) t := by
  let g := fun v => -(1/2:ℝ)*rowDirectionPairing q.1 r.1 (E.derivative (rowProfileMix q r v))
  have hc : Continuous g := continuous_const.mul (E.pairing_continuous q r)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (E.value q)
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro v hv
  have he := rowGeneralFTC hu hL hH hb E q r hv
  dsimp [g]
  linarith

lemma rowGeneral_lipschitz {u : ℝ → ℝ} {L H Q : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (E : RowExtensionData u L Q) (q r : RowProfile Q) :
    |E.value q-E.value r| ≤ (1/2:ℝ)*L^2*sphericalProfileDistance q.1.val r.1.val := by
  have he := rowGeneralFTC hu hL hH hb E r q (b := 1) (by norm_num)
  rw [rowProfileMix_one] at he
  rw [he]
  let g := fun t => -(1/2:ℝ)*rowDirectionPairing r.1 q.1 (E.derivative (rowProfileMix r q t))
  have hc : Continuous g := continuous_const.mul (E.pairing_continuous r q)
  calc
    _ ≤ ∫ _ in (0:ℝ)..1, (1/2:ℝ)*L^2*sphericalProfileDistance q.1.val r.1.val := by
      refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
      apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable 0 1).abs intervalIntegrable_const
      intro t ht
      dsimp [g]
      rw [abs_mul]
      norm_num only [abs_neg,abs_div,abs_one]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (rowDirectionPairing_bound r.1 q.1 (E.derivative (rowProfileMix r q t)) (E.bound _)) (by norm_num : (0:ℝ) ≤ 1/2)
    _ = _ := by simp
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
 

lemma rowRankDerivative_segment (rs : List (ℝ × ℝ)) (u : ℝ → ℝ)
    (hord : rs.Pairwise (fun r t => r.1 ≤ t.1)) {s t : ℝ} (hst : s ≤ t)
    (hz : ∀ r ∈ rs, s < r.1 → r.1 ≤ t → r.2=0) (x : ℝ) :
    rowDerivativeRankMoment rs u s x = rowDerivativeRankMoment rs u t x := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨hr,htail⟩ := List.pairwise_cons.mp hord
    have hz' : ∀ v ∈ rs, s < v.1 → v.1 ≤ t → v.2=0 :=
      fun v hv => hz v (List.mem_cons_of_mem r hv)
    rw [rowDerivativeRankMoment_cons,rowDerivativeRankMoment_cons]
    by_cases hs : s < r.1
    · rw [ite_eq_left hs]
      by_cases ht : t < r.1
      · rw [ite_eq_left ht]
      · rw [ite_eq_right ht]
        have hv := hz r (List.mem_cons_self) hs (le_of_not_gt ht)
        rw [hv,rowTiltStep_zero]
        have hg : gaussianRowComposition (r::rs) u = gaussianRowComposition rs u := by
          funext y
          change gaussianRowOperator r.1 r.2 (gaussianRowComposition rs u) y = _
          rw [hv,gaussianRowOperator_zero]
        rw [hg]
        rw [← ih htail hz' x]
        exact (rowDerivativeRankMoment_below rs u s x (fun v hv => hs.trans_le (hr v hv))).symm
    · rw [ite_eq_right hs,ite_eq_right (not_lt.mpr ((le_of_not_gt hs).trans hst))]
      congr 1
      exact funext (ih htail hz')

lemma sphericalProfile_plateau_pointwise (q : SphericalProfile) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hc : ∀ᵐ s ∂volume.restrict (Set.Ioo a b), q.val s=c) :
    ∀ s ∈ Set.Ioo a b, q.val s=c := by
  intro s hs
  have hl : volume (Set.Ioo a s) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hs.1))
  have hr : volume (Set.Ioo s b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hs.2))
  obtain ⟨l,hlm,hle⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hl
    (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo_right hs.2.le) le_rfl) hc)
  obtain ⟨r,hrm,hre⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hr
    (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo_left hs.1.le) le_rfl) hc)
  have hsl : s ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩
  have h1 := q.mono (show l ∈ Set.Icc (0:ℝ) 1 from ⟨ha.trans hlm.1.le,hlm.2.le.trans hsl.2⟩) hsl hlm.2.le
  have h2 := q.mono hsl (show r ∈ Set.Icc (0:ℝ) 1 from ⟨hsl.1.trans hrm.1.le,hrm.2.le.trans hb⟩) hrm.1.le
  rw [hle] at h1
  rw [hre] at h2
  exact le_antisymm h2 h1

lemma rowGaussianBlocks_mem_index (ms : List ℝ) (d : ℕ → ℝ≥0) (r : ℝ × ℝ)
    (hr : r ∈ rowGaussianBlocks ms d) :
    ∃ j, j < ms.length ∧ r.1 = ms[j]! ∧ r.2 = (d j:ℝ) := by
  induction ms generalizing d with
  | nil => simp [rowGaussianBlocks] at hr
  | cons m ms ih =>
    simp only [rowGaussianBlocks,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨0,by simp,by simp,rfl⟩
    · obtain ⟨j,hj,h1,h2⟩ := ih _ hr
      exact ⟨j+1,by simpa using Nat.succ_lt_succ hj,by simpa using h1,h2⟩
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowGrid_derivative_plateau {u : ℝ → ℝ} {L H Q : ℝ} (hu : RowBoundedTerminal u L H)
    (q : RowProfile Q) {a b c x y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hc : ∀ s ∈ Set.Ioo a b, q.1.val s=c) (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hxy : x ≤ y) :
    ∀ᶠ n : ℕ in atTop, (q.1.rowGrid q.2 n).derivative u x = (q.1.rowGrid q.2 n).derivative u y := by
  have hsmall : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hs := hsmall.eventually (gt_mem_nhds (sub_pos.mpr hx.1))
  filter_upwards [hs] with n hn
  let P := q.1.rowGrid q.2 n
  have hx' : x ∈ Set.Ico (0:ℝ) 1 := ⟨ha.trans hx.1.le,hx.2.trans_le hb⟩
  have hy' : y ∈ Set.Ico (0:ℝ) 1 := ⟨ha.trans hy.1.le,hy.2.trans_le hb⟩
  rw [←rowFullBlocks_derivative hu P hx',←rowFullBlocks_derivative hu P hy']
  apply rowRankDerivative_segment _ _ (rowRootResidual_sorted P.ranks P.increment P.root P.residual P.ordered P.valid) hxy
  intro r hr hxr hry
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact False.elim (not_lt.mpr hx'.1 hxr)
  · obtain ⟨j,hj,h1,h2⟩ := rowGaussianBlocks_mem_index P.ranks P.increment r hr
    change j < (spinGridRanks n).length at hj
    rw [spinGridRanks_length] at hj
    change r.1 = (spinGridRanks n)[j]! at h1
    rw [spinGridRanks_get n j hj] at h1
    have hdiff : spinGridPoint n (j+1) = spinGridPoint n j+1/((n:ℝ)+1) := by
      simp only [spinGridPoint,Nat.cast_add,Nat.cast_one]
      ring
    have hg1 : spinGridPoint n (j+1) ∈ Set.Ioo a b := by
      rw [←h1]
      exact ⟨hx.1.trans hxr,hry.trans_lt hy.2⟩
    have hg0 : spinGridPoint n j ∈ Set.Ioo a b := by
      constructor
      · rw [h1,hdiff] at hxr
        linarith
      · exact (spinGridPoint_mono n (Nat.le_succ j)).trans_lt hg1.2
    rw [h2]
    change ((q.1.gridStep n).variance j:ℝ)=0
    rw [gridStep_variance q.1 n j hj,hc _ hg1,hc _ hg0,sub_self]
  · exact False.elim (not_le.mpr hy'.2 hry)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
 

lemma profileCompactFilter_pointwise (pn : ℕ → SphericalProfile) (B : ℝ)
    (hpn : ∀ n s, s ∈ Set.Icc 0 1 → (pn n).val s ≤ B) :
    ∃ (p : SphericalProfile) (l : Filter ℕ), l.NeBot ∧ l ≤ atTop ∧
      (∀ s ∈ Set.Icc 0 1, p.val s ≤ B) ∧
      Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) l (𝓝 0) ∧
      (∀ s ∈ Set.Icc 0 1, Tendsto (fun n => (pn n).val s) l (𝓝 (p.val s))) := by
  let c : ℝ → ℝ := fun s => max 0 (min s 1)
  have hc (s : ℝ) : c s ∈ Set.Icc 0 1 :=
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩
  have hce (s : ℝ) (hs : s ∈ Set.Icc 0 1) : c s = s := by
    simp only [c,min_eq_left hs.2,max_eq_right hs.1]
  let seq : ℕ → (ℝ → Set.Icc (0:ℝ) B) := fun n s => ⟨(pn n).val (c s),
    (pn n).nonneg (c s) (hc s),hpn n (c s) (hc s)⟩
  let U := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨f,hf⟩ := exists_clusterPt_of_compactSpace (U.map seq : Filter (ℝ → Set.Icc (0:ℝ) B))
  have hf' : Tendsto seq (U : Filter ℕ) (𝓝 f) := (Ultrafilter.clusterPt_iff).mp hf
  have hfpoint (s : ℝ) : Tendsto (fun n => (pn n).val (c s)) (U : Filter ℕ) (𝓝 (f s:ℝ)) :=
    (continuous_subtype_val.tendsto (f s)).comp (((continuous_apply s).tendsto f).comp hf')
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
      Tendsto (fun n => (pn n).val s) (U : Filter ℕ) (𝓝 (f s:ℝ)) := by
    simpa only [hce s hs] using hfpoint s
  let p : SphericalProfile :=
    { val := fun s => (f s:ℝ)
      nonneg := fun s _ => (f s).property.1
      mono := fun s hs t ht hst => le_of_tendsto_of_tendsto (hpoint s hs) (hpoint t ht)
        (Eventually.of_forall fun n => (pn n).mono hs ht hst) }
  have hp : ∀ s ∈ Set.Icc 0 1, p.val s ≤ B := fun s _ => (f s).property.2
  exact ⟨p,(U:Filter ℕ),inferInstance,Ultrafilter.of_le atTop,hp,
    profileDistance_tendsto_pointwise pn p B hpn hp hpoint,hpoint⟩

lemma sphericalProfileDistance_zero_ae (p q : SphericalProfile)
    (h : sphericalProfileDistance p.val q.val=0) :
    p.val =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] q.val := by
  have hi := (p.integrable.sub q.integrable).abs
  have he : ∫ s in Set.Ioc (0:ℝ) 1, |p.val s-q.val s| = 0 := by
    simpa only [sphericalProfileDistance,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using h
  have hz := (integral_eq_zero_iff_of_nonneg (fun s => abs_nonneg (p.val s-q.val s)) hi.1).mp he
  rw [restrict_Ioc_eq_restrict_Icc] at hz
  filter_upwards [hz] with s hs
  exact sub_eq_zero.mp (abs_eq_zero.mp hs)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowGeneral_plateau {u : ℝ → ℝ} {L H Q : ℝ} (hu : RowBoundedTerminal u L H)
    (E : RowExtensionData u L Q) (q : RowProfile Q) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a<b) (hb : b≤1)
    (hc : ∀ᵐ s ∂volume.restrict (Set.Ioo a b), q.1.val s=c) :
    ∃ d : ℝ, ∀ᵐ s ∂volume.restrict (Set.Ioo a b), (E.derivative q).val s=d := by
  let P := q.1.rowGrid q.2
  let dn := fun n => (P n).derivativeProfile hu
  have hbound : ∀ n s, s ∈ Set.Icc (0:ℝ) 1 → (dn n).val s ≤ L^2 :=
    fun n s _ => ((P n).derivative_bounds hu s).2
  obtain ⟨p,l,hl,hla,hp,hlim,hpoint⟩ := profileCompactFilter_pointwise dn (L^2) hbound
  let : l.NeBot := hl
  have hlimE : Tendsto (fun n => sphericalProfileDistance (dn n).val (E.derivative q).val) l (𝓝 0) :=
    (E.finite_derivative_limit q P (rowGrid_distance_tendsto q.1 q.2)).mono_left hla
  have hzero : sphericalProfileDistance p.val (E.derivative q).val=0 := by
    have hh : Tendsto (fun _ : ℕ => sphericalProfileDistance p.val (E.derivative q).val) l (𝓝 0) := by
      apply squeeze_zero (fun _ => sphericalProfileDistance_nonneg p (E.derivative q))
        (fun n => ?_) (show Tendsto (fun n => sphericalProfileDistance (dn n).val p.val+sphericalProfileDistance (dn n).val (E.derivative q).val) l (𝓝 0) by simpa using hlim.add hlimE)
      simpa only [sphericalProfileDistance_comm p (dn n)] using sphericalProfileDistance_triangle p (dn n) (E.derivative q)
    exact tendsto_nhds_unique tendsto_const_nhds hh
  have hpE := sphericalProfileDistance_zero_ae p (E.derivative q) hzero
  have hc' := sphericalProfile_plateau_pointwise q.1 ha hb hc
  have hmem (s : ℝ) (hs : s ∈ Set.Ioo a b) : s ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩
  have hpeq (x y : ℝ) (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) (hxy : x≤y) : p.val x=p.val y := by
    have he : ∀ᶠ n in l, (dn n).val x=(dn n).val y :=
      hla (rowGrid_derivative_plateau hu q ha hb hc' hx hy hxy)
    exact tendsto_nhds_unique (hpoint x (hmem x hx)) ((hpoint y (hmem y hy)).congr' (he.mono (fun _ h => h.symm)))
  have hm : (a+b)/2 ∈ Set.Ioo a b := ⟨by linarith,by linarith⟩
  refine ⟨p.val ((a+b)/2),?_⟩
  have hpE' : p.val =ᵐ[volume.restrict (Set.Ioo a b)] (E.derivative q).val :=
    ae_mono (Measure.restrict_mono (fun s hs => hmem s hs) le_rfl) hpE
  filter_upwards [hpE',ae_restrict_mem measurableSet_Ioo] with s hs hsm
  rw [←hs]
  rcases le_total s ((a+b)/2) with hle | hle
  · exact hpeq s ((a+b)/2) hsm hm hle
  · exact (hpeq ((a+b)/2) s hm hsm hle).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
 

theorem rowGeneralInterpolation : RowGeneralInterpolationStatement := by
  intro u L H hu hL hH hb Q
  obtain ⟨E⟩ := rowExtension_exists hu hL hH hb Q
  refine ⟨E.value,E.derivative,E.bound,?_,?_,?_,?_,?_⟩
  · intro q P hP
    exact ⟨E.finite_value_limit q P hP,E.finite_derivative_limit q P hP⟩
  · intro q qn hqn
    exact ⟨E.value_continuous q qn hqn,E.derivative_continuous q qn hqn⟩
  · intro q r t ht
    exact rowGeneral_hasDerivWithinAt hu hL hH hb E q r ht
  · exact rowGeneral_lipschitz hu hL hH hb E
  · intro q a b c ha hab hb'
    exact rowGeneral_plateau (rowTerminal_of_C2 hu hL hH hb) E q ha hab hb'
end MicroscopicJamming

end

end OAI
