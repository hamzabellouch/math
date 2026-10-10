import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralUniform
import OAI.Combinatorics.KMedianRecovery.Algorithms.GlobalCall

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalRounding
open LocalSearch BinaryDuplicateMatrix BinaryTaggedSets IntegralAssembly
variable {n : ℕ}
lemma ceil_cast (r : ℚ) : ⌈(r:ℝ)⌉₊=⌈r⌉₊ := by
  apply eq_of_forall_ge_iff
  intro a
  rw [Nat.ceil_le,Nat.ceil_le]
  exact_mod_cast (Iff.rfl : r≤(a:ℚ) ↔ r≤(a:ℚ))
lemma round_edge [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (u : ℚ) (C : ℕ) (i j : Fin n) :
    BinaryRoundingMatrix.round δ u C i j=(Rounding.edge (u:ℝ) C i j:ℚ) := by
  unfold BinaryRoundingMatrix.round Rounding.edge
  by_cases hij : i=j
  · simp only [hij,ite_true,Nat.cast_zero]
  · rw [ite_eq_right hij,ite_eq_right hij,←hδ,←Rat.cast_div,ceil_cast]
@[instance_reducible]
noncomputable def duplicateMetric (I : RationalMetricInput) : PseudoMetricSpace (Fin (I.pointCount+I.pointCount)) :=
  PseudoMetricSpace.induced forget I.metric
lemma duplicate_dist (I : RationalMetricInput) (i j : Fin (I.pointCount+I.pointCount)) :
    @dist _ (duplicateMetric I).toDist i j=(duplicate I.distance i j:ℝ) := rfl
lemma left_injective : Function.Injective (@left n) := by
  intro a b h
  have hh:=congrArg (fun x:Fin (n+n)=>x.val) h
  exact Fin.ext hh
lemma right_injective : Function.Injective (@right n) := by
  intro a b h
  have hh:=congrArg Fin.val h
  simp only [right,Fin.val_natAdd] at hh
  exact Fin.ext (by omega)
lemma card_left (D : Finset (Fin n)) : (D.image left).card=D.card := Finset.card_image_of_injective _ left_injective
lemma card_right (F : Finset (Fin n)) : (F.image right).card=F.card := Finset.card_image_of_injective _ right_injective
lemma dist_left_right (I : RationalMetricInput) (p f : Fin I.pointCount) :
    @dist _ (duplicateMetric I).toDist (left p) (right f)=@dist _ I.metric.toDist p f := by
  change (I.distance (forget (left p)) (forget (right f)):ℝ)=(I.distance p f:ℝ)
  rw [show forget (left p)=p from forget_left p,show forget (right f)=f from forget_right f]
lemma connection_image (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) (p : Fin I.pointCount) :
    @connection _ (duplicateMetric I) (S.image right) (left p)=@connection _ I.metric S p := by
  let := I.metric
  let := duplicateMetric I
  by_cases hS : S.Nonempty
  · have hs:=hS.image (@right I.pointCount)
    rw [connection,dite_eq_left hs,connection,dite_eq_left hS]
    apply le_antisymm
    · apply Finset.le_inf' hS
      intro f hf
      have hh:=Finset.inf'_le (fun q=>@dist _ (duplicateMetric I).toDist (left p) q)
        (show right f∈S.image right from Finset.mem_image.mpr ⟨f,hf,rfl⟩)
      simpa only [dist_left_right] using hh
    · apply Finset.le_inf' hs
      intro f hf
      obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hf
      rw [dist_left_right]
      exact Finset.inf'_le (fun q=>dist p q) hq
  · have hs : ¬(S.image right).Nonempty := by simpa only [Finset.image_nonempty] using hS
    rw [connection,dite_eq_right hs,connection,dite_eq_right hS]
lemma cost_image (I : RationalMetricInput) (D S : Finset (Fin I.pointCount)) :
    @cost _ (duplicateMetric I) (D.image left) (S.image right)=@cost _ I.metric D S := by
  let := I.metric
  let := duplicateMetric I
  rw [cost,Finset.sum_image (fun _ _ _ _ h=>left_injective h)]
  simp only [connection_image,cost]
lemma project_subset (F : Finset (Fin n)) (T : Finset (Fin (n+n))) (hT : T⊆F.image right) :
    ∃ S : Finset (Fin n), S⊆F ∧ S.image right=T ∧ S.card=T.card := by
  let S:=F.filter (fun f=>right f∈T)
  have hS : S.image right=T := by
    ext i
    simp only [S,Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨f,⟨_,hf⟩,rfl⟩;exact hf
    · intro hi
      obtain ⟨f,hf,he⟩:=Finset.mem_image.mp (hT hi)
      exact ⟨f,⟨hf,he.symm ▸ hi⟩,he⟩
  exact ⟨S,Finset.filter_subset _ _,hS,by rw [←hS,card_right]⟩
end MetricKMedianRecovery.BitMachine.BinaryGlobalRounding

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalRounding
open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison BinaryTaggedSets
attribute [local irreducible] BinaryIntegralAll.output BinaryIntegralAll.run BinaryIntegralDispatch.budget
  BinaryGlobalCall.run

theorem rounded_program (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ (I : RationalMetricInput) (_hD : I.clients.Nonempty) (M : ℚ) (_hM : 0<M),
    let K := (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
    ∃ out : (Fin K→Bool)→Finset (Fin I.pointCount),
      (∀ seed, BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M (List.ofFn seed))=BinaryFinSet.encode (out seed)) ∧
      (∀ seed,(out seed)⊆I.facilities ∧ (out seed).Nonempty ∧ (out seed).card≤I.budget) ∧
      ∀ O⊆I.facilities, O.Nonempty→O.card≤I.budget→
        (M:ℝ)≤(I.cost O:ℝ)→(I.cost O:ℝ)≤I.clients.card*(M:ℝ)→
        (∀ seed,(I.cost (out seed):ℝ)≤6*(I.cost O:ℝ)) ∧
        1-FailureBudget.failure gamma e I.size≤probability
          (fun seed=>(I.cost (out seed):ℝ)≤(2-gamma/2)*(I.cost O:ℝ)) := by
  obtain ⟨v,C,Q,d,hU⟩:=BinaryIntegralAll.uniform_program_long e
  refine ⟨v,C,Q,d,?_⟩
  intro I hD M hM
  dsimp only
  let := I.metric
  let := duplicateMetric I
  let eps : ℝ := gamma/16
  let u : ℚ := (gammaRat/16)*M/I.clients.card
  let cap:=Rounding.cap I.clients.card eps
  have heps : 0<eps := div_pos gamma_pos (by norm_num)
  have heps1 : eps<1 := by dsimp [eps];linarith [gamma_lt_one]
  have huR : (u:ℝ)=eps*(M:ℝ)/I.clients.card := by simp only [u,eps,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,gammaRat_cast]
  have hu : (0:ℝ)<u := by rw [huR];exact div_pos (mul_pos heps (by exact_mod_cast hM)) (by exact_mod_cast hD.card_pos)
  have hc : 0<cap := Rounding.cap_pos _ _
  let rm : MetricSpace (Fin (I.pointCount+I.pointCount)) := Rounding.metric (u:ℝ) hu cap hc
  let D:=I.clients.image left
  let F:=I.facilities.image right
  let k:=min I.budget I.facilities.card
  let δ : Fin (I.pointCount+I.pointCount)→Fin (I.pointCount+I.pointCount)→ℕ := Rounding.edge (u:ℝ) cap
  have hδ : ∀ i j,(δ i j:ℝ)=@dist _ rm.toDist i j := fun _ _=>rfl
  have hDE : D.card=I.clients.card := card_left _
  have hFE : F.card=I.facilities.card := card_right _
  have hk : 0<k := lt_min I.budget_pos I.facilities_nonempty.card_pos
  have hkF : k≤F.card := by rw [hFE];exact min_le_right _ _
  have hmat : (fun i j=>(δ i j:ℚ))=BinaryGlobalCall.matrix I M := by
    funext i j
    exact (round_edge (BinaryDuplicateMatrix.duplicate I.distance) (fun _ _=>rfl) u cap i j).symm
  have hb (x) (f) (_hf:f∈F) : δ x f≤Rounding.cap D.card (gamma/16) := by
    rw [hDE];exact Rounding.edge_le_cap _ _ _ _
  have hsep (w) (hw:w∈D) (f) (hf:f∈F) : (1:ℝ)≤@dist _ rm.toDist w f := by
    change (1:ℝ)≤(δ w f:ℝ)
    have hn : w≠f := fun he=>(Finset.disjoint_left.mp (BinaryTaggedSets.disjoint I.clients I.facilities) hw (he ▸ hf)).elim
    exact_mod_cast Rounding.edge_pos (u:ℝ) hc hn
  have hg : D.card+F.card≤I.bits.length := by rw [hDE,hFE];exact I.size_le_bitLength
  have hh:=@hU (I.pointCount+I.pointCount) rm δ hδ D F k (hD.image _) hk hkF hb hsep I.bits hg
  dsimp only at hh
  rw [hmat,hDE,hFE] at hh
  obtain ⟨S,hRun,hFeas,hProb,_⟩:=hh
  let K := (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
  let R (seed:Fin K→Bool) := BinaryIntegralAll.output v C Q d (BinaryGlobalCall.matrix I M) D F S cap k I.bits (List.ofFn seed)
  have hRF (seed:Fin K→Bool) : R seed⊆F := (hFeas seed).1
  choose out houtF houtImage houtcard using fun seed:Fin K→Bool=>project_subset I.facilities (R seed) (hRF seed)
  have houtN (seed:Fin K→Bool) : (out seed).Nonempty := by
    have h:((out seed).image right).Nonempty := by rw [houtImage];exact (hFeas seed).2.1
    exact Finset.image_nonempty.mp h
  have houtK (seed:Fin K→Bool) : (out seed).card≤I.budget :=
    (houtcard seed).trans_le ((hFeas seed).2.2.1.trans (min_le_left _ _))
  refine ⟨out,?_,fun seed=>⟨houtF seed,houtN seed,houtK seed⟩,?_⟩
  · intro seed
    rw [BinaryGlobalCall.run_pack]
    have ht : (List.ofFn seed).take K=List.ofFn seed := by exact List.take_of_length_le (by rw [List.length_ofFn])
    change BinaryTaggedSets.unshift (pairBits (I.pointCount.bits,
      BinaryIntegralAll.run v C Q d (BinaryGlobalCall.integralPack I M ((List.ofFn seed).take K))))=_
    rw [ht]
    have hr:=hRun seed
    change BinaryIntegralAll.run v C Q d (BinaryGlobalCall.integralPack I M (List.ofFn seed))=BinaryFinSet.encode (R seed) at hr
    rw [hr,←houtImage seed,BinaryTaggedSets.unshift_encode]
  · intro O hOF hO hOk hMP hPM
    have hOk' : (O.image right).card≤k := by rw [card_right];exact le_min hOk (Finset.card_le_card hOF)
    have hopt:=@optimum_le _ rm.toPseudoMetricSpace F D (O.image right) k (Finset.image_subset_image hOF) (hO.image _) hOk'
    have heq (T : Finset (Fin (I.pointCount+I.pointCount))) :
        @Completion.realCost _ rm.toPseudoMetricSpace D T=(Rounding.cost (u:ℝ) cap D T:ℝ) := by
      let := rm
      rw [IntegralCandidates.realCost_eq];exact Rounding.metric_cost _ _ _ _ _ _
    have hcO : @cost _ (duplicateMetric I) D (O.image right)=(I.cost O:ℝ) := by
      rw [show D=I.clients.image left from rfl,cost_image,I.metric_cost]
    have hcS (seed:Fin K→Bool) : @cost _ (duplicateMetric I) D (R seed)=(I.cost (out seed):ℝ) := by
      rw [←houtImage seed,show D=I.clients.image left from rfl,cost_image,I.metric_cost]
    have htransfer (seed:Fin K→Bool) (A : ℝ) (hA : 0≤A) (hA5 : A≤5)
        (hs : @Completion.realCost _ rm.toPseudoMetricSpace D (R seed)≤A*@optimum _ rm.toPseudoMetricSpace F D k) :
        (I.cost (out seed):ℝ)≤A*(1+eps)*(I.cost O:ℝ) := by
      have hs':=hs.trans (mul_le_mul_of_nonneg_left hopt hA)
      rw [heq,Rounding.metric_cost] at hs'
      have ht:=Rounding.factor_transfer D (O.image right) (R seed) (hO.image _) (hFeas seed).2.1
        (by rw [hDE];exact hD.card_pos) eps (M:ℝ) A heps heps1 (by exact_mod_cast hM)
        (by rw [hcO];exact hMP) (by rw [hcO,hDE];exact hPM) hA hA5
      rw [hDE,←huR] at ht
      have hlast:=ht hs'
      rw [hcS,hcO] at hlast
      exact hlast
    have hcost0 : 0≤(I.cost O:ℝ) := by exact_mod_cast I.cost_nonneg O
    constructor
    · intro seed
      exact (htransfer seed 5 (by norm_num) le_rfl (hFeas seed).2.2.2).trans
        (mul_le_mul_of_nonneg_right RoundedAssembly.rounded_fallback_factor hcost0)
    · apply hProb.trans
      apply probability_mono
      intro seed hs
      exact (htransfer seed _ RoundedAssembly.successful_factor_nonneg RoundedAssembly.successful_factor_le_five hs).trans
        (mul_le_mul_of_nonneg_right RoundedAssembly.rounded_successful_factor hcost0)
end MetricKMedianRecovery.BitMachine.BinaryGlobalRounding

end OAI
