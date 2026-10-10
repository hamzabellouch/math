import OAI.Combinatorics.Sidorenko.Refinement

namespace OAI


section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Mix
variable {A : Type*} [Fintype A]
lemma exists_positive_perturbation (f g : A → ℝ) (hf : ∀ a,0≤f a)
    (hg : ∀ a,f a=0 → 0≤g a) :
    ∃ ε : ℝ,0<ε ∧ ∀ a,0≤f a+ε*g a ∧ (f a+ε*g a=0 ↔ f a=0 ∧ g a=0) := by
  have hv : ∀ᶠ ε : ℝ in nhds 0,∀ a,f a≠0 → 0<f a+ε*g a := by
    apply eventually_all.mpr; intro a
    by_cases h : f a=0
    · exact Filter.Eventually.of_forall (fun _ hn => (hn h).elim)
    · have hpos : 0<f a := lt_of_le_of_ne (hf a) (Ne.symm h)
      have ht : Tendsto (fun ε : ℝ => f a+ε*g a) (nhds 0) (nhds (f a)) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => f a) (nhds 0) (nhds (f a))).add ((tendsto_id : Tendsto (fun ε : ℝ => ε) (nhds 0) (nhds 0)).mul_const (g a))
      exact (ht.eventually (lt_mem_nhds hpos)).mono (fun _ h _ => h)
  have hw : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),0<ε ∧ ∀ a,f a≠0 → 0<f a+ε*g a :=
    eventually_mem_nhdsWithin.and (hv.filter_mono nhdsWithin_le_nhds)
  obtain ⟨ε,hε,he⟩ := hw.exists
  refine ⟨ε,hε,fun a => ?_⟩
  by_cases ha : f a=0
  · have hga := hg a ha
    rw [ha,zero_add]
    refine ⟨mul_nonneg hε.le hga,?_⟩
    simp only [true_and]
    exact mul_eq_zero.trans (or_iff_right (ne_of_gt hε))
  · have hp := he a ha
    exact ⟨hp.le,iff_of_false (ne_of_gt hp) (fun h => ha h.1)⟩
end Mix
section Pin
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
omit [DecidableEq I] [DecidableEq C] in
lemma sum_hist_sq_nonneg (f g : I → C → ℕ) :
    0≤∑ i,∑ c,((f i c:ℝ)-(g i c:ℝ))^2 :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
omit [DecidableEq I] [DecidableEq C] in
lemma sum_hist_sq_eq_zero (f g : I → C → ℕ) :
    (∑ i,∑ c,((f i c:ℝ)-(g i c:ℝ))^2)=0 ↔ f=g := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Finset.mem_univ,forall_true_left]
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),Finset.mem_univ,forall_true_left,
    sq_eq_zero_iff,sub_eq_zero,Nat.cast_inj]
  exact ⟨fun h => funext (fun i => funext (h i)),fun h => by rw [h]; simp⟩
lemma roundScore_loss_properties (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    let loss := (roundScores t h cI cJ).score t h id id-(roundScores t h cI cJ).score t h a b
    0≤loss ∧ (loss=0 ↔
      (∀ i,neighborHistogram t (cJ ∘ h) (a i)=neighborHistogram t (cJ ∘ h) i) ∧
      (∀ j,neighborHistogram h (cI ∘ t) (b j)=neighborHistogram h (cI ∘ t) j)) := by
  dsimp only
  rw [roundScore_loss t h cI cJ a b ha hb]
  have hL := sum_hist_sq_nonneg (fun i => neighborHistogram t (cJ ∘ h) (a i)) (neighborHistogram t (cJ ∘ h))
  have hR := sum_hist_sq_nonneg (fun j => neighborHistogram h (cI ∘ t) (b j)) (neighborHistogram h (cI ∘ t))
  refine ⟨add_nonneg hL hR,?_⟩
  rw [add_eq_zero_iff_of_nonneg hL hR,sum_hist_sq_eq_zero,sum_hist_sq_eq_zero]
  simp only [funext_iff]

noncomputable def VertexPairScores.mix (s r : VertexPairScores I J) (ε : ℝ) : VertexPairScores I J where
  left i := s.left i+ε*r.left i
  right j := s.right j+ε*r.right j
  pair i j := s.pair i j+ε*r.pair i j
omit [DecidableEq I] [DecidableEq J] in
lemma VertexPairScores.score_mix (s r : VertexPairScores I J) (ε : ℝ)
    (t : E → I) (h : E → J) (a : I → I) (b : J → J) :
    (s.mix r ε).score t h a b=s.score t h a b+ε*r.score t h a b := by
  simp only [score,mix,Finset.sum_add_distrib,←Finset.mul_sum]; ring

def PreservesColors (cI : I → C) (cJ : J → C) (m : (I → I) × (J → J)) : Prop :=
  (∀ i,cI (m.1 i)=cI i) ∧ ∀ j,cJ (m.2 j)=cJ j
lemma pinning_step (t : E → I) (h : E → J) (cI dI : I → C) (cJ dJ : J → C)
    (hI : ∀ v w,dI v=dI w ↔ cI v=cI w ∧ neighborHistogram t (cJ ∘ h) v=neighborHistogram t (cJ ∘ h) w)
    (hJ : ∀ v w,dJ v=dJ w ↔ cJ v=cJ w ∧ neighborHistogram h (cI ∘ t) v=neighborHistogram h (cI ∘ t) w)
    (s : VertexPairScores I J)
    (hs : ∀ m : (I → I) × (J → J),0≤ s.score t h id id-s.score t h m.1 m.2 ∧
      (s.score t h id id-s.score t h m.1 m.2=0 ↔ PreservesColors cI cJ m)) :
    ∃ snew : VertexPairScores I J,∀ m : (I → I) × (J → J),0≤ snew.score t h id id-snew.score t h m.1 m.2 ∧
      (snew.score t h id id-snew.score t h m.1 m.2=0 ↔ PreservesColors dI dJ m) := by
  let r := roundScores t h cI cJ
  let f (m : (I → I) × (J → J)) := s.score t h id id-s.score t h m.1 m.2
  let g (m : (I → I) × (J → J)) := r.score t h id id-r.score t h m.1 m.2
  have hg (m) (hm : f m=0) := (hs m).2.mp hm
  have hp (m) (hm : f m=0) := roundScore_loss_properties t h cI cJ m.1 m.2 (hg m hm).1 (hg m hm).2
  obtain ⟨ε,hε,he⟩ := exists_positive_perturbation f g (fun m => (hs m).1) (fun m hm => (hp m hm).1)
  refine ⟨s.mix r ε,fun m => ?_⟩
  have halg : (s.mix r ε).score t h id id-(s.mix r ε).score t h m.1 m.2=f m+ε*g m := by
    simp only [VertexPairScores.score_mix,f,g]; ring
  rw [halg]
  refine ⟨(he m).1,(he m).2.trans ?_⟩
  constructor
  · rintro ⟨hf,hg0⟩
    obtain ⟨hL,hR⟩ := (hp m hf).2.mp hg0
    exact ⟨fun i => (hI _ _).mpr ⟨(hg m hf).1 i,hL i⟩,fun j => (hJ _ _).mpr ⟨(hg m hf).2 j,hR j⟩⟩
  · intro hm
    have hc : PreservesColors cI cJ m := ⟨fun i => ((hI _ _).mp (hm.1 i)).1,fun j => ((hJ _ _).mp (hm.2 j)).1⟩
    have hf := (hs m).2.mpr hc
    exact ⟨hf,(hp m hf).2.mpr ⟨fun i => ((hI _ _).mp (hm.1 i)).2,fun j => ((hJ _ _).mp (hm.2 j)).2⟩⟩
end Pin
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
lemma pinning_complex : ∃ s : VertexPairScores (Fin 13) (Fin 22),
    ∀ a b,(a,b)≠(id,id) → s.score cornerPoint (fun k : ActCorner => k.1) a b < s.score cornerPoint (fun k : ActCorner => k.1) id id := by
  let t := cornerPoint
  let h := fun k : ActCorner => k.1
  let s0 : VertexPairScores (Fin 13) (Fin 22) := ⟨fun _ => 0,fun _ => 0,fun _ _ => 0⟩
  have hcI : ∀ i,refineLeft0 i=0 := by decide
  have hcJ : ∀ j,refineRight0 j=1 := by decide
  have hs0 (m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22)) :
      0 ≤ s0.score t h id id-s0.score t h m.1 m.2 ∧
      (s0.score t h id id-s0.score t h m.1 m.2=0 ↔ PreservesColors refineLeft0 refineRight0 m) := by
    simp only [VertexPairScores.score,s0,Finset.sum_const_zero,add_zero,sub_self,le_refl,true_and]
    exact iff_of_true trivial ⟨fun i => (hcI _).trans (hcI i).symm,fun j => (hcJ _).trans (hcJ j).symm⟩
  have hL0 : neighborHistogram t (refineRight0 ∘ h)=histLeft0 := funext (fun i => funext (histLeft0_correct i))
  have hR0 : neighborHistogram h (refineLeft0 ∘ t)=histRight0 := funext (fun j => funext (histRight0_correct j))
  have hI0 : ∀ v w,refineLeft1 v=refineLeft1 w ↔ refineLeft0 v=refineLeft0 w ∧
      neighborHistogram t (refineRight0 ∘ h) v=neighborHistogram t (refineRight0 ∘ h) w := by
    simpa only [hL0] using refineLeft0_iff
  have hJ0 : ∀ v w,refineRight1 v=refineRight1 w ↔ refineRight0 v=refineRight0 w ∧
      neighborHistogram h (refineLeft0 ∘ t) v=neighborHistogram h (refineLeft0 ∘ t) w := by
    simpa only [hR0] using refineRight0_iff
  obtain ⟨s1,hs1⟩ := pinning_step t h refineLeft0 refineLeft1 refineRight0 refineRight1 hI0 hJ0 s0 hs0
  have hL1 : neighborHistogram t (refineRight1 ∘ h)=histLeft1 := funext (fun i => funext (histLeft1_correct i))
  have hR1 : neighborHistogram h (refineLeft1 ∘ t)=histRight1 := funext (fun j => funext (histRight1_correct j))
  have hI1 : ∀ v w,refineLeft2 v=refineLeft2 w ↔ refineLeft1 v=refineLeft1 w ∧
      neighborHistogram t (refineRight1 ∘ h) v=neighborHistogram t (refineRight1 ∘ h) w := by
    simpa only [hL1] using refineLeft1_iff
  have hJ1 : ∀ v w,refineRight2 v=refineRight2 w ↔ refineRight1 v=refineRight1 w ∧
      neighborHistogram h (refineLeft1 ∘ t) v=neighborHistogram h (refineLeft1 ∘ t) w := by
    simpa only [hR1] using refineRight1_iff
  obtain ⟨s2,hs2⟩ := pinning_step t h refineLeft1 refineLeft2 refineRight1 refineRight2 hI1 hJ1 s1 hs1
  have hL2 : neighborHistogram t (refineRight2 ∘ h)=histLeft2 := funext (fun i => funext (histLeft2_correct i))
  have hR2 : neighborHistogram h (refineLeft2 ∘ t)=histRight2 := funext (fun j => funext (histRight2_correct j))
  have hI2 : ∀ v w,refineLeft3 v=refineLeft3 w ↔ refineLeft2 v=refineLeft2 w ∧
      neighborHistogram t (refineRight2 ∘ h) v=neighborHistogram t (refineRight2 ∘ h) w := by
    simpa only [hL2] using refineLeft2_iff
  have hJ2 : ∀ v w,refineRight3 v=refineRight3 w ↔ refineRight2 v=refineRight2 w ∧
      neighborHistogram h (refineLeft2 ∘ t) v=neighborHistogram h (refineLeft2 ∘ t) w := by
    simpa only [hR2] using refineRight2_iff
  obtain ⟨s3,hs3⟩ := pinning_step t h refineLeft2 refineLeft3 refineRight2 refineRight3 hI2 hJ2 s2 hs2
  have hL3 : neighborHistogram t (refineRight3 ∘ h)=histLeft3 := funext (fun i => funext (histLeft3_correct i))
  have hR3 : neighborHistogram h (refineLeft3 ∘ t)=histRight3 := funext (fun j => funext (histRight3_correct j))
  have hI3 : ∀ v w,refineLeft4 v=refineLeft4 w ↔ refineLeft3 v=refineLeft3 w ∧
      neighborHistogram t (refineRight3 ∘ h) v=neighborHistogram t (refineRight3 ∘ h) w := by
    simpa only [hL3] using refineLeft3_iff
  have hJ3 : ∀ v w,refineRight4 v=refineRight4 w ↔ refineRight3 v=refineRight3 w ∧
      neighborHistogram h (refineLeft3 ∘ t) v=neighborHistogram h (refineLeft3 ∘ t) w := by
    simpa only [hR3] using refineRight3_iff
  obtain ⟨s4,hs4⟩ := pinning_step t h refineLeft3 refineLeft4 refineRight3 refineRight4 hI3 hJ3 s3 hs3
  refine ⟨s4,fun a b hne => ?_⟩
  have hp := hs4 (a,b)
  have hn : s4.score t h id id-s4.score t h a b≠0 := by
    intro hz
    have hc := hp.2.mp hz
    apply hne
    exact Prod.ext (funext (fun i => refineLeft_final (hc.1 i))) (funext (fun j => refineRight_final (hc.2 j)))
  exact sub_pos.mp (lt_of_le_of_ne hp.1 (Ne.symm hn))
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Weights
variable {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
noncomputable def exponentialNormalizer (s : A → ℝ) (ρ : ℝ) : ℝ := ∑ a,Real.exp (ρ*s a)
lemma exponentialNormalizer_pos (s : A → ℝ) (ρ : ℝ) : 0<exponentialNormalizer s ρ :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
noncomputable def exponentialPrior (s : A → ℝ) (ρ : ℝ) : FiniteLaw A where
  weight a := Real.exp (ρ*s a)/exponentialNormalizer s ρ
  nonneg _ := div_nonneg (Real.exp_pos _).le (exponentialNormalizer_pos s ρ).le
  total := by rw [←Finset.sum_div]; exact div_self (ne_of_gt (exponentialNormalizer_pos s ρ))
lemma prod_exp_weight (ρ : ℝ) (s : I → ℝ) :
    (∏ i,Real.exp (ρ*s i))=Real.exp (ρ*∑ i,s i) := by
  rw [Finset.mul_sum,Real.exp_sum]
lemma exponentialPrior_product (s : A → ℝ) (ρ : ℝ) (a : I → A) :
    (∏ i,(exponentialPrior s ρ).weight (a i))=
      Real.exp (ρ*∑ i,s (a i))/(exponentialNormalizer s ρ)^Fintype.card I := by
  simp only [exponentialPrior,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,prod_exp_weight]
omit [Nonempty A] in
lemma exponential_dominant_limit (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀) :
    Tendsto (fun ρ : ℝ => ∑ a,c a*Real.exp (ρ*(s a-s a₀))) atTop (nhds (c a₀)) := by
  have h (a : A) : Tendsto (fun ρ : ℝ => c a*Real.exp (ρ*(s a-s a₀))) atTop
      (nhds (if a=a₀ then c a₀ else 0)) := by
    by_cases ha : a=a₀
    · subst a; simp
    · have hd : s a-s a₀<0 := sub_neg.mpr (hs a ha)
      have ht := Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg hd (tendsto_id : Tendsto (fun ρ : ℝ => ρ) atTop atTop))
      simpa only [ha,ite_false,mul_comm,mul_zero,Function.comp_def,id_eq] using ht.const_mul (c a)
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using tendsto_finsetSum Finset.univ (fun a _ => h a)
omit [Nonempty A] in
lemma exponential_dominant_negative (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀)
    (hc : c a₀<0) : ∃ ρ : ℝ,0<ρ ∧ (∑ a,c a*Real.exp (ρ*s a))<0 := by
  have hlim := exponential_dominant_limit s c a₀ hs
  have he := (hlim.eventually (gt_mem_nhds hc)).and (eventually_gt_atTop 0)
  obtain ⟨ρ,hρ,hpos⟩ := he.exists
  refine ⟨ρ,hpos,?_⟩
  have halg : (∑ a,c a*Real.exp (ρ*s a))=
      Real.exp (ρ*s a₀)*(∑ a,c a*Real.exp (ρ*(s a-s a₀))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [mul_left_comm,←Real.exp_add]
    congr 2; ring
  rw [halg]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hρ
end Weights
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Gibbs
variable {I J E : Type*} [Fintype I] [Fintype J] [Fintype E] [Nonempty I] [Nonempty J]
noncomputable def gibbsThinning (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J) : ℝ :=
  Real.exp (ρ*(s.pair a b-M))
omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
lemma gibbsThinning_pos (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J) :
    0<gibbsThinning s ρ M a b := Real.exp_pos _
omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
lemma gibbsThinning_le_one (s : VertexPairScores I J) (ρ M : ℝ) (hρ : 0≤ρ)
    (hM : ∀ a b,s.pair a b≤M) (a : I) (b : J) : gibbsThinning s ρ M a b≤1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos hρ (sub_nonpos.mpr (hM a b))
noncomputable def gibbsPrefactor (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-ρ*(n:ℝ)*M)/((exponentialNormalizer s.left ρ)^Fintype.card I*(exponentialNormalizer s.right ρ)^Fintype.card J)
lemma gibbsPrefactor_pos (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ) : 0<gibbsPrefactor s ρ M n := by
  unfold gibbsPrefactor
  exact div_pos (Real.exp_pos _) (mul_pos (pow_pos (exponentialNormalizer_pos _ _) _) (pow_pos (exponentialNormalizer_pos _ _) _))
lemma gibbs_weight_formula (s : VertexPairScores I J) (ρ M : ℝ) (t : E → I) (h : E → J)
    (a : I → I) (b : J → J) :
    (∏ i,(exponentialPrior s.left ρ).weight (a i))*(∏ j,(exponentialPrior s.right ρ).weight (b j))*
        (∏ e,gibbsThinning s ρ M (a (t e)) (b (h e)))=
      gibbsPrefactor s ρ M (Fintype.card E)*Real.exp (ρ*s.score t h a b) := by
  simp only [exponentialPrior_product,gibbsThinning,prod_exp_weight]
  rw [div_mul_div_comm,div_mul_eq_mul_div,mul_assoc,←Real.exp_add,←Real.exp_add]
  unfold gibbsPrefactor
  rw [div_mul_eq_mul_div,←Real.exp_add]
  congr 2
  simp only [VertexPairScores.score,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring
end Gibbs
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
lemma averagedCoefficient_gibbs (s : VertexPairScores (Fin 13) (Fin 22)) (ρ M : ℝ)
    (h0 : ∀ a b,0≤gibbsThinning s ρ M a b) (h1 : ∀ a b,gibbsThinning s ρ M a b≤1) :
    averagedCoefficient (exponentialPrior s.left ρ) (exponentialPrior s.right ρ)
      (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b))=
      gibbsPrefactor s ρ M 66*(∑ m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22),
        typedCoefficient basePairLaw m.1 m.2*Real.exp (ρ*s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2)) := by
  unfold averagedCoefficient FiniteLaw.mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  dsimp only
  rw [typedCoefficient_thinned]
  change ((∏ i,(exponentialPrior s.left ρ).weight (m.1 i))*(∏ j,(exponentialPrior s.right ρ).weight (m.2 j)))*
    ((∏ k : ActCorner,gibbsThinning s ρ M (m.1 (cornerPoint k)) (m.2 k.1))*typedCoefficient basePairLaw m.1 m.2)=_
  rw [←mul_assoc,gibbs_weight_formula]
  have hc : Fintype.card ActCorner=66 := by decide
  rw [hc]; ring
lemma exists_negative_coefficient : ∃ (π : FiniteLaw (Fin 13)) (ν : FiniteLaw (Fin 22))
    (p : Fin 13 → Fin 22 → FiniteLaw (Activation ActCorner)),
    (∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) ∧ averagedCoefficient π ν p<0 := by
  obtain ⟨s,hs⟩ := pinning_complex
  let Q := fun m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22) => s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2
  let C := fun m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22) => typedCoefficient basePairLaw m.1 m.2
  have hc : C (id,id)<0 := by
    change activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))<0
    rw [basePairLaw_identity]; exact neg_neg_of_pos (pow_pos (by norm_num) _)
  obtain ⟨ρ,hρ,hneg⟩ := exponential_dominant_negative Q C (id,id) (fun m hm => hs m.1 m.2 hm) hc
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun ab : Fin 13 × Fin 22 => s.pair ab.1 ab.2)
  have hM (a : Fin 13) (b : Fin 22) : s.pair a b≤M := Finset.le_sup' (fun ab : Fin 13 × Fin 22 => s.pair ab.1 ab.2) (Finset.mem_univ (a,b))
  have h0 (a : Fin 13) (b : Fin 22) : 0≤gibbsThinning s ρ M a b := (gibbsThinning_pos s ρ M a b).le
  have h1 (a : Fin 13) (b : Fin 22) : gibbsThinning s ρ M a b≤1 := gibbsThinning_le_one s ρ M hρ.le hM a b
  refine ⟨exponentialPrior s.left ρ,exponentialPrior s.right ρ,
    (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b)),?_,?_⟩
  · intro a b α hα
    exact thinnedLaw_zero _ (basePairLaw_zero a b) _ _ _ α hα
  · rw [averagedCoefficient_gibbs]
    exact mul_neg_of_pos_of_neg (gibbsPrefactor_pos s ρ M 66) hneg
end SidorenkoCounterexample

end

end OAI
