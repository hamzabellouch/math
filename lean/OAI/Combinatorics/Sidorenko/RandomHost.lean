import OAI.Combinatorics.Sidorenko.Symmetrization

namespace OAI

/-! # Sampling a finite simple counterexample

The strict kernel inequality survives independent random sampling at sufficiently
large finite size. Homomorphism counts include noninjective maps, whose collision
error is bounded separately. The resulting simple graph has at least one edge.
-/

section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
lemma independent_mean_unit (p : FiniteLaw A) (f : A → ℝ) :
    (independent (fun _ : Unit => p)).mean (fun x => f (x ()))=p.mean f := by
  unfold mean independent
  apply Fintype.sum_equiv (Equiv.funUnique Unit A)
  intro x
  simp only [Fintype.prod_unique]; rfl
lemma independent_mean_apply (p : I → FiniteLaw A) (i : I) (f : A → ℝ) :
    (independent p).mean (fun x => f (x i))=(p i).mean f := by
  have h := independent_mean_injective p (fun _ : Unit => i) (fun _ _ _ => Subsingleton.elim _ _)
    (fun x => f (x ()))
  exact h.trans (independent_mean_unit (p i) f)
lemma independent_mean_two (p : FiniteLaw A) {i j : I} (hij : i≠j) (f : A → A → ℝ) :
    (independent (fun _ : I => p)).mean (fun x => f (x i) (x j))=p.mean (fun a => p.mean (f a)) := by
  let e : Unit ⊕ Unit → I := Sum.elim (fun _ => i) (fun _ => j)
  have he : Function.Injective e := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact (hij h).elim
    · exact (hij h.symm).elim
    · rfl
  have h := independent_mean_injective (fun _ : I => p) e he
    (fun x => f (x (.inl ())) (x (.inr ())))
  dsimp [e] at h
  rw [h,independent_mean_sum]
  change (independent (fun _ : Unit => p)).mean (fun x =>
    (independent (fun _ : Unit => p)).mean (fun y => f (x ()) (y ())))=_
  simp_rw [independent_mean_unit]
  exact independent_mean_unit p (fun a => p.mean (f a))
lemma uniform_mean_equal [Nonempty A] :
    (uniform : FiniteLaw A).mean (fun a => uniform.mean (fun b => if a=b then (1:ℝ) else 0))=
      (Fintype.card A : ℝ)⁻¹ := by
  have hi (a : A) : (uniform : FiniteLaw A).mean (fun b => if a=b then (1:ℝ) else 0)=(Fintype.card A : ℝ)⁻¹ := by
    simp [mean,uniform]
  simp only [hi,mean_const]
noncomputable def coin (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : FiniteLaw Bool :=
  mixture (dirac true) (dirac false) t ht ht1
noncomputable def boolValue (b : Bool) : ℝ := if b then 1 else 0
lemma boolValue_nonneg (b : Bool) : 0≤boolValue b := by cases b <;> norm_num [boolValue]
lemma boolValue_le_one (b : Bool) : boolValue b≤1 := by cases b <;> norm_num [boolValue]
lemma coin_mean (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : (coin t ht ht1).mean boolValue=t := by
  simp [coin,mean_mixture,boolValue]
end FiniteLaw
section Sample
variable {V : Type*} [Fintype V] [DecidableEq V]
def bitsGraph (b : Sym2 V → Bool) : SimpleGraph V where
  Adj x y := x≠y ∧ b s(x,y)=true
  symm.symm := by intro x y h; exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
  loopless.irrefl := by intro x h; exact h.1 rfl
omit [Fintype V] in
lemma bitsGraph_edgeIndicator (b : Sym2 V → Bool) (x y : V) :
    edgeIndicator (bitsGraph b) x y=if x=y then 0 else FiniteLaw.boolValue (b s(x,y)) := by
  by_cases h : x=y <;> simp [edgeIndicator,bitsGraph,FiniteLaw.boolValue,h]
noncomputable def edgeCoinLaw (U : SymmetricCounterKernel) (z : V → U.Ω) : FiniteLaw (Sym2 V → Bool) :=
  FiniteLaw.independent (fun e => FiniteLaw.coin
    (Sym2.lift ⟨fun a b => U.value (z a) (z b),fun a b => U.symm (z a) (z b)⟩ e)
    (by induction e using Sym2.inductionOn; exact U.nonneg _ _)
    (by induction e using Sym2.inductionOn; exact U.le_one _ _))
lemma edgeCoinLaw_mean (U : SymmetricCounterKernel) (z : V → U.Ω) (x y : V) :
    (edgeCoinLaw U z).mean (fun b => edgeIndicator (bitsGraph b) x y)=
      if x=y then 0 else U.value (z x) (z y) := by
  simp only [bitsGraph_edgeIndicator]
  by_cases h : x=y
  · simp [h]
  · simp only [h,ite_false,edgeCoinLaw]
    rw [FiniteLaw.independent_mean_apply,FiniteLaw.coin_mean]; rfl
end Sample
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
def cornerEdge (k : ActCorner) : Sym2 PatternVertex := s(Sum.inl (cornerPoint k),Sum.inr k.1)
lemma cornerEdge_injective : Function.Injective cornerEdge := by
  rintro ⟨j,r⟩ ⟨j',r'⟩ h
  simp only [cornerEdge,cornerPoint,Sym2.eq_iff,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,and_false,or_false] at h
  obtain ⟨h,hj⟩ := h
  subst j'
  exact congrArg (Prod.mk j) (faceVertex_injective j h)
section Random
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
lemma mappedCorner_injective (f : PatternVertex → V) (hf : Function.Injective f) :
    Function.Injective (fun k : ActCorner => s(f (.inl (cornerPoint k)),f (.inr k.1))) :=
  (Sym2.map.injective hf).comp cornerEdge_injective
omit [Fintype V] [DecidableEq V] in
lemma mappedCorner_ne (f : PatternVertex → V) (hf : Function.Injective f) (k : ActCorner) :
    f (.inl (cornerPoint k))≠f (.inr k.1) := by
  intro h; have hc := hf h; cases hc
lemma expectedHom_conditional (U : SymmetricCounterKernel) (z : V → U.Ω)
    (f : PatternVertex → V) (hf : Function.Injective f) :
    (edgeCoinLaw U z).mean (fun b => homIndicator (bitsGraph b) f)=
      ∏ k : ActCorner,U.value (z (f (.inl (cornerPoint k)))) (z (f (.inr k.1))) := by
  simp only [homIndicator,bitsGraph_edgeIndicator,mappedCorner_ne f hf,ite_false]
  unfold edgeCoinLaw
  rw [FiniteLaw.independent_mean_injective _ _ (mappedCorner_injective f hf)
    (fun b => ∏ k : ActCorner,FiniteLaw.boolValue (b k))]
  rw [FiniteLaw.independent_mean_product]
  apply Finset.prod_congr rfl; intro k _
  rw [FiniteLaw.coin_mean]; rfl
noncomputable def hostBitsLaw (U : SymmetricCounterKernel) : FiniteLaw (Sym2 V → Bool) :=
  (FiniteLaw.independent (fun _ : V => U.law)).bind (edgeCoinLaw U)
lemma expectedHom_injective (U : SymmetricCounterKernel) (f : PatternVertex → V) (hf : Function.Injective f) :
    (hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f)=bipartiteMoment U.law U.law U.value := by
  rw [hostBitsLaw,FiniteLaw.mean_bind]
  simp_rw [expectedHom_conditional U _ f hf]
  rw [FiniteLaw.independent_mean_injective _ _ hf (fun z =>
    ∏ k : ActCorner,U.value (z (.inl (cornerPoint k))) (z (.inr k.1)))]
  exact sourceMoment_eq_bipartite U.law U.value
lemma expectedEdge (U : SymmetricCounterKernel) (x y : V) :
    (hostBitsLaw U).mean (fun b => edgeIndicator (bitsGraph b) x y)=
      if x=y then 0 else kernelMean U.law U.law U.value := by
  rw [hostBitsLaw,FiniteLaw.mean_bind]
  simp_rw [edgeCoinLaw_mean]
  by_cases h : x=y
  · simp only [h,ite_true,FiniteLaw.mean_const]
  · simp only [h,ite_false]
    exact FiniteLaw.independent_mean_two U.law h U.value
lemma expectedHom_nonneg (U : SymmetricCounterKernel) (f : PatternVertex → V) :
    0≤(hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f) :=
  FiniteLaw.mean_nonneg _ (fun _b => homIndicator_nonneg _ _)
lemma expectedHom_le_one (U : SymmetricCounterKernel) (f : PatternVertex → V) :
    (hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f)≤1 :=
  FiniteLaw.mean_bound _ (fun _b => homIndicator_le_one _ _)
end Random
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
abbrev CollisionPair := {ab : Fin 35 × Fin 35 // ab.1<ab.2}
def sourceFinEquiv : PatternVertex ≃ Fin 35 := finSumFinEquiv
lemma collisionPair_card : Fintype.card CollisionPair=595 := by
  rw [Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin 35)))
  simpa only [Finset.univ_product_univ,Finset.card_univ,Fintype.card_fin,
    show Nat.choose 35 2=595 by decide] using h
noncomputable def collisionValue {V : Type*} (p : CollisionPair) (f : PatternVertex → V) : ℝ :=
  if f (sourceFinEquiv.symm p.1.1)=f (sourceFinEquiv.symm p.1.2) then 1 else 0
lemma collisionValue_nonneg {V : Type*} (p : CollisionPair) (f : PatternVertex → V) : 0≤collisionValue p f := by
  unfold collisionValue; split <;> norm_num
noncomputable def noninjectiveIndicator {V : Type*} (f : PatternVertex → V) : ℝ :=
  if Function.Injective f then 0 else 1
lemma noninjective_le_collisionSum {V : Type*} (f : PatternVertex → V) :
    noninjectiveIndicator f≤∑ p : CollisionPair,collisionValue p f := by
  unfold noninjectiveIndicator
  by_cases hf : Function.Injective f
  · simp only [hf,ite_true]; exact Finset.sum_nonneg (fun p _ => collisionValue_nonneg p f)
  · rw [ite_eq_right hf]
    have hm : ∃ p : CollisionPair,f (sourceFinEquiv.symm p.1.1)=f (sourceFinEquiv.symm p.1.2) := by
      simp only [Function.Injective,not_forall] at hf
      obtain ⟨a,b,hfab,hne⟩ := hf
      rcases lt_or_gt_of_ne (fun h => hne (sourceFinEquiv.injective h)) with h|h
      · exact ⟨⟨(sourceFinEquiv a,sourceFinEquiv b),h⟩,by simpa using hfab⟩
      · exact ⟨⟨(sourceFinEquiv b,sourceFinEquiv a),h⟩,by simpa using hfab.symm⟩
    obtain ⟨p,hp⟩ := hm
    calc
      1 = collisionValue p f := by simp [collisionValue,hp]
      _ ≤ _ := Finset.single_le_sum (fun q _ => collisionValue_nonneg q f) (Finset.mem_univ p)
lemma collisionPair_ne (p : CollisionPair) : sourceFinEquiv.symm p.1.1≠sourceFinEquiv.symm p.1.2 :=
  fun h => (ne_of_lt p.2) (sourceFinEquiv.symm.injective h)
lemma collisionValue_mean {V : Type*} [Fintype V] [Nonempty V] (p : CollisionPair) :
    (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean (collisionValue p)=
      (Fintype.card V : ℝ)⁻¹ := by
  unfold collisionValue
  rw [FiniteLaw.independent_mean_two FiniteLaw.uniform (collisionPair_ne p) (fun a b : V => if a=b then (1:ℝ) else 0)]
  exact FiniteLaw.uniform_mean_equal
lemma noninjective_mean_bound {V : Type*} [Fintype V] [Nonempty V] :
    (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
      noninjectiveIndicator≤595/(Fintype.card V : ℝ) := by
  calc
    _ ≤ (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
        (fun f => ∑ p : CollisionPair,collisionValue p f) := FiniteLaw.mean_mono _ noninjective_le_collisionSum
    _ = _ := by
      rw [FiniteLaw.mean_sum]
      simp only [collisionValue_mean,Finset.sum_const,Finset.card_univ,collisionPair_card,nsmul_eq_mul]
      norm_num [div_eq_mul_inv]
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Bounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
lemma uniformMean_offdiag (c : ℝ) :
    uniformMean (fun ab : V × V => if ab.1=ab.2 then 0 else c)=(1-(Fintype.card V : ℝ)⁻¹)*c := by
  rw [uniformMean_prod]
  have hi (a : V) : uniformMean (fun b : V => if a=b then 0 else c)=(1-(Fintype.card V : ℝ)⁻¹)*c := by
    calc
      _ = uniformMean (fun b : V => c-c*(if a=b then (1:ℝ) else 0)) := by
        apply uniformMean_congr; intro b; split <;> simp_all
      _ = _ := by
        rw [uniformMean_sub,uniformMean_const,uniformMean_mul]
        simp [uniformMean]; ring
  simp only [hi,uniformMean_const]
lemma expectedEdgeDensity (U : SymmetricCounterKernel) :
    (hostBitsLaw U).mean (fun b : Sym2 V → Bool => edgeDensity (bitsGraph b))=
      (1-(Fintype.card V : ℝ)⁻¹)*kernelMean U.law U.law U.value := by
  simp_rw [edgeDensity_eq_mean]
  rw [←uniformMean_law_swap]
  simp_rw [expectedEdge]
  exact uniformMean_offdiag _
omit [Nonempty V] in
lemma expectedHom_map_bound (U : SymmetricCounterKernel) (f : PatternVertex → V) :
    (hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f)≤
      bipartiteMoment U.law U.law U.value+noninjectiveIndicator f := by
  unfold noninjectiveIndicator
  by_cases hf : Function.Injective f
  · rw [ite_eq_left hf,add_zero,expectedHom_injective U f hf]
  · rw [ite_eq_right hf]
    have hτ := bipartiteMoment_nonneg U.law U.law U.value U.nonneg
    exact (expectedHom_le_one U f).trans (by linarith)
lemma expectedHomDensity_bound (U : SymmetricCounterKernel) :
    (hostBitsLaw U).mean (fun b : Sym2 V → Bool => homDensity H (bitsGraph b))≤
      bipartiteMoment U.law U.law U.value+595/(Fintype.card V : ℝ) := by
  simp_rw [homDensity_eq_mean]
  rw [←uniformMean_law_swap,←FiniteLaw.independent_uniform_mean]
  calc
    _ ≤ (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
        (fun f => bipartiteMoment U.law U.law U.value+noninjectiveIndicator f) :=
      FiniteLaw.mean_mono _ (expectedHom_map_bound U)
    _ = bipartiteMoment U.law U.law U.value+
        (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
          noninjectiveIndicator := by rw [FiniteLaw.mean_add,FiniteLaw.mean_const]
    _ ≤ _ := add_le_add le_rfl (noninjective_mean_bound (V := V))
end Bounds
lemma finiteHost_arithmetic {μ τ : ℝ} (hμ : 0≤μ) (hgap : τ<μ^66) {n : ℕ} (hn : 0<n)
    (hsize : (595+66*μ^66)/(μ^66-τ)<n) :
    τ+595/(n:ℝ)<((1-1/(n:ℝ))*μ)^66 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hΔ : 0<μ^66-τ := sub_pos.mpr hgap
  have hs := (div_lt_iff₀ hΔ).mp hsize
  have hd : (595+66*μ^66)/(n:ℝ)<μ^66-τ := (div_lt_iff₀ hn').mpr (by nlinarith [hs])
  rw [add_div] at hd
  have hfirst : τ+595/(n:ℝ)<μ^66-66*μ^66/(n:ℝ) := by linarith
  apply hfirst.trans_le
  have hinv : 1/(n:ℝ)≤1 := (div_le_one hn').mpr hn1
  have hb := one_add_mul_le_pow (a := -(1/(n:ℝ))) (by linarith : (-2:ℝ)≤-(1/(n:ℝ))) 66
  have hmul := mul_le_mul_of_nonneg_right hb (pow_nonneg hμ 66)
  calc
    _ = (1+(66:ℝ)* -(1/(n:ℝ)))*μ^66 := by ring
    _ ≤ (1+ -(1/(n:ℝ)))^66*μ^66 := hmul
    _ = _ := by rw [sub_eq_add_neg,mul_pow]
lemma finiteHost_exists_at_size (U : SymmetricCounterKernel) {n : ℕ} (hn : 0<n)
    (hsize : (595+66*(kernelMean U.law U.law U.value)^66)/
      ((kernelMean U.law U.law U.value)^66-bipartiteMoment U.law U.law U.value)<n) :
    ∃ G : SimpleGraph (Fin n),(∃ u v,G.Adj u v) ∧ homDensity H G<(edgeDensity G)^66 := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hmean := finiteHost_arithmetic U.mean_pos.le U.gap hn hsize
  have hexp : (hostBitsLaw U).mean (fun b : Sym2 (Fin n) → Bool => homDensity H (bitsGraph b))<
      ((hostBitsLaw U).mean (fun b : Sym2 (Fin n) → Bool => edgeDensity (bitsGraph b)))^66 := by
    rw [expectedEdgeDensity,Fintype.card_fin]
    exact (expectedHomDensity_bound U).trans_lt (by simpa only [Fintype.card_fin,one_div] using hmean)
  have hj := FiniteLaw.mean_pow_le (hostBitsLaw U)
    (fun b : Sym2 (Fin n) → Bool => edgeDensity (bitsGraph b)) (fun _b => edgeDensity_nonneg _) 66
  obtain ⟨b,hb⟩ := FiniteLaw.exists_lt_of_mean_lt (hostBitsLaw U) (hexp.trans_le hj)
  refine ⟨bitsGraph b,?_,hb⟩
  by_contra h
  push Not at h
  rw [edgeDensity_eq_zero_of_edgeless _ h,zero_pow (by decide : 66≠0)] at hb
  exact (not_lt_of_ge (homDensity_nonneg _)) hb
lemma finiteHost_main (U : SymmetricCounterKernel) : MainClaim := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 0 ((595+66*(kernelMean U.law U.law U.value)^66)/
    ((kernelMean U.law U.law U.value)^66-bipartiteMoment U.law U.law U.value)))
  have hnpos : 0<n := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hn
  have hsize := lt_of_le_of_lt (le_max_right _ _) hn
  obtain ⟨G,hG,hgap⟩ := finiteHost_exists_at_size U hnpos hsize
  exact ⟨n,hnpos,G,hG,hgap⟩
theorem main_proved : MainClaim := by
  obtain ⟨U⟩ := exists_symmetric_kernel
  exact finiteHost_main U
end SidorenkoCounterexample

end


namespace SidorenkoCounterexample


/-- The exact finite simple host conclusion of the counterexample theorem. -/
theorem main : ∃ n : ℕ, 0 < n ∧ ∃ G : SimpleGraph (Fin n),
    (∃ u v, G.Adj u v) ∧ homDensity H G < (edgeDensity G) ^ 66 := by
  exact main_proved

end SidorenkoCounterexample

end OAI
