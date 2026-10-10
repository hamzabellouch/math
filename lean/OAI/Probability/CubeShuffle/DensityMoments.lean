import OAI.Probability.CubeShuffle.RecursiveDensity

namespace OAI

namespace CubeShuffle
section ParallelExposure
variable {α B : Type*} {r s : ℕ}

def parallelFreshPre (pre : α ≃ B × Card (s+r))
    (lo : B → Card r × SwitchIndex s → Bool) : α ≃ (B × Card s) × Card r :=
  ((pre.trans (Equiv.prodCongr (Equiv.refl B) (cardSplit r s))).trans
    (Equiv.prodCongrRight (fun b =>
      (parallelPerm (lo b)).trans (Equiv.prodComm _ _)))).trans
    (Equiv.prodAssoc _ _ _).symm

def parallelFreshPost (post : B × Card (s+r) ≃ α) : (B × Card s) × Card r ≃ α :=
  (((Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl B)
    (Equiv.prodComm _ _))).trans (Equiv.prodCongr (Equiv.refl B) (cardSplit r s).symm)).trans post

def parallelAssembled (lo : B → Card r × SwitchIndex s → Bool)
    (hi : (B × Card s) × SwitchIndex r → Bool) : B × SwitchIndex (s+r) → Bool :=
  fun i => assembleBits r s (lo i.1) (fun j => hi ((i.1,j.1),j.2)) i.2

lemma parallel_exposed_perm (pre : α ≃ B × Card (s+r)) (post : B × Card (s+r) ≃ α)
    (lo : B → Card r × SwitchIndex s → Bool)
    (hi : (B × Card s) × SwitchIndex r → Bool) :
    relabeledPerm pre post (parallelAssembled lo hi) =
      relabeledPerm (parallelFreshPre pre lo) (parallelFreshPost post) hi := by
  ext x
  have h := butterfly_split r s (lo (pre x).1)
    (fun j => hi (((pre x).1,j.1),j.2)) (pre x).2
  have hh := congrArg (fun y => post ((pre x).1,(cardSplit r s).symm y)) h
  simpa only [relabeledPerm,parallelAssembled,parallelPerm,parallelFreshPre,parallelFreshPost,
    Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.prodCongrRight,Equiv.coe_fn_mk,
    Equiv.refl_apply,Equiv.prodComm_apply,Prod.swap,Equiv.prodAssoc_apply,
    Equiv.prodAssoc_symm_apply,Prod.map,Equiv.symm_apply_apply] using hh

/-- Uniform conditional FAC.4 for an actual parallel network, after fixed
exposure of every low layer and with arbitrary fixed endpoint relabelings. -/
theorem parallel_partially_exposed_log_mgf [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B]
    (pre : α ≃ B × Card (s+r)) (post : B × Card (s+r) ≃ α)
    (lo : B → Card r × SwitchIndex s → Bool) (S : Finset α)
    (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    Real.log (finiteMean (fun hi : (B × Card s) × SwitchIndex r → Bool =>
      q^(Fintype.card (RoutingNetwork.SelectedCycle
        (relabeledPerm pre post (parallelAssembled lo hi)) S)))) ≤
      (S.card:ℝ)/J*Real.log q + 2*q*S.card*Real.sqrt J/Real.sqrt ((2:ℝ)^r) := by
  simp_rw [parallel_exposed_perm]
  exact parallel_cycle_log_mgf (parallelFreshPre pre lo) (parallelFreshPost post) S J hJ q hq

end ParallelExposure
end CubeShuffle
namespace CubeShuffle
section CycleRelabel
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_inverse (p : Equiv.Perm α) (x : α) : orbitSet p⁻¹ x = orbitSet p x := by
  ext y
  simp only [mem_orbitSet,Equiv.Perm.sameCycle_inv]

lemma selectedCycle_inverse (p : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle p⁻¹ S) =
      Fintype.card (RoutingNetwork.SelectedCycle p S) := by
  apply Fintype.card_congr
  refine { toFun := fun C => ⟨C.val,?_,C.property.2⟩
           invFun := fun C => ⟨C.val,?_,C.property.2⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl }
  · obtain ⟨x,hx⟩ := C.property.1
    exact ⟨x,hx.trans (orbitSet_inverse p x)⟩
  · obtain ⟨x,hx⟩ := C.property.1
    exact ⟨x,hx.trans (orbitSet_inverse p x).symm⟩

lemma orbitSet_conjugate (p g : Equiv.Perm α) (x : α) :
    orbitSet (g*p*g⁻¹) (g x) = (orbitSet p x).image g := by
  ext y
  simp only [mem_orbitSet,Finset.mem_image]
  rw [Equiv.Perm.sameCycle_conj]
  change p.SameCycle (g.symm (g x)) (g.symm y) ↔ ∃ z, p.SameCycle x z ∧ g z = y
  rw [Equiv.symm_apply_apply]
  constructor
  · intro h
    exact ⟨g.symm y,h,g.apply_symm_apply y⟩
  · rintro ⟨z,hz,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hz

noncomputable def conjugateCycle (p g : Equiv.Perm α) (S : Finset α)
    (C : RoutingNetwork.SelectedCycle p S) :
    RoutingNetwork.SelectedCycle (g*p*g⁻¹) (S.image g) := by
  refine ⟨C.val.image g,?_,Finset.image_subset_image C.property.2⟩
  obtain ⟨x,hx⟩ := C.property.1
  exact ⟨g x,by rw [hx,orbitSet_conjugate]⟩

lemma conjugateCycle_injective (p g : Equiv.Perm α) (S : Finset α) :
    Function.Injective (conjugateCycle p g S) := by
  intro C D he
  apply Subtype.ext
  exact (Finset.image_injective g.injective) (congrArg Subtype.val he)

lemma selectedCycle_conjugate (p g : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle (g*p*g⁻¹) (S.image g)) =
      Fintype.card (RoutingNetwork.SelectedCycle p S) := by
  apply Nat.le_antisymm
  · have h := Fintype.card_le_of_injective _
      (conjugateCycle_injective (g*p*g⁻¹) g⁻¹ (S.image g))
    have hp : g⁻¹*(g*p*g⁻¹)*g = p := by group
    rw [inv_inv,hp] at h
    have hs : (S.image g).image g.symm = S := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,he⟩
        have hz' : z = x := by simpa only [Equiv.symm_apply_apply] using he
        exact hz' ▸ hz
      · intro hx
        exact ⟨g x,⟨x,hx,rfl⟩,g.symm_apply_apply x⟩
    change _ ≤ Fintype.card (RoutingNetwork.SelectedCycle p ((S.image g).image g.symm)) at h
    rw [hs] at h
    exact h
  · exact Fintype.card_le_of_injective _ (conjugateCycle_injective p g S)

lemma alternatingCycles_le_projection {ι : Type*} [Fintype ι]
    (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    PairRouting.alternatingCycles e p ≤
      Fintype.card (RoutingNetwork.SelectedCycle (PairRouting.alternatingProjection p)
        (boolFiber (PairRouting.labelSet e) false)) := by
  have h := CycleColoring.card_alternating_cycles_le (PairRouting.alternatingProjection p)
    (boolFiber (PairRouting.labelSet e) false) (boolFiber (PairRouting.labelSet e) true)
  simpa only [PairRouting.alternatingCycles,childJoin_boolFiber] using h

/-- Cycle orientation is explicitly reversed after conjugating by the fixed
input map. The remaining random zero-side map is a forward butterfly. -/
lemma projectionCycles_forward (X₀ X₁ Y₀ Y₁ : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle
      ((Y₀*X₀⁻¹)⁻¹*(Y₁*X₁⁻¹)) S) =
    Fintype.card (RoutingNetwork.SelectedCycle
      (X₀⁻¹*X₁*Y₁⁻¹*Y₀) (S.image X₀.symm)) := by
  let p := (Y₀*X₀⁻¹)⁻¹*(Y₁*X₁⁻¹)
  calc
    _ = Fintype.card (RoutingNetwork.SelectedCycle (X₀⁻¹*p*X₀)
        (S.image X₀.symm)) := by
      change Fintype.card (RoutingNetwork.SelectedCycle p S) = _
      have h := (selectedCycle_conjugate p X₀⁻¹ S).symm
      rw [inv_inv] at h
      exact h
    _ = Fintype.card (RoutingNetwork.SelectedCycle (X₀⁻¹*p*X₀)⁻¹
        (S.image X₀.symm)) := (selectedCycle_inverse _ _).symm
    _ = _ := by
      have he : (X₀⁻¹*p*X₀)⁻¹ = X₀⁻¹*X₁*Y₁⁻¹*Y₀ := by dsimp only [p]; group
      rw [he]

end CycleRelabel
end CubeShuffle
namespace CubeShuffle

noncomputable def cycleCoefficient (r J : ℕ) (q : ℝ) : ℝ :=
  Real.log q / J + 2*q*Real.sqrt J/Real.sqrt ((2:ℝ)^r)

lemma cycleCoefficient_nonneg (r J : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    0 ≤ cycleCoefficient r J q := by
  unfold cycleCoefficient
  exact add_nonneg (div_nonneg (Real.log_nonneg hq) (Nat.cast_nonneg _))
    (div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

lemma projectionSide_card_le {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (e : ι ↪ Bool × α) : (boolFiber (PairRouting.labelSet e) false).card ≤ Fintype.card ι := by
  have h := card_childJoin (boolFiber (PairRouting.labelSet e) false)
    (boolFiber (PairRouting.labelSet e) true)
  rw [childJoin_boolFiber,PairRouting.card_labelSet] at h
  omega

/-- Conditional moment for one actual pair-routing node. The input-side maps
are fixed; only the unexposed zero-side output butterfly is averaged. -/
theorem node_partial_mgf (r s : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Bool × Card (s+r)) (X₀ X₁ Y₁ : Equiv.Perm (Card (s+r)))
    (lo : Card r × SwitchIndex s → Bool) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(PairRouting.alternatingCycles e (fun b => if b then Y₁*X₁⁻¹ else
        butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi))*X₀⁻¹))) ≤
      Real.exp (Fintype.card ι * cycleCoefficient r J q) := by
  classical
  let S := boolFiber (PairRouting.labelSet e) false
  let S' := S.image X₀.symm
  let post := X₀⁻¹*X₁*Y₁⁻¹
  let count := fun hi : Card s × SwitchIndex r → Bool =>
    Fintype.card (RoutingNetwork.SelectedCycle
      ((Equiv.refl _).trans (butterflyPerm (s+r)
        (decodeButterfly (s+r) (assembleBits r s lo hi))) |>.trans post) S')
  have hpoint (hi : Card s × SwitchIndex r → Bool) :
      PairRouting.alternatingCycles e (fun b => if b then Y₁*X₁⁻¹ else
        butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi))*X₀⁻¹) ≤ count hi := by
    refine (alternatingCycles_le_projection e _).trans_eq ?_
    simp only [PairRouting.alternatingProjection,Bool.false_eq_true,↓reduceIte]
    change Fintype.card (RoutingNetwork.SelectedCycle
      ((butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi))*X₀⁻¹)⁻¹ * (Y₁*X₁⁻¹)) S) = count hi
    exact projectionCycles_forward X₀ X₁ _ Y₁ S
  have hm := partially_exposed_cycle_log_mgf (Equiv.refl (Card (s+r))) post lo S' J hJ q hq
  have hp : 0 < finiteMean (fun hi : Card s × SwitchIndex r → Bool => q^(count hi)) :=
    finiteMean_pos (fun _ => pow_pos (by linarith) _)
  have hb : finiteMean (fun hi : Card s × SwitchIndex r → Bool => q^(count hi)) ≤
      Real.exp (S'.card * cycleCoefficient r J q) := by
    rw [←Real.exp_log hp]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ _ := hm
      _ = _ := by unfold cycleCoefficient; ring
  have hcard : S'.card ≤ Fintype.card ι := by
    rw [show S'.card = S.card from Finset.card_image_of_injective _ X₀.symm.injective]
    exact projectionSide_card_le e
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool => q^(count hi)) :=
      finiteMean_mono (fun hi => pow_le_pow_right₀ hq (hpoint hi))
    _ ≤ Real.exp (S'.card * cycleCoefficient r J q) := hb
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (cycleCoefficient_nonneg r J q hq))

end CubeShuffle
namespace CubeShuffle

/-- Expose the last fresh layer, retaining the two independent lower fresh
halves. This is a bijection of the original fair coin spaces. -/
def highStepEquiv (r s : ℕ) : (Card s × SwitchIndex (r+1) → Bool) ≃
    (((Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool)) ×
      (Card s × Card r → Bool)) where
  toFun hi := ((fun j => hi (j.1,Sum.inr (false,j.2)),
    fun j => hi (j.1,Sum.inr (true,j.2))),fun j => hi (j.1,Sum.inl j.2))
  invFun c := fun j => match j.2 with
    | Sum.inl y => c.2 (j.1,y)
    | Sum.inr (b,i) => if b then c.1.2 (j.1,i) else c.1.1 (j.1,i)
  left_inv hi := by
    funext j
    rcases j with ⟨z,y|⟨b,i⟩⟩
    · rfl
    · cases b <;> rfl
  right_inv c := by
    rcases c with ⟨⟨h₀,h₁⟩,η⟩
    rfl

lemma assembleBits_step (r s : ℕ) (lo : Card (r+1) × SwitchIndex s → Bool)
    (c : ((Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool)) ×
      (Card s × Card r → Bool)) :
    assembleBits (r+1) s lo ((highStepEquiv r s).symm c) =
      (coinStepEquiv (s+r)).symm
        ((assembleBits r s (fun j => lo (Fin.cons false j.1,j.2)) c.1.1,
          assembleBits r s (fun j => lo (Fin.cons true j.1,j.2)) c.1.2),
        fun y => c.2 ((cardSplit r s y).2,(cardSplit r s y).1)) := by
  funext i
  rcases i with y | ⟨b,i⟩
  · rfl
  · cases b <;> rfl

/-- The exact level cost in the actual palindrome recursion. It stops at the
specified height, and sums across all independent child nodes. -/
noncomputable def palindromeLevelCost (t : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) σ.1.1 +
          palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) σ.1.2

lemma palindromeLevelCost_step (t d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (X Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool))
    (ξ η : Card d → Bool) :
    palindromeLevelCost t (d+1) e
      ((coinStepEquiv d).symm (Y,η),(coinStepEquiv d).symm (X,ξ)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => palindromePerm d (if b then (Y.2,X.2) else (Y.1,X.1))) else
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) (Y.1,X.1) +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) (Y.2,X.2) := by
  rw [palindromeLevelCost]
  rfl

lemma palindromeLevelCost_gt (t d : ℕ) (h : d < t) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeLevelCost t d e ω = 0 := by
  classical
  induction d generalizing ι with
  | zero => rfl
  | succ d ih =>
    rw [palindromeLevelCost,ite_eq_right (by omega : t ≠ d+1),ih (by omega),ih (by omega),Nat.zero_add]

end CubeShuffle
namespace CubeShuffle

/-- Uniform conditional FAC.4 for the actual sum of node cycles at one height.
All input coins and all output layers through s are fixed. The only average
is over the disjoint, still-fresh output layers. -/
theorem palindrome_level_partial_mgf (r s u : ℕ) (hu : u < r)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r)) (X : SwitchIndex (s+r) → Bool)
    (lo : Card r × SwitchIndex s → Bool) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(palindromeLevelCost (s+u+1) (s+r) e (assembleBits r s lo hi,X))) ≤
      Real.exp (Fintype.card ι * cycleCoefficient u J q) := by
  classical
  induction r generalizing u ι with
  | zero => omega
  | succ r ih =>
    simp only [Nat.add_succ] at *
    let χ := coinStepEquiv (s+r) X
    let x := e.trans (headTailEquiv (s+r)).toEmbedding
    let c := PairRouting.colors x χ.2
    let hc := PairRouting.colors_compatible x χ.2
    let e₀ := PairRouting.childEmbedding x c hc false
    let e₁ := PairRouting.childEmbedding x c hc true
    let e' := PairRouting.switchedEmbedding x χ.2
    let lo₀ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons false j.1,j.2)
    let lo₁ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons true j.1,j.2)
    let Y₀ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₀ hi
    let Y₁ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₁ hi
    let N := fun hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool) =>
      PairRouting.alternatingCycles e' (fun b => if b then palindromePerm (s+r) (Y₁ hi.2,χ.1.2)
        else palindromePerm (s+r) (Y₀ hi.1,χ.1.1))
    let L₀ := fun hi : Card s × SwitchIndex r → Bool =>
      palindromeLevelCost (s+u+1) (s+r) e₀ (Y₀ hi,χ.1.1)
    let L₁ := fun hi : Card s × SwitchIndex r → Bool =>
      palindromeLevelCost (s+u+1) (s+r) e₁ (Y₁ hi,χ.1.2)
    have hs (hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool))
        (η : Card s × Card r → Bool) :
        palindromeLevelCost (s+u+1) (s+r+1) e
          (assembleBits (r+1) s lo ((highStepEquiv r s).symm (hi,η)),X) =
          if u = r then N hi else L₀ hi.1 + L₁ hi.2 := by
      rw [assembleBits_step]
      conv_lhs => rw [←(coinStepEquiv (s+r)).symm_apply_apply X]
      rw [palindromeLevelCost_step]
      simp only [Nat.add_right_cancel_iff,Nat.add_left_cancel_iff]
      dsimp only [χ,x,c,hc,e₀,e₁,e',lo₀,lo₁,Y₀,Y₁,N,L₀,L₁]
      congr 2
      funext b
      cases b <;> rfl
    rw [finiteMean_equiv (highStepEquiv r s),finiteMean_prod]
    simp_rw [hs,finiteMean_const]
    by_cases hur : u = r
    · subst u
      simp only [ite_true]
      rw [finiteMean_prod,finiteMean_comm]
      calc
        _ ≤ finiteMean (fun _hi : Card s × SwitchIndex r → Bool =>
          Real.exp (Fintype.card ι * cycleCoefficient r J q)) := by
          apply finiteMean_mono
          intro hi
          have hn := node_partial_mgf r s e'
            (butterflyPerm (s+r) (decodeButterfly (s+r) χ.1.1))
            (butterflyPerm (s+r) (decodeButterfly (s+r) χ.1.2))
            (butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi))) lo₀ J hJ q hq
          exact hn
        _ = _ := finiteMean_const _
    · simp only [ite_eq_right hur,pow_add]
      rw [finiteMean_prod_mul (fun hi => q ^ L₀ hi) (fun hi => q ^ L₁ hi)]
      have hu' : u < r := by omega
      have h₀ := ih u hu' e₀ χ.1.1 lo₀
      have h₁ := ih u hu' e₁ χ.1.2 lo₁
      have hp := mul_le_mul h₀ h₁ (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
        (Real.exp_nonneg _)
      refine hp.trans_eq ?_
      rw [←Real.exp_add]
      congr 1
      have hcount := PairRouting.color_card_add c
      have hcount' : (Fintype.card {i : ι // c i = false} : ℝ) +
          Fintype.card {i : ι // c i = true} = Fintype.card ι := by exact_mod_cast hcount
      change (Fintype.card {i : ι // c i = false} : ℝ) * cycleCoefficient u J q +
          Fintype.card {i : ι // c i = true} * cycleCoefficient u J q = _
      rw [←add_mul,hcount']

end CubeShuffle
namespace CubeShuffle

/-- Physical outward height of a switch in a butterfly. -/
def switchHeight : (d : ℕ) → SwitchIndex d → ℕ
  | 0, i => nomatch i
  | d+1, Sum.inl _ => d+1
  | d+1, Sum.inr (_,i) => switchHeight d i

lemma switchHeight_le (d : ℕ) (i : SwitchIndex d) : switchHeight d i ≤ d := by
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    rcases i with y | ⟨b,i⟩
    · exact le_refl _
    · exact (ih i).trans (Nat.le_succ d)

/-- Equality of the already exposed outward layers. -/
def AgreeThrough (d s : ℕ) (Y Y' : SwitchIndex d → Bool) : Prop :=
  ∀ i, switchHeight d i ≤ s → Y i = Y' i

/-- A function of the revealed layers only. -/
def LayerAdapted (d s : ℕ) {β : Type*} (f : (SwitchIndex d → Bool) → β) : Prop :=
  ∀ Y Y', AgreeThrough d s Y Y' → f Y = f Y'

lemma agreeThrough_mono {d s t : ℕ} (h : s ≤ t) {Y Y' : SwitchIndex d → Bool}
    (hh : AgreeThrough d t Y Y') : AgreeThrough d s Y Y' :=
  fun i hi => hh i (hi.trans h)

lemma layerAdapted_mono {d s t : ℕ} {β : Type*} {f : (SwitchIndex d → Bool) → β}
    (hf : LayerAdapted d s f) (h : s ≤ t) : LayerAdapted d t f :=
  fun Y Y' hh => hf Y Y' (agreeThrough_mono h hh)

lemma layerAdapted_comp {d s : ℕ} {α β : Type*} {f : (SwitchIndex d → Bool) → α}
    (hf : LayerAdapted d s f) (g : α → β) : LayerAdapted d s (g ∘ f) :=
  fun Y Y' h => congrArg g (hf Y Y' h)

lemma layerAdapted_sum {d s : ℕ} {ι : Type*} (A : Finset ι)
    (f : ι → (SwitchIndex d → Bool) → ℕ)
    (hf : ∀ i ∈ A, LayerAdapted d s (f i)) :
    LayerAdapted d s (fun Y => ∑ i ∈ A, f i Y) := by
  intro Y Y' h
  exact Finset.sum_congr rfl (fun i hi => hf i hi Y Y' h)

lemma assembleBits_agree (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi hi' : Card s × SwitchIndex r → Bool) :
    AgreeThrough (s+r) s (assembleBits r s lo hi) (assembleBits r s lo hi') := by
  induction r with
  | zero => intro i _; rfl
  | succ r ih =>
    intro i h
    rcases i with y | ⟨b,i⟩
    · have : s+r+1 ≤ s := h
      omega
    · exact ih (fun j => lo (Fin.cons b j.1,j.2))
        (fun j => hi (j.1,Sum.inr (b,j.2))) (fun j => hi' (j.1,Sum.inr (b,j.2))) i h

lemma palindromeLevelCost_adapted (t d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (t-1) (fun Y => palindromeLevelCost t d e (Y,X)) := by
  classical
  induction d generalizing ι with
  | zero => intro Y Y' _; rfl
  | succ d ih =>
    intro Y Y' h
    change palindromeLevelCost t (d+1) e (Y,X) = palindromeLevelCost t (d+1) e (Y',X)
    conv_lhs => rw [←(coinStepEquiv d).symm_apply_apply Y,←(coinStepEquiv d).symm_apply_apply X]
    conv_rhs => rw [←(coinStepEquiv d).symm_apply_apply Y',←(coinStepEquiv d).symm_apply_apply X]
    rw [palindromeLevelCost_step,palindromeLevelCost_step]
    by_cases ht : t = d+1
    · subst t
      rw [ite_eq_left rfl,ite_eq_left rfl]
      have he₀ : (coinStepEquiv d Y).1.1 = (coinStepEquiv d Y').1.1 := by
        funext i
        exact h (Sum.inr (false,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      have he₁ : (coinStepEquiv d Y).1.2 = (coinStepEquiv d Y').1.2 := by
        funext i
        exact h (Sum.inr (true,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      rw [he₀,he₁]
    · rw [ite_eq_right ht,ite_eq_right ht]
      congr 1
      · apply ih
        intro i hi
        exact h (Sum.inr (false,i)) hi
      · apply ih
        intro i hi
        exact h (Sum.inr (true,i)) hi

/-- A conditional estimate on the still-fresh layers can be multiplied by
any nonnegative function of the revealed layers. This finite product-space
identity is the tower argument used between non-adjacent height slabs. -/
lemma adapted_mul_mean_le (r s : ℕ) (F G : (SwitchIndex (s+r) → Bool) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted (s+r) s F) (B : ℝ)
    (hG : ∀ lo : Card r × SwitchIndex s → Bool,
      finiteMean (fun hi : Card s × SwitchIndex r → Bool => G (assembleBits r s lo hi)) ≤ B) :
    finiteMean (fun Y => F Y*G Y) ≤ finiteMean F * B := by
  rw [finiteMean_split r s,finiteMean_split r s F,←finiteMean_mul_const]
  apply finiteMean_mono
  intro lo
  let H : Card s × SwitchIndex r → Bool := fun _ => false
  have hh (hi : Card s × SwitchIndex r → Bool) :
      F (assembleBits r s lo hi) = F (assembleBits r s lo H) :=
    hA _ _ (assembleBits_agree r s lo hi H)
  simp_rw [hh,finiteMean_const]
  rw [show (fun hi => F (assembleBits r s lo H) * G (assembleBits r s lo hi)) =
      (fun hi => G (assembleBits r s lo hi) * F (assembleBits r s lo H)) by
        funext hi; exact mul_comm _ _,finiteMean_mul_const]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hG lo) (hF _)

end CubeShuffle
namespace CubeShuffle

/-- A completely explicit FAC.5 bound. The ceiling is part of the actual
finite-cycle cutoff; there is no unverified numerical certificate. -/
theorem cycleCoefficient_decay (l r : ℕ) (hr : (l:ℝ)/2 ≤ r)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ (l:ℝ)/250) :
    cycleCoefficient r ⌈Real.exp ((l:ℝ)/32)⌉₊ q ≤
      68 * Real.exp (-(l:ℝ)/64) := by
  let E := Real.exp ((l:ℝ)/32)
  let J := ⌈E⌉₊
  have hl : (0:ℝ) ≤ l := Nat.cast_nonneg _
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hEpos : 0 < E := Real.exp_pos _
  have hEJ : E ≤ (J:ℝ) := Nat.le_ceil E
  have hJ : (1:ℝ) ≤ J := hE.trans hEJ
  have hJpos : (0:ℝ) < J := lt_of_lt_of_le (by norm_num) hJ
  have hJE : (J:ℝ) ≤ 2*E := by
    have h := Nat.ceil_lt_add_one (le_of_lt hEpos)
    change (J:ℝ) < E+1 at h
    linarith
  have hsqJ : Real.sqrt J ≤ (J:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqE : q ≤ Real.exp ((l:ℝ)/250) := by
    rw [←Real.exp_log hqp]
    exact Real.exp_le_exp.mpr hlog
  have hln : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hden : Real.exp ((l:ℝ)/8) ≤ Real.sqrt ((2:ℝ)^r) := by
    have he : (2:ℝ)^r = Real.exp ((r:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    rw [he,Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    apply Real.exp_le_exp.mpr
    have hrn : (0:ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith
  have hlog' : Real.log q ≤ (l:ℝ) := by linarith
  have h₁ : Real.log q / (J:ℝ) ≤ 64*Real.exp (-(l:ℝ)/64) := by
    calc
      _ ≤ (l:ℝ)/E := div_le_div₀ (by positivity) hlog' hEpos hEJ
      _ ≤ (64*Real.exp ((l:ℝ)/64))/E := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hEpos)
        have hh := Real.add_one_le_exp ((l:ℝ)/64)
        linarith
      _ = _ := by
        dsimp [E]
        rw [mul_div_assoc,←Real.exp_sub]
        congr 2
        ring
  have h₂ : 2*q*Real.sqrt J / Real.sqrt ((2:ℝ)^r) ≤
      4*Real.exp (-(l:ℝ)/64) := by
    calc
      _ ≤ (4*Real.exp ((l:ℝ)/250)*E)/Real.exp ((l:ℝ)/8) := by
        apply div_le_div₀ (by positivity) _ (Real.exp_pos _) hden
        have hs := hsqJ.trans hJE
        have hm := mul_le_mul hqE hs (Real.sqrt_nonneg _) (Real.exp_nonneg _)
        nlinarith
      _ = 4*Real.exp ((l:ℝ)/250+(l:ℝ)/32-(l:ℝ)/8) := by
        dsimp [E]
        rw [mul_assoc,←Real.exp_add,mul_div_assoc,←Real.exp_sub]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
        linarith
  change Real.log q / (J:ℝ) + 2*q*Real.sqrt J / Real.sqrt ((2:ℝ)^r) ≤ _
  linarith

lemma cycleCutoff_pos (l : ℕ) : 0 < ⌈Real.exp ((l:ℝ)/32)⌉₊ := by
  have h := Nat.le_ceil (Real.exp ((l:ℝ)/32))
  have he := Real.exp_pos ((l:ℝ)/32)
  have : (0:ℝ) < ⌈Real.exp ((l:ℝ)/32)⌉₊ := lt_of_lt_of_le he h
  exact_mod_cast this

end CubeShuffle
namespace CubeShuffle

lemma pow_sum_le_mean_powers {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℕ) (q : ℝ) (hq : 0 < q) :
    q^(∑ i, z i) ≤ finiteMean (fun i => q^(Fintype.card ι*z i)) := by
  have hn : (Fintype.card ι:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : finiteMean (fun i => (Fintype.card ι*z i:ℕ)*Real.log q) =
      (∑ i, z i:ℕ)*Real.log q := by
    simp only [finiteMean,Nat.cast_mul,Nat.cast_sum,←Finset.mul_sum,←Finset.sum_mul]
    field_simp
  have he := exp_finiteMean_le (fun i => (Fintype.card ι*z i:ℕ)*Real.log q)
  rw [hm,Real.exp_nat_mul,Real.exp_log hq] at he
  simpa only [Real.exp_nat_mul,Real.exp_log hq] using he

/-- Sum over a slab, padded by its actual zero costs when its levels exceed d. -/
noncomputable def palindromeSlabCost (l d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ i : Fin l, palindromeLevelCost (l+i.1+1) d e ω

lemma palindromeSlabCost_adapted (l d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (2*l) (fun Y => palindromeSlabCost l d e (Y,X)) := by
  apply layerAdapted_sum
  intro i _
  exact layerAdapted_mono (palindromeLevelCost_adapted (l+i.1+1) d e X) (by omega)

/-- The genuine conditional slab estimate: no independence is asserted among
node cycles or among levels in the slab. Jensen costs l on the exponent. -/
theorem palindrome_slab_partial_mgf (r s l : ℕ) (hl : 0 < l) (hs : 2*s ≤ l)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r)) (X : SwitchIndex (s+r) → Bool)
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(palindromeSlabCost l (s+r) e (assembleBits r s lo hi,X))) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  classical
  let : NeZero l := ⟨ne_of_gt hl⟩
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      finiteMean (fun i : Fin l => q^(l*palindromeLevelCost (l+i.1+1) (s+r) e
        (assembleBits r s lo hi,X)))) := by
      apply finiteMean_mono
      intro hi
      simpa only [palindromeSlabCost,Fintype.card_fin] using
        pow_sum_le_mean_powers (fun i : Fin l => palindromeLevelCost (l+i.1+1) (s+r) e
          (assembleBits r s lo hi,X)) q hqp
    _ = finiteMean (fun i : Fin l => finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(l*palindromeLevelCost (l+i.1+1) (s+r) e (assembleBits r s lo hi,X)))) := finiteMean_comm _
    _ ≤ finiteMean (fun _i : Fin l =>
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64)))) := by
      apply finiteMean_mono
      intro i
      by_cases ht : l+i.1+1 ≤ s+r
      · have hs' : s ≤ l+i.1 := by omega
        have he : l+i.1+1 = s+(l+i.1-s)+1 := by omega
        have hu : l+i.1-s < r := by omega
        have hm := palindrome_level_partial_mgf r s (l+i.1-s) hu e X lo
          ⌈Real.exp ((l:ℝ)/32)⌉₊ (cycleCutoff_pos l) (q^l) (one_le_pow₀ hq)
        have hc := cycleCoefficient_decay l (l+i.1-s) (by
          rw [Nat.cast_sub hs',Nat.cast_add]
          have hsr : (2:ℝ)*s ≤ l := by exact_mod_cast hs
          have hi : (0:ℝ) ≤ i.1 := Nat.cast_nonneg _
          linarith) (q^l) (one_le_pow₀ hq) (by
            rw [Real.log_pow]
            nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l)])
        simp_rw [he,pow_mul]
        exact hm.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))
      · have hz := palindromeLevelCost_gt (l+i.1+1) (s+r) (by omega) e
        simp only [hz,Nat.mul_zero,pow_zero,finiteMean_const]
        exact Real.one_le_exp_iff.mpr (by positivity)
    _ = _ := finiteMean_const _

end CubeShuffle
namespace CubeShuffle

lemma palindromeSlabCost_gt (l d : ℕ) (h : d ≤ l) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeSlabCost l d e ω = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact palindromeLevelCost_gt _ _ (by omega) _ _

lemma palindrome_slab_adapted_mul_le (d s l : ℕ) (hsd : s ≤ d) (hl : 0 < l)
    (hs : 2*s ≤ l) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (X : SwitchIndex d → Bool) (F : (SwitchIndex d → Bool) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted d s F) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => F Y*q^(palindromeSlabCost l d e (Y,X))) ≤
      finiteMean F * Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hsd
  exact adapted_mul_mean_le r s F _ hF hA _
    (fun lo => palindrome_slab_partial_mgf r s l hl hs e X lo q hq hlog)

def familyEnd (L n : ℕ) : ℕ := if n = 0 then 0 else 2*(L*4^(n-1))

lemma familyEnd_two (L n : ℕ) : 2*familyEnd L n ≤ L*4^n := by
  cases n with
  | zero => simp [familyEnd]
  | succ n => simp only [familyEnd,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one,pow_succ]; nlinarith

lemma familyEnd_ge (L n j : ℕ) (hj : j < n) : 2*(L*4^j) ≤ familyEnd L n := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [familyEnd,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one]
    apply Nat.mul_le_mul_left
    exact Nat.mul_le_mul_left L (Nat.pow_le_pow_right (by decide) (by omega : j ≤ n))

noncomputable def palindromeFamilyCost (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ j ∈ Finset.range n, palindromeSlabCost (L*4^j) d e ω

lemma palindromeFamilyCost_adapted (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (familyEnd L n) (fun Y => palindromeFamilyCost L n d e (Y,X)) := by
  apply layerAdapted_sum
  intro j hj
  exact layerAdapted_mono (palindromeSlabCost_adapted (L*4^j) d e X)
    (familyEnd_ge L n j (Finset.mem_range.mp hj))

/-- Time-ordered multiplication across one family of nonadjacent slabs.
The proof uses only the already proved finite conditional estimate. -/
theorem palindrome_family_mgf (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι * (68*∑ j ∈ Finset.range n,
        Real.exp (-((L*4^j:ℕ):ℝ)/64))) := by
  induction n with
  | zero => simp only [palindromeFamilyCost,Finset.range_zero,Finset.sum_empty,pow_zero,
      finiteMean_const,mul_zero,Real.exp_zero,le_refl]
  | succ n ih =>
    let l := L*4^n
    have hl : 0 < l := Nat.mul_pos hL (pow_pos (by decide) _)
    have hs : 2*familyEnd L n ≤ l := familyEnd_two L n
    have hc : ∀ Y, palindromeFamilyCost L (n+1) d e (Y,X) =
        palindromeFamilyCost L n d e (Y,X)+palindromeSlabCost l d e (Y,X) := by
      intro Y
      exact Finset.sum_range_succ _ _
    have hm : finiteMean (fun Y => q^(palindromeFamilyCost L (n+1) d e (Y,X))) ≤
        finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) *
          Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
      by_cases hld : l ≤ d
      · simp_rw [hc,pow_add]
        exact palindrome_slab_adapted_mul_le d (familyEnd L n) l (by omega) hl hs e X _
          (fun _ => pow_nonneg (by linarith) _)
          (layerAdapted_comp (palindromeFamilyCost_adapted L n d e X) (fun c => q^c))
          q hq hlog
      · simp_rw [hc,palindromeSlabCost_gt l d (by omega) e,Nat.add_zero]
        exact le_mul_of_one_le_right
          (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
          (Real.one_le_exp_iff.mpr (by positivity))
    refine (hm.trans (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _))).trans_eq ?_
    rw [←Real.exp_add,Finset.sum_range_succ]
    congr 1
    dsimp [l]
    ring

lemma pow_four_ge (j : ℕ) : j+1 ≤ 4^j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

lemma sum_family_decay (L n : ℕ) (hL : 0 < L) :
    (∑ j ∈ Finset.range n, Real.exp (-((L*4^j:ℕ):ℝ)/64)) ≤
      Real.exp (-(L:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64)) := by
  let r := Real.exp (-(1:ℝ)/64)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hg : (∑ j ∈ Finset.range n, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<1-r)).mpr
    have hh := geom_sum_mul r n
    nlinarith [pow_nonneg (le_of_lt hr) n]
  calc
    _ ≤ ∑ j ∈ Finset.range n, Real.exp (-(L:ℝ)/64)*r^j := by
      apply Finset.sum_le_sum
      intro j _
      have hj := pow_four_ge j
      have hlj : L+j ≤ L*4^j := by nlinarith
      have hlj' : (L:ℝ)+j ≤ (L*4^j:ℕ) := by exact_mod_cast hlj
      rw [←Real.exp_nat_mul,←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(L:ℝ)/64)*(∑ j ∈ Finset.range n, r^j) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(L:ℝ)/64)*(1/(1-r)) :=
      mul_le_mul_of_nonneg_left hg (Real.exp_nonneg _)
    _ = _ := by ring

end CubeShuffle
namespace CubeShuffle

lemma palindromeLevelCost_step_add (t d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (ω : BenesCoins (d+1)) :
    palindromeLevelCost t (d+1) e ω =
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) σ.1.2 := by
  classical
  rw [palindromeLevelCost]
  dsimp only
  split_ifs with h
  · simp only [palindromeLevelCost_gt t d (by omega),Nat.add_zero]
  · simp only [Nat.zero_add]

/-- The recursive low cost is literally the sum of its physical node levels. -/
lemma palindromeLowCost_sum (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost H d e ω = ∑ i ∈ Finset.range H, palindromeLevelCost (i+1) d e ω := by
  classical
  induction d generalizing ι with
  | zero => simp only [palindromeLowCost,palindromeLevelCost,Finset.sum_const_zero]
  | succ d ih =>
    rw [palindromeLowCost]
    simp only [palindromeLevelCost_step_add,Finset.sum_add_distrib]
    rw [←ih,←ih]
    congr 2
    simp only [Nat.add_right_cancel_iff,Finset.sum_ite_eq',Finset.mem_range,Nat.succ_le_iff]

lemma palindromeLowCost_slab (L d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost L d e ω + palindromeSlabCost L d e ω = palindromeLowCost (2*L) d e ω := by
  rw [palindromeLowCost_sum,palindromeLowCost_sum,show 2*L=L+L by omega,Finset.sum_range_add]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => palindromeLevelCost (L+i+1) d e ω) L

lemma palindromeCost_family (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost L d e ω + palindromeFamilyCost L n d e ω +
      palindromeFamilyCost (2*L) n d e ω = palindromeLowCost (L*4^n) d e ω := by
  induction n with
  | zero => simp only [palindromeFamilyCost,Finset.range_zero,Finset.sum_empty,Nat.add_zero,
      pow_zero,mul_one]
  | succ n ih =>
    have he : (2*L)*4^n = 2*(L*4^n) := by ring
    have he' : L*4^(n+1) = 2*(2*(L*4^n)) := by rw [pow_succ]; ring
    simp only [palindromeFamilyCost,Finset.sum_range_succ] at ih ⊢
    rw [he,he',←palindromeLowCost_slab,←palindromeLowCost_slab,←ih]
    omega

end CubeShuffle
namespace CubeShuffle

lemma finiteMean_mul_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    (finiteMean (fun ω => f ω*g ω))^2 ≤ finiteMean (fun ω => (f ω)^2)*finiteMean (fun ω => (g ω)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp only [finiteMean,div_pow,div_mul_div_comm,←pow_two]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

lemma finiteMean_mul_exp_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) (A B : ℝ)
    (hf : finiteMean (fun ω => (f ω)^2) ≤ Real.exp A)
    (hg : finiteMean (fun ω => (g ω)^2) ≤ Real.exp B) :
    finiteMean (fun ω => f ω*g ω) ≤ Real.exp ((A+B)/2) := by
  have hc := finiteMean_mul_sq_le f g
  have hn : 0 ≤ finiteMean (fun ω => (g ω)^2) := finiteMean_nonneg (fun _ => sq_nonneg _)
  have hu := mul_le_mul hf hg hn (Real.exp_nonneg _)
  have he : Real.exp A*Real.exp B = (Real.exp ((A+B)/2))^2 := by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he] at hu
  have hh := hc.trans hu
  have hep := Real.exp_pos ((A+B)/2)
  nlinarith

end CubeShuffle
namespace CubeShuffle

noncomputable def heightDecay (H : ℕ) : ℝ :=
  68*Real.exp (-(H:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64))

lemma heightDecay_nonneg (H : ℕ) : 0 ≤ heightDecay H := by
  have h : Real.exp (-(1:ℝ)/64) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  apply div_nonneg (by positivity) (by linarith)

lemma heightDecay_antitone : Antitone heightDecay := by
  intro L H h
  have hden : 0 ≤ 1-Real.exp (-(1:ℝ)/64) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
    linarith
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h' : (L:ℝ) ≤ H := by exact_mod_cast h
  linarith

lemma palindrome_family_mgf_decay (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*heightDecay L) := by
  apply (palindrome_family_mgf L n d hL e X q hq hlog).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using h

/-- The two interlaced slab families have a uniform conditional high-level
moment bound. This is FAC.6, including all dependence between families. -/
theorem palindrome_high_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(palindromeFamilyCost H n d e (Y,X)+
      palindromeFamilyCost (2*H) n d e (Y,X))) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/250 := by rw [Real.log_pow]; norm_num; linarith
  have h₀ := palindrome_family_mgf_decay H n d hH e X (q^2) hq2 hlog2
  have h₁ := palindrome_family_mgf_decay (2*H) n d (by omega) e X (q^2) hq2 hlog2
  have h₁' := h₁.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (heightDecay_antitone (show H ≤ 2*H by omega)) (Nat.cast_nonneg _)))
  have hh := finiteMean_mul_exp_le (fun Y => q^(palindromeFamilyCost H n d e (Y,X)))
    (fun Y => q^(palindromeFamilyCost (2*H) n d e (Y,X)))
    (Fintype.card ι*heightDecay H) (Fintype.card ι*heightDecay H)
    (by simpa only [pow_right_comm] using h₀) (by simpa only [pow_right_comm] using h₁')
  simpa only [←pow_add,add_self_div_two] using hh

lemma palindrome_high_full_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeFamilyCost H n d e ω+
      palindromeFamilyCost (2*H) n d e ω)) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  rw [finiteMean_prod,finiteMean_comm]
  calc
    _ ≤ finiteMean (fun _X : SwitchIndex d → Bool => Real.exp (Fintype.card ι*heightDecay H)) := by
      apply finiteMean_mono
      intro X
      exact palindrome_high_mgf H n d hH e X q hq hlog
    _ = _ := finiteMean_const _

/-- Combination with the genuine sparse low-block estimate. The factor 2 in
that estimate and both Cauchy steps are retained explicitly. -/
theorem palindrome_cost_mgf_cutoff (r H : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/1000)
    (hr : (2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*(q^2)^H) ≤ 1/2) :
    finiteMean (fun ω : BenesCoins (H+r) => q^(palindromeCost (H+r) e ω)) ≤
      Real.exp (((2:ℝ)^r*(2*((2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*(q^2)^H))^2)+
        Fintype.card ι*heightDecay H)/2) := by
  let d := H+r
  have hd : d ≤ H*4^d := by
    have hh := pow_four_ge d
    nlinarith
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost H d e ω+
      (palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω) := by
    have hh := palindromeCost_family H d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/500 := by rw [Real.log_pow]; norm_num; linarith
  have hlow := palindrome_low_mgf r H e (q^2) hq2 hr
  have hhigh := palindrome_high_full_mgf H d d hH e (q^2) hq2 hlog2
  have hh := finiteMean_mul_exp_le (fun ω : BenesCoins d => q^(palindromeLowCost H d e ω))
    (fun ω : BenesCoins d => q^(palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω))
    _ _ (by simpa only [pow_right_comm] using hlow) (by simpa only [pow_right_comm] using hhigh)
  change finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤ _
  simpa only [hcost,pow_add,pow_right_comm] using hh

end CubeShuffle
namespace CubeShuffle

lemma cutoffMass_le (H d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (ω : BenesCoins d) :
    cutoffMass H d e ω ≤ Fintype.card ι := by
  classical
  induction d generalizing ι with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    rw [cutoffMass]
    split_ifs
    · exact crowdedMass_le _
    · exact (Nat.add_le_add (ih _ _) (ih _ _)).trans_eq (PairRouting.color_card_add _)

lemma palindromeLowCost_le (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeLowCost H d e ω ≤ H*Fintype.card ι :=
  (palindromeLowCost_le_cutoff H d e ω).trans (Nat.mul_le_mul_left H (cutoffMass_le H d e ω))

/-- Dense rows are included. The cutoff-one estimate gives a uniform O(k)
log moment without any small-density or dimension hypothesis. -/
theorem palindrome_cost_mgf_coarse (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/1000) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤
      Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  have hd : d ≤ 1*4^d := by have hh := pow_four_ge d; omega
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost 1 d e ω+
      (palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω) := by
    have hh := palindromeCost_family 1 d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/500 := by rw [Real.log_pow]; norm_num; linarith
  have hlow : finiteMean (fun ω : BenesCoins d => (q^2)^(palindromeLowCost 1 d e ω)) ≤
      Real.exp (Fintype.card ι) := by
    calc
      _ ≤ finiteMean (fun _ω : BenesCoins d => (q^2)^(Fintype.card ι)) := by
        apply finiteMean_mono
        intro ω
        apply pow_le_pow_right₀ hq2
        simpa only [one_mul] using palindromeLowCost_le 1 d e ω
      _ = (q^2)^(Fintype.card ι) := finiteMean_const _
      _ = Real.exp (Fintype.card ι * Real.log (q^2)) := by
        rw [Real.exp_nat_mul,Real.exp_log (by positivity : 0<q^2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ)≤_)
        nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)])
  have hhigh := palindrome_high_full_mgf 1 d d (by decide) e (q^2) hq2 hlog2
  have hh := finiteMean_mul_exp_le (fun ω : BenesCoins d => q^(palindromeLowCost 1 d e ω))
    (fun ω : BenesCoins d => q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω))
    (Fintype.card ι) (Fintype.card ι*heightDecay 1)
    (by simpa only [pow_right_comm] using hlow) (by simpa only [pow_right_comm] using hhigh)
  simp only [←pow_add,←hcost] at hh
  apply hh.trans (Real.exp_le_exp.mpr _)
  have hk : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hD := heightDecay_nonneg 1
  nlinarith

/-- The exponent remains the literal 1/1000 fixed by the manuscript. -/
noncomputable def momentBase : ℝ := (2:ℝ)^(1/1000:ℝ)

lemma momentBase_one_le : 1 ≤ momentBase := by
  exact Real.one_le_rpow (by norm_num) (by norm_num)

lemma momentBase_log : Real.log momentBase ≤ 1/1000 := by
  rw [momentBase,Real.log_rpow (by norm_num)]
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh ⊢
  linarith

lemma momentBase_pow (c : ℕ) : momentBase^c = (2:ℝ)^((c:ℝ)*(1/1000:ℝ)) := by
  rw [mul_comm,Real.rpow_mul_natCast (by norm_num)]
  rfl

/-- Remove only the source's non-increasing falling-factorial normalization;
no change is made to the tuple law or the (1+a)-moment. -/
lemma palindromeRowMoment_le_cost (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) :
    palindromeRowMoment d e (1/1000) ≤
      finiteMean (fun ω : BenesCoins d => momentBase^(palindromeCost d e ω)) := by
  have hn : (0:ℝ) < ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn0 : (0:ℝ) ≤ ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn1 : ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.descFactorial_le_pow (2^d) (Fintype.card ι)
  have hpow := Real.rpow_le_one hn0 hn1 (by norm_num : (0:ℝ)≤1/1000)
  have hm := palindrome_row_density_moment d e (1/1000) (by norm_num)
  simp_rw [←momentBase_pow] at hm
  exact hm.trans (mul_le_of_le_one_left (finiteMean_nonneg (fun _ =>
    pow_nonneg (le_trans (by norm_num) momentBase_one_le) _)) hpow)

theorem palindrome_row_moment_coarse (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    palindromeRowMoment d e (1/1000) ≤ Real.exp (Fintype.card ι*(1+heightDecay 1)) :=
  (palindromeRowMoment_le_cost d e).trans
    (palindrome_cost_mgf_coarse d e momentBase momentBase_one_le momentBase_log)

end CubeShuffle
namespace CubeShuffle

noncomputable def densityCutoff (p : ℝ) : ℕ := ⌊-Real.log p/(4*Real.log 2)⌋₊

lemma log_small_density {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    Real.log p ≤ -8*Real.log 2 := by
  have he : Real.log (1/256:ℝ) = -8*Real.log 2 := by
    rw [show (1/256:ℝ) = 1/2^8 by norm_num,
      Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow]
    ring
  exact (Real.log_le_log hp hs).trans_eq he

lemma densityCutoff_bounds {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    0 < densityCutoff p ∧
    (densityCutoff p:ℝ)*(4*Real.log 2) ≤ -Real.log p ∧
    -Real.log p < ((densityCutoff p:ℝ)+1)*(4*Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < 4*Real.log 2 := by positivity
  have hh := log_small_density hp hs
  have hx : 1 ≤ -Real.log p/(4*Real.log 2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  refine ⟨Nat.floor_pos.mpr hx,?_,?_⟩
  · exact (le_div_iff₀ hd).mp (Nat.floor_le (by linarith : 0 ≤ -Real.log p/(4*Real.log 2)))
  · exact (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (-Real.log p/(4*Real.log 2)))

lemma densityCutoff_decay {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    Real.exp (-(densityCutoff p:ℝ)/64) ≤ Real.exp (1/64) * p^(1/512:ℝ) := by
  have hh := (densityCutoff_bounds hp hs).2.2
  have hb : Real.log 2 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hH : 0 ≤ (densityCutoff p:ℝ)+1 := by positivity
  have hu := mul_le_mul_of_nonneg_left hb hH
  rw [Real.rpow_def_of_pos hp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma densityCutoff_power {p q : ℝ} (hp : 0 < p) (hs : p ≤ 1/256)
    (hq : 0 < q) (hlog : Real.log q ≤ Real.log 2/4) (n : ℕ) (hn : n ≤ 4)
    (hq1 : 1 ≤ q) :
    p*(2:ℝ)^(densityCutoff p)*q^(n*densityCutoff p) ≤ p^(1/2:ℝ) := by
  have hcut := (densityCutoff_bounds hp hs).2.1
  have hH : 0 ≤ (densityCutoff p:ℝ) := Nat.cast_nonneg _
  have hn' : (n:ℝ) ≤ 4 := by exact_mod_cast hn
  have hln := Real.log_nonneg hq1
  have hl := mul_le_mul_of_nonneg_right hn' hln
  have hnl : (n:ℝ)*Real.log q ≤ Real.log 2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hnl hH
  have heq : p*(2:ℝ)^(densityCutoff p)*q^(n*densityCutoff p) =
      Real.exp (Real.log p+(densityCutoff p:ℝ)*Real.log 2+
        (n*densityCutoff p:ℕ)*Real.log q) := by
    rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul,
      Real.exp_log hp,Real.exp_log hq,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [heq,Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

lemma densityCutoff_sparse {p q : ℝ} (hp : 0 < p) (hs : p ≤ 1/256)
    (hq : 0 < q) (hlog : Real.log q ≤ Real.log 2/4) (hq1 : 1 ≤ q) :
    (2:ℝ)^(densityCutoff p)*(p*(q^2)^(densityCutoff p)) ≤ 1/2 := by
  have hh := densityCutoff_power hp hs hq hlog 2 (by decide) hq1
  rw [←pow_mul] at ⊢
  have hle : p^(1/2:ℝ) ≤ 1/2 := by
    have hlogp := log_small_density hp hs
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.rpow_def_of_pos hp]
    calc
      _ ≤ Real.exp (-Real.log 2) := by apply Real.exp_le_exp.mpr; nlinarith
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  nlinarith [hh.trans hle]

end CubeShuffle
namespace CubeShuffle

lemma momentBase_log_exact : Real.log momentBase = Real.log 2/1000 := by
  rw [momentBase,Real.log_rpow (by norm_num)]
  ring

lemma densityCutoff_le_height (d k : ℕ) (hk : 0 < k) :
    densityCutoff ((k:ℝ)/(2:ℝ)^d) ≤ d := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < (k:ℝ)/(2:ℝ)^d := by positivity
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogk := Real.log_nonneg hk'
  by_cases hx : 0 ≤ -Real.log ((k:ℝ)/(2:ℝ)^d)/(4*Real.log 2)
  · have hh := (le_div_iff₀ (by positivity : 0 < 4*Real.log 2)).mp (Nat.floor_le hx)
    have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
    have hH : (0:ℝ) ≤ densityCutoff ((k:ℝ)/(2:ℝ)^d) := Nat.cast_nonneg _
    change (densityCutoff ((k:ℝ)/(2:ℝ)^d):ℝ)*(4*Real.log 2) ≤ -Real.log ((k:ℝ)/(2:ℝ)^d) at hh
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow] at hh
    have hle : (densityCutoff ((k:ℝ)/(2:ℝ)^d):ℝ) ≤ d := by nlinarith
    exact_mod_cast hle
  · have hz := Nat.floor_of_nonpos (le_of_not_ge hx)
    simp only [densityCutoff,hz,Nat.zero_le]

noncomputable def densityTailConstant : ℝ :=
  68*Real.exp (1/64)/(1-Real.exp (-(1:ℝ)/64))

lemma densityTailConstant_nonneg : 0 ≤ densityTailConstant := by
  have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
  apply div_nonneg (by positivity) (by linarith)

lemma heightDecay_cutoff {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    heightDecay (densityCutoff p) ≤ densityTailConstant*p^(1/512:ℝ) := by
  have hden : 0 ≤ 1-Real.exp (-(1:ℝ)/64) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
    linarith
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (densityCutoff_decay hp hs) (by norm_num : (0:ℝ)≤68)) hden
  simpa only [heightDecay,densityTailConstant,mul_assoc,div_mul_eq_mul_div] using hh

lemma sparse_low_algebra (r H k : ℕ) (q : ℝ) :
    (2:ℝ)^r*(2*((2:ℝ)^H*(((k:ℝ)/(2:ℝ)^(H+r))*(q^2)^H))^2) =
    2*k*(((k:ℝ)/(2:ℝ)^(H+r))*(2:ℝ)^H*q^(4*H)) := by
  rw [pow_add,←pow_mul,show 4*H = (2*H)*2 by omega,pow_mul]
  have hH : (2:ℝ)^H ≠ 0 := by positivity
  have hr : (2:ℝ)^r ≠ 0 := by positivity
  field_simp
  ring

lemma palindrome_row_moment_small (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι)
    (hs : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1/256) :
    palindromeRowMoment d e (1/1000) ≤
      Real.exp (Fintype.card ι*(1+densityTailConstant)*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ)) := by
  generalize hpdef : ((Fintype.card ι:ℝ)/(2:ℝ)^d) = p at hs ⊢
  have hp : 0 < p := by rw [←hpdef]; positivity
  have hle := densityCutoff_le_height d (Fintype.card ι) hk
  rw [hpdef] at hle
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hle
  subst d
  have hH := (densityCutoff_bounds hp hs).1
  have hq := momentBase_one_le
  have hqp : 0 < momentBase := by linarith
  have hlog : Real.log momentBase ≤ Real.log 2/4 := by
    rw [momentBase_log_exact]
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hsp := densityCutoff_sparse hp hs hqp hlog hq
  rw [←hpdef] at hsp
  have hh := palindrome_cost_mgf_cutoff r (densityCutoff p) hH e momentBase hq momentBase_log
    (by simpa only [hpdef] using hsp)
  apply (palindromeRowMoment_le_cost _ e).trans (hh.trans (Real.exp_le_exp.mpr _))
  rw [sparse_low_algebra,hpdef]
  have hlow := densityCutoff_power hp hs hqp hlog 4 (by decide) hq
  have hp1 : p ≤ 1 := by linarith
  have he := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num : (1:ℝ)/512 ≤ 1/2)
  have hlow' := mul_le_mul_of_nonneg_left (hlow.trans he)
    (by positivity : (0:ℝ)≤2*Fintype.card ι)
  have hhigh := mul_le_mul_of_nonneg_left (heightDecay_cutoff hp hs)
    (Nat.cast_nonneg (Fintype.card ι): (0:ℝ)≤_)
  have hnon : 0 ≤ Fintype.card ι*densityTailConstant*p^(1/512:ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) densityTailConstant_nonneg)
      (Real.rpow_nonneg (le_of_lt hp) _)
  nlinarith

noncomputable def densityConstant : ℝ :=
  256*(1+heightDecay 1)+1+densityTailConstant

lemma densityConstant_pos : 0 < densityConstant := by
  dsimp [densityConstant]
  have hh := heightDecay_nonneg 1
  have ht := densityTailConstant_nonneg
  linarith

/-- The absolute power improvement in the first clause of fac:density,
for the actual full palindrome and all labelled distinct input tuples. -/
theorem palindrome_row_moment_bound (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι) :
    palindromeRowMoment d e (1/1000) ≤ Real.exp (densityConstant*Fintype.card ι*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ)) := by
  have hp : 0 < (Fintype.card ι:ℝ)/(2:ℝ)^d := by positivity
  have hp1 : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have h := Fintype.card_le_of_injective e e.injective
    rw [card_positions] at h
    exact_mod_cast h
  have hk0 : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hpow := Real.rpow_nonneg (le_of_lt hp) (1/512:ℝ)
  by_cases hs : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1/256
  · apply (palindrome_row_moment_small d e hk hs).trans (Real.exp_le_exp.mpr _)
    have hD : 1+densityTailConstant ≤ densityConstant := by
      dsimp [densityConstant]
      have := heightDecay_nonneg 1
      linarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hk0) hpow
    nlinarith
  · have hlow : (1:ℝ)/256 ≤ ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ) := by
      have he := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num : (1:ℝ)/512 ≤ 1)
      rw [Real.rpow_one] at he
      exact (le_of_not_ge hs).trans he
    have hD : 256*(1+heightDecay 1) ≤ densityConstant := by
      dsimp [densityConstant]
      have := densityTailConstant_nonneg
      linarith
    apply (palindrome_row_moment_coarse d e).trans (Real.exp_le_exp.mpr _)
    have hD0 : 0 ≤ 1+heightDecay 1 := by have := heightDecay_nonneg 1; linarith
    have ha := mul_le_mul_of_nonneg_left hlow (mul_nonneg (by norm_num : (0:ℝ)≤256) hD0)
    have hb := mul_le_mul_of_nonneg_right hD hpow
    have hc := mul_le_mul_of_nonneg_right (ha.trans hb) hk0
    nlinarith

lemma palindromeRowMoment_nonneg (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) : 0 ≤ palindromeRowMoment d e a := by
  apply finiteMean_nonneg
  intro f
  exact Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (PairRouting.tupleProbability_nonneg _ _ _)) _

/-- Literal logarithmic row-density estimate with a=1/1000, eta=1/512,
and one explicit absolute positive constant. -/
theorem palindrome_log_row_moment (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι) :
    Real.log (palindromeRowMoment d e (1/1000)) ≤ densityConstant*Fintype.card ι*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ) := by
  by_cases hz : palindromeRowMoment d e (1/1000) = 0
  · rw [hz,Real.log_zero]
    exact mul_nonneg (mul_nonneg (le_of_lt densityConstant_pos) (Nat.cast_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  · exact (Real.log_le_iff_le_exp (lt_of_le_of_ne (palindromeRowMoment_nonneg _ _ _) (Ne.symm hz))).mpr
      (palindrome_row_moment_bound d e hk)

end CubeShuffle

end OAI
