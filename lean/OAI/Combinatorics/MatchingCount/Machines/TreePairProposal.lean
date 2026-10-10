import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.LocalVariance

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [DecidableEq V] in
lemma cycleProposal_min (w : E → ℝ)
    (a b : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    min (pairLaw ends w w a) (pairLaw ends w w b)*cycleProposal a b =
      pairLaw ends w w a*cycleProposal a b := by
  rw [min_mul_of_nonneg _ _ (cycleProposal_nonneg a b)]
  have h := cycleProposal_gibbs w a b
  rw [cycleProposal_symmetric b a] at h
  change pairLaw ends w w a*cycleProposal a b = pairLaw ends w w b*cycleProposal a b at h
  rw [h,min_self]




theorem pairKernel_energy (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM (fun e v => v ∈ ends e))
    (f g : Finset E → ℝ) :
    localEnergy (metropolisCapacity (pairProposal ends hloop hpar) (pairLaw ends w w))
      (fun a => f a.1.val+g a.2.val) = pairDirichlet ends w f g := by
  classical
  rw [metropolis_energy]
  let F := fun a : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e) =>
    f a.1.val+g a.2.val
  let π := pairLaw ends w w
  let S := ∑ a, ∑ b, min (π a) (π b)*firstLift (switchProposal ends) a b*(F a-F b)^2
  let C := ∑ a, ∑ b, min (π a) (π b)*firstLift (colorProposal ends) a b*(F a-F b)^2
  let Y := ∑ a, ∑ b, min (π a) (π b)*cycleProposal a b*(F a-F b)^2
  have he : localEnergy (offCapacity (pairProposal ends hloop hpar) π) F = (S+C+Y)/6 := by
    unfold localEnergy offCapacity
    change (∑ a, ∑ b, min (π a) (π b)*
      ((firstLift (switchProposal ends) a b+firstLift (colorProposal ends) a b+cycleProposal a b)/3)*
      (F a-F b)^2)/2 = _
    dsimp only [S,C,Y]
    simp only [add_div,Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  have hs : S/6 = switchDirichlet (inc := fun e v => v ∈ ends e) w f := by
    dsimp only [S,π,pairLaw,F]
    rw [firstLift_energy _ (fun A => (gibbs_pos w hw A).le) (gibbs_sum w hw M) _ (fun A => f A.val) (fun A => g A.val)]
    exact switchProposal_dirichlet ends hloop w f
  have hc : C/6 = colorDirichlet ends w f := by
    dsimp only [C,π,pairLaw,F]
    rw [firstLift_energy _ (fun A => (gibbs_pos w hw A).le) (gibbs_sum w hw M) _ (fun A => f A.val) (fun A => g A.val)]
    exact colorProposal_dirichlet ends hloop w f
  have hy : Y/6 = cycleDirichlet (inc := fun e v => v ∈ ends e) w f g := by
    dsimp only [Y,π]
    simp_rw [cycleProposal_min]
    simp only [Fintype.sum_prod_type,pairLaw,F]
    simpa only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc] using
      cycleProposal_dirichlet (inc := fun e v => v ∈ ends e) w f g
  change localEnergy (offCapacity (pairProposal ends hloop hpar) π) F = _
  rw [he,add_div,add_div,hs,hc,hy]
  rfl

end

section

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

noncomputable def treePairProposal : SymmetricProposal (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) :=
  pairProposal (fun e : BagEdge bags => e.val.val.1) (fun e => e.val.property)
    (fun e => BagEdge.parallels_card_le (label_memberships_le_two hbags hG) e)

noncomputable def treePairLaw (w z : BagEdge bags → ℝ)
    (a : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) : ℝ := gibbs w a.1*gibbs z a.2

noncomputable def treePairEnergy (w z : BagEdge bags → ℝ)
    (f : (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) → ℝ) : ℝ := by
  classical
  exact localEnergy (metropolisCapacity (treePairProposal hbags hG) (treePairLaw w z)) f

end

section

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

theorem tree_pair_poincare (hN : 2 ≤ Fintype.card V)
    (M : PM (BagEdge.Incident (bags := bags)))
    (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (a b : PM (BagEdge.Incident (bags := bags)) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    localVariance (gibbs wt) a ≤ ((10^4:ℝ)*Fintype.card V*D)^100 *
      treePairEnergy hbags hG wt wt (fun z => a z.1+b z.2) := by
  classical
  let wt := fun e => max lo (min hi (w e))
  have hwt : ∀ e, 0 < wt e := fun e => lt_of_lt_of_le hlo (le_max_left _ _)
  let af : Finset (BagEdge bags) → ℝ := fun S => if h : MatchingOn BagEdge.Incident S Finset.univ then a ⟨S,h⟩ else 0
  let bf : Finset (BagEdge bags) → ℝ := fun S => if h : MatchingOn BagEdge.Incident S Finset.univ then b ⟨S,h⟩ else 0
  have ha (A : PM (BagEdge.Incident (bags := bags))) : af A.val = a A := by simp [af,A.property]
  have hb (A : PM (BagEdge.Incident (bags := bags))) : bf A.val = b A := by simp [bf,A.property]
  have ht := CellDemands.pair_energy_inequality (hbags := hbags) (hG := hG)
    height hheight hstep D hD w hw lo hi hlo hlohi hN M af bf
  have he := pairKernel_energy (fun e : BagEdge bags => e.val.val.1) (fun e => e.val.property)
    (fun e => BagEdge.parallels_card_le (label_memberships_le_two hbags hG) e) wt hwt M af bf
  have he' : treePairEnergy hbags hG wt wt (fun z => af z.1.val+bf z.2.val) =
      pairDirichlet (fun e : BagEdge bags => e.val.val.1) wt af bf := by
    unfold treePairEnergy treePairProposal treePairLaw
    unfold pairLaw at he
    convert he using 1
    congr 4 <;> first | rfl | exact Subsingleton.elim _ _
  change localVariance (gibbs wt) a ≤ _
  change localVariance (gibbs wt) (fun A => af A.val) ≤ _ at ht
  simp_rw [ha,hb] at he' ht
  exact ht.trans_eq (congrArg (fun z => ((10^4:ℝ)*Fintype.card V*D)^100*z) he'.symm)

end

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

theorem adjacent_tree_pair_poincare (hN : 2 ≤ Fintype.card V)
    (M : PM (BagEdge.Incident (bags := bags))) (t : ℕ)
    (a b : PM (BagEdge.Incident (bags := bags)) → ℝ) :
    let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
    let upper := fun e => tierClamp c (t+1) (w e)
    let lower := fun e => tierClamp c t (w e)
    localVariance (gibbs upper) a ≤ (2*((10^4:ℝ)*Fintype.card V*D)^100) *
      treePairEnergy hbags hG upper lower (fun z => a z.1+b z.2) := by
  classical
  let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]; have : 0 ≤ ((Fintype.card V:ℝ)^2)⁻¹ := by positivity
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hp1 : 1 ≤ c^(t+1) := one_le_pow₀ hc
  have hp0 : 0 < c^(t+1) := pow_pos hc0 _
  have hilo : (c^(t+1))⁻¹ ≤ c^(t+1) := (inv_le_one₀ hp0).mpr hp1 |>.trans hp1
  let upper := fun e => tierClamp c (t+1) (w e)
  let lower := fun e => tierClamp c t (w e)
  have hupper : ∀ e, 0 < upper e := fun e => tierClamp_pos hc0 _ _
  have hwpos : ∀ e, 0 < w e := fun e =>
    lt_of_lt_of_le (div_pos (hheight e.color) (lt_of_lt_of_le (by norm_num) hD)) (hw e).1
  have hv := tree_pair_poincare (hbags := hbags) (hG := hG)
    height hheight hstep D hD w hw hN M (c^(t+1))⁻¹ (c^(t+1)) (inv_pos.mpr hp0) hilo a b
  change localVariance (gibbs upper) a ≤ ((10^4:ℝ)*Fintype.card V*D)^100 *
    treePairEnergy hbags hG upper upper (fun z => a z.1+b z.2) at hv
  have hd (z : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) :
      (1/2:ℝ)*treePairLaw upper upper z ≤ treePairLaw upper lower z := by
    have h := (adjacent_gibbs (fun e : BagEdge bags => e.val.val.1) (fun e => e.val.property)
      hN w hwpos t z.2).1
    change gibbs upper z.2/2 ≤ gibbs lower z.2 at h
    have h := mul_le_mul_of_nonneg_left h (gibbs_pos upper hupper z.1).le
    dsimp only [treePairLaw]
    nlinarith only [h]
  have he := metropolis_energy_domination (treePairProposal hbags hG)
    (treePairLaw upper upper) (treePairLaw upper lower) (1/2) (by norm_num) hd
    (fun z => a z.1+b z.2)
  change (1/2:ℝ)*treePairEnergy hbags hG upper upper (fun z => a z.1+b z.2) ≤
    treePairEnergy hbags hG upper lower (fun z => a z.1+b z.2) at he
  have hL : 0 ≤ ((10^4:ℝ)*Fintype.card V*D)^100 := by positivity
  have hh := mul_le_mul_of_nonneg_left he hL
  change localVariance (gibbs upper) a ≤ _
  nlinarith only [hv,hh]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Replica.Ladder

open Finset

abbrev Slot (T q : ℕ) := Lex (Fin (T+1) × Fin q)

def rank {T q : ℕ} (x : Slot T q) : ℕ := (ofLex x).1.val

def tier {T q : ℕ} (x : Slot T q) : ℕ := T-rank x

def base (T q : ℕ) : Finset (Slot T q) := Finset.univ.image (fun j => toLex (⟨T,by omega⟩,j))

def guides {T q : ℕ} (x : Slot T q) : Finset (Slot T q) :=
  if h : rank x < T then Finset.univ.image (fun j => toLex (⟨rank x+1,by omega⟩,j)) else ∅

lemma rank_le {T q : ℕ} (x : Slot T q) : rank x ≤ T := by
  have h := (ofLex x).1.isLt
  dsimp [rank]; omega

lemma mem_base {T q : ℕ} (x : Slot T q) : x ∈ base T q ↔ rank x = T := by
  constructor
  · rintro hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
    rw [← hj]; rfl
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨(ofLex x).2,Finset.mem_univ _,?_⟩
    apply ofLex.injective
    apply Prod.ext
    · apply Fin.ext; exact hx.symm
    · rfl

lemma base_card (T q : ℕ) : (base T q).card = q := by
  rw [base,Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact congrArg (fun x : Slot T q => (ofLex x).2) h

lemma base_nonempty (T q : ℕ) (hq : 0 < q) : (base T q).Nonempty := by
  rw [← Finset.card_pos,base_card]
  exact hq

lemma guides_base {T q : ℕ} (x : Slot T q) (hx : x ∈ base T q) : guides x = ∅ := by
  simp [guides,(mem_base x).mp hx]

lemma guides_card {T q : ℕ} (x : Slot T q) (hx : x ∉ base T q) : (guides x).card = q := by
  have h : rank x < T := lt_of_le_of_ne (rank_le x) (fun he => hx ((mem_base x).mpr he))
  rw [guides,dite_eq_left h,Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact congrArg (fun x : Slot T q => (ofLex x).2) h

lemma guides_order {T q : ℕ} (x y : Slot T q) (hy : y ∈ guides x) : x < y := by
  unfold guides at hy
  split_ifs at hy with h
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact Prod.Lex.left (ofLex x).2 j (show (ofLex x).1 < ⟨rank x+1,by omega⟩ from by
      change rank x < rank x+1; omega)
  · simp at hy

lemma guides_tier {T q : ℕ} (x y : Slot T q) (hy : y ∈ guides x) : tier x = tier y+1 := by
  unfold guides at hy
  split_ifs at hy with h
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    simp only [tier,rank]
    change T-rank x = T-(rank x+1)+1
    omega
  · simp at hy

lemma slots_card (T q : ℕ) : Fintype.card (Slot T q) = (T+1)*q := by
  rw [Fintype.card_congr (ofLex : Slot T q ≃ Fin (T+1) × Fin q)]
  simp

lemma updates_count (T q : ℕ) : (∑ x : Slot T q, (guides x).card)+(base T q).card = T*q^2+q := by
  classical
  have hc : ((base T q)ᶜ).card = T*q := by
    rw [Finset.card_compl,slots_card,base_card,Nat.add_mul,one_mul,Nat.add_sub_cancel]
  have hs : ∑ x : Slot T q, (guides x).card = T*q*q := by
    rw [← Finset.sum_add_sum_compl (base T q)]
    have hb : (∑ x ∈ base T q, (guides x).card) = 0 := by
      apply Finset.sum_eq_zero; intro x hx; rw [guides_base x hx]; rfl
    have hg : (∑ x ∈ (base T q)ᶜ, (guides x).card) = ∑ x ∈ (base T q)ᶜ, q := by
      apply Finset.sum_congr rfl; intro x hx
      exact guides_card x (Finset.mem_compl.mp hx)
    rw [hb,hg,Finset.sum_const,smul_eq_mul,hc,zero_add]
  rw [hs,base_card]; ring

end MatchingFPRAS.Replica.Ladder

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable def tierBase (V : Type*) [Fintype V] : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹

lemma tierBase_pos (V : Type*) [Fintype V] : 0 < tierBase V := by
  unfold tierBase; positivity

noncomputable def slotWeight {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q) (e : BagEdge bags) : ℝ :=
  tierClamp (tierBase V) (tier x) (w e)

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
lemma slotWeight_pos {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q) (e : BagEdge bags) :
    0 < slotWeight w x e := tierClamp_pos (tierBase_pos V) _ _

noncomputable def slotLaw {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q)
    (A : PM (BagEdge.Incident (bags := bags))) : ℝ := gibbs (slotWeight w x) A

omit [DecidableEq V] [DecidableEq J] in
lemma slotLaw_pos {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q)
    (A : PM (BagEdge.Incident (bags := bags))) : 0 < slotLaw w x A := gibbs_pos _ (slotWeight_pos w x) A

omit [DecidableEq V] [DecidableEq J] in
lemma slotLaw_sum {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q)
    (M : PM (BagEdge.Incident (bags := bags))) : (∑ A, slotLaw w x A) = 1 :=
  gibbs_sum _ (slotWeight_pos w x) M

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

noncomputable def treeLadderCapacity {T q : ℕ} (w : BagEdge bags → ℝ) (x y : Slot T q) :
    PairCapacity (slotLaw w) x y := by
  classical
  let π : (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) → ℝ :=
    fun a => slotLaw w x a.1*slotLaw w y a.2
  exact {
    q := metropolisCapacity (treePairProposal hbags hG) π
    nonneg := metropolisCapacity_nonneg _ _ (fun a => mul_nonneg (slotLaw_pos w x a.1).le (slotLaw_pos w y a.2).le)
    row := metropolisCapacity_row _ _
    col := metropolisCapacity_col _ _ }

end

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : J → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

theorem concrete_ladder_poincare (hN : 2 ≤ Fintype.card V)
    (M₀ : PM (BagEdge.Incident (bags := bags))) (T : ℕ)
    (f : (Slot T (32*(10^4*Fintype.card V*D)^100) → PM (BagEdge.Incident (bags := bags))) → ℝ) :
    let q := 32*(10^4*Fintype.card V*D)^100
    MatchingFPRAS.Replica.variance (slotLaw w) f ≤ ((8*(T*q^2+q):ℕ):ℝ)/3 *
      scanEnergy (slotLaw w) guides (base T q) (treeLadderCapacity hbags hG w) f := by
  classical
  let q : ℕ := 32*(10^4*Fintype.card V*D)^100
  let L : ℝ := ((10^4:ℝ)*Fintype.card V*D)^100
  have hDc : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hNp : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hDp : 0 < (D:ℝ) := lt_of_lt_of_le (by norm_num) hDc
  have hL : 0 < L := by dsimp [L]; positivity
  have hq : (q:ℝ) = 32*L := by norm_num [q,L,Nat.cast_mul,Nat.cast_pow]
  have hqn : 0 < q := by
    have : (0:ℝ) < (q:ℝ) := by rw [hq]; positivity
    exact_mod_cast this
  have hQ : ∀ x y : Slot T q, y ∈ guides x →
      PairPoincare (slotLaw w) x y (treeLadderCapacity hbags hG w x y) (2*L) := by
    intro x y hy a b
    have ht := adjacent_tree_pair_poincare (hbags := hbags) (hG := hG)
      height hheight hstep (D:ℝ) hDc w hw hN M₀ (tier y) a b
    change localVariance (gibbs (slotWeight w x)) a ≤ (2*L)*
      treePairEnergy hbags hG (slotWeight w x) (slotWeight w y) (fun z => a z.1+b z.2)
    unfold slotWeight
    rw [guides_tier x y hy]
    exact ht
  have hh := replica_gap (slotLaw w) (fun x A => (slotLaw_pos w x A).le)
    (fun x => slotLaw_sum w x M₀) guides (base T q) (base_nonempty T q hqn)
    q L hL hq (fun x hx => guides_card x hx) (fun x hx => guides_base x hx)
    (fun x y hy => guides_order x y hy) (treeLadderCapacity hbags hG w) hQ f
  rw [updates_count] at hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

end MatchingFPRAS.Transport

end OAI
