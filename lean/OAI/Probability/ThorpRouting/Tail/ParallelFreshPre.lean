import Mathlib
import OAI.Probability.ThorpRouting.Tail.BenesCoins

namespace OAI

namespace ThorpNine.Tail

namespace Thorp

lemma mem_centralBlock (r H : ℕ) (b : Card r) (x : Card (H+r)) :
    x ∈ centralBlock r H b ↔ (cardSplit r H x).1 = b := by
  classical
  constructor
  · intro h
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h
    simp only [Equiv.apply_symm_apply]
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(cardSplit r H x).2,Finset.mem_univ _,?_⟩
    rw [←h,Prod.mk.eta,Equiv.symm_apply_apply]

lemma centralBlock_card (r H : ℕ) (b : Card r) : (centralBlock r H b).card = 2^H := by
  classical
  rw [centralBlock,Finset.card_image_of_injective]
  · exact card_positions H
  · intro x y h
    exact congrArg Prod.snd ((cardSplit r H).symm.injective h)

lemma centralBlock_disjoint (r H : ℕ) :
    Pairwise (fun b b' => Disjoint (centralBlock r H b) (centralBlock r H b')) := by
  classical
  intro b b' h
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (((mem_centralBlock r H b x).mp hx).symm.trans
    ((mem_centralBlock r H b' x).mp hy))

lemma centralBlock_zero (H : ℕ) (b : Card 0) : centralBlock 0 H b = Finset.univ := by
  classical
  ext x
  simp only [mem_centralBlock,Finset.mem_univ,iff_true]
  exact Subsingleton.elim _ _

lemma centralBlock_step (r H : ℕ) (b : Bool) (c : Card r) :
    centralBlock (r+1) H (Fin.cons b c) = (centralBlock r H c).image (Fin.cons b) := by
  classical
  simp only [centralBlock,Finset.image_image,cardSplit,Equiv.coe_fn_symm_mk,
    Fin.cons_zero,Fin.tail_cons,Function.comp_def]

lemma block_inter_step (r H : ℕ) (b : Bool) (c : Card r) (A : Finset (Card (H+(r+1)))) :
    centralBlock (r+1) H (Fin.cons b c) ∩ A =
      (centralBlock r H c ∩ childMarks A b).image (Fin.cons b) := by
  classical
  rw [centralBlock_step]
  ext x
  constructor
  · intro hx
    obtain ⟨hxB,hxA⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hxB
    exact Finset.mem_image.mpr ⟨y,Finset.mem_inter.mpr ⟨hy,(mem_childMarks A b y).mpr hxA⟩,rfl⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y,(Finset.mem_inter.mp hy).1,rfl⟩,
      (mem_childMarks A b y).mp (Finset.mem_inter.mp hy).2⟩

lemma sparseMass_central_zero (H : ℕ) (A : Finset (Card H)) :
    sparseMass (centralBlock 0 H) A = crowdedMass A.card := by
  classical
  simp only [sparseMass,centralBlock_zero,Finset.univ_inter,crowdedMass,
    Finset.sum_const,Finset.card_univ,card_positions,pow_zero,one_nsmul]

lemma sparseMass_central_step (r H : ℕ) (A : Finset (Card (H+(r+1)))) :
    sparseMass (centralBlock (r+1) H) A =
      sparseMass (centralBlock r H) (childMarks A false) +
        sparseMass (centralBlock r H) (childMarks A true) := by
  classical
  unfold sparseMass
  rw [←Equiv.sum_comp (headTailEquiv r).symm,Fintype.sum_prod_type]
  have ht (b : Bool) (c : Card r) : (headTailEquiv r).symm (b,c) = Fin.cons b c := rfl
  simp only [Fintype.sum_bool,ht]
  have hc (b : Bool) (c : Card r) :
      (centralBlock (r+1) H (Fin.cons b c) ∩ A).card =
      (centralBlock r H c ∩ childMarks A b).card := by
    rw [block_inter_step]
    apply Finset.card_image_of_injective
    intro x y h
    simpa only [Fin.tail_cons] using congrArg Fin.tail h
  simp only [hc]
  exact add_comm _ _


lemma inverseButterfly_coordinates_step (d : ℕ)
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool)
    (x : Card (d+1)) :
    headTailEquiv d ((butterflyPerm (d+1)
      (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ)))).symm x) =
      (Bool.xor (x 0) (ξ (Fin.tail x)),
        (butterflyPerm d (decodeButterfly d
          (if Bool.xor (x 0) (ξ (Fin.tail x)) then c.2 else c.1))).symm (Fin.tail x)) := by
  rw [butterflyPerm_step]
  rfl

lemma inverseButterflyMarks_child (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1))
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool) (b : Bool) :
    childMarks (inverseButterflyMarks (d+1) (Finset.univ.image e)
      ((coinStepEquiv d).symm (c,ξ))) b =
      inverseButterflyMarks d
        (Finset.univ.image (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ)
            (PairRouting.colors_compatible _ _) b)) (if b then c.2 else c.1) := by
  classical
  let x := e.trans (headTailEquiv d).toEmbedding
  let col := PairRouting.colors x ξ
  let child := PairRouting.childEmbedding x col (PairRouting.colors_compatible x ξ) b
  have hp (i : ι) : headTailEquiv d ((butterflyPerm (d+1)
      (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ)))).symm (e i)) =
      (col i,(butterflyPerm d (decodeButterfly d (if col i then c.2 else c.1))).symm (x i).2) :=
    inverseButterfly_coordinates_step d c ξ (e i)
  ext y
  simp only [mem_childMarks,inverseButterflyMarks,Finset.image_image,
    Finset.mem_image,Finset.mem_univ,true_and,Function.comp_def]
  constructor
  · rintro ⟨i,hi⟩
    have he := congrArg (headTailEquiv d) hi
    rw [hp i] at he
    change (col i,_) = (b,y) at he
    have hb := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only at hb hy
    refine ⟨⟨i,hb⟩,?_⟩
    change (butterflyPerm d (decodeButterfly d (if b then c.2 else c.1))).symm (x i).2 = y
    simpa only [hb] using hy
  · rintro ⟨i,hi⟩
    refine ⟨i.val,?_⟩
    apply (headTailEquiv d).injective
    rw [hp]
    change (col i.val,_) = (b,y)
    have hb : col i.val = b := i.property
    rw [hb]
    exact Prod.ext rfl hi

lemma inverseButterflyMarks_card (d : ℕ) (A : Finset (Card d)) (ω : SwitchIndex d → Bool) :
    (inverseButterflyMarks d A ω).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (butterflyPerm d (decodeButterfly d ω)).symm.injective

lemma benes_input_coordinates (d : ℕ) (ω : BenesCoins (d+1)) :
    ω.2 = (coinStepEquiv d).symm
      (((benesStepEquiv d ω).1.1.2,(benesStepEquiv d ω).1.2.2),(benesStepEquiv d ω).2.1) := by
  change ω.2 = (coinStepEquiv d).symm (coinStepEquiv d ω.2)
  exact ((coinStepEquiv d).symm_apply_apply ω.2).symm

lemma cutoffMass_central (r H : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (ω : BenesCoins (H+r)) :
    cutoffMass H (H+r) e ω =
      sparseMass (centralBlock r H) (inverseButterflyMarks (H+r) (Finset.univ.image e) ω.2) := by
  classical
  induction r generalizing ι with
  | zero =>
    rw [sparseMass_central_zero,inverseButterflyMarks_card,
      Finset.card_image_of_injective _ e.injective,Finset.card_univ]
    cases H with
    | zero =>
      have hcard : Fintype.card ι ≤ 1 := by
        have hh := Fintype.card_le_of_injective e e.injective
        simpa only [Nat.add_zero,card_positions,pow_zero] using hh
      simp [cutoffMass,crowdedMass,show ¬2≤Fintype.card ι by omega]
    | succ H => simp only [cutoffMass,le_refl,ite_true]
  | succ r ih =>
    simp only [Nat.add_succ] at *
    rw [cutoffMass,ite_eq_right (by omega : ¬H+r+1≤H)]
    let σ := benesStepEquiv (H+r) ω
    let x := e.trans (headTailEquiv (H+r)).toEmbedding
    let col := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    change cutoffMass H (H+r) (PairRouting.childEmbedding x col hc false) σ.1.1 +
      cutoffMass H (H+r) (PairRouting.childEmbedding x col hc true) σ.1.2 = _
    rw [ih,ih,sparseMass_central_step,benes_input_coordinates (H+r) ω]
    rw [inverseButterflyMarks_child,inverseButterflyMarks_child]
    rfl


theorem palindrome_low_mgf (r H : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (q : ℝ) (hq : 1 ≤ q)
    (hr : (2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*q^H) ≤ 1/2) :
    finiteMean (fun ω : BenesCoins (H+r) => q^(palindromeLowCost H (H+r) e ω)) ≤
      Real.exp ((2:ℝ)^r * (2 * ((2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*q^H))^2)) := by
  classical
  have hec : (Finset.univ.image e).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ e.injective,Finset.card_univ]
  have hm := inverseButterfly_sparse_mgf (H+r) (centralBlock r H)
    (centralBlock_disjoint r H) (Finset.univ.image e) (q^H)
    (pow_nonneg (by linarith) _) (fun b => by
      simpa only [centralBlock_card,hec,Nat.cast_pow,Nat.cast_ofNat] using hr)
  calc
    _ ≤ finiteMean (fun ω : BenesCoins (H+r) => (q^H)^(cutoffMass H (H+r) e ω)) := by
      apply finiteMean_mono
      intro ω
      rw [←pow_mul]
      exact pow_le_pow_right₀ hq (palindromeLowCost_le_cutoff H (H+r) e ω)
    _ = finiteMean (fun ω : SwitchIndex (H+r) → Bool =>
        (q^H)^(sparseMass (centralBlock r H)
          (inverseButterflyMarks (H+r) (Finset.univ.image e) ω))) := by
      simp_rw [cutoffMass_central]
      simp only [finiteMean_prod,finiteMean_const]
    _ ≤ _ := by
      simpa only [centralBlock_card,hec,Nat.cast_pow,Nat.cast_ofNat,Finset.sum_const,
        Finset.card_univ,card_positions,nsmul_eq_mul] using hm

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

end Thorp
namespace Thorp
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

end Thorp
namespace Thorp

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

def AgreeThrough (d s : ℕ) (Y Y' : SwitchIndex d → Bool) : Prop :=
  ∀ i, switchHeight d i ≤ s → Y i = Y' i

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

noncomputable def palindromeSlabCost (l d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ i : Fin l, palindromeLevelCost (l+i.1+1) d e ω

lemma palindromeSlabCost_adapted (l d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (2*l) (fun Y => palindromeSlabCost l d e (Y,X)) := by
  apply layerAdapted_sum
  intro i _
  exact layerAdapted_mono (palindromeLevelCost_adapted (l+i.1+1) d e X) (by omega)

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

end Thorp

end ThorpNine.Tail

end OAI
