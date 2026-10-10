import Mathlib
import OAI.Algebra.GroupRing.GridUniform
import OAI.Algebra.GroupRing.ChainActiveStages

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T QV QD : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]
    [Fintype QV] [Fintype QD]
variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

/-- Restriction needs only injectivity, not a bijection onto the whole image.
In particular, inactive marked vertices are never carried into a stage. -/
def restrict (Q : PortGraph QV QD) (fv : QV ↪ PV) (fd : QD ↪ PD)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d)) (pin' : QV → Option TV)
    (hp : ∀ v y,pin' v=some y → pin (fv v)=some y) :
    Embedding Q (plabel ∘ fd) outgoing pin' bar r where
  vertex := fv.trans e.vertex
  port := fd.trans e.port
  origin_eq d := by simpa only [Function.Embedding.trans_apply,ho] using e.origin_eq (fd d)
  label_eq d := e.label_eq (fd d)
  reverse_eq d := by simpa only [Function.Embedding.trans_apply,hr] using e.reverse_eq (fd d)
  pin_eq v y hy := e.pin_eq (fv v) y (hp v y hy)

/-- Change the displayed port labeling by a literal pointwise equality. -/
def congrLabel (label' : PD → T) (hl : ∀ d,label' d=plabel d) :
    Embedding Γ label' outgoing pin bar r where
  vertex := e.vertex
  port := e.port
  origin_eq := e.origin_eq
  label_eq d := (e.label_eq d).trans (hl d).symm
  reverse_eq := e.reverse_eq
  pin_eq := e.pin_eq

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.ActualStageRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "len" => ChainStageEmbedding.length Γ mark h2 paths j
local notation "Q" => ChainStageEmbedding.graph Γ mark h2 paths j
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)

/-- The actual signed labels, at every position of every active chain. -/
def word (label : D → Types.Letter) : ComparedBlocks.Position len → WordEstimate.Letter :=
  fun x => Types.signedLetter.symm (label (F^[x.2.val.toNat] x.1.val.val.val))

lemma index_mem (c : ChainActiveStages.ActiveChain Γ mark h2 paths j) (i : Fin (len c)) :
    (i.val:ℤ)∈BlockAlignment.positions 0 (len c) := by
  rw [AffineIntervals.nat_positions]
  simp only [Finset.mem_Ico]
  constructor
  · omega
  · exact_mod_cast i.isLt

lemma label_eq (label : D → Types.Letter) (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (d : ChainSubdivision.Dart len) :
    ChainRealization.label len (StageExpectation.readWord len (word Γ mark h2 paths j label)) d =
      label (ChainStageEmbedding.dartMap Γ mark h2 paths j d) := by
  rcases d with ⟨⟨c,i⟩,b⟩
  have hi := index_mem Γ mark h2 paths j c i
  cases b <;>
    simp only [ChainRealization.label,Bool.false_eq_true,ite_false,ite_true,StageExpectation.readWord,
      dite_eq_left hi,word,Int.toNat_natCast,Types.signedLetter.apply_symm_apply,
      ChainStageEmbedding.dartMap,Function.comp_apply,SubdivisionRestriction.dart,ChainIsomorphism.dartMap,hl]

variable [Fintype V] {TV : Type} [Fintype TV]
    {outgoing : TV → Finset Types.Letter} {pin : V → Option TV}
    {r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse}

/-- An actual sampled graph embedding yields the exact stage realization
counted by the conditional-matching first moment. -/
def embedding (label : D → Types.Letter)
    (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (e : RealizationTransport.Embedding Γ label outgoing pin Types.inverse r)
    (pin' : StageSubgraphs.ActiveV (S) (ListStageExponents.mult (S) paths) j → Option TV)
    (hp : ∀ v y,pin' v=some y → pin v.val=some y) :
    RealizationTransport.Embedding (Q)
      (ChainRealization.label len (StageExpectation.readWord len (word Γ mark h2 paths j label)))
      outgoing (ChainRealization.pin len pin') Types.inverse r := by
  let fv : ChainSubdivision.Vertex len ↪ V :=
    ⟨ChainStageEmbedding.vertexMap Γ mark h2 paths j,ChainStageEmbedding.vertexMap_injective Γ mark h2 paths j⟩
  let fd : ChainSubdivision.Dart len ↪ D :=
    ⟨ChainStageEmbedding.dartMap Γ mark h2 paths j,ChainStageEmbedding.dartMap_injective Γ mark h2 paths j⟩
  have hp' : ∀ v y,ChainRealization.pin len pin' v=some y → pin (fv v)=some y := by
    intro v y hy
    cases v with
    | inl v => exact hp v y hy
    | inr v => cases hy
  exact RealizationTransport.congrLabel (RealizationTransport.restrict e (Q) fv fd
    (ChainStageEmbedding.origin_map Γ mark h2 paths j)
    (ChainStageEmbedding.reverse_map Γ mark h2 paths j) _ hp') _
      (label_eq Γ mark h2 paths j label hl)

end TorsionFreeZeroDivisors.ActualStageRealization

namespace TorsionFreeZeroDivisors.ActualStageFeasibility
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

lemma signed_inverse (t : Types.Letter) :
    Types.signedLetter.symm (Types.inverse t)=inverse (Types.signedLetter.symm t) := by
  simp [Types.inverse,inverse]

lemma signed_choice (b : Bool) (t : Types.Letter) :
    Types.signedLetter.symm (if b then Types.inverse t else t)=
      if b then inverse (Types.signedLetter.symm t) else Types.signedLetter.symm t := by
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,signed_inverse]

lemma weight_pos {t u : Letter} (h : u≠inverse t) : 0 < weight t u := by
  unfold weight baseWeight p
  simp only [ite_eq_right h]
  split_ifs <;> norm_num

variable {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)

omit [Fintype C] in
lemma block_weight_pos (w : C → ℤ → Letter) (hw : ActualStageLabels.Immersed s len w)
    (i : Underlying s len) : 0 < wordWeight (height s len i) (RepeatedBlocks.word s len w i) := by
  rw [ChainWeights.wordWeight_pred]
  apply Finset.prod_pos
  intro k _
  apply weight_pos
  have hq := (ChainWeights.firstCoordinate s len i k).property
  have hq' := (ChainWeights.nextCoordinate s len i k).property
  simp only [ChainWeights.firstCoordinate_val,block_interval,Finset.mem_Ico] at hq
  simp only [ChainWeights.nextCoordinate_val,block_interval,Finset.mem_Ico] at hq'
  have hh := hw i ((k.val:ℤ)+lower s len i) hq.1 (by omega)
  simpa only [RepeatedBlocks.word,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hh

def bins (w : C → ℤ → Letter) (i : Underlying s len) : ℤ :=
  ⌊-Real.log (wordWeight (height s len i) (RepeatedBlocks.word s len w i))⌋

omit [Fintype C] in
lemma mem_bin (w : C → ℤ → Letter) (hw : ActualStageLabels.Immersed s len w)
    (i : Underlying s len) : RepeatedBlocks.word s len w i ∈ binWords (height s len i) (bins s len w i) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,block_weight_pos s len w hw i,rfl⟩

lemma fullWords_of_comparing {E : Type*} (m : C → ℕ)
    (cmp : Comparisons (E:=E) (RepeatedBlocks.traversalLength len m))
    (j : ℕ) (w : C → ℤ → Letter) (hw : ActualStageLabels.Comparing len m cmp w)
    (hr : ActualStageLabels.Immersed s len w) :
    (fun x : ChainStageLabels.StagePosition len m j => w x.1.val x.2.val) ∈
      ChainStageLabels.fullWords s len m j cmp (bins s len w) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,w,hw,hr,mem_bin s len w hr,rfl⟩

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "lenR" => repLength Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (ChainChunkTransport.color Γ mark h2 paths)

def globalWord (label : D → Types.Letter) (c : R) (q : ℤ) : Letter :=
  Types.signedLetter.symm (label (F^[q.toNat] c.val.val))

lemma immersed (hs : 0<s) (label : D → Types.Letter)
    (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (hinj : ∀ d e,Γ.origin d=Γ.origin e → label d=label e → d=e) :
    ActualStageLabels.Immersed s (lenR) (globalWord Γ mark h2 label) := by
  intro i q hq hq'
  have hb : q∈block s i.2.val := by rw [block_interval s (lenR) i]; simp only [Finset.mem_Ico]; omega
  have hb' : q+1∈block s i.2.val := by rw [block_interval s (lenR) i]; simp only [Finset.mem_Ico]; omega
  have ht := full_subset s hs (lenR i.1) i.2 hb
  have ht' := full_subset s hs (lenR i.1) i.2 hb'
  rw [AffineIntervals.nat_positions,Finset.mem_Ico] at ht ht'
  have hn := normalized_immersed Γ mark h2 Types.inverse label hl hinj i.1 q ht.1 ht'.2
  intro he
  apply hn
  apply Types.signedLetter.symm.injective
  rw [signed_inverse]
  exact he

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

lemma comparing (label : D → Types.Letter)
    (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (hc : ∀ x e,cmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if cmp.reverse e then Types.inverse (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ActualStageLabels.Comparing (lenR) (m)
      ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi) (globalWord Γ mark h2 label) := by
  intro x a ha
  have hh := normalized_compatible Γ mark h2 paths cmp lo hi hlo hhi Types.inverse
    Types.inverse_inverse label hl hc x a ha
  apply_fun Types.signedLetter.symm at hh
  rw [signed_choice] at hh
  have hp : ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).pairing=
      (repeatedChunks Γ mark h2 paths).pairing cmp := rfl
  rw [hp]
  exact hh

lemma feasible (hs : 0<s) (label : D → Types.Letter)
    (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (hinj : ∀ d e,Γ.origin d=Γ.origin e → label d=label e → d=e)
    (hc : ∀ x e,cmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if cmp.reverse e then Types.inverse (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ActualStageLabels.Feasible s (lenR) (m)
      ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi)
      (bins s (lenR) (globalWord Γ mark h2 label))
      (RepeatedBlocks.word s (lenR) (globalWord Γ mark h2 label)) := by
  have hr := immersed s Γ mark h2 hs label hl hinj
  exact ⟨mem_bin s (lenR) _ hr,_,comparing Γ mark h2 paths cmp lo hi hlo hhi label hl hc,hr,rfl⟩

lemma fullWords_mem (hs : 0<s) (j : ℕ) (label : D → Types.Letter)
    (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (hinj : ∀ d e,Γ.origin d=Γ.origin e → label d=label e → d=e)
    (hc : ∀ x e,cmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if cmp.reverse e then Types.inverse (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    (fun x : ChainStageLabels.StagePosition (lenR) (m) j => globalWord Γ mark h2 label x.1.val x.2.val) ∈
      ChainStageLabels.fullWords s (lenR) (m) j
        ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi)
        (bins s (lenR) (globalWord Γ mark h2 label)) := by
  exact fullWords_of_comparing s (lenR) (m) _ j _
    (comparing Γ mark h2 paths cmp lo hi hlo hhi label hl hc)
    (immersed s Γ mark h2 hs label hl hinj)

end TorsionFreeZeroDivisors.ActualStageFeasibility

namespace TorsionFreeZeroDivisors.StagePartition
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks ChainStageLabels WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)

abbrev CA := {a : C // j < m a ∧ side a=true}
abbrev CB := {b : C // j < m b ∧ side b=false}
abbrev lenA : CA m side j → ℕ := fun a => len a.val
abbrev lenB : CB m side j → ℕ := fun b => len b.val

def restrictA (F : StagePosition len m j → Letter) : Position (lenA len m side j) → Letter :=
  fun x => F ⟨⟨x.1.val,x.1.property.1⟩,x.2⟩
def restrictB (F : StagePosition len m j → Letter) : Position (lenB len m side j) → Letter :=
  fun x => F ⟨⟨x.1.val,x.1.property.1⟩,x.2⟩

def indexA (i : Underlying s (lenA len m side j)) : Underlying s len := ⟨i.1.val,i.2⟩
def indexB (i : Underlying s (lenB len m side j)) : Underlying s len := ⟨i.1.val,i.2⟩

include hs in
theorem binsA (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    ∀ i, word s (lenA len m side j) (StageExpectation.readWord (lenA len m side j)
      (restrictA len m side j F)) i ∈ binWords (height s (lenA len m side j) i) (d (indexA s len m side j i)) := by
  obtain ⟨w,_,_,hb,rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenA len m side j) (StageExpectation.readWord (lenA len m side j)
      (restrictA len m side j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexA s len m side j i) := by
    funext k
    dsimp only [word,StageExpectation.readWord]
    rw [dite_eq_left (StageExpectation.word_position s hs (lenA len m side j) i k)]
    rfl
  rw [he]
  exact hb (indexA s len m side j i)

include hs in
theorem binsB (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    ∀ i, word s (lenB len m side j) (StageExpectation.readWord (lenB len m side j)
      (restrictB len m side j F)) i ∈ binWords (height s (lenB len m side j) i) (d (indexB s len m side j i)) := by
  obtain ⟨w,_,_,hb,rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenB len m side j) (StageExpectation.readWord (lenB len m side j)
      (restrictB len m side j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexB s len m side j i) := by
    funext k
    dsimp only [word,StageExpectation.readWord]
    rw [dite_eq_left (StageExpectation.word_position s hs (lenB len m side j) i k)]
    rfl
  rw [he]
  exact hb (indexB s len m side j i)

def joinBlock : Underlying s (lenA len m side j) ⊕ Underlying s (lenB len m side j) →
    Underlying s (StageExpectation.activeLen len m j)
  | .inl i => ⟨⟨i.1.val,i.1.property.1⟩,i.2⟩
  | .inr i => ⟨⟨i.1.val,i.1.property.1⟩,i.2⟩

omit [Fintype C] in
theorem joinBlock_bijective : Function.Bijective (joinBlock s len m side j) := by
  constructor
  · intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        rcases x with ⟨⟨a,ha⟩,ix⟩
        rcases y with ⟨⟨b,hb⟩,iy⟩
        have hab : a=b := congrArg (fun z => z.1.val) he
        subst b
        have hii : ix=iy := Fin.ext (congrArg (fun z => z.2.val) he)
        subst iy
        rfl
      | inr y =>
        have h := congrArg (fun z => side z.1.val) he
        change side x.1.val=side y.1.val at h
        rw [x.1.property.2,y.1.property.2] at h
        cases h
    | inr x =>
      cases y with
      | inl y =>
        have h := congrArg (fun z => side z.1.val) he
        change side x.1.val=side y.1.val at h
        rw [x.1.property.2,y.1.property.2] at h
        cases h
      | inr y =>
        rcases x with ⟨⟨a,ha⟩,ix⟩
        rcases y with ⟨⟨b,hb⟩,iy⟩
        have hab : a=b := congrArg (fun z => z.1.val) he
        subst b
        have hii : ix=iy := Fin.ext (congrArg (fun z => z.2.val) he)
        subst iy
        rfl
  · rintro ⟨⟨c,hc⟩,b⟩
    cases hh : side c with
    | true => exact ⟨.inl ⟨⟨c,hc,hh⟩,b⟩,rfl⟩
    | false => exact ⟨.inr ⟨⟨c,hc,hh⟩,b⟩,rfl⟩

def blockEquiv := Equiv.ofBijective (joinBlock s len m side j) (joinBlock_bijective s len m side j)

theorem bin_sum (d : Underlying s len → ℤ) :
    (∑ i, (d (indexA s len m side j i) : ℝ)) + (∑ i, (d (indexB s len m side j i) : ℝ)) =
      ∑ i ∈ activeBlocks s len m j, (d i : ℝ) := by
  rw [← StageExpectation.active_bin_sum s len m j d]
  calc
    _ = ∑ i : Underlying s (lenA len m side j) ⊕ Underlying s (lenB len m side j),
        (d (StageExpectation.activeIndex s len m j (joinBlock s len m side j i)) : ℝ) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := Fintype.sum_equiv (blockEquiv s len m side j) _ _ (fun _ => rfl)

variable (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)

def sideA : TwoSideStage.Side where
  C := CA m side j; V := VA; TV := TA
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenA len m side j
  first := firstA; last := lastA; outgoing := outA; pin := pinA

def sideB : TwoSideStage.Side where
  C := CB m side j; V := VB; TV := TB
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenB len m side j
  first := firstB; last := lastB; outgoing := outB; pin := pinB

local notation "SA" => sideA len m side j firstA lastA outA pinA
local notation "SB" => sideB len m side j firstB lastB outB pinB

theorem exponential_fusion (u v k x y z : ℝ) (hz : x+y=z) :
    Real.exp (u+v)*(k*Real.exp (-x-y)) = k*Real.exp (u-z+v) := by
  rw [← hz]
  simp only [sub_eq_add_neg,Real.exp_add,Real.exp_neg]
  ring

include hs in
/-- The joint matching expectation applied to the actual fullWords projection,
including cross-side comparisons. All entropy and bin costs are computed on
that one global pattern. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (n p : ℝ) (N D R : ℕ) (hA : TwoSideStage.Conditions SA n p N D R)
    (hB : TwoSideStage.Conditions SB n p N D R) :
    TwoSideMean.mean (((SA).samples N) ×ˢ ((SB).samples N))
      (TwoSideStage.count SA SB (fullWords s len m j cmp d)
        (restrictA len m side j) (restrictB len m side j)) ≤
      ((SA).cost n p R * (SB).cost n p R) *
        Real.exp ((∑ c : StageLabels.activeComponents
          (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
          ActualStageLabels.cost s hs len m cmp err d c.val) -
          (∑ i ∈ activeBlocks s len m j, (d i : ℝ)) +
          (2*(err : ℝ)*Fintype.card (Underlying s len)+(s+1)*Fintype.card C)*
            Real.log (Fintype.card Letter)) := by
  have h := TwoSideStage.mean_bound s hs SA SB (fullWords s len m j cmp d)
    (restrictA len m side j) (restrictB len m side j) n p N D R hA hB
    (fun i => d (indexA s len m side j i)) (fun i => d (indexB s len m side j i))
    (binsA s hs len m side j cmp d) (binsB s hs len m side j cmp d)
  have hc := full_stage_count s hs len m j cmp d err hlarge hscale hreduced
  have hn : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TA)).trans hA.vertices
  have hp := hA.nonneg
  have hcost : 0 ≤ (SA).cost n p R * (SB).cost n p R := by unfold TwoSideStage.Side.cost; positivity
  have h' := h.trans (mul_le_mul_of_nonneg_right hc
    (mul_nonneg hcost (Real.exp_pos _).le))
  exact h'.trans_eq (exponential_fusion _ _ _ _ _ _ (bin_sum s len m side j d))

end TorsionFreeZeroDivisors.StagePartition

end

end OAI
