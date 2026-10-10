import OAI.Computability.TypeSystem.Wrappers

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
open Classical
variable {S : Type u} {P : Specification S}

namespace ProofWrapper.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    {C : Set (Set S)} {I J : Set S} {b : Bool}
theorem of_path (hC : IsComponent (PrimaryEdge P) C) (hI : I ∈ C) (hJ : J ∈ C)
    (hp : SignedPath (PrimaryEdge P) I J b) : ∃ R, Formed W C I J b R := by
  obtain ⟨R,hr⟩ := (Formed.identity (W := W) (C := C) (I := I)).path (hC.restrict_path hI hJ hp)
  exact ⟨R,by simpa only [Bool.false_xor] using hr⟩
end ProofWrapper.Formed

/-- Quantification uses the displayed direct-vertex annotation throughout. -/
structure QuantifierRoute {Γ : List (Expr S)} {γ : Nat → Mode}
    (W : WitnessFamily P Γ γ) (C : Set (Set S)) (b I : Set S) where
  codomain : Set S
  product : Set S
  triple : ProfileTriple P I codomain product
  inCode : ProofWrapper S
  inFormed : inCode.Formed W C b codomain false
  outCode : ProofWrapper S
  outFormed : outCode.Formed W C product b false

namespace QuantifierRoute
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {b I : Set S}
def rename (R : QuantifierRoute W C b I) (e : Embedding P Γ γ Δ δ) :
    QuantifierRoute (W.rename e) C b I where
  codomain := R.codomain
  product := R.product
  triple := R.triple
  inCode := R.inCode.rename e.names
  inFormed := R.inFormed.rename e
  outCode := R.outCode.rename e.names
  outFormed := R.outFormed.rename e

theorem exists_route (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    (hb : b ∈ C) (hI : DirectLayer P C I) : Nonempty (QuantifierRoute W C b I) := by
  obtain ⟨J,hJ,K,hK,ht⟩ := hI.2
  obtain ⟨R,hR⟩ := ProofWrapper.Formed.of_path W hC hb hJ (hC.all_parities hr ho hb hJ false)
  obtain ⟨R',hR'⟩ := ProofWrapper.Formed.of_path W hC hK hb (hC.all_parities hr ho hK hb false)
  exact ⟨⟨J,K,ht,R,hR,R',hR'⟩⟩
end QuantifierRoute

/-- Actual finite ambient context data for the source's classical logical
calculus. All fields are constructed below from fixed graph paths and terms. -/
structure LogicSetup (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode)
    (C : Set (Set S)) where
  witnesses : WitnessFamily P Γ γ
  converters : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
    Transfer P Γ γ (witnesses.type J) (witnesses.type J')
  base : Set S
  domain : Set S
  product : Set S
  triple : ProfileTriple P domain base product
  domain_mem : domain ∈ C
  base_mem : base ∈ C
  product_mem : product ∈ C
  inCode : ProofWrapper S
  inFormed : inCode.Formed witnesses C base domain false
  outCode : ProofWrapper S
  outFormed : outCode.Formed witnesses C product base false
  quantifiers : ∀ I, DirectLayer P C I → QuantifierRoute witnesses C base I

namespace LogicSetup

section
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}

def rename (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ) : LogicSetup P Δ δ C where
  witnesses := L.witnesses.rename e
  converters J J' hJ hJ' := by
    obtain ⟨s,hs⟩ := hJ.feasible.1
    exact (L.converters J J' hJ hJ').rename e (L.witnesses.sorted J hJ.feasible s hs)
  base := L.base
  domain := L.domain
  product := L.product
  triple := L.triple
  domain_mem := L.domain_mem
  base_mem := L.base_mem
  product_mem := L.product_mem
  inCode := L.inCode.rename e.names
  inFormed := L.inFormed.rename e
  outCode := L.outCode.rename e.names
  outFormed := L.outFormed.rename e
  quantifiers I hI := (L.quantifiers I hI).rename e

def bottom (L : LogicSetup P Γ γ C) : Expr S := L.witnesses.type L.base

theorem terminal_base (L : LogicSetup P Γ γ C) : TerminalProfile P C L.base :=
  ⟨L.domain,L.product,L.triple,L.domain_mem,L.product_mem⟩

def Formula (L : LogicSetup P Γ γ C) (A : Expr S) : Prop :=
  SortedAt P Γ A L.base ∧ WellModed γ A .data ∧ StableExtraction L.witnesses C A

theorem Formula.rename {L : LogicSetup P Γ γ C} {A : Expr S} (h : L.Formula A)
    (e : Embedding P Γ γ Δ δ) : (L.rename e).Formula (A.rename e.names) :=
  ⟨fun _ hs => e.typing (h.1 _ hs),e.moded h.2.1,h.2.2.rename e⟩

theorem bottom_formula (L : LogicSetup P Γ γ C) : L.Formula L.bottom :=
  ⟨L.witnesses.sorted L.base L.triple.codomain,L.witnesses.type_mode L.base L.triple.codomain,
    StableExtraction.terminal L.terminal_base⟩

/-- The ambient proof declarations are only the actual terminal converters, and
hence the no-normal-proof criterion applies to the eventual bottom inhabitant. -/
theorem exists_setup [Fintype S] (C : Set (Set S)) (hC : IsComponent (PrimaryEdge P) C)
    (ho : ∃ r ∈ C, SignedPath (PrimaryEdge P) r r true)
    (ht : ∃ I J K, ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C) :
    ∃ Γ γ, ProofContext Γ γ ∧ Nonempty (LogicSetup P Γ γ C) := by
  obtain ⟨Γ,hv,⟨W⟩⟩ := WitnessFamily.exists_family (P := P)
  have hc : ProofContext Γ (fun _ => .data) := by intro n A hn hm; cases hm
  obtain ⟨Δ,δ,e,hΔ,hτ⟩ := W.terminal_network hC hv hc
  let W' := W.rename e
  obtain ⟨r,hr,ho⟩ := ho
  obtain ⟨I,J,K,ht,hI,hJ,hK⟩ := ht
  obtain ⟨R,hR⟩ := ProofWrapper.Formed.of_path W' hC hJ hI (hC.all_parities hr ho hJ hI false)
  obtain ⟨R',hR'⟩ := ProofWrapper.Formed.of_path W' hC hK hJ (hC.all_parities hr ho hK hJ false)
  let qs (A : Set S) (hA : DirectLayer P C A) : QuantifierRoute W' C J A :=
    (QuantifierRoute.exists_route hC hr ho hJ hA).some
  exact ⟨Δ,δ,hΔ,⟨⟨W',hτ,J,I,K,ht,hI,hJ,hK,R,hR,R',hR',qs⟩⟩⟩

variable (L : LogicSetup P Γ γ C) {A B : Expr S}

def imp (A B : Expr S) : Expr S :=
  L.outCode.apply (Expr.arrow .pp (L.inCode.apply A) B)

theorem imp_rename (e : Embedding P Γ γ Δ δ) (A B : Expr S) :
    (L.imp A B).rename e.names = (L.rename e).imp (A.rename e.names) (B.rename e.names) := by
  simp only [imp,ProofWrapper.apply_rename,Expr.arrow_rename,rename]

theorem bottom_rename (e : Embedding P Γ γ Δ δ) :
    L.bottom.rename e.names = (L.rename e).bottom := rfl

theorem Formula.sorted {A : Expr S} (h : L.Formula A) :
    ∃ s, HasType P Γ A (.sort s) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact ⟨s,h.1 s hs⟩

theorem raw_imp (hA : L.Formula A) (hB : L.Formula B) :
    SortedAt P Γ (Expr.arrow .pp (L.inCode.apply A) B) L.product ∧
    WellModed γ (Expr.arrow .pp (L.inCode.apply A) B) .data ∧
    StableExtraction L.witnesses C (Expr.arrow .pp (L.inCode.apply A) B) := by
  obtain ⟨ha,ma,pa⟩ := L.inFormed.sound L.converters hA.1 hA.2.1
  have hs : SortedAt P Γ (Expr.arrow .pp (L.inCode.apply A) B) L.product :=
    ha.arrow hB.1 .pp (by rw [L.triple.output])
  obtain ⟨r,hr⟩ := L.triple.product.1
  obtain ⟨s,hss,t,htt,hst⟩ := L.triple.output ▸ hr
  exact ⟨hs,ma.arrow hB.2.1,StableExtraction.arrow (ha s hss) ma (hs r hr) rfl hB.2.2⟩

theorem imp_formula (hA : L.Formula A) (hB : L.Formula B) : L.Formula (L.imp A B) := by
  obtain ⟨hs,hm,hx⟩ := L.raw_imp hA hB
  obtain ⟨hs',hm',hp⟩ := L.outFormed.sound L.converters hs hm
  exact ⟨hs',hm',(L.outFormed.stable L.converters hs hm).1 hx⟩

theorem imp_intro (hA : L.Formula A) (hB : L.Formula B)
    (ht : Transfer P Γ γ A B) : Proves P Γ γ (L.imp A B) := by
  obtain ⟨ha,ma,pa⟩ := L.inFormed.sound L.converters hA.1 hA.2.1
  obtain ⟨hs,hm,hx⟩ := L.raw_imp hA hB
  obtain ⟨hs',hm',po⟩ := L.outFormed.sound L.converters hs hm
  obtain ⟨r,hr⟩ := L.triple.product.1
  obtain ⟨s,hss,t,htt,hst⟩ := L.triple.output ▸ hr
  have hd := pa.down hA.2.2 (ha s hss)
  have hc := hd.trans ht (ha s hss) (hA.1 t htt)
  exact (po.into (hs r hr)).prove (hc.abstract ma (hs r hr))

theorem imp_elim (hA : L.Formula A) (hB : L.Formula B)
    (hf : Proves P Γ γ (L.imp A B)) (hp : Proves P Γ γ A) : Proves P Γ γ B := by
  obtain ⟨ha,ma,pa⟩ := L.inFormed.sound L.converters hA.1 hA.2.1
  obtain ⟨hs,hm,hx⟩ := L.raw_imp hA hB
  obtain ⟨hs',hm',po⟩ := L.outFormed.sound L.converters hs hm
  obtain ⟨r,hr⟩ := L.triple.product.1
  obtain ⟨s,hss,t,htt,hst⟩ := L.triple.output ▸ hr
  obtain ⟨q,hq⟩ := L.triple.codomain.1
  exact ((po.down hx (hs' q hq)).prove hf).apply_arrow ((pa.into (hA.1 t htt)).prove hp)

/-- Logical abstraction is uniform in every future typing/mode embedding. This
is stronger than a meta-level map on the inhabitants in one context. -/
theorem imp_intro_future (hA : L.Formula A) (hB : L.Formula B)
    (h : ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names)) :
    Proves P Γ γ (L.imp A B) := by
  obtain ⟨s,hs⟩ := hA.sorted L
  exact L.imp_intro hA hB (h _ _ (Embedding.cons hs .proof) (Proves.of_var hs))

 theorem imp_future_iff (hA : L.Formula A) (hB : L.Formula B) :
    Proves P Γ γ (L.imp A B) ↔
    ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names) := by
  constructor
  · intro hp Δ δ e ha
    exact (L.rename e).imp_elim (hA.rename e) (hB.rename e)
      (by simpa only [L.imp_rename] using hp.rename e) ha
  · exact L.imp_intro_future hA hB

/-- Stable extraction plus the actual finite converters gives ex falso. -/
theorem explosion (hA : L.Formula A) (hf : Proves P Γ γ L.bottom) : Proves P Γ γ A := by
  have hv := (hA.sorted L).choose_spec.valid
  have hs := hA.2.2 Γ γ (Embedding.refl hv γ)
  simp only [Embedding.refl,Expr.rename_id] at hs
  apply hs
  intro Δ δ e J hJ ht
  obtain ⟨s,hss⟩ := L.triple.codomain.1
  have hc := (L.converters L.base J L.terminal_base hJ).rename e (hA := L.witnesses.sorted L.base L.triple.codomain s hss)
  have hp := hc.prove (hf.rename e)
  simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using hp

/-- Double negation elimination uses callbacks at each terminal, and therefore
constructs labelled terms for every stable formula, including dependent ones. -/
theorem dne (hA : L.Formula A)
    (hw : Proves P Γ γ (L.imp (L.imp A L.bottom) L.bottom)) : Proves P Γ γ A := by
  have hv := (hA.sorted L).choose_spec.valid
  have hb := L.bottom_formula
  have hn := L.imp_formula hA hb
  have hs := hA.2.2 Γ γ (Embedding.refl hv γ)
  simp only [Embedding.refl,Expr.rename_id] at hs
  apply hs
  intro Δ δ e J hJ ht
  obtain ⟨s,hss⟩ := L.triple.codomain.1
  obtain ⟨t,htt⟩ := hJ.feasible.1
  have hA' := hA.rename e
  have hb' := hb.rename e
  have ht' : Transfer P Δ δ (A.rename e.names) ((L.witnesses.type J).rename e.names) := by
    simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using ht
  have hjb := (L.converters J L.base hJ L.terminal_base).rename e
    (L.witnesses.sorted J hJ.feasible t htt)
  have hbj := (L.converters L.base J L.terminal_base hJ).rename e
    (L.witnesses.sorted L.base L.triple.codomain s hss)
  obtain ⟨a,ha⟩ := hA'.sorted (L.rename e)
  have negp := (L.rename e).imp_intro hA' hb' (ht'.trans hjb ha
    (e.typing (L.witnesses.sorted J hJ.feasible t htt)))
  have hw' : Proves P Δ δ ((L.rename e).imp ((L.rename e).imp (A.rename e.names) (L.rename e).bottom) (L.rename e).bottom) := by
    simpa only [L.imp_rename,L.bottom_rename] using hw.rename e
  have hbot := (L.rename e).imp_elim ((L.rename e).imp_formula hA' hb') hb' hw' negp
  simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using hbj.prove hbot

end

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I : Set S} {T Q : Expr S} {s : S}

/-- The route is selected by its original direct annotation, not by a later
sorting profile of the domain. -/
def all (R : QuantifierRoute L.witnesses C L.base I) (T Q : Expr S) : Expr S :=
  R.outCode.apply (.pi .dp T ((R.inCode.rename Nat.succ).apply Q))

theorem all_rename (R : QuantifierRoute L.witnesses C L.base I)
    (e : Embedding P Γ γ Δ δ) (T Q : Expr S) :
    (all R T Q).rename e.names = all (L := L.rename e) (R.rename e) (T.rename e.names) (Q.rename (Expr.liftRen e.names)) := by
  simp only [all,ProofWrapper.apply_rename,Expr.rename,QuantifierRoute.rename,ProofWrapper.rename_comp]
  rfl

 theorem raw_all (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q) :
    SortedAt P Γ (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) R.product ∧
    WellModed γ (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) .data ∧
    StableExtraction L.witnesses C (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) := by
  let e : Embedding P Γ γ (T :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hr := R.inFormed.rename e
  obtain ⟨hq,mq,pq⟩ := hr.sound (L.rename e).converters hQ.1 hQ.2.1
  have hsrt : SortedAt P Γ (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) R.product := by
    intro r hr
    obtain ⟨a,ha,b,hb,hab⟩ := R.triple.output ▸ hr
    exact .product (hT a ha) (hq b hb) hab
  obtain ⟨r,hr⟩ := R.triple.product.1
  exact ⟨hsrt,.pi mT mq,StableExtraction.product hs mT (hsrt r hr) rfl
    ((R.inFormed.rename e).stable (L.rename e).converters hQ.1 hQ.2.1 |>.1 hQ.2.2)⟩

 theorem all_formula (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q) : L.Formula (all R T Q) := by
  obtain ⟨ht,mt,st⟩ := raw_all R hT mT hs hQ
  obtain ⟨ha,ma,pa⟩ := R.outFormed.sound L.converters ht mt
  exact ⟨ha,ma,(R.outFormed.stable L.converters ht mt).1 st⟩

 theorem all_intro (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q)
    (hp : Proves P (T :: Γ) (modeCons .data γ) Q) : Proves P Γ γ (all R T Q) := by
  let e : Embedding P Γ γ (T :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  obtain ⟨ht,mt,st⟩ := raw_all R hT mT hs hQ
  obtain ⟨ha,ma,pa⟩ := R.outFormed.sound L.converters ht mt
  obtain ⟨hb,mb,pb⟩ := (R.inFormed.rename e).sound (L.rename e).converters hQ.1 hQ.2.1
  obtain ⟨a,ha'⟩ := hQ.sorted (L.rename e)
  obtain ⟨q,hq,mq⟩ := (pb.into ha').prove hp
  obtain ⟨r,hr⟩ := R.triple.product.1
  exact (pa.into (ht r hr)).prove ⟨_,.abstraction hq (ht r hr),.lam mT mq⟩

 theorem all_elim (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q)
    {a : Expr S} (ha : HasType P Γ a T) (ma : WellModed γ a .data)
    (hQa : L.Formula (Q.instantiate a))
    (hp : Proves P Γ γ (all R T Q)) : Proves P Γ γ (Q.instantiate a) := by
  obtain ⟨ht,mt,st⟩ := raw_all R hT mT hs hQ
  obtain ⟨ho,mo,po⟩ := R.outFormed.sound L.converters ht mt
  obtain ⟨r,hr⟩ := L.triple.codomain.1
  obtain ⟨f,hf,mf⟩ := (po.down st (ho r hr)).prove hp
  have heq : ((R.inCode.rename Nat.succ).apply Q).instantiate a = R.inCode.apply (Q.instantiate a) := by
    simp only [Expr.instantiate,ProofWrapper.apply_subst,ProofWrapper.instantiate_raise]
  have hap : Proves P Γ γ (R.inCode.apply (Q.instantiate a)) :=
    ⟨_,by simpa only [heq] using HasType.application hf ha,WellModed.app mf ma⟩
  obtain ⟨hq,mq,pq⟩ := R.inFormed.sound L.converters hQa.1 hQa.2.1
  obtain ⟨t,htt⟩ := R.triple.codomain.1
  exact (pq.down hQa.2.2 (hq t htt)).prove hap

end LogicSetup
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace Transfer
variable {Γ : List (Expr S)} {γ : Nat → Mode} {A B : Expr S} {s t : S}
theorem of_conversion (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hc : Converts A B) : Transfer P Γ γ A B :=
  ⟨_,.conversion (.var hA) (.weaken hB hA) (hc.rename Nat.succ),.var 0⟩
end Transfer

/-- Logical equivalence retains two actual typed open proof transformers.
No data term is ever replaced using this relation. -/
def Equivalent (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode) (A B : Expr S) : Prop :=
  Transfer P Γ γ A B ∧ Transfer P Γ γ B A
namespace Equivalent
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {A B D : Expr S} {s t r : S}
theorem refl (hA : HasType P Γ A (.sort s)) : Equivalent P Γ γ A A :=
  ⟨.refl hA,.refl hA⟩
theorem symm (h : Equivalent P Γ γ A B) : Equivalent P Γ γ B A := ⟨h.2,h.1⟩
theorem trans (h : Equivalent P Γ γ A B) (k : Equivalent P Γ γ B D)
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t)) (hD : HasType P Γ D (.sort r)) :
    Equivalent P Γ γ A D := ⟨h.1.trans k.1 hA hB,k.2.trans h.2 hD hB⟩
theorem rename (h : Equivalent P Γ γ A B) (e : Embedding P Γ γ Δ δ)
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t)) :
    Equivalent P Δ δ (A.rename e.names) (B.rename e.names) := ⟨h.1.rename e hA,h.2.rename e hB⟩
theorem of_conversion (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hc : Converts A B) : Equivalent P Γ γ A B :=
  ⟨.of_conversion hA hB hc,.of_conversion hB hA (.symm _ _ hc)⟩
end Equivalent

namespace ProofWrapper
variable {T T' : Expr S}
theorem apply_converts (R : ProofWrapper S) (h : Converts T T') : Converts (R.apply T) (R.apply T') := by
  induction R with
  | identity => exact h
  | positive R D ih => exact .pi (.refl _) (ih.rename Nat.succ)
  | negative R F ih => exact .pi ih (.refl _)

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {I J K : Set S} {a : Bool} {R : ProofWrapper S}
 theorem odd_negative (h : Formed W C I J a R) (ha : a = true) : R.containsNegative = true := by
  induction h with
  | identity => cases ha
  | inclusion h hh ih => exact ih ha
  | positive h ht ih => exact ih ha
  | negative h ht hi hk ih => rfl

 theorem edge_negative (h : Formed W C I J a R) (hn : R.containsNegative = true)
    {b : Bool} (he : PrimaryEdge P J K b) (hJ : J ∈ C) (hK : K ∈ C) :
    ∃ R', Formed W C I K (Bool.xor a b) R' ∧ R'.containsNegative = true := by
  cases he with
  | inclusion hJ' hK' hsub => exact ⟨R,by simpa only [Bool.xor_false] using h.inclusion hsub.1,hn⟩
  | domain ht => exact ⟨_,by simpa only [Bool.xor_true] using h.negative ht hJ hK,rfl⟩
  | codomain ht => exact ⟨_,by simpa only [Bool.xor_false] using h.positive ht,by simpa only [containsNegative] using hn⟩

 theorem path_negative (h : Formed W C I J a R) (hn : R.containsNegative = true)
    {b : Bool} (hp : SignedPath (fun x y s => PrimaryEdge P x y s ∧ x ∈ C ∧ y ∈ C) J K b) :
    ∃ R', Formed W C I K (Bool.xor a b) R' ∧ R'.containsNegative = true := by
  induction hp generalizing a R with
  | nil _ => exact ⟨R,by simpa only [Bool.xor_false] using h,hn⟩
  | @cons J K L b c he hp ih =>
    obtain ⟨R',hr,hn'⟩ := h.edge_negative hn he.1 he.2.1 he.2.2
    obtain ⟨R'',hr',hn''⟩ := ih hr hn'
    exact ⟨R'',by simpa only [Bool.xor_assoc] using hr',hn''⟩

 theorem exists_even_negative (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true) (hI : I ∈ C) (hJ : J ∈ C) :
    ∃ R, Formed W C I J false R ∧ R.containsNegative = true := by
  obtain ⟨R,hR⟩ := Formed.of_path W hC hI hJ (hC.all_parities hr ho hI hJ true)
  obtain ⟨R',hR',hn⟩ := hR.path_negative (hR.odd_negative rfl)
    (hC.restrict_path hJ hJ (hC.all_parities hr ho hJ hJ true))
  exact ⟨R',hR',hn⟩
end Formed
end ProofWrapper

/-- A fixed all-positive data path, with its original dummy argument values. -/
inductive PositiveDataWrapper (S : Type u)
  | identity
  | step : PositiveDataWrapper S → Expr S → Expr S → PositiveDataWrapper S
namespace PositiveDataWrapper

def apply : PositiveDataWrapper S → Expr S → Expr S
  | .identity,T => T
  | .step R D _,T => Expr.arrow .dd D (R.apply T)

def inject : PositiveDataWrapper S → Expr S → Expr S
  | .identity,t => t
  | .step R D _,t => Expr.constLam .dd D (R.inject t)

def project : PositiveDataWrapper S → Expr S → Expr S
  | .identity,w => w
  | .step R _ e,w => R.project (.app .dd w e)

def rename (ρ : Nat → Nat) : PositiveDataWrapper S → PositiveDataWrapper S
  | .identity => .identity
  | .step R D e => .step (R.rename ρ) (D.rename ρ) (e.rename ρ)

def subst (σ : Nat → Expr S) : PositiveDataWrapper S → PositiveDataWrapper S
  | .identity => .identity
  | .step R D e => .step (R.subst σ) (D.subst σ) (e.subst σ)

theorem apply_rename (R : PositiveDataWrapper S) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename]
theorem inject_rename (R : PositiveDataWrapper S) (t : Expr S) (ρ : Nat → Nat) :
    (R.inject t).rename ρ = (R.rename ρ).inject (t.rename ρ) := by
  induction R <;> simp_all only [inject,rename,Expr.constLam_rename]
theorem project_rename (R : PositiveDataWrapper S) (w : Expr S) (ρ : Nat → Nat) :
    (R.project w).rename ρ = (R.rename ρ).project (w.rename ρ) := by
  induction R generalizing w <;> simp_all only [project,rename,Expr.rename]
theorem apply_subst (R : PositiveDataWrapper S) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst]
theorem inject_subst (R : PositiveDataWrapper S) (t : Expr S) (σ : Nat → Expr S) :
    (R.inject t).subst σ = (R.subst σ).inject (t.subst σ) := by
  induction R <;> simp_all only [inject,subst,Expr.constLam_subst]
theorem project_subst (R : PositiveDataWrapper S) (w : Expr S) (σ : Nat → Expr S) :
    (R.project w).subst σ = (R.subst σ).project (w.subst σ) := by
  induction R generalizing w <;> simp_all only [project,subst,Expr.subst]
theorem rename_comp (R : PositiveDataWrapper S) (ρ τ : Nat → Nat) :
    (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp]
theorem rename_id (R : PositiveDataWrapper S) : R.rename id = R := by
  induction R <;> simp_all only [rename,Expr.rename_id]
theorem instantiate_raise (R : PositiveDataWrapper S) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single]

theorem project_reduces (R : PositiveDataWrapper S) {w w' : Expr S}
    (h : Reduces w w') : Reduces (R.project w) (R.project w') := by
  induction R generalizing w w' with
  | identity => exact h
  | step R D e ih => exact ih (h.app .refl)

theorem cancel (R : PositiveDataWrapper S) (t : Expr S) : Reduces (R.project (R.inject t)) t := by
  induction R with
  | identity => exact .refl
  | step R D e ih =>
    exact (R.project_reduces (.single (positive_cancel .dd D e (R.inject t)))).trans ih

inductive Formed {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (I : Set S) : Set S → PositiveDataWrapper S → Prop
  | identity : Formed W I I .identity
  | inclusion {J K R} : Formed W I J R → K ⊆ J → Formed W I K R
  | positive {A J K R} : Formed W I J R → ProfileTriple P A J K →
      Formed W I K (.step R (W.type A) (W.value A))
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {I J K : Set S} {R : PositiveDataWrapper S}
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (h : Formed W I J R) (e : Embedding P Γ γ Δ δ) : Formed (W.rename e) I J (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht

theorem path (h : Formed W I J R) (hp : PositivePath (PrimaryEdge P) J K) :
    ∃ R', Formed W I K R' := by
  induction hp with
  | refl => exact ⟨R,h⟩
  | tail hp he ih =>
    obtain ⟨R',hr⟩ := ih
    cases he with
    | inclusion hJ hK hsub => exact ⟨_,hr.inclusion hsub.1⟩
    | codomain ht => exact ⟨_,hr.positive ht⟩

theorem sorted (h : Formed W I J R) {T : Expr S} (ht : SortedAt P Γ T I) :
    SortedAt P Γ (R.apply T) J := by
  induction h with
  | identity => exact ht
  | inclusion h hh ih => exact ih.mono hh
  | positive h ht ih => exact (W.sorted _ ht.domain).arrow ih .dd (by rw [ht.output])

theorem modes (h : Formed W I J R) :
    (∀ T, WellModed γ T .data → WellModed γ (R.apply T) .data) ∧
    (∀ t, WellModed γ t .data → WellModed γ (R.inject t) .data) ∧
    (∀ w, WellModed γ w .data → WellModed γ (R.project w) .data) := by
  induction h with
  | identity => exact ⟨fun _ h => h,fun _ h => h,fun _ h => h⟩
  | inclusion h hh ih => exact ih
  | @positive A J K R h ht ih =>
    exact ⟨fun T hT => (W.type_mode A ht.domain).arrow (ih.1 T hT),
      fun t ht' => (W.type_mode A ht.domain).constLam (ih.2.1 t ht'),
      fun w hw => ih.2.2 _ (.app hw (W.value_mode A ht.domain))⟩

theorem typed (h : Formed W I J R) {T : Expr S} (ht : SortedAt P Γ T I) :
    (∀ t, HasType P Γ t T → HasType P Γ (R.inject t) (R.apply T)) ∧
    (∀ w, HasType P Γ w (R.apply T) → HasType P Γ (R.project w) T) := by
  induction h with
  | identity => exact ⟨fun _ h => h,fun _ h => h⟩
  | inclusion h hh ih => exact ih
  | @positive A J K R h htr ih =>
    have hR := h.sorted ht
    have hpi : SortedAt P Γ (Expr.arrow .dd (W.type A) (R.apply T)) K :=
      (W.sorted A htr.domain).arrow hR .dd (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,htt,hst⟩ := htr.output ▸ hr
    exact ⟨fun a ha => (ih.1 a ha).constLam (W.sorted A htr.domain s hs) (hpi r hr),
      fun w hw => ih.2 _ (hw.apply_arrow (W.typed A htr.domain))⟩
end Formed
end PositiveDataWrapper

structure DataTail (S : Type u) where
  sort : S
  positive : PositiveDataWrapper S
  encode : ProofWrapper S
  decode : ProofWrapper S

namespace DataTail

def carrier (U : DataTail S) : Expr S := U.positive.apply (.sort U.sort)
def send (U : DataTail S) (Q : Expr S) : Expr S := U.positive.inject (U.encode.apply Q)
def read (U : DataTail S) (w : Expr S) : Expr S := U.decode.apply (U.positive.project w)
def rename (U : DataTail S) (ρ : Nat → Nat) : DataTail S :=
  ⟨U.sort,U.positive.rename ρ,U.encode.rename ρ,U.decode.rename ρ⟩
def subst (U : DataTail S) (σ : Nat → Expr S) : DataTail S :=
  ⟨U.sort,U.positive.subst σ,U.encode.subst σ,U.decode.subst σ⟩

theorem carrier_rename (U : DataTail S) (ρ : Nat → Nat) :
    U.carrier.rename ρ = (U.rename ρ).carrier := U.positive.apply_rename _ _
theorem send_rename (U : DataTail S) (Q : Expr S) (ρ : Nat → Nat) :
    (U.send Q).rename ρ = (U.rename ρ).send (Q.rename ρ) := by
  simp only [send,rename,PositiveDataWrapper.inject_rename,ProofWrapper.apply_rename]
theorem read_rename (U : DataTail S) (w : Expr S) (ρ : Nat → Nat) :
    (U.read w).rename ρ = (U.rename ρ).read (w.rename ρ) := by
  simp only [read,rename,PositiveDataWrapper.project_rename,ProofWrapper.apply_rename]
theorem carrier_subst (U : DataTail S) (σ : Nat → Expr S) :
    U.carrier.subst σ = (U.subst σ).carrier := U.positive.apply_subst _ _
theorem send_subst (U : DataTail S) (Q : Expr S) (σ : Nat → Expr S) :
    (U.send Q).subst σ = (U.subst σ).send (Q.subst σ) := by
  simp only [send,subst,PositiveDataWrapper.inject_subst,ProofWrapper.apply_subst]
theorem read_subst (U : DataTail S) (w : Expr S) (σ : Nat → Expr S) :
    (U.read w).subst σ = (U.subst σ).read (w.subst σ) := by
  simp only [read,subst,PositiveDataWrapper.project_subst,ProofWrapper.apply_subst]
theorem rename_comp (U : DataTail S) (ρ τ : Nat → Nat) :
    (U.rename τ).rename ρ = U.rename (ρ ∘ τ) := by
  cases U; simp only [rename,PositiveDataWrapper.rename_comp,ProofWrapper.rename_comp]
theorem rename_id (U : DataTail S) : U.rename id = U := by
  cases U; simp only [rename,PositiveDataWrapper.rename_id,ProofWrapper.rename_id]
theorem instantiate_raise (U : DataTail S) (a : Expr S) :
    (U.rename Nat.succ).subst (Expr.single a) = U := by
  cases U; simp only [rename,subst,PositiveDataWrapper.instantiate_raise,ProofWrapper.instantiate_raise]

structure Formed {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (J : Set S) (U : DataTail S) : Prop where
  mem : {U.sort} ∈ C
  nonempty : (AxProfile P U.sort).Nonempty
  positive : U.positive.Formed L.witnesses (AxProfile P U.sort) J
  encode : U.encode.Formed L.witnesses C L.base {U.sort} false
  decode : U.decode.Formed L.witnesses C {U.sort} L.base false
  negative : U.decode.containsNegative = true

namespace Formed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {J : Set S} {U : DataTail S}

theorem rename (h : Formed L J U) (e : Embedding P Γ γ Δ δ) :
    Formed (L.rename e) J (U.rename e.names) := by
  refine ⟨h.mem,h.nonempty,h.positive.rename e,h.encode.rename e,h.decode.rename e,?_⟩
  have hn (R : ProofWrapper S) : (R.rename e.names).containsNegative = R.containsNegative := by
    induction R <;> simp_all only [ProofWrapper.rename,ProofWrapper.containsNegative]
  exact (hn U.decode).trans h.negative

theorem sort_sorted (_h : Formed L J U) : SortedAt P Γ (.sort U.sort) (AxProfile P U.sort) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  intro t ht
  exact HasType.sort_of_valid (L.bottom_formula.1 s hs).valid ht

theorem carrier_sorted (h : Formed L J U) : SortedAt P Γ U.carrier J := h.positive.sorted h.sort_sorted

theorem carrier_mode (h : Formed L J U) : WellModed γ U.carrier .data :=
  h.positive.modes.1 _ (.sort _)

theorem send_typed (h : Formed L J U) {Q : Expr S} (hQ : L.Formula Q) :
    HasType P Γ (U.send Q) U.carrier ∧ WellModed γ (U.send Q) .data := by
  obtain ⟨hE,mE,_⟩ := h.encode.sound L.converters hQ.1 hQ.2.1
  exact ⟨h.positive.typed h.sort_sorted |>.1 _ (hE U.sort rfl),h.positive.modes.2.1 _ mE⟩

theorem read_formula (h : Formed L J U) {w : Expr S}
    (hw : HasType P Γ w U.carrier) (mw : WellModed γ w .data) : L.Formula (U.read w) := by
  have ht := h.positive.typed h.sort_sorted |>.2 _ hw
  have mt := h.positive.modes.2.2 _ mw
  have hs : SortedAt P Γ (U.positive.project w) {U.sort} := by intro s hs; cases hs; exact ht
  obtain ⟨hd,md,_⟩ := h.decode.sound L.converters hs mt
  exact ⟨hd,md,(h.decode.stable L.converters hs mt).2 h.negative⟩

theorem read_send (h : Formed L J U) {Q : Expr S} (hQ : L.Formula Q) :
    Equivalent P Γ γ (U.read (U.send Q)) Q := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  obtain ⟨hE,mE,pE⟩ := h.encode.sound L.converters hQ.1 hQ.2.1
  have stE := (h.encode.stable L.converters hQ.1 hQ.2.1).1 hQ.2.2
  obtain ⟨hD,mD,pD⟩ := h.decode.sound L.converters hE mE
  have he : Equivalent P Γ γ (U.encode.apply Q) Q :=
    ⟨pE.down hQ.2.2 (hE U.sort rfl),pE.into (hQ.1 s hs)⟩
  have hd : Equivalent P Γ γ (U.decode.apply (U.encode.apply Q)) (U.encode.apply Q) :=
    ⟨pD.down stE (hD s hs),pD.into (hE U.sort rfl)⟩
  have hm := h.send_typed hQ
  have hf := h.read_formula hm.1 hm.2
  have hc : Converts (U.read (U.send Q)) (U.decode.apply (U.encode.apply Q)) :=
    U.decode.apply_converts (U.positive.cancel (U.encode.apply Q)).converts
  exact (Equivalent.of_conversion (hf.1 s hs) (hD s hs) hc).trans
    (hd.trans he (hD s hs) (hE U.sort rfl) (hQ.1 s hs)) (hf.1 s hs) (hD s hs) (hQ.1 s hs)

theorem exists_tail (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    (hJ : J ∈ ObservationLayers P C) : ∃ U, Formed L J U := by
  obtain ⟨u,hu,hne,hpath⟩ := hJ
  obtain ⟨R,hR⟩ := (PositiveDataWrapper.Formed.identity (W := L.witnesses) (I := AxProfile P u)).path hpath
  obtain ⟨E,hE⟩ := ProofWrapper.Formed.of_path L.witnesses hC L.base_mem hu
    (hC.all_parities hr ho L.base_mem hu false)
  obtain ⟨D,hD,hn⟩ := ProofWrapper.Formed.exists_even_negative (W := L.witnesses) hC hr ho hu L.base_mem
  exact ⟨⟨u,R,E,D⟩,⟨hu,hne,hR,hE,hD,hn⟩⟩
end Formed
end DataTail
end

section
universe u
variable {S : Type u}

/-- A retained data path, with fixed tail codes and fixed positive witnesses. -/
inductive DataWrapper (S : Type u) : Bool → Type u
  | identity : DataWrapper S false
  | positive {b} : DataWrapper S b → Expr S → Expr S → DataWrapper S b
  | negative {b} : DataWrapper S b → DataTail S → DataWrapper S (!b)
namespace DataWrapper

def apply {b} : DataWrapper S b → Expr S → Expr S
  | .identity,T => T
  | .positive R D _,T => Expr.arrow .dd D (R.apply T)
  | .negative R U,T => Expr.arrow .dd (R.apply T) U.carrier

def rename {b} (ρ : Nat → Nat) : DataWrapper S b → DataWrapper S b
  | .identity => .identity
  | .positive R D e => .positive (R.rename ρ) (D.rename ρ) (e.rename ρ)
  | .negative R U => .negative (R.rename ρ) (U.rename ρ)

def subst {b} (σ : Nat → Expr S) : DataWrapper S b → DataWrapper S b
  | .identity => .identity
  | .positive R D e => .positive (R.subst σ) (D.subst σ) (e.subst σ)
  | .negative R U => .negative (R.subst σ) (U.subst σ)

def depth {b} : DataWrapper S b → Nat
  | .identity => 0
  | .positive R _ _ => R.depth + 1
  | .negative R _ => R.depth + 1

theorem depth_rename {b} (R : DataWrapper S b) (ρ : Nat → Nat) :
    (R.rename ρ).depth = R.depth := by
  induction R <;> simp_all only [rename,depth]

def argRen (b : Bool) (ρ : Nat → Nat) : Nat → Nat := if b then Expr.liftRen ρ else ρ
def argSub (b : Bool) (σ : Nat → Expr S) : Nat → Expr S := if b then Expr.liftSub σ else σ

mutual
  def build {b} : DataWrapper S b → Expr S → Expr S → Expr S
    | .identity,_,a => a
    | .positive R D _,T,a => Expr.constLam .dd D (R.build T a)
    | @negative _ b R U,T,a =>
        .lam .dd (R.apply T) ((U.rename Nat.succ).send
          ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
            (a.rename (argRen (!b) Nat.succ))))
  termination_by R _ _ => R.depth
  decreasing_by all_goals simp [depth_rename,depth]
  def observe {b} : DataWrapper S b → Expr S → Expr S → Expr S → Expr S
    | .identity,_,w,a => a.instantiate w
    | .positive R _ e,T,w,a => R.observe T (.app .dd w e) a
    | .negative R U,T,w,a => U.read (.app .dd w (R.build T a))
  termination_by R _ _ _ => R.depth
  decreasing_by all_goals simp [depth]
end

theorem apply_rename {b} (R : DataWrapper S b) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename,DataTail.carrier_rename]
theorem apply_subst {b} (R : DataWrapper S b) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst,DataTail.carrier_subst]
theorem rename_comp {b} (R : DataWrapper S b) (ρ τ : Nat → Nat) :
    (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp,DataTail.rename_comp]
theorem rename_id {b} (R : DataWrapper S b) : R.rename id = R := by
  induction R <;> simp_all only [rename,Expr.rename_id,DataTail.rename_id]
theorem instantiate_raise {b} (R : DataWrapper S b) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single,DataTail.instantiate_raise]

theorem argRen_comp (b : Bool) (ρ τ : Nat → Nat) :
    argRen b ρ ∘ argRen b τ = argRen b (ρ ∘ τ) := by
  cases b <;> funext n <;> cases n <;> rfl

theorem rename_build_observe {b} (R : DataWrapper S b) :
    (∀ T a ρ, (R.build T a).rename ρ = (R.rename ρ).build (T.rename ρ) (a.rename (argRen b ρ))) ∧
    (∀ T w a ρ, (R.observe T w a).rename ρ =
      (R.rename ρ).observe (T.rename ρ) (w.rename ρ) (a.rename (argRen (!b) ρ))) := by
  generalize he : R.depth = n
  induction n using Nat.strong_induction_on generalizing b R with
  | h n rec =>
   cases R with
   | identity =>
     constructor
     · intro T a ρ; simp only [build,rename,argRen,Bool.false_eq_true,ite_false]
     · intro T w a ρ
       simpa only [observe,rename,argRen,Bool.not_false,ite_true] using (Expr.instantiate_rename a w ρ).symm
   | positive R D e =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     exact ⟨fun T a ρ => by simp only [build,rename,Expr.constLam_rename,ih.1],
       fun T w a ρ => by simpa only [observe,rename,Expr.rename] using ih.2 T (.app .dd w e) a ρ⟩
   | @negative b R U =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     constructor
     · intro T a ρ
       simp only [build,Expr.rename,DataTail.send_rename,rename]
       rw [show (((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0) (a.rename (argRen (!b) Nat.succ))).rename (Expr.liftRen ρ)) =
         ((R.rename Nat.succ).rename (Expr.liftRen ρ)).observe ((T.rename Nat.succ).rename (Expr.liftRen ρ))
           ((Expr.var 0).rename (Expr.liftRen ρ)) ((a.rename (argRen (!b) Nat.succ)).rename (argRen (!b) (Expr.liftRen ρ))) from
         (rec R.depth (by simp only [← he,depth]; omega) (R.rename Nat.succ) (R.depth_rename Nat.succ)).2 _ _ _ _]
       simp only [apply_rename,rename_comp,DataTail.rename_comp,Expr.rename_comp,argRen_comp]
       have e : Expr.liftRen ρ ∘ Nat.succ = Nat.succ ∘ ρ := rfl
       rw [e]
       rfl
     · intro T w a ρ
       simp only [observe,rename,DataTail.read_rename,Expr.rename,ih.1,Bool.not_not]
end DataWrapper
end

universe u
variable {S : Type u} {P : Specification S}

namespace WitnessFamily
variable {Γ Δ Θ : List (Expr S)} {γ δ θ : Nat → Mode}
theorem rename_comp (W : WitnessFamily P Γ γ) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) : (W.rename e).rename f = W.rename (e.comp f) := by
  cases W
  simp only [rename,Embedding.comp,Expr.rename_comp]
theorem rename_refl (W : WitnessFamily P Γ γ) (hv : ValidContext P Γ) :
    W.rename (Embedding.refl hv γ) = W := by
  cases W
  simp only [rename,Embedding.refl,Expr.rename_id]
end WitnessFamily

namespace LogicSetup
variable {Γ Δ Θ : List (Expr S)} {γ δ θ : Nat → Mode} {C : Set (Set S)}
theorem Formula.rename_comp_iff (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) (Q : Expr S) :
    ((L.rename e).rename f).Formula Q ↔ (L.rename (e.comp f)).Formula Q := by
  change (SortedAt P Θ Q L.base ∧ WellModed θ Q .data ∧ StableExtraction ((L.witnesses.rename e).rename f) C Q) ↔
    (SortedAt P Θ Q L.base ∧ WellModed θ Q .data ∧ StableExtraction (L.witnesses.rename (e.comp f)) C Q)
  rw [WitnessFamily.rename_comp]

theorem Formula.rename_refl_iff (L : LogicSetup P Γ γ C) (hv : ValidContext P Γ) (Q : Expr S) :
    (L.rename (Embedding.refl hv γ)).Formula Q ↔ L.Formula Q := by
  change (SortedAt P Γ Q L.base ∧ WellModed γ Q .data ∧ StableExtraction (L.witnesses.rename (Embedding.refl hv γ)) C Q) ↔
    (SortedAt P Γ Q L.base ∧ WellModed γ Q .data ∧ StableExtraction L.witnesses C Q)
  rw [WitnessFamily.rename_refl]

/-- A raw callback with uniform stable instances in every subsequent context.
This is an internal syntax interface, not a hypothesis on the PTS. -/
def Family (L : LogicSetup P Γ γ C) (T Q : Expr S) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
    (a : Expr S), HasType P Δ a (T.rename e.names) → WellModed δ a .data →
    (L.rename e).Formula ((Q.rename (Expr.liftRen e.names)).instantiate a)

namespace Family
variable {L : LogicSetup P Γ γ C} {T Q : Expr S}
theorem rename (h : L.Family T Q) (e : Embedding P Γ γ Δ δ) :
    (L.rename e).Family (T.rename e.names) (Q.rename (Expr.liftRen e.names)) := by
  intro Θ θ f a ha ma
  have hh := h Θ θ (e.comp f) a (by simpa only [Embedding.comp,Expr.rename_comp] using ha) ma
  apply (Formula.rename_comp_iff L e f _).2
  convert hh using 1
  simp only [Expr.rename_comp,Embedding.comp]
  have he : Expr.liftRen f.names ∘ Expr.liftRen e.names = Expr.liftRen (f.names ∘ e.names) := by
    funext n; cases n <;> rfl
  rw [he]

theorem instantiate (h : L.Family T Q) {a : Expr S}
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) : L.Formula (Q.instantiate a) := by
  have hh := h Γ γ (Embedding.refl ha.valid γ) a (by simpa only [Embedding.refl,Expr.rename_id] using ha) ma
  have he : Expr.liftRen id = id := by funext n; cases n <;> rfl
  apply (Formula.rename_refl_iff L ha.valid _).1
  simpa only [Embedding.refl,he,Expr.rename_id] using hh

theorem opened (h : L.Family T Q) {s : S} (ht : HasType P Γ T (.sort s)) :
    (L.rename (Embedding.cons ht .data)).Formula Q := by
  have hh := h _ _ (Embedding.cons ht .data) (.var 0) (HasType.var ht) (.var 0)
  have heq : (Q.rename (Expr.liftRen Nat.succ)).instantiate (.var 0) = Q := by
    simp only [Expr.instantiate,Expr.subst_rename]
    have he : Expr.single (.var 0 : Expr S) ∘ Expr.liftRen Nat.succ = Expr.var := by
      funext n; cases n <;> rfl
    rw [he,Expr.subst_var]
  exact heq ▸ hh
end Family

theorem Family.rename_comp_iff (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) (T Q : Expr S) :
    ((L.rename e).rename f).Family T Q ↔ (L.rename (e.comp f)).Family T Q := by
  constructor <;> intro h Ω ω g a ha ma
  · have hh := h Ω ω g a ha ma
    simpa only [Formula.rename_comp_iff,Embedding.comp,Function.comp_assoc] using hh
  · have hh := h Ω ω g a ha ma
    simpa only [Formula.rename_comp_iff,Embedding.comp,Function.comp_assoc] using hh

/-- Even builders accept a raw data element; odd builders accept a raw callback. -/
def DataArg (L : LogicSetup P Γ γ C) (b : Bool) (T a : Expr S) : Prop :=
  if b then L.Family T a else HasType P Γ a T ∧ WellModed γ a .data

namespace DataArg
variable {L : LogicSetup P Γ γ C} {b : Bool} {T a : Expr S}
theorem rename (h : L.DataArg b T a) (e : Embedding P Γ γ Δ δ) :
    (L.rename e).DataArg b (T.rename e.names) (a.rename (DataWrapper.argRen b e.names)) := by
  cases b
  · exact ⟨e.typing h.1,e.moded h.2⟩
  · exact h.rename e

theorem rename_comp_iff (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) (b : Bool) (T a : Expr S) :
    ((L.rename e).rename f).DataArg b T a ↔ (L.rename (e.comp f)).DataArg b T a := by
  cases b
  · rfl
  · exact Family.rename_comp_iff L e f T a
end DataArg
end LogicSetup

namespace DataWrapper
inductive Formed {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I : Set S) : (J : Set S) → {b : Bool} → DataWrapper S b → Prop
  | identity : Formed L I I .identity
  | inclusion {J K b} {R : DataWrapper S b} : Formed L I J R → K ⊆ J → Formed L I K R
  | positive {A J K b} {R : DataWrapper S b} : Formed L I J R → ProfileTriple P A J K →
      Formed L I K (.positive R (L.witnesses.type A) (L.witnesses.value A))
  | negative {J B K b} {R : DataWrapper S b} {U : DataTail S} :
      Formed L I J R → ProfileTriple P J B K → U.Formed L B → Formed L I K (.negative R U)
namespace Formed

section
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {b : Bool} {R : DataWrapper S b}

theorem rename (h : Formed L I J R) (e : Embedding P Γ γ Δ δ) :
    Formed (L.rename e) I J (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht
  | negative h ht hU ih => exact ih.negative ht (hU.rename e)

theorem sorted (h : Formed L I J R) {T : Expr S} (ht : SortedAt P Γ T I) :
    SortedAt P Γ (R.apply T) J := by
  induction h with
  | identity => exact ht
  | inclusion h hh ih => exact ih.mono hh
  | positive h ht ih => exact (L.witnesses.sorted _ ht.domain).arrow ih .dd (by rw [ht.output])
  | negative h ht hU ih => exact ih.arrow hU.carrier_sorted .dd (by rw [ht.output])

theorem mode (h : Formed L I J R) {T : Expr S} (mt : WellModed γ T .data) :
    WellModed γ (R.apply T) .data := by
  induction h with
  | identity => exact mt
  | inclusion h hh ih => exact ih
  | positive h ht ih => exact (L.witnesses.type_mode _ ht.domain).arrow ih
  | negative h ht hU ih => exact ih.arrow hU.carrier_mode

theorem edge (h : Formed L I J R) (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    {c : Bool} (he : SecondaryEdge P C J K c) : ∃ R', Formed L I K (b := Bool.xor b c) R' := by
  cases he with
  | positive hJ hK he =>
    cases he with
    | inclusion _ _ hsub => cases b <;> exact ⟨R,h.inclusion hsub.1⟩
    | codomain ht => cases b <;> exact ⟨_,h.positive ht⟩
  | negative hJ hB hK ht =>
    obtain ⟨U,hU⟩ := DataTail.Formed.exists_tail (L := L) hC hr ho hB
    cases b <;> exact ⟨_,h.negative ht hU⟩

theorem path (h : Formed L I J R) (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    {c : Bool} (hp : SignedPath (SecondaryEdge P C) J K c) : ∃ R', Formed L I K (b := Bool.xor b c) R' := by
  induction hp generalizing b R with
  | nil _ => cases b <;> exact ⟨R,h⟩
  | @cons J K M a c he hp ih =>
    obtain ⟨R',hR'⟩ := h.edge hC hr ho he
    obtain ⟨R'',hR''⟩ := ih hR'
    rw [← Bool.xor_assoc]; exact ⟨R'',hR''⟩

theorem positive_path (h : Formed L I J R) (hp : PositivePath (PrimaryEdge P) J K) :
    ∃ R', Formed L I K (b := b) R' := by
  induction hp with
  | refl => exact ⟨R,h⟩
  | tail hp he ih =>
    obtain ⟨R',hR'⟩ := ih
    cases he with
    | inclusion _ _ hsub => exact ⟨R',hR'.inclusion hsub.1⟩
    | codomain ht => exact ⟨_,hR'.positive ht⟩
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {b : Bool} {R : DataWrapper S b}

/-- Uniform typing includes all future raw input types, so negative-edge
callbacks are checked under their fresh data variable without a closure axiom. -/
theorem sound_rename (h : Formed L I J R) :
    ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
      (T : Expr S), SortedAt P Δ T I → WellModed δ T .data →
    (∀ a, (L.rename e).DataArg b T a →
      HasType P Δ ((R.rename e.names).build T a) ((R.rename e.names).apply T) ∧
      WellModed δ ((R.rename e.names).build T a) .data) ∧
    (∀ w a, HasType P Δ w ((R.rename e.names).apply T) → WellModed δ w .data →
      (L.rename e).DataArg (!b) T a → (L.rename e).Formula ((R.rename e.names).observe T w a)) := by
  induction h with
  | identity =>
    intro Δ δ e T ht mt
    constructor
    · intro a ha; simpa only [DataWrapper.rename,DataWrapper.build,DataWrapper.apply,LogicSetup.DataArg, Bool.false_eq_true,ite_false] using ha
    · intro w a hw mw ha
      simpa only [DataWrapper.rename,DataWrapper.observe] using ha.instantiate hw mw
  | inclusion h hh ih => exact ih
  | @positive A J K b R h ht ih =>
    intro Δ δ e T hT mT
    obtain ⟨hb,ho⟩ := ih Δ δ e T hT mT
    have hR := (h.rename e).sorted hT
    have hD := (L.rename e).witnesses.sorted A ht.domain
    have hpi : SortedAt P Δ (Expr.arrow .dd ((L.rename e).witnesses.type A) ((R.rename e.names).apply T)) K :=
      hD.arrow hR .dd (by rw [ht.output])
    obtain ⟨r,hr⟩ := ht.product.1
    obtain ⟨s,hs,t,htt,hst⟩ := ht.output ▸ hr
    constructor
    · intro a ha
      obtain ⟨hba,mba⟩ := hb a ha
      simpa only [DataWrapper.rename,DataWrapper.build,DataWrapper.apply,LogicSetup.rename,WitnessFamily.rename,Label.result] using
        And.intro (hba.constLam (hD s hs) (hpi r hr))
          (((L.rename e).witnesses.type_mode A ht.domain).constLam (l := .dd) mba)
    · intro w a hw mw ha
      simpa only [DataWrapper.rename,DataWrapper.observe,LogicSetup.rename,WitnessFamily.rename] using ho (.app .dd w (((L.rename e).witnesses.value A))) a
        (hw.apply_arrow ((L.rename e).witnesses.typed A ht.domain))
        (.app mw ((L.rename e).witnesses.value_mode A ht.domain)) ha
  | @negative J B K b R U h ht hU ih =>
    intro Δ δ e T hT mT
    have hR := (h.rename e).sorted hT
    have mR := (h.rename e).mode mT
    have hUe := hU.rename e
    have hpi : SortedAt P Δ (Expr.arrow .dd ((R.rename e.names).apply T) ((U.rename e.names).carrier)) K :=
      hR.arrow hUe.carrier_sorted .dd (by rw [ht.output])
    obtain ⟨r,hr⟩ := ht.product.1
    obtain ⟨s,hs,t,htt,hst⟩ := ht.output ▸ hr
    constructor
    · intro a ha
      let d : Embedding P Δ δ ((R.rename e.names).apply T :: Δ) (modeCons .data δ) :=
        Embedding.cons (hR s hs) .data
      have hT' : SortedAt P ((R.rename e.names).apply T :: Δ) (T.rename Nat.succ) I :=
        fun u hu => d.typing (hT u hu)
      have hv : HasType P ((R.rename e.names).apply T :: Δ) (.var 0)
          ((R.rename (e.comp d).names).apply (T.rename Nat.succ)) := by
        simpa only [Embedding.comp,d,Embedding.cons,DataWrapper.apply_rename,DataWrapper.rename_comp]
          using HasType.var (hR s hs)
      have ha' : (L.rename (e.comp d)).DataArg (!b) (T.rename Nat.succ)
          (a.rename (argRen (!b) Nat.succ)) :=
        (LogicSetup.DataArg.rename_comp_iff L e d _ _ _).1 (ha.rename d)
      have hf := (ih _ _ (e.comp d) (T.rename Nat.succ) hT' (d.moded mT)).2
        (.var 0) (a.rename (argRen (!b) Nat.succ)) hv (.var 0) ha'
      have hsnd := (hU.rename (e.comp d)).send_typed hf
      have hbody : HasType P ((R.rename e.names).apply T :: Δ)
          (((U.rename e.names).rename Nat.succ).send
            (((R.rename e.names).rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
              (a.rename (argRen (!b) Nat.succ))))
          (((U.rename e.names).carrier).rename Nat.succ) := by
        simpa only [DataWrapper.rename_comp,DataTail.rename_comp,DataTail.carrier_rename,
          Embedding.comp,d,Embedding.cons] using hsnd.1
      have mbody : WellModed (modeCons .data δ)
          (((U.rename e.names).rename Nat.succ).send
            (((R.rename e.names).rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
              (a.rename (argRen (!b) Nat.succ)))) .data := by
        simpa only [DataWrapper.rename_comp,DataTail.rename_comp,Embedding.comp,d,Embedding.cons] using hsnd.2
      exact ⟨by simpa only [DataWrapper.rename,DataWrapper.build,DataWrapper.apply,Expr.arrow]
          using HasType.abstraction hbody (hpi r hr),
        by simpa only [DataWrapper.rename,DataWrapper.build,Label.result] using WellModed.lam (l := .dd) mR mbody⟩
    · intro w a hw mw ha
      have ha' : (L.rename e).DataArg b T a := by simpa only [Bool.not_not] using ha
      have hba := (ih Δ δ e T hT mT).1 a ha'
      simpa only [DataWrapper.rename,DataWrapper.observe] using hUe.read_formula (hw.apply_arrow hba.1) (.app mw hba.2)

/-- The four displayed operations of the manuscript, on the fixed unrenamed code. -/
theorem sound (h : Formed L I J R) {T : Expr S} (hT : SortedAt P Γ T I)
    (mT : WellModed γ T .data) :
    (∀ a, L.DataArg b T a → HasType P Γ (R.build T a) (R.apply T) ∧ WellModed γ (R.build T a) .data) ∧
    (∀ w a, HasType P Γ w (R.apply T) → WellModed γ w .data →
      L.DataArg (!b) T a → L.Formula (R.observe T w a)) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  let e := Embedding.refl (L.bottom_formula.1 s hs).valid γ
  have hh := h.sound_rename Γ γ e T hT mT
  have harg (c : Bool) (a : Expr S) : L.DataArg c T a ↔ (L.rename e).DataArg c T a := by
    cases c
    · rfl
    · constructor <;> intro ha Δ δ f v hv mv
      · have hh := ha Δ δ f v hv mv
        apply (LogicSetup.Formula.rename_comp_iff L e f _).2
        simpa only [Embedding.comp,e,Embedding.refl,Function.comp_id] using hh
      · have hh := ha Δ δ f v hv mv
        apply (LogicSetup.Formula.rename_comp_iff L e f _).1 at hh
        simpa only [Embedding.comp,e,Embedding.refl,Function.comp_id] using hh
  constructor
  · intro a ha
    simpa only [e,Embedding.refl,DataWrapper.rename_id] using hh.1 a ((harg b a).1 ha)
  · intro w a hw mw ha
    have hf := hh.2 w a (by simpa only [e,Embedding.refl,DataWrapper.rename_id] using hw) mw ((harg (!b) a).1 ha)
    apply (LogicSetup.Formula.rename_refl_iff L (L.bottom_formula.1 s hs).valid _).1
    simpa only [e,Embedding.refl,DataWrapper.rename_id] using hf
end Formed

/-- Concatenate retained wrapper syntax, never selecting new positive witnesses. -/
def reindex {b c : Bool} (h : b = c) (R : DataWrapper S b) : DataWrapper S c := h ▸ R
@[simp] theorem apply_reindex {b c : Bool} (h : b = c) (R : DataWrapper S b) (T : Expr S) :
    (reindex h R).apply T = R.apply T := by cases h; rfl
@[simp] theorem rename_reindex {b c : Bool} (h : b = c) (R : DataWrapper S b) (ρ : Nat → Nat) :
    (reindex h R).rename ρ = reindex h (R.rename ρ) := by cases h; rfl

def append {b : Bool} (R : DataWrapper S b) : {c : Bool} → DataWrapper S c → DataWrapper S (b.xor c)
  | _, .identity => reindex (by cases b <;> rfl) R
  | _, .positive Q D e => .positive (R.append Q) D e
  | _, @negative _ c Q U => reindex (by cases b <;> cases c <;> rfl) (.negative (R.append Q) U)

theorem apply_append {b c : Bool} (R : DataWrapper S b) (Q : DataWrapper S c) (T : Expr S) :
    (R.append Q).apply T = Q.apply (R.apply T) := by
  induction Q with
  | identity => simp only [append,apply_reindex,apply]
  | positive Q D e ih => simp only [append,apply,ih]
  | @negative c Q U ih => simp only [append,apply_reindex,apply,ih]

theorem append_rename {b c : Bool} (R : DataWrapper S b) (Q : DataWrapper S c) (ρ : Nat → Nat) :
    (R.append Q).rename ρ = (R.rename ρ).append (Q.rename ρ) := by
  induction Q with
  | identity => simp only [append,rename,rename_reindex]
  | positive Q D e ih => simp only [append,rename,ih]
  | @negative c Q U ih => simp only [append,rename_reindex,rename,ih]

namespace Formed
theorem reindex {b c : Bool} (hb : b = c)
    {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {R : DataWrapper S b}
    (h : R.Formed L I J) : (DataWrapper.reindex hb R).Formed L I J := by cases hb; exact h
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {b c : Bool}
    {R : DataWrapper S b} {Q : DataWrapper S c}
theorem append (h : R.Formed L I J) (g : Q.Formed L J K) : (R.append Q).Formed L I K := by
  induction g with
  | identity => exact h.reindex _
  | inclusion g hs ih => exact ih.inclusion hs
  | positive g ht ih => exact ih.positive ht
  | @negative J B K c Q U g ht hU ih => exact (ih.negative ht hU).reindex _
end Formed
end DataWrapper
end PureTypeSystem.Labelled

/- A small finite compiler for the propositional term construction.
It has no type-theoretic assumptions. -/
namespace FiniteClassical
universe u
inductive Formula (α : Type u) where
  | atom : α → Formula α
  | bot : Formula α
  | imp : Formula α → Formula α → Formula α
  deriving DecidableEq
namespace Formula
variable {α : Type u}
def neg (A : Formula α) := imp A bot
def eval (v : α → Bool) : Formula α → Bool
  | atom a => v a
  | bot => false
  | imp A B => !(A.eval v) || B.eval v

def sign (A : Formula α) (b : Bool) := if b then A else A.neg

def support [DecidableEq α] : Formula α → Finset α
  | atom a => {a}
  | bot => ∅
  | imp A B => A.support ∪ B.support
end Formula
open Formula
variable {α : Type u}

inductive Derives : Set (Formula α) → Formula α → Prop
  | ax {Γ A} : A ∈ Γ → Derives Γ A
  | intro {Γ A B} : Derives (insert A Γ) B → Derives Γ (.imp A B)
  | elim {Γ A B} : Derives Γ (.imp A B) → Derives Γ A → Derives Γ B
  | dne {Γ A} : Derives Γ A.neg.neg → Derives Γ A

namespace Derives
variable {Γ Δ : Set (Formula α)} {A B R : Formula α}

theorem mono (h : Derives Γ A) (hsub : Γ ⊆ Δ) : Derives Δ A := by
  induction h generalizing Δ with
  | ax h => exact .ax (hsub h)
  | intro h ih => exact .intro (ih (Set.insert_subset_insert hsub))
  | elim h k ih ik => exact .elim (ih hsub) (ik hsub)
  | dne h ih => exact .dne (ih hsub)

theorem weaken (h : Derives Γ A) (B : Formula α) : Derives (insert B Γ) A :=
  h.mono (Set.subset_insert _ _)

theorem cut (h : Derives Γ A) (hs : ∀ B ∈ Γ, Derives Δ B) : Derives Δ A := by
  induction h generalizing Δ with
  | ax h => exact hs _ h
  | @intro Γ A B h ih =>
    apply Derives.intro
    apply ih
    intro Q hQ
    rcases hQ with rfl | hQ
    · exact .ax (Set.mem_insert _ _)
    · exact (hs _ hQ).weaken A
  | elim h k ih ik => exact .elim (ih hs) (ik hs)
  | dne h ih => exact .dne (ih hs)

theorem absurd (h : Derives Γ .bot) : Derives Γ A :=
  .dne (.intro (h.weaken A.neg))

theorem by_cases (h : Derives (insert A Γ) R) (k : Derives (insert A.neg Γ) R) : Derives Γ R := by
  apply Derives.dne
  apply Derives.intro
  have hn : Derives (insert R.neg Γ) A.neg := by
    apply Derives.intro
    have hr : Derives (insert A (insert R.neg Γ)) R := h.mono (by
      intro Q hQ
      rcases hQ with rfl | hQ
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hQ))
    exact .elim (.ax (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hr
  have hr : Derives (insert R.neg Γ) R := k.cut (by
    intro Q hQ
    rcases hQ with rfl | hQ
    · exact hn
    · exact .ax (Set.mem_insert_of_mem _ hQ))
  exact .elim (.ax (Set.mem_insert _ _)) hr

/-- The signed recursive branch of the source's truth-table compiler. -/
theorem signed [DecidableEq α] (v : α → Bool) (A : Formula α)
    (h : ∀ a ∈ A.support, Derives Γ ((Formula.atom a).sign (v a))) :
    Derives Γ (A.sign (A.eval v)) := by
  induction A with
  | atom a => exact h a (by simp only [support,Finset.mem_singleton])
  | bot => exact .intro (.ax (Set.mem_insert _ _))
  | imp A B ihA ihB =>
    have ha := ihA (fun a ha => h a (Finset.mem_union_left _ ha))
    have hb := ihB (fun a hb => h a (Finset.mem_union_right _ hb))
    cases hA : A.eval v <;> cases hB : B.eval v
    · simp only [sign,eval,hA,hB,Bool.not_false,Bool.true_or,ite_true] at ha hb ⊢
      exact .intro (.absurd (.elim (ha.weaken A) (.ax (Set.mem_insert _ _))))
    · simp only [sign,eval,hA,hB,Bool.not_false,Bool.true_or,ite_true] at ha hb ⊢
      exact .intro (hb.weaken A)
    · simp only [sign,eval,hA,hB,Bool.not_true,Bool.false_or,ite_true,neg] at ha hb ⊢
      exact .intro (.elim (hb.weaken (.imp A B)) (.elim (.ax (Set.mem_insert _ _)) (ha.weaken (.imp A B))))
    · simp only [sign,eval,hA,hB,Bool.not_true,Bool.false_or,ite_true] at ha hb ⊢
      exact .intro (hb.weaken A)

/-- Exhaustive finite case elimination, with no evaluation reflection axiom. -/
theorem branch [DecidableEq α] (s : Finset α)
    (h : ∀ v : α → Bool, Derives ((fun A => ∃ a ∈ s, A = (Formula.atom a).sign (v a)) ∪ Γ) R) :
    Derives Γ R := by
  induction s using Finset.induction_on generalizing Γ with
  | empty =>
    have hh := h (fun _ => false)
    exact hh.mono (by
      intro X hX
      rcases hX with ⟨a,ha,_⟩ | hX
      · exact False.elim (Finset.notMem_empty a ha)
      · exact hX)
  | @insert a s has ih =>
    apply Derives.by_cases (A := Formula.atom a)
    · apply ih
      intro v
      apply (h (Function.update v a true)).mono
      intro X hX
      rcases hX with ⟨b,hb,rfl⟩ | hX
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · right
          simp only [Function.update_self,sign,ite_true]
          exact Set.mem_insert _ _
        · left
          refine ⟨b,hb,?_⟩
          rw [Function.update_of_ne (by intro he; subst b; exact has hb)]
      · exact Or.inr (Set.mem_insert_of_mem _ hX)
    · apply ih
      intro v
      apply (h (Function.update v a false)).mono
      intro X hX
      rcases hX with ⟨b,hb,rfl⟩ | hX
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · right
          simp only [Function.update_self,sign]
          exact Set.mem_insert _ _
        · left
          refine ⟨b,hb,?_⟩
          rw [Function.update_of_ne (by intro he; subst b; exact has hb)]
      · exact Or.inr (Set.mem_insert_of_mem _ hX)

/-- Boolean truth-table validity compiles to a finite typed-use derivation. -/
theorem tautology [DecidableEq α] (A : Formula α) (h : ∀ v, A.eval v = true) : Derives Γ A := by
  apply branch A.support
  intro v
  have hh := signed (Γ := (fun X => ∃ a ∈ A.support, X = (Formula.atom a).sign (v a)) ∪ Γ) v A
    (fun a ha => .ax (Or.inl ⟨a,ha,rfl⟩))
  simpa only [h v,sign,ite_true] using hh
end Derives
end FiniteClassical

namespace PureTypeSystem.Labelled
universe u v
open Classical
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {α : Type v}

 def interpret (a : α → Expr S) : FiniteClassical.Formula α → Expr S
  | .atom i => a i
  | .bot => L.bottom
  | .imp A B => L.imp (interpret a A) (interpret a B)

 theorem interpret_rename (a : α → Expr S) (F : FiniteClassical.Formula α)
    (e : Embedding P Γ γ Δ δ) :
    (L.interpret a F).rename e.names = (L.rename e).interpret (fun i => (a i).rename e.names) F := by
  induction F with
  | atom i => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [interpret,L.imp_rename,ihA,ihB]

 theorem interpret_formula (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (F : FiniteClassical.Formula α) : L.Formula (L.interpret a F) := by
  induction F with
  | atom i => exact ha i
  | bot => exact L.bottom_formula
  | imp A B ihA ihB => exact L.imp_formula ihA ihB

/-- Compilation of every node of the finite classical derivation to actual
labelled typing/proof-mode judgments. -/
 theorem propositional_sound {Ξ : Set (FiniteClassical.Formula α)} {F : FiniteClassical.Formula α}
    (h : FiniteClassical.Derives Ξ F) (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (hp : ∀ Q ∈ Ξ, Proves P Γ γ (L.interpret a Q)) : Proves P Γ γ (L.interpret a F) := by
  induction h generalizing Γ γ L a with
  | ax h => exact hp _ h
  | @intro Ξ A B h ih =>
    apply L.imp_intro_future (L.interpret_formula a ha A) (L.interpret_formula a ha B)
    intro Δ δ e hA
    rw [L.interpret_rename]
    apply ih (L := L.rename e) (fun i => (a i).rename e.names) (fun i => (ha i).rename e)
    intro Q hQ
    rcases hQ with rfl | hQ
    · simpa only [L.interpret_rename] using hA
    · simpa only [L.interpret_rename] using (hp _ hQ).rename e
  | @elim Ξ A B h k ih ik =>
    exact L.imp_elim (L.interpret_formula a ha A) (L.interpret_formula a ha B) (ih L a ha hp) (ik L a ha hp)
  | @dne Ξ A h ih => exact L.dne (L.interpret_formula a ha A) (ih L a ha hp)

 theorem propositional_tautology (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (F : FiniteClassical.Formula α) (hf : ∀ v, F.eval v = true) :
    Proves P Γ γ (L.interpret a F) :=
  L.propositional_sound (FiniteClassical.Derives.tautology (Γ := ∅) F hf) a ha (by simp)
end LogicSetup
end PureTypeSystem.Labelled

namespace FiniteClassical.Formula
universe u
variable {α : Type u}
def top : Formula α := .imp .bot .bot
def conj (A B : Formula α) : Formula α := (A.imp B.neg).neg
def disj (A B : Formula α) : Formula α := (A.neg.conj B.neg).neg
def iff (A B : Formula α) : Formula α := (A.imp B).conj (B.imp A)
def chain (hs : List (Formula α)) (Q : Formula α) : Formula α := hs.foldr .imp Q
end FiniteClassical.Formula

namespace PureTypeSystem.Labelled

section
universe u v
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
def top : Expr S := L.imp L.bottom L.bottom
def neg (A : Expr S) : Expr S := L.imp A L.bottom
def conj (A B : Expr S) : Expr S := L.neg (L.imp A (L.neg B))
def disj (A B : Expr S) : Expr S := L.neg (L.conj (L.neg A) (L.neg B))
def iff (A B : Expr S) : Expr S := L.conj (L.imp A B) (L.imp B A)

theorem top_formula : L.Formula L.top := L.imp_formula L.bottom_formula L.bottom_formula
theorem neg_formula {A : Expr S} (ha : L.Formula A) : L.Formula (L.neg A) := L.imp_formula ha L.bottom_formula
theorem conj_formula {A B : Expr S} (ha : L.Formula A) (hb : L.Formula B) :
    L.Formula (L.conj A B) := L.neg_formula (L.imp_formula ha (L.neg_formula hb))
theorem disj_formula {A B : Expr S} (ha : L.Formula A) (hb : L.Formula B) :
    L.Formula (L.disj A B) := L.neg_formula (L.conj_formula (L.neg_formula ha) (L.neg_formula hb))
theorem iff_formula {A B : Expr S} (ha : L.Formula A) (hb : L.Formula B) :
    L.Formula (L.iff A B) := L.conj_formula (L.imp_formula ha hb) (L.imp_formula hb ha)

theorem top_rename (e : Embedding P Γ γ Δ δ) : L.top.rename e.names = (L.rename e).top := by
  simp only [top,imp_rename,bottom_rename]
theorem neg_rename (A : Expr S) (e : Embedding P Γ γ Δ δ) :
    (L.neg A).rename e.names = (L.rename e).neg (A.rename e.names) := by
  simp only [neg,imp_rename,bottom_rename]
theorem conj_rename (A B : Expr S) (e : Embedding P Γ γ Δ δ) :
    (L.conj A B).rename e.names = (L.rename e).conj (A.rename e.names) (B.rename e.names) := by
  simp only [conj,neg_rename,imp_rename]
theorem disj_rename (A B : Expr S) (e : Embedding P Γ γ Δ δ) :
    (L.disj A B).rename e.names = (L.rename e).disj (A.rename e.names) (B.rename e.names) := by
  simp only [disj,neg_rename,conj_rename]
theorem iff_rename (A B : Expr S) (e : Embedding P Γ γ Δ δ) :
    (L.iff A B).rename e.names = (L.rename e).iff (A.rename e.names) (B.rename e.names) := by
  simp only [iff,conj_rename,imp_rename]

/-- Arbitrary finite propositional chaining, compiled to actual open terms. -/
theorem propositional_consequence {α : Type v} (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (hs : List (FiniteClassical.Formula α)) (Q : FiniteClassical.Formula α)
    (hv : ∀ v, (FiniteClassical.Formula.chain hs Q).eval v = true)
    (hp : ∀ R ∈ hs, Proves P Γ γ (L.interpret a R)) :
    Proves P Γ γ (L.interpret a Q) := by
  have hf := L.propositional_tautology a ha (FiniteClassical.Formula.chain hs Q) hv
  clear hv
  induction hs with
  | nil => exact hf
  | cons A hs ih =>
    apply ih (fun R hR => hp R (List.mem_cons_of_mem _ hR))
    exact L.imp_elim (L.interpret_formula a ha A) (L.interpret_formula a ha (FiniteClassical.Formula.chain hs Q))
      hf (hp A (List.mem_cons_self))

theorem top_intro : Proves P Γ γ L.top := by
  obtain ⟨s,hs⟩ := L.bottom_formula.sorted L
  exact L.imp_intro L.bottom_formula L.bottom_formula (.refl hs)

theorem conj_intro {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (ha : Proves P Γ γ A) (hb : Proves P Γ γ B) : Proves P Γ γ (L.conj A B) := by
  apply L.propositional_consequence (fun b : Bool => if b then B else A)
      (fun b => by cases b; exact hA; exact hB)
      [.atom false,.atom true] ((FiniteClassical.Formula.atom false).conj (.atom true))
  · intro v; cases h0 : v false <;> cases h1 : v true <;>
      simp only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.conj,
        FiniteClassical.Formula.neg,FiniteClassical.Formula.eval,h0,h1] <;> rfl
  · intro R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl
    · exact ha
    · exact hb

theorem conj_left {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (hp : Proves P Γ γ (L.conj A B)) : Proves P Γ γ A := by
  apply L.propositional_consequence (fun b : Bool => if b then B else A)
      (fun b => by cases b; exact hA; exact hB)
      [(FiniteClassical.Formula.atom false).conj (.atom true)] (.atom false)
  · intro v; cases h0 : v false <;> cases h1 : v true <;>
      simp only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.conj,
        FiniteClassical.Formula.neg,FiniteClassical.Formula.eval,h0,h1] <;> rfl
  · intro R hR
    have he : R = (FiniteClassical.Formula.atom false).conj (.atom true) := by simpa only [List.mem_singleton] using hR
    subst R; exact hp

theorem conj_right {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (hp : Proves P Γ γ (L.conj A B)) : Proves P Γ γ B := by
  apply L.propositional_consequence (fun b : Bool => if b then B else A)
      (fun b => by cases b; exact hA; exact hB)
      [(FiniteClassical.Formula.atom false).conj (.atom true)] (.atom true)
  · intro v; cases h0 : v false <;> cases h1 : v true <;>
      simp only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.conj,
        FiniteClassical.Formula.neg,FiniteClassical.Formula.eval,h0,h1] <;> rfl
  · intro R hR
    have he : R = (FiniteClassical.Formula.atom false).conj (.atom true) := by simpa only [List.mem_singleton] using hR
    subst R; exact hp

theorem iff_of_equivalent {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (he : Equivalent P Γ γ A B) : Proves P Γ γ (L.iff A B) :=
  L.conj_intro (L.imp_formula hA hB) (L.imp_formula hB hA)
    (L.imp_intro hA hB he.1) (L.imp_intro hB hA he.2)

theorem equivalent_of_iff {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (hp : Proves P Γ γ (L.iff A B)) : Equivalent P Γ γ A B := by
  have hab := L.conj_left (L.imp_formula hA hB) (L.imp_formula hB hA) hp
  have hba := L.conj_right (L.imp_formula hA hB) (L.imp_formula hB hA) hp
  obtain ⟨s,hs⟩ := hA.sorted L
  obtain ⟨t,ht⟩ := hB.sorted L
  exact ⟨(L.imp_future_iff hA hB).1 hab _ _ (Embedding.cons hs .proof) (Proves.of_var hs),
    (L.imp_future_iff hB hA).1 hba _ _ (Embedding.cons ht .proof) (Proves.of_var ht)⟩
end LogicSetup
end

section
universe u
variable {S : Type u}
namespace Converts
theorem app {l : Label} {f f' a a' : Expr S} (hf : Converts f f') (ha : Converts a a') :
    Converts (.app l f a) (.app l f' a') := by
  obtain ⟨g,hg,hg'⟩ := hf.join
  obtain ⟨u,hu,hu'⟩ := ha.join
  exact .trans _ _ _ (hg.app hu).converts (.symm _ _ (hg'.app hu').converts)
end Converts
namespace ProofWrapper
theorem subst_rename (R : ProofWrapper S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename]
theorem rename_subst (R : ProofWrapper S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst]
end ProofWrapper
namespace PositiveDataWrapper
theorem subst_rename (R : PositiveDataWrapper S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename]
theorem rename_subst (R : PositiveDataWrapper S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst]
theorem project_converts (R : PositiveDataWrapper S) {w w' : Expr S} (h : Converts w w') :
    Converts (R.project w) (R.project w') := by
  induction R generalizing w w' with
  | identity => exact h
  | step R D e ih => exact ih (.app h (.refl _))
end PositiveDataWrapper
namespace DataTail
theorem subst_rename (U : DataTail S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (U.rename ρ).subst σ = U.subst (σ ∘ ρ) := by
  cases U
  simp only [rename,subst,ProofWrapper.subst_rename,PositiveDataWrapper.subst_rename]
theorem rename_subst (U : DataTail S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (U.subst σ).rename ρ = U.subst (fun n => (σ n).rename ρ) := by
  cases U
  simp only [rename,subst,ProofWrapper.rename_subst,PositiveDataWrapper.rename_subst]
theorem read_converts (U : DataTail S) {w w' : Expr S} (h : Converts w w') :
    Converts (U.read w) (U.read w') := U.decode.apply_converts (U.positive.project_converts h)
end DataTail
namespace DataWrapper

theorem subst_rename {b} (R : DataWrapper S b) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename,DataTail.subst_rename]
theorem rename_subst {b} (R : DataWrapper S b) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst,DataTail.rename_subst]

theorem argSub_shift (b : Bool) (σ : Nat → Expr S) :
    argSub b (Expr.liftSub σ) ∘ argRen b Nat.succ =
      fun n => (argSub b σ n).rename (argRen b Nat.succ) := by
  cases b
  · rfl
  · funext n
    cases n with
    | zero => rfl
    | succ n => simp only [argSub,argRen,ite_true,Function.comp_apply,Expr.liftRen,
        PureTypeSystem.Expr.liftRen,Expr.liftSub,Expr.rename_comp]; rfl

theorem subst_build_observe {b} (R : DataWrapper S b) :
    (∀ T a σ, (R.build T a).subst σ = (R.subst σ).build (T.subst σ) (a.subst (argSub b σ))) ∧
    (∀ T w a σ, (R.observe T w a).subst σ =
      (R.subst σ).observe (T.subst σ) (w.subst σ) (a.subst (argSub (!b) σ))) := by
  generalize he : R.depth = n
  induction n using Nat.strong_induction_on generalizing b R with
  | h n rec =>
   cases R with
   | identity =>
     constructor
     · intro T a σ; simp only [build,subst,argSub,Bool.false_eq_true,ite_false]
     · intro T w a σ
       simpa only [observe,subst,argSub,Bool.not_false,ite_true] using (Expr.instantiate_subst a w σ).symm
   | positive R D e =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     exact ⟨fun T a σ => by simp only [build,subst,Expr.constLam_subst,ih.1],
       fun T w a σ => by simpa only [observe,subst,Expr.subst] using ih.2 T (.app .dd w e) a σ⟩
   | @negative b R U =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     constructor
     · intro T a σ
       simp only [build,Expr.subst,DataTail.send_subst,subst]
       rw [(rec R.depth (by simp only [← he,depth]; omega) (R.rename Nat.succ) (R.depth_rename Nat.succ)).2]
       simp only [apply_subst,subst_rename,rename_subst,DataTail.subst_rename,DataTail.rename_subst,
         Expr.subst_rename,Expr.rename_subst,argSub_shift]
       rfl
     · intro T w a σ
       simp only [observe,subst,DataTail.read_subst,Expr.subst,ih.1,Bool.not_not]

theorem observe_converts {b} (R : DataWrapper S b) (T a : Expr S) {w w' : Expr S}
    (h : Converts w w') : Converts (R.observe T w a) (R.observe T w' a) := by
  induction R generalizing w w' with
  | identity => simpa only [observe] using h.instantiate_right a
  | positive R D e ih => simpa only [observe] using ih (.app h (.refl _))
  | negative R U ih => simpa only [observe] using U.read_converts (Converts.app (l := .dd) h (.refl (R.build T a)))

/-- The exact substitution equation exposed by a negative-edge beta step. -/
theorem observe_open {b} (R : DataWrapper S b) (T a v : Expr S) :
    ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
      (a.rename (argRen (!b) Nat.succ))).instantiate v = R.observe T v a := by
  simp only [Expr.instantiate,(R.rename Nat.succ).subst_build_observe.2,
    instantiate_raise,Expr.subst,Expr.single,Expr.subst_rename]
  have he : argSub (!b) (Expr.single v) ∘ argRen (!b) Nat.succ = Expr.var := by
    cases b <;> funext n <;> cases n <;> rfl
  rw [he,Expr.subst_var]
  rw [show Expr.single v ∘ Nat.succ = Expr.var from rfl,Expr.subst_var]
end DataWrapper
end

universe u
variable {S : Type u} {P : Specification S}
namespace DataWrapper
theorem build_rename {b} (R : DataWrapper S b) (T a : Expr S) (ρ : Nat → Nat) :
    (R.build T a).rename ρ = (R.rename ρ).build (T.rename ρ) (a.rename (argRen b ρ)) :=
  R.rename_build_observe.1 T a ρ
theorem observe_rename {b} (R : DataWrapper S b) (T w a : Expr S) (ρ : Nat → Nat) :
    (R.observe T w a).rename ρ = (R.rename ρ).observe (T.rename ρ) (w.rename ρ) (a.rename (argRen (!b) ρ)) :=
  R.rename_build_observe.2 T w a ρ
theorem build_subst {b} (R : DataWrapper S b) (T a : Expr S) (σ : Nat → Expr S) :
    (R.build T a).subst σ = (R.subst σ).build (T.subst σ) (a.subst (argSub b σ)) :=
  R.subst_build_observe.1 T a σ
theorem observe_subst {b} (R : DataWrapper S b) (T w a : Expr S) (σ : Nat → Expr S) :
    (R.observe T w a).subst σ = (R.subst σ).observe (T.subst σ) (w.subst σ) (a.subst (argSub (!b) σ)) :=
  R.subst_build_observe.2 T w a σ
end DataWrapper
namespace Expr
/-- Composition of one-variable open terms, preserving the common ambient
context. No logical equivalence is used as a data equality. -/
def compose (f g : Expr S) : Expr S := (f.rename (liftRen Nat.succ)).instantiate g

theorem compose_instantiate (f g a : Expr S) :
    (f.compose g).instantiate a = f.instantiate (g.instantiate a) := by
  simp only [compose,instantiate,subst_subst,subst_rename]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem compose_rename (f g : Expr S) (ρ : Nat → Nat) :
    (f.compose g).rename (liftRen ρ) =
      (f.rename (liftRen ρ)).compose (g.rename (liftRen ρ)) := by
  simp only [compose,← instantiate_rename,rename_comp]
  congr 2
  funext n
  cases n <;> rfl
end Expr

/-- An ordinary raw data callback. Its uniformity is a consequence of the
already proved labelled substitution theorem. -/
def DataMap (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode)
    (T U f : Expr S) : Prop :=
  HasType P (T :: Γ) f (U.rename Nat.succ) ∧ WellModed (modeCons .data γ) f .data

namespace DataMap
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {T U f : Expr S} {s : S}
theorem apply (hf : DataMap P Γ γ T U f) {a : Expr S}
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) :
    HasType P Γ (f.instantiate a) U ∧ WellModed γ (f.instantiate a) .data := by
  exact ⟨by simpa only [Expr.instantiate_raise] using hf.1.instantiate ha,
    hf.2.instantiate ma⟩

theorem rename (hf : DataMap P Γ γ T U f) (hT : HasType P Γ T (.sort s))
    (e : Embedding P Γ γ Δ δ) :
    DataMap P Δ δ (T.rename e.names) (U.rename e.names) (f.rename (Expr.liftRen e.names)) := by
  constructor
  · simpa only [Embedding.lift,Expr.rename_comp,show Expr.liftRen e.names ∘ Nat.succ = Nat.succ ∘ e.names from rfl] using (e.lift hT .data).typing hf.1
  · exact (e.lift hT .data).moded hf.2
end DataMap

namespace LogicSetup.Family
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {T U Q f : Expr S} {s : S}
theorem compose (hQ : L.Family U Q) (hf : DataMap P Γ γ T U f)
    (hT : HasType P Γ T (.sort s)) : L.Family T (Q.compose f) := by
  intro Δ δ e a ha ma
  have hd := (hf.rename hT e).apply ha ma
  have hh := hQ Δ δ e ((f.rename (Expr.liftRen e.names)).instantiate a) hd.1 hd.2
  simpa only [Expr.compose_rename,Expr.compose_instantiate] using hh
end LogicSetup.Family

namespace DataWrapper

def evalCallback (R : DataWrapper S true) (T w : Expr S) : Expr S :=
  (R.rename Nat.succ).observe (T.rename Nat.succ) (w.rename Nat.succ) (.var 0)

theorem evalCallback_instantiate (R : DataWrapper S true) (T w a : Expr S) :
    (R.evalCallback T w).instantiate a = R.observe T w a := by
  simp only [evalCallback,Expr.instantiate,observe_subst,instantiate_raise,
    Expr.subst_lift_single,argSub,Bool.not_true,Bool.false_eq_true,ite_false,Expr.subst,Expr.single]

theorem evalCallback_rename (R : DataWrapper S true) (T w : Expr S) (ρ : Nat → Nat) :
    (R.evalCallback T w).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalCallback (T.rename ρ) (w.rename ρ) := by
  simp only [evalCallback,observe_rename,rename_comp,Expr.rename_comp,
    argRen,Bool.not_true,Bool.false_eq_true,ite_false,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {R : DataWrapper S true}

theorem evalCallback_family (hR : Formed L I J R) {T w : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hw : HasType P Γ w (R.apply T)) (mw : WellModed γ w .data) :
    L.Family T (R.evalCallback T w) := by
  intro Δ δ e a ha ma
  rw [evalCallback_rename,evalCallback_instantiate]
  exact ((hR.rename e).sound (fun s hs => e.typing (hT s hs)) (e.moded mT)).2
    (w.rename e.names) a (by simpa only [apply_rename] using e.typing hw) (e.moded mw) ⟨ha,ma⟩
end Formed

def reencode (R R' : DataWrapper S true) (T w : Expr S) : Expr S :=
  R'.build T (R.evalCallback T w)

theorem reencode_rename (R R' : DataWrapper S true) (T w : Expr S) (ρ : Nat → Nat) :
    (reencode R R' T w).rename ρ = reencode (R.rename ρ) (R'.rename ρ) (T.rename ρ) (w.rename ρ) := by
  simp only [reencode,build_rename,argRen,ite_true,evalCallback_rename]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {R R' : DataWrapper S true}

theorem reencode_typed (hR : Formed L I J R) (hR' : Formed L I K R') {T w : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hw : HasType P Γ w (R.apply T)) (mw : WellModed γ w .data) :
    HasType P Γ (reencode R R' T w) (R'.apply T) ∧ WellModed γ (reencode R R' T w) .data :=
  (hR'.sound hT mT).1 _ (hR.evalCallback_family hT mT hw mw)
end Formed

def cancelFormula (b : Bool) (a q : Expr S) : Expr S :=
  if b then a.instantiate q else q.instantiate a

theorem cancelFormula_swap (b : Bool) (a q : Expr S) :
    cancelFormula (!b) a q = cancelFormula b q a := by cases b <;> rfl

theorem negative_beta {b} (R : DataWrapper S b) (U : DataTail S) (T a q : Expr S) :
    Converts ((R.negative U).observe T ((R.negative U).build T a) q)
      (U.read (U.send (R.observe T (R.build T q) a))) := by
  simp only [observe,build]
  apply U.read_converts
  have hh := Reduces.converts (Relation.ReflTransGen.single (Beta.head .dd (R.apply T)
    ((U.rename Nat.succ).send ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
      (a.rename (argRen (!b) Nat.succ)))) (R.build T q)))
  have he : ((U.rename Nat.succ).send ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
      (a.rename (argRen (!b) Nat.succ)))).instantiate (R.build T q) =
        U.send (R.observe T (R.build T q) a) := by
    simp only [Expr.instantiate,DataTail.send_subst,DataTail.instantiate_raise]
    exact congrArg U.send (R.observe_open T a (R.build T q))
  exact he ▸ hh

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {b : Bool} {R : DataWrapper S b}

theorem cancellation (h : Formed L I J R) {T a q : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (ha : L.DataArg b T a) (hq : L.DataArg (!b) T q) :
    Equivalent P Γ γ (R.observe T (R.build T a) q) (cancelFormula b a q) := by
  have htarget : L.Formula (cancelFormula b a q) := by
    cases b
    · exact hq.instantiate ha.1 ha.2
    · exact ha.instantiate hq.1 hq.2
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  induction h generalizing a q with
  | identity => simpa only [observe,build,cancelFormula,Bool.false_eq_true,ite_false] using Equivalent.refl (γ := γ) (htarget.1 s hs)
  | inclusion h hh ih => exact ih ha hq htarget
  | @positive A J K b R h ht ih =>
    have hb := (h.sound hT mT).1 a ha
    have hf := (h.sound hT mT).2 (R.build T a) q hb.1 hb.2 hq
    have hsnd := (h.positive ht).sound hT mT
    have hb' := hsnd.1 a ha
    have hf' := hsnd.2 _ q hb'.1 hb'.2 hq
    have hc : Converts ((R.positive (L.witnesses.type A) (L.witnesses.value A)).observe T
        ((R.positive (L.witnesses.type A) (L.witnesses.value A)).build T a) q)
        (R.observe T (R.build T a) q) := by
      simpa only [build,observe] using R.observe_converts T q
        (Reduces.converts (Relation.ReflTransGen.single (positive_cancel .dd (L.witnesses.type A) (L.witnesses.value A) (R.build T a))))
    exact (Equivalent.of_conversion (hf'.1 s hs) (hf.1 s hs) hc).trans
      (ih ha hq htarget) (hf'.1 s hs) (hf.1 s hs) (htarget.1 s hs)
  | @negative J B K b R U h ht hU ih =>
    have hq' : L.DataArg b T q := by simpa only [Bool.not_not] using hq
    have hb := (h.sound hT mT).1 q hq'
    have hf := (h.sound hT mT).2 (R.build T q) a hb.1 hb.2 ha
    have hsnd := (h.negative ht hU).sound hT mT
    have hb' := hsnd.1 a ha
    have hf' := hsnd.2 _ q hb'.1 hb'.2 hq
    have hsend := hU.send_typed hf
    have hread := hU.read_formula hsend.1 hsend.2
    have hc := Equivalent.of_conversion (γ := γ) (hf'.1 s hs) (hread.1 s hs) (R.negative_beta U T a q)
    have ih' := ih hq' ha (by simpa only [cancelFormula_swap] using htarget)
    have he := (hU.read_send hf).trans ih' (hread.1 s hs) (hf.1 s hs)
      (by simpa only [cancelFormula_swap] using htarget.1 s hs)
    simpa only [cancelFormula_swap] using hc.trans he (hf'.1 s hs) (hread.1 s hs)
      (by simpa only [cancelFormula_swap] using htarget.1 s hs)
end Formed
end DataWrapper

namespace Expr
theorem compose_subst (f g : Expr S) (σ : Nat → Expr S) :
    (f.compose g).subst (liftSub σ) =
      (f.subst (liftSub σ)).compose (g.subst (liftSub σ)) := by
  simp only [compose,← instantiate_subst,subst_rename,rename_subst]
  congr 2
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [liftRen,PureTypeSystem.Expr.liftRen,liftSub,Function.comp_apply,rename_comp]; rfl

end Expr
namespace DataWrapper

theorem evalCallback_subst (R : DataWrapper S true) (T w : Expr S) (σ : Nat → Expr S) :
    (R.evalCallback T w).subst (Expr.liftSub σ) =
      (R.subst σ).evalCallback (T.subst σ) (w.subst σ) := by
  simp only [evalCallback,observe_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,argSub,Bool.not_true,Bool.false_eq_true,
    ite_false,Expr.subst,Expr.liftSub]
  rfl

theorem reencode_subst (R R' : DataWrapper S true) (T w : Expr S) (σ : Nat → Expr S) :
    (reencode R R' T w).subst σ = reencode (R.subst σ) (R'.subst σ) (T.subst σ) (w.subst σ) := by
  simp only [reencode,build_subst,argSub,ite_true,evalCallback_subst]

def reencodeBody (R R' : DataWrapper S true) (T : Expr S) : Expr S :=
  reencode (R.rename Nat.succ) (R'.rename Nat.succ) (T.rename Nat.succ) (.var 0)

theorem reencodeBody_instantiate (R R' : DataWrapper S true) (T w : Expr S) :
    (reencodeBody R R' T).instantiate w = reencode R R' T w := by
  simp only [reencodeBody,Expr.instantiate,reencode_subst,instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]

theorem reencodeBody_rename (R R' : DataWrapper S true) (T : Expr S) (ρ : Nat → Nat) :
    (reencodeBody R R' T).rename (Expr.liftRen ρ) =
      reencodeBody (R.rename ρ) (R'.rename ρ) (T.rename ρ) := by
  simp only [reencodeBody,reencode_rename,rename_comp,Expr.rename_comp,Expr.rename,
    Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {R R' : DataWrapper S true}

theorem reencode_map (hR : Formed L I J R) (hR' : Formed L I K R') {T : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ (R.apply T) (.sort s)) :
    DataMap P Γ γ (R.apply T) (R'.apply T) (reencodeBody R R' T) := by
  let e := Embedding.cons (γ := γ) hs Mode.data
  have hh := (hR.rename e).reencode_typed (hR'.rename e)
    (fun t ht => e.typing (hT t ht)) (e.moded mT)
    (by simpa only [e,Embedding.cons,apply_rename] using HasType.var hs)
    (WellModed.var (γ := modeCons .data γ) 0)
  simpa only [DataMap,reencodeBody,e,Embedding.cons,← apply_rename] using hh

theorem reencode_evaluation (hR : Formed L I J R) (hR' : Formed L I K R') {T w a : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hw : HasType P Γ w (R.apply T)) (mw : WellModed γ w .data)
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) :
    Equivalent P Γ γ (R'.observe T (reencode R R' T w) a) (R.observe T w a) := by
  simpa only [reencode,cancelFormula,ite_true,evalCallback_instantiate] using
    hR'.cancellation hT mT (hR.evalCallback_family hT mT hw mw) ⟨ha,ma⟩
end Formed
end DataWrapper

/-- Raw code for the already constructed logical operations. This separates
syntax naturality from the dependent typing certificate of a logic setup. -/
structure LogicCode (S : Type u) where
  bottom : Expr S
  into : ProofWrapper S
  out : ProofWrapper S
namespace LogicCode
variable (L : LogicCode S)
def rename (ρ : Nat → Nat) : LogicCode S := ⟨L.bottom.rename ρ,L.into.rename ρ,L.out.rename ρ⟩
def subst (σ : Nat → Expr S) : LogicCode S := ⟨L.bottom.subst σ,L.into.subst σ,L.out.subst σ⟩
def imp (A B : Expr S) := L.out.apply (Expr.arrow .pp (L.into.apply A) B)
def neg (A : Expr S) := L.imp A L.bottom
def top := L.imp L.bottom L.bottom
def conj (A B : Expr S) := L.neg (L.imp A (L.neg B))
def disj (A B : Expr S) := L.neg (L.conj (L.neg A) (L.neg B))
def iff (A B : Expr S) := L.conj (L.imp A B) (L.imp B A)
def cond (G A B : Expr S) := L.disj (L.conj G A) (L.conj (L.neg G) B)
def sign (b : Bool) (A : Expr S) := if b then A else L.neg A

theorem rename_comp (ρ τ : Nat → Nat) : (L.rename τ).rename ρ = L.rename (ρ ∘ τ) := by
  cases L; simp only [rename,Expr.rename_comp,ProofWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (L.rename Nat.succ).subst (Expr.single a) = L := by
  cases L; simp only [rename,subst,Expr.subst_lift_single,ProofWrapper.instantiate_raise]
theorem rename_lift_instantiate (ρ : Nat → Nat) (a : Expr S) :
    ((L.rename Nat.succ).rename (Expr.liftRen ρ)).subst (Expr.single a) = L.rename ρ := by
  rw [rename_comp]
  change (L.rename (Nat.succ ∘ ρ)).subst (Expr.single a) = _
  rw [← rename_comp]
  exact instantiate_raise _ a

theorem imp_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.imp A B).rename ρ = (L.rename ρ).imp (A.rename ρ) (B.rename ρ) := by
  simp only [imp,ProofWrapper.apply_rename,Expr.arrow_rename,rename]
theorem imp_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.imp A B).subst σ = (L.subst σ).imp (A.subst σ) (B.subst σ) := by
  simp only [imp,ProofWrapper.apply_subst,Expr.arrow_subst,subst]
theorem neg_rename (A : Expr S) (ρ : Nat → Nat) :
    (L.neg A).rename ρ = (L.rename ρ).neg (A.rename ρ) := by
  simp only [neg,imp_rename,rename]
theorem neg_subst (A : Expr S) (σ : Nat → Expr S) :
    (L.neg A).subst σ = (L.subst σ).neg (A.subst σ) := by
  simp only [neg,imp_subst,subst]
theorem top_rename (ρ : Nat → Nat) : L.top.rename ρ = (L.rename ρ).top := by
  simp only [top,imp_rename,rename]
theorem top_subst (σ : Nat → Expr S) : L.top.subst σ = (L.subst σ).top := by
  simp only [top,imp_subst,subst]
theorem conj_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.conj A B).rename ρ = (L.rename ρ).conj (A.rename ρ) (B.rename ρ) := by
  simp only [conj,neg_rename,imp_rename]
theorem conj_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.conj A B).subst σ = (L.subst σ).conj (A.subst σ) (B.subst σ) := by
  simp only [conj,neg_subst,imp_subst]
theorem disj_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.disj A B).rename ρ = (L.rename ρ).disj (A.rename ρ) (B.rename ρ) := by
  simp only [disj,neg_rename,conj_rename]
theorem disj_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.disj A B).subst σ = (L.subst σ).disj (A.subst σ) (B.subst σ) := by
  simp only [disj,neg_subst,conj_subst]
theorem iff_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.iff A B).rename ρ = (L.rename ρ).iff (A.rename ρ) (B.rename ρ) := by
  simp only [iff,imp_rename,conj_rename]
theorem iff_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.iff A B).subst σ = (L.subst σ).iff (A.subst σ) (B.subst σ) := by
  simp only [iff,imp_subst,conj_subst]
theorem cond_rename (G A B : Expr S) (ρ : Nat → Nat) :
    (L.cond G A B).rename ρ = (L.rename ρ).cond (G.rename ρ) (A.rename ρ) (B.rename ρ) := by
  simp only [cond,conj_rename,disj_rename,neg_rename]
theorem cond_subst (G A B : Expr S) (σ : Nat → Expr S) :
    (L.cond G A B).subst σ = (L.subst σ).cond (G.subst σ) (A.subst σ) (B.subst σ) := by
  simp only [cond,conj_subst,disj_subst,neg_subst]
theorem sign_rename (b : Bool) (A : Expr S) (ρ : Nat → Nat) :
    (L.sign b A).rename ρ = (L.rename ρ).sign b (A.rename ρ) := by
  cases b <;> simp only [sign,ite_false,ite_true,Bool.false_eq_true,neg_rename]
theorem sign_subst (b : Bool) (A : Expr S) (σ : Nat → Expr S) :
    (L.sign b A).subst σ = (L.subst σ).sign b (A.subst σ) := by
  cases b <;> simp only [sign,ite_false,ite_true,Bool.false_eq_true,neg_subst]
theorem sign_instantiate_raise (b : Bool) (Q a : Expr S) :
    ((L.rename Nat.succ).sign b Q).instantiate a = L.sign b (Q.instantiate a) := by
  simp only [Expr.instantiate,sign_subst,instantiate_raise]
end LogicCode
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
def code : LogicCode S := ⟨L.bottom,L.inCode,L.outCode⟩
theorem code_rename (e : Embedding P Γ γ Δ δ) : (L.rename e).code = L.code.rename e.names := rfl
theorem cond_formula {G A B : Expr S} (hG : L.Formula G) (hA : L.Formula A) (hB : L.Formula B) :
    L.Formula (L.code.cond G A B) :=
  L.disj_formula (L.conj_formula hG hA) (L.conj_formula (L.neg_formula hG) hB)
theorem sign_formula (b : Bool) {A : Expr S} (hA : L.Formula A) : L.Formula (L.code.sign b A) := by
  cases b
  · exact L.neg_formula hA
  · exact hA

namespace Family
variable {L} {T Q Q' : Expr S} {s : S}
theorem constant (hQ : L.Formula Q) : L.Family T (Q.rename Nat.succ) := by
  intro Δ δ e a ha ma
  rw [Expr.rename_comp]
  rw [show Expr.liftRen e.names ∘ Nat.succ = Nat.succ ∘ e.names from rfl, ← Expr.rename_comp]
  rw [Expr.instantiate_raise]
  exact hQ.rename e

theorem code_imp (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).imp Q Q') := by
  intro Δ δ e a hA mA
  simp only [LogicCode.imp_rename,Expr.instantiate,LogicCode.imp_subst,
    LogicCode.rename_lift_instantiate]
  exact (L.rename e).imp_formula (ha _ _ e a hA mA) (hb _ _ e a hA mA)

theorem code_neg (hQ : L.Family T Q) : L.Family T ((L.code.rename Nat.succ).neg Q) :=
  hQ.code_imp (constant L.bottom_formula)

theorem code_sign (hQ : L.Family T Q) (b : Bool) : L.Family T ((L.code.rename Nat.succ).sign b Q) := by
  cases b
  · exact hQ.code_neg
  · exact hQ

theorem code_conj (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).conj Q Q') :=
  (ha.code_imp hb.code_neg).code_neg

theorem code_disj (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).disj Q Q') :=
  (ha.code_neg.code_conj hb.code_neg).code_neg

theorem code_iff (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).iff Q Q') :=
  (ha.code_imp hb).code_conj (hb.code_imp ha)

theorem code_cond {G : Expr S} (hg : L.Family T G) (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).cond G Q Q') :=
  (hg.code_conj ha).code_disj (hg.code_neg.code_conj hb)
end Family
end LogicSetup

namespace DataWrapper
/-- The other slot of odd evaluation, exposed as an actual raw callback. -/
def contraCallback (R : DataWrapper S true) (T t : Expr S) : Expr S :=
  (R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0) (t.rename Nat.succ)

theorem contraCallback_instantiate (R : DataWrapper S true) (T t f : Expr S) :
    (R.contraCallback T t).instantiate f = R.observe T f t := by
  simp only [contraCallback,Expr.instantiate,observe_subst,instantiate_raise,
    Expr.subst_lift_single,argSub,Bool.not_true,Bool.false_eq_true,ite_false,Expr.subst,Expr.single]

theorem contraCallback_rename (R : DataWrapper S true) (T t : Expr S) (ρ : Nat → Nat) :
    (R.contraCallback T t).rename (Expr.liftRen ρ) =
      (R.rename ρ).contraCallback (T.rename ρ) (t.rename ρ) := by
  simp only [contraCallback,observe_rename,rename_comp,Expr.rename_comp,
    argRen,Bool.not_true,Bool.false_eq_true,ite_false,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem contraCallback_subst (R : DataWrapper S true) (T t : Expr S) (σ : Nat → Expr S) :
    (R.contraCallback T t).subst (Expr.liftSub σ) =
      (R.subst σ).contraCallback (T.subst σ) (t.subst σ) := by
  simp only [contraCallback,observe_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,argSub,Bool.not_true,Bool.false_eq_true,
    ite_false,Expr.subst,Expr.liftSub]
  rfl
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {R : DataWrapper S true}

theorem contraCallback_family (hR : Formed L I J R) {T t : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    L.Family (R.apply T) (R.contraCallback T t) := by
  intro Δ δ e f hf mf
  rw [contraCallback_rename,contraCallback_instantiate]
  exact ((hR.rename e).sound (fun s hs => e.typing (hT s hs)) (e.moded mT)).2
    f (t.rename e.names) (by simpa only [apply_rename] using hf) mf ⟨e.typing ht,e.moded mt⟩
end Formed
end DataWrapper
end PureTypeSystem.Labelled

/- A proof-producing reflection tactic for the source's `pl`. The Boolean
truth table is proved by kernel reduction, not by native evaluation. -/
namespace PTSPropositional
open Lean Meta Elab Tactic

inductive Node where
  | atom : Nat → Node
  | bot : Node
  | imp : Node → Node → Node

def Node.neg (A : Node) := Node.imp A .bot
def Node.conj (A B : Node) := (Node.imp A B.neg).neg
def Node.disj (A B : Node) := (A.neg.conj B.neg).neg
def Node.iff (A B : Node) := (Node.imp A B).conj (.imp B A)

partial def reify (e : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Node := do
  let args := e.getAppArgs
  let nm := e.getAppFn.constName?
  match nm with
  | some ``PureTypeSystem.Labelled.LogicSetup.bottom
  | some ``PureTypeSystem.Labelled.LogicCode.bottom => return .bot
  | some ``PureTypeSystem.Labelled.LogicSetup.top
  | some ``PureTypeSystem.Labelled.LogicCode.top => return .imp .bot .bot
  | some ``PureTypeSystem.Labelled.LogicSetup.imp
  | some ``PureTypeSystem.Labelled.LogicCode.imp =>
    return .imp (← reify args[args.size-2]!) (← reify args[args.size-1]!)
  | some ``PureTypeSystem.Labelled.LogicSetup.neg
  | some ``PureTypeSystem.Labelled.LogicCode.neg =>
    return (← reify args[args.size-1]!).neg
  | some ``PureTypeSystem.Labelled.LogicSetup.conj
  | some ``PureTypeSystem.Labelled.LogicCode.conj =>
    return (← reify args[args.size-2]!).conj (← reify args[args.size-1]!)
  | some ``PureTypeSystem.Labelled.LogicSetup.disj
  | some ``PureTypeSystem.Labelled.LogicCode.disj =>
    return (← reify args[args.size-2]!).disj (← reify args[args.size-1]!)
  | some ``PureTypeSystem.Labelled.LogicSetup.iff
  | some ``PureTypeSystem.Labelled.LogicCode.iff =>
    return (← reify args[args.size-2]!).iff (← reify args[args.size-1]!)
  | some ``PureTypeSystem.Labelled.LogicCode.cond =>
    let g ← reify args[args.size-3]!
    let a ← reify args[args.size-2]!
    let b ← reify args[args.size-1]!
    return (g.conj a).disj (g.neg.conj b)
  | _ =>
    let atoms ← get
    for i in [:atoms.size] do
      if ← isDefEq e atoms[i]! then return .atom i
    modify (·.push e)
    return .atom atoms.size

partial def Node.syntax : Node → MetaM (TSyntax `term)
  | .atom n => `(FiniteClassical.Formula.atom $(quote n))
  | .bot => `(FiniteClassical.Formula.bot)
  | .imp a b => do `(FiniteClassical.Formula.imp $(← a.syntax) $(← b.syntax))

partial def atomFunction (atoms : Array Lean.Expr) (L : TSyntax `term) (n : Nat := 0) :
    TermElabM (TSyntax `term) := do
  if n < atoms.size then do
    let atm ← Term.exprToSyntax atoms[n]!
    let rest ← atomFunction atoms L (n+1)
    `(if i = $(quote n) then $atm else $rest)
  else `(($L).bottom)

partial def truthCases (v : TSyntax `term) (n : Nat) : TacticM (TSyntax `tactic) := do
  if n = 0 then
    `(tactic| simp_all only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.eval] <;> rfl)
  else
    let k := n-1
    let h := mkIdent (Name.mkSimple s!"pl_bit_{k}")
    `(tactic| cases $h:ident : ($v $(quote k) : Bool) <;> $(← truthCases v k))

partial def memCases (r hr : Ident) (ps : Array (TSyntax `term)) (n : Nat := 0) :
    TacticM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  if n < ps.size then
    let rest ← memCases r hr ps (n+1)
    let he := mkIdent `__pts_pl_eq
    `(tacticSeq| rcases $hr:term with $he:ident | $hr:ident
                 · subst $r:ident
                   exact $(ps[n]!)
                 · $rest)
  else `(tacticSeq| cases $hr:term)

partial def formulaProof (l e : Lean.Expr) : MetaM Lean.Expr := do
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.getAppFn.isConstOf ``PureTypeSystem.Labelled.LogicSetup.Formula then
        if ← isDefEq ty.getAppArgs.back! e then return decl.toExpr
  let args := e.getAppArgs
  let nm := e.getAppFn.constName?
  let unary (n : Name) : MetaM Lean.Expr := do
    mkAppM n #[l, ← formulaProof l args.back!]
  let binary (n : Name) : MetaM Lean.Expr := do
    mkAppM n #[l, ← formulaProof l args[args.size-2]!, ← formulaProof l args.back!]
  match nm with
  | some ``PureTypeSystem.Labelled.LogicSetup.bottom
  | some ``PureTypeSystem.Labelled.LogicCode.bottom => mkAppM ``PureTypeSystem.Labelled.LogicSetup.bottom_formula #[l]
  | some ``PureTypeSystem.Labelled.LogicSetup.top
  | some ``PureTypeSystem.Labelled.LogicCode.top => mkAppM ``PureTypeSystem.Labelled.LogicSetup.top_formula #[l]
  | some ``PureTypeSystem.Labelled.LogicSetup.imp
  | some ``PureTypeSystem.Labelled.LogicCode.imp => binary ``PureTypeSystem.Labelled.LogicSetup.imp_formula
  | some ``PureTypeSystem.Labelled.LogicSetup.neg
  | some ``PureTypeSystem.Labelled.LogicCode.neg => unary ``PureTypeSystem.Labelled.LogicSetup.neg_formula
  | some ``PureTypeSystem.Labelled.LogicSetup.conj
  | some ``PureTypeSystem.Labelled.LogicCode.conj => binary ``PureTypeSystem.Labelled.LogicSetup.conj_formula
  | some ``PureTypeSystem.Labelled.LogicSetup.disj
  | some ``PureTypeSystem.Labelled.LogicCode.disj => binary ``PureTypeSystem.Labelled.LogicSetup.disj_formula
  | some ``PureTypeSystem.Labelled.LogicSetup.iff
  | some ``PureTypeSystem.Labelled.LogicCode.iff => binary ``PureTypeSystem.Labelled.LogicSetup.iff_formula
  | some ``PureTypeSystem.Labelled.LogicCode.cond =>
    mkAppM ``PureTypeSystem.Labelled.LogicSetup.cond_formula #[l,
      ← formulaProof l args[args.size-3]!, ← formulaProof l args[args.size-2]!, ← formulaProof l args.back!]
  | _ => throwError "No formula evidence for {e}"

elab "pts_pl " L:term " using " "[" ps:term,* "]" : tactic => withMainContext do
  let l ← Term.elabTerm L none
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let mut proofs : Array (TSyntax `term) := #[]
  let mut fs : Array Lean.Expr := #[]
  for p in ps.getElems do
    let pe ← Term.elabTerm p none
    let ty ← instantiateMVars (← inferType pe)
    let args := ty.getAppArgs
    if ty.getAppFn.isConstOf ``PureTypeSystem.Labelled.Proves then
      proofs := proofs.push p
      fs := fs.push args[args.size-1]!
    else if ty.getAppFn.isConstOf ``PureTypeSystem.Labelled.Equivalent then
      let a := args[args.size-2]!
      let b := args[args.size-1]!
      let iff ← mkAppM ``PureTypeSystem.Labelled.LogicSetup.iff #[l,a,b]
      fs := fs.push iff
      let fp ← mkAppM ``PureTypeSystem.Labelled.LogicSetup.iff_of_equivalent
        #[l, ← formulaProof l a, ← formulaProof l b, pe]
      proofs := proofs.push (← Term.exprToSyntax fp)
    else throwError "pts_pl input is neither Proves nor Equivalent: {ty}"
  unless target.getAppFn.isConstOf ``PureTypeSystem.Labelled.Proves do
    throwError "pts_pl expects a Proves goal; use equivalent_of_iff first: {target}"
  let goalFormula := target.getAppArgs.back!
  let ((hs,q),atoms) ← (do
    let hs ← fs.mapM reify
    let q ← reify goalFormula
    pure (hs,q)).run #[]
  let hsyntax := Syntax.TSepArray.ofElems (← hs.mapM (fun n => n.syntax))
  let qsyntax ← q.syntax
  let body ← atomFunction atoms L
  let a ← `(fun i : Nat => $body)
  let ha ← `(by
    have hb := ($L).bottom_formula
    intro i
    try dsimp only
    split_ifs <;> solve_by_elim [($L).imp_formula,($L).neg_formula,($L).conj_formula,($L).disj_formula,($L).iff_formula,($L).cond_formula,($L).bottom_formula,($L).top_formula])
  let v := mkIdent `__pts_pl_v
  let hr := mkIdent `__pts_pl_mem
  let hv ← `(by
    intro $v:ident
    simp only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.eval,
      Bool.or_eq_true_eq_eq_true_or_eq_true,Bool.or_eq_false_eq_eq_false_and_eq_false,
      Bool.not_eq_true_eq_eq_false,Bool.not_eq_false_eq_eq_true,
      Bool.true_eq_false_eq_False,Bool.false_eq_true_eq_False,
      eq_self_iff_true,← Bool.eq_false_eq_not_eq_true]
    tauto)
  let r := mkIdent `__pts_pl_R
  let mem ← memCases r hr proofs
  let mt ← `(tactic| ($mem:tacticSeq))
  let hp ← `(by intro $r:ident $hr:ident; simp only [List.mem_cons,List.not_mem_nil] at $hr:ident; $mt)
  evalTactic (← `(tactic| refine ($L).propositional_consequence $a ?_ [$hsyntax,*] $qsyntax ?_ ?_))
  evalTactic (← `(tactic| exact $ha))
  evalTactic (← `(tactic| exact $hv))
  evalTactic (← `(tactic| exact $hp))
end PTSPropositional

end OAI
