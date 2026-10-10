import OAI.ModelTheory.Choiceless.Hereditary

namespace OAI

noncomputable section

namespace CPTSeparation.Forms

open Classical Counting Hereditary

open scoped BigOperators

private theorem card_eq_mul_fiber {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (y₀ : Y)
    (h : ∀ y, Fintype.card {x // f x = y} = Fintype.card {x // f x = y₀}) :
    Fintype.card X = Fintype.card Y * Fintype.card {x // f x = y₀} := by
  calc
    Fintype.card X = Fintype.card (Σ y, {x // f x = y}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ y, Fintype.card {x // f x = y} := Fintype.card_sigma
    _ = _ := by simp only [h,Finset.sum_const,Finset.card_univ,smul_eq_mul]

private theorem card_eq_of_uniform_fibers {X X' Y Y' : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (f : X → Y) (f' : X' → Y') (y : Y) (y' : Y')
    (hx : Fintype.card X = Fintype.card X')
    (hf : ∀ z, Fintype.card {x // f x = z} = Fintype.card {x // f x = y})
    (hf' : ∀ z, Fintype.card {x // f' x = z} = Fintype.card {x // f' x = y'})
    (hy : 0 < Fintype.card {x // f x = y})
    (he : Fintype.card {x // f x = y} = Fintype.card {x // f' x = y'}) :
    Fintype.card Y = Fintype.card Y' := by
  have h := (card_eq_mul_fiber f y hf).symm.trans
    (hx.trans (card_eq_mul_fiber f' y' hf'))
  rw [←he] at h
  exact Nat.eq_of_mul_eq_mul_right hy h

private theorem range_card_mul_fiber {X Y : Type*} [Fintype X]
    (f : X → Y) (x₀ : X)
    (h : ∀ x, Nat.card {z // f z = f x} = Nat.card {z // f z = f x₀}) :
    Fintype.card X = Nat.card (Set.range f) * Nat.card {z // f z = f x₀} := by
  let := (Set.finite_range f).fintype
  let fR : X → Set.range f := fun x => ⟨f x,⟨x,rfl⟩⟩
  have k (y : Set.range f) : Nat.card {x // fR x = y} =
      Nat.card {z // f z = f x₀} := by
    have hp (x : X) : fR x = y ↔ f x = y.1 := Subtype.ext_iff
    rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
    obtain ⟨x,hx⟩ := y.2
    rw [←hx]
    exact h x
  have hh := card_eq_mul_fiber fR (fR x₀) (fun y => by
    simpa only [←Nat.card_eq_fintype_card] using (k y).trans (k (fR x₀)).symm)
  have hh' : Nat.card X = Nat.card (Set.range f) * Nat.card {x // fR x = fR x₀} := by
    simpa only [←Nat.card_eq_fintype_card] using hh
  rw [k] at hh'
  simpa only [←Nat.card_eq_fintype_card] using hh'

variable {R I A B P : Type*} [finiteI : Fintype I] [DecidableEq I]

variable [finiteA : Fintype A] [Fintype B] [nonemptyA : Nonempty A] [Nonempty B] [finiteP : Fintype P]

variable {s : ℕ}

def Molecules (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) :=
  {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ}

instance (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) : Fintype (Molecules S ep p τ) :=
  inferInstanceAs (Fintype {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ})

def labelValues (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Set (HF A) :=
  Set.range (fun a : Molecules S ep p τ => Form.value S e2 φ a.1)

instance (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Fintype (labelValues S ep e2 p τ φ) :=
  (Set.finite_range _).fintype

section Group

variable {G : Type*} [Group G] [MulAction G A]

variable (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (p : P → A) (τ : Set (Formula R I))

omit R I A P s G S ep hAut p in
private theorem mol_type_smul.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A) (g : G) (hp : ∀ i, g • p i = p i) (a : Fin s → A) :
    tupleType S ep (Sum.elim p (fun i => g • a i)) = tupleType S ep (Sum.elim p a) := by
  have hh := tupleType_iso S S ep (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm)
    (Sum.elim p a)
  have hh' : (MulAction.toPerm g) ∘ Sum.elim p a = Sum.elim p (fun i => g • a i) := by
    funext i; rcases i with i|i
    · exact hp i
    · rfl
  rw [hh'] at hh
  exact hh.symm

def moleculesPerm (g : G) (hp : ∀ i, g • p i = p i) :
    Molecules S ep p τ ≃ Molecules S ep p τ :=
  (Equiv.piCongrRight (fun _ : Fin s => MulAction.toPerm g)).subtypeEquiv
    (fun a => by
      change tupleType S ep (Sum.elim p a) = τ ↔
        tupleType S ep (Sum.elim p (fun i => g • a i)) = τ
      rw [mol_type_smul S ep hAut p g hp a])

include hAut in

omit R I A P s G S ep e2 hAut p τ in
theorem uniform_value_fibers.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A)
    (τ : Set (Counting.Formula R I))
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (a a' : Molecules S ep p τ) :
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} =
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a'.1} := by
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p a'.1) (a.2.trans a'.2.symm)
  have hp : ∀ i, g • p i = p i := fun i => hg (.inl i)
  have ha : (fun i => g • a.1 i) = a'.1 := funext (fun i => hg (.inr i))
  let f := moleculesPerm S ep hAut p τ g hp
  have hv (b : Molecules S ep p τ) :
      Form.value S e2 φ (f b).1 = g • Form.value S e2 φ b.1 := by
    exact (value_smul S e2 hAut g φ b.1).symm
  have hv' : Form.value S e2 φ a'.1 = g • Form.value S e2 φ a.1 := by
    rw [←ha]
    exact (value_smul S e2 hAut g φ a.1).symm
  apply Fintype.card_congr
  apply f.subtypeEquiv
  intro b
  rw [hv,hv']
  exact (MulAction.injective g).eq_iff.symm

omit R I A P s G S ep e2 hAut p τ in
private theorem label_orbit.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A)
    (τ : Set (Counting.Formula R I))
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (x y : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hy : y ∈ labelValues S ep e2 p τ φ) :
    ∃ g : G, (∀ i, g • p i = p i) ∧ g • x = y := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p b.1) (a.2.trans b.2.symm)
  refine ⟨g,fun i => hg (.inl i),?_⟩
  rw [value_smul S e2 hAut]
  exact congrArg (Form.value S e2 φ) (funext (fun i => hg (.inr i)))

omit R I A P s G S ep e2 hAut p τ in
private theorem label_smul_mem.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A)
    (τ : Set (Counting.Formula R I)) (g : G) (hp : ∀ i, g • p i = p i)
    (φ : Form (Fin s) (Set (Formula R I))) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) : g • x ∈ labelValues S ep e2 p τ φ := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨moleculesPerm S ep hAut p τ g hp a,?_⟩
  exact (value_smul S e2 hAut g φ a.1).symm

include hAut in

theorem label_partition
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (σ : Set (Formula R I)) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hx' : x ∈ labelValues S ep e2 p σ ψ) :
    labelValues S ep e2 p τ φ = labelValues S ep e2 p σ ψ := by
  ext y
  constructor
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p τ hHom φ x y hx hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p σ g hp ψ x hx'
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p σ hHom ψ x y hx' hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p τ g hp φ x hx

end Group

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

private def skipMiddle : P ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inl (Function.Embedding.refl _)

private def lastTwo : Fin s ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inr (Function.Embedding.refl _)

omit A P s in
@[simp] private theorem elim_skipMiddle.{uDecl3, uDecl5}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ} (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ skipMiddle = Sum.elim p b := by
  funext j; cases j <;> rfl

omit A P s in
@[simp] private theorem elim_lastTwo.{uDecl3, uDecl5}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ} (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ lastTwo = Sum.elim a b := by
  funext j; cases j <;> rfl

include epp e3 e4 in

theorem value_fiber_equiv (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nonempty ({b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} ≃
    {b : Molecules T ep q τ // Form.value T e2 φ b.1 = Form.value T e2 φ a'.1}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T ep epp
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  have htype (b : Fin s → A) : tupleType S ep (Sum.elim p b) =
      tupleType T ep (Sum.elim q (f b)) := by
    have hh := tupleType_project S T epp ep skipMiddle _ _ (hf b)
    simpa only [elim_skipMiddle] using hh
  have hval (b : Fin s → A) : Form.value S e2 φ b = Form.value S e2 φ a.1 ↔
      Form.value T e2 φ (f b) = Form.value T e2 φ a'.1 := by
    have hh := tupleType_project S T epp e2 lastTwo _ _ (hf b)
    simp only [elim_lastTwo] at hh
    simpa only [eq_comm] using equality_transfer S T e2 e3 e4 φ φ a.1 b a'.1 (f b) hh
  let F : {b : Fin s → A // tupleType S ep (Sum.elim p b) = τ ∧
      Form.value S e2 φ b = Form.value S e2 φ a.1} ≃
      {b : Fin s → B // tupleType T ep (Sum.elim q b) = τ ∧
      Form.value T e2 φ b = Form.value T e2 φ a'.1} := f.subtypeEquiv (fun b => show
      (tupleType S ep (Sum.elim p b) = τ ∧ Form.value S e2 φ b = Form.value S e2 φ a.1) ↔
      (tupleType T ep (Sum.elim q (f b)) = τ ∧ Form.value T e2 φ (f b) = Form.value T e2 φ a'.1)
    from and_congr (by rw [htype b]) (hval b))
  exact ⟨(Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (F.trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)⟩

include epp e3 e4 in

theorem label_overlap_transfer (e0 : P ↪ I) (p : P → A) (q : P → B)
    (hp : tupleType S e0 p = tupleType T e0 q)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (τ σ : Set (Formula R I))
    (hx : ∃ x, x ∈ labelValues S ep e2 p τ φ ∧ x ∈ labelValues S ep e2 p σ ψ) :
    ∃ y, y ∈ labelValues T ep e2 q τ φ ∧ y ∈ labelValues T ep e2 q σ ψ := by
  obtain ⟨x,⟨a,ha⟩,⟨b,hb⟩⟩ := hx
  obtain ⟨a',ha'⟩ := tupleType_append S T e0 ep p q a.1 hp
  obtain ⟨b',hb'⟩ := tupleType_append S T ep epp
    (Sum.elim p a.1) (Sum.elim q a') b.1 ha'
  have ht := tupleType_project S T epp ep skipMiddle _ _ hb'
  simp only [elim_skipMiddle] at ht
  have he := tupleType_project S T epp e2 lastTwo _ _ hb'
  simp only [elim_lastTwo] at he
  have hv := (equality_transfer S T e2 e3 e4 φ ψ a.1 b.1 a' b' he).mp (ha.trans hb.symm)
  refine ⟨Form.value T e2 φ a',?_,?_⟩
  · exact ⟨⟨a',ha'.symm.trans a.2⟩,rfl⟩
  · exact ⟨⟨b',ht.symm.trans b.2⟩,hv.symm⟩

include epp e3 e4 in

theorem label_values_card
    {G H : Type*} [Group G] [MulAction G A] [Group H] [MulAction H B]
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nat.card (labelValues S ep e2 p τ φ) = Nat.card (labelValues T ep e2 q τ φ) := by
  let va : Molecules S ep p τ → HF A := fun b => Form.value S e2 φ b.1
  let vb : Molecules T ep q τ → HF B := fun b => Form.value T e2 φ b.1
  have ha := range_card_mul_fiber va a (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers S ep e2 hAutA p τ hHomA φ b a)
  have hb := range_card_mul_fiber vb a' (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers T ep e2 hAutB q τ hHomB φ b a')
  let e0 := Function.Embedding.inl.trans ep
  have hp := tupleType_project S T ep e0 Function.Embedding.inl
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  change tupleType S e0 p = tupleType T e0 q at hp
  obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp τ
  have hn : Fintype.card (Molecules S ep p τ) = Fintype.card (Molecules T ep q τ) :=
    Fintype.card_congr f
  obtain ⟨fv⟩ := value_fiber_equiv S T ep epp e2 e3 e4 p q τ φ a a'
  have he : Nat.card {b // va b = va a} = Nat.card {b // vb b = vb a'} :=
    Nat.card_congr fv
  have hpos : 0 < Nat.card {b // va b = va a} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨a,rfl⟩⟩
  have hc := ha.symm.trans (hn.trans hb)
  rw [←he] at hc
  have hh := Nat.eq_of_mul_eq_mul_right hpos hc
  simpa only [←Nat.card_eq_fintype_card,labelValues,va,vb] using hh

end CPTSeparation.Forms

namespace CPTSeparation

open Classical

private def cellSetoid {L X : Type*} (C : L → Set X) : Setoid L :=
  ⟨fun l k => C l = C k,⟨fun _ => rfl,Eq.symm,Eq.trans⟩⟩

theorem glue_finite_cells {L X Y : Type*} (C : L → Set X) (D : L → Set Y)
    (coverC : ∀ x, ∃ l, x ∈ C l) (coverD : ∀ y, ∃ l, y ∈ D l)
    (partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k)
    (partD : ∀ l k y, y ∈ D l → y ∈ D k → D l = D k)
    (same : ∀ l k, C l = C k ↔ D l = D k)
    (finC : ∀ l, (C l).Finite) (finD : ∀ l, (D l).Finite)
    (card : ∀ l, Nat.card (C l) = Nat.card (D l)) :
    ∃ f : X ≃ Y, ∀ x, ∃ l, x ∈ C l ∧ f x ∈ D l := by
  let Q := Quotient (cellSetoid C)
  let lc : X → L := fun x => (coverC x).choose
  let ld : Y → L := fun y => (coverD y).choose
  have hc (x : X) : x ∈ C (lc x) := (coverC x).choose_spec
  have hd (y : Y) : y ∈ D (ld y) := (coverD y).choose_spec
  let c : X → Q := fun x => Quotient.mk _ (lc x)
  let d : Y → Q := fun y => Quotient.mk _ (ld y)
  have ce (x : X) (q : Q) : c x = q ↔ x ∈ C q.out := by
    constructor
    · intro h
      have he : C (lc x) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←he]; exact hc x
    · intro h
      have he := partC (lc x) q.out x (hc x) h
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have de (y : Y) (q : Q) : d y = q ↔ y ∈ D q.out := by
    constructor
    · intro h
      have he : C (ld y) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←(same _ _).mp he]; exact hd y
    · intro h
      have he := (same _ _).mpr (partD (ld y) q.out y (hd y) h)
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have ef (q : Q) : Nonempty ({x // c x = q} ≃ {y // d y = q}) := by
    let := (finC q.out).fintype
    let := (finD q.out).fintype
    have hcard : Fintype.card (C q.out) = Fintype.card (D q.out) := by
      simpa only [Nat.card_eq_fintype_card] using card q.out
    let e := Fintype.equivOfCardEq hcard
    exact ⟨(Equiv.subtypeEquivRight (fun x => ce x q)).trans
      (e.trans (Equiv.subtypeEquivRight (fun y => de y q)).symm)⟩
  let F := Equiv.ofFiberEquiv (fun q => Classical.choice (ef q))
  refine ⟨F,fun x => ⟨(c x).out,(ce x (c x)).mp rfl,?_⟩⟩
  apply (de (F x) (c x)).mp
  exact Equiv.ofFiberEquiv_map _ x

end CPTSeparation

namespace CPTSeparation.Forms

section

open Classical Counting Hereditary

variable {R I A B P G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype P]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

abbrev Domain (G : Type*) [Group G] [MulAction G A] (s : ℕ) :=
  {x : HF A // HereditarilySupported (G := G) s x}

def Cell (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Set (Domain (A := A) G s) :=
  {x | x.1 ∈ labelValues S ep e2 p τ φ}

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I) (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

def cellEquiv (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Cell (G := G) S ep e2 p φ τ ≃ labelValues S ep e2 p τ φ :=
  Equiv.subtypeSubtypeEquivSubtype
    (p := HereditarilySupported (G := G) s)
    (q := fun x => x ∈ labelValues S ep e2 p τ φ) (fun hx => by
    obtain ⟨a,rfl⟩ := hx
    exact value_hereditarily_supported S e2 hAutA φ a.1)

include hAutA in
private theorem cell_finite (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    (Cell (G := G) S ep e2 p φ τ).Finite := by
  let := Fintype.ofEquiv (labelValues S ep e2 p τ φ) (cellEquiv S ep e2 hAutA p φ τ).symm
  exact Set.toFinite _

include hAutA hAutB epp e3 e4 in

theorem supported_domain_bijection (hs : 0 < s) (e0 : P ↪ I)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (hp : tupleType S e0 p = tupleType T e0 q) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, ∃ b : Fin s → B,
        Form.value S e2 φ a = x.1 ∧ Form.value T e2 φ b = (f x).1 ∧
        tupleType S ep (Sum.elim p a) = tupleType T ep (Sum.elim q b) := by
  let L := {l : Form (Fin s) (Set (Formula R I)) × Set (Formula R I) //
    Nonempty (Molecules S ep p l.2)}
  let C : L → Set (Domain (A := A) G s) := fun l => Cell S ep e2 p l.1.1 l.1.2
  let D : L → Set (Domain (A := B) H s) := fun l => Cell T ep e2 q l.1.1 l.1.2
  have nonemptyB (l : L) : Nonempty (Molecules T ep q l.1.2) := by
    obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp l.1.2
    exact Nonempty.map f l.2
  have coverC : ∀ x, ∃ l, x ∈ C l := by
    intro x
    obtain ⟨φ,a,ha⟩ := representation S e2 hAutA hs hHomA2 x.1 x.2
    let τ := tupleType S ep (Sum.elim p a)
    let l : L := ⟨(φ,τ),⟨⟨a,rfl⟩⟩⟩
    exact ⟨l,⟨⟨a,rfl⟩,ha⟩⟩
  have coverD : ∀ y, ∃ l, y ∈ D l := by
    intro y
    obtain ⟨φ,b,hb⟩ := representation T e2 hAutB hs hHomB2 y.1 y.2
    obtain ⟨a,ha⟩ := tupleType_append T S e0 ep q p b hp.symm
    let τ := tupleType T ep (Sum.elim q b)
    let l : L := ⟨(φ,τ),⟨⟨a,ha.symm⟩⟩⟩
    exact ⟨l,⟨⟨b,rfl⟩,hb⟩⟩
  have partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k := by
    intro l k x hx hk
    have hh := label_partition S ep e2 hAutA p l.1.2 hHomA l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF A) => {x : Domain G s | x.1 ∈ Z}) hh
  have partD : ∀ l k x, x ∈ D l → x ∈ D k → D l = D k := by
    intro l k x hx hk
    have hh := label_partition T ep e2 hAutB q l.1.2 hHomB l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF B) => {x : Domain H s | x.1 ∈ Z}) hh
  have same : ∀ l k, C l = C k ↔ D l = D k := by
    intro l k
    constructor
    · intro he
      obtain ⟨a⟩ := l.2
      let x : Domain G s := ⟨Form.value S e2 l.1.1 a.1,
        value_hereditarily_supported S e2 hAutA _ _⟩
      have hx : x ∈ C l := ⟨a,rfl⟩
      have hk : x ∈ C k := he ▸ hx
      obtain ⟨y,hy,hy'⟩ := label_overlap_transfer S T ep epp e2 e3 e4 e0 p q hp
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨x.1,hx,hk⟩
      have hsupp : HereditarilySupported (G := H) s y := by
        obtain ⟨b,rfl⟩ := hy
        exact value_hereditarily_supported T e2 hAutB _ _
      exact partD l k ⟨y,hsupp⟩ hy hy'
    · intro he
      obtain ⟨b⟩ := nonemptyB l
      let y : Domain H s := ⟨Form.value T e2 l.1.1 b.1,
        value_hereditarily_supported T e2 hAutB _ _⟩
      have hy : y ∈ D l := ⟨b,rfl⟩
      have hk : y ∈ D k := he ▸ hy
      obtain ⟨x,hx,hx'⟩ := label_overlap_transfer T S ep epp e2 e3 e4 e0 q p hp.symm
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨y.1,hy,hk⟩
      have hsupp : HereditarilySupported (G := G) s x := by
        obtain ⟨a,rfl⟩ := hx
        exact value_hereditarily_supported S e2 hAutA _ _
      exact partC l k ⟨x,hsupp⟩ hx hx'
  have card : ∀ l, Nat.card (C l) = Nat.card (D l) := by
    intro l
    obtain ⟨a⟩ := l.2
    obtain ⟨b⟩ := nonemptyB l
    have hh := label_values_card S T ep epp e2 e3 e4 hAutA hAutB hHomA hHomB
      p q l.1.2 l.1.1 a b
    have he := Nat.card_congr (cellEquiv S ep e2 hAutA p l.1.1 l.1.2)
    have hf := Nat.card_congr (cellEquiv T ep e2 hAutB q l.1.1 l.1.2)
    exact he.trans (hh.trans hf.symm)
  obtain ⟨f,hf⟩ := CPTSeparation.glue_finite_cells C D coverC coverD partC partD same
    (fun l => cell_finite S ep e2 hAutA p l.1.1 l.1.2)
    (fun l => cell_finite T ep e2 hAutB q l.1.1 l.1.2) card
  refine ⟨f,fun x => ?_⟩
  obtain ⟨l,⟨a,ha⟩,⟨b,hb⟩⟩ := hf x
  exact ⟨l.1.1,a.1,b.1,ha,hb,a.2.trans b.2.symm⟩

end

open Classical Counting Hereditary

variable {R I A B V G H : Type*}

variable [finiteI : Fintype I] [DecidableEq I] [finiteA : Fintype A] [Fintype B]

variable [nonemptyA : Nonempty A] [Nonempty B] [finiteV : Fintype V] [decidableV : DecidableEq V]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

inductive HFRelation (R : Type*)
  | mem | atom | base (r : R)

def hfStructure (S : Structure R A) : Structure (HFRelation R) (Domain (A := A) G s) where
  rel
    | .mem, x, y => x.1 ∈ y.1
    | .atom, x, _ => isSet x.1 = false
    | .base r, x, y => ∃ a b, x.1 = Hereditary.atom a ∧ y.1 = Hereditary.atom b ∧ S.rel r a b

def Represented (S : Structure R A) (T : Structure R B)
    (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) : Prop :=
  ∃ φ : V → Form (Fin s) (Set (Formula R I)), ∃ a : V × Fin s → A,
    ∃ b : V × Fin s → B,
      (∀ i, Form.value S e2 (φ i) (fun j => a (i,j)) = (v i).1) ∧
      (∀ i, Form.value T e2 (φ i) (fun j => b (i,j)) = (w i).1) ∧
      tupleType S ef a = tupleType T ef b

def twoBlocks (i j : V) (h : i ≠ j) : Fin s ⊕ Fin s ↪ V × Fin s where
  toFun := Sum.elim (Prod.mk i) (Prod.mk j)
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp only [Sum.elim_inl,Sum.elim_inr,Prod.mk.injEq] at hab
    · congr 1; exact hab.2
    · exact (h hab.1).elim
    · exact (h hab.1.symm).elim
    · congr 1; exact hab.2

omit A V s in
@[simp] theorem comp_twoBlocks.{uDecl3, uDecl5}
    {A : Type uDecl3}
    {V : Type uDecl5}
    [Fintype A]
    [Nonempty A]
    [Fintype V]
    [DecidableEq V]
    {s : ℕ} (i j : V) (h : i ≠ j) (a : V × Fin s → A) :
    a ∘ twoBlocks i j h = Sum.elim (fun k => a (i,k)) (fun k => a (j,k)) := by
  funext x; cases x <;> rfl

def splitBlock (i : V) : ({j : V // j ≠ i} × Fin s) ⊕ Fin s ≃ V × Fin s where
  toFun := Sum.elim (fun x => (x.1.1,x.2)) (fun j => (i,j))
  invFun := fun x => if h : x.1 = i then .inr x.2 else .inl (⟨x.1,h⟩,x.2)
  left_inv := by
    intro x; cases x with
    | inl x => simp [x.1.2]
    | inr j => simp
  right_inv := by
    intro x; by_cases h : x.1 = i
    · simp [h]; exact Prod.ext h.symm rfl
    · simp [h]

variable (S : Structure R A) (T : Structure R B)

variable (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

include e3 e4 in
theorem represented_equal (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : v i = v j ↔ w i = w j := by
  by_cases hij : i = j
  · subst j; simp
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := equality_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb,Subtype.ext_iff] using he

include e3 e4 in
theorem represented_mem (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : (v i).1 ∈ (v j).1 ↔ (w i).1 ∈ (w j).1 := by
  by_cases hij : i = j
  · subst j
    exact iff_of_false (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
      (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := membership_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb] using he

omit R I A B V G H s S T ef e2 in
theorem represented_atom.{uDecl1, uDecl2, uDecl3, uDecl4, uDecl5, uDecl6, uDecl7}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {B : Type uDecl4}
    {V : Type uDecl5}
    {G : Type uDecl6}
    {H : Type uDecl7}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Fintype B]
    [Nonempty A]
    [Nonempty B]
    [Fintype V]
    [DecidableEq V]
    [Group G]
    [MulAction G A]
    [Group H]
    [MulAction H B]
    {s : ℕ}
    (S : Counting.Structure R A)
    (T : Counting.Structure R B)
    (ef : V × Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) : isSet (v i).1 = false ↔ isSet (w i).1 = false := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  rw [←ha i,←hb i]
  cases φ i <;> simp

omit R I A s S e2 in
private theorem base_value.{uDecl1, uDecl2, uDecl3}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I) (φ ψ : Form (Fin s) (Set (Formula R I)))
    (a b : Fin s → A) (r : R) :
    (∃ x y, Form.value S e2 φ a = Hereditary.atom x ∧
      Form.value S e2 ψ b = Hereditary.atom y ∧ S.rel r x y) ↔
    match φ,ψ with
    | .atom i, .atom j => S.rel r (a i) (b j)
    | _, _ => False := by
  have hn (n : ℕ) (child : Fin n → Form (Fin s) (Set (Formula R I)))
      (label : Fin n → Set (Formula R I)) (c : Fin s → A) (x : A) :
      Form.value S e2 (.set n child label) c ≠ Hereditary.atom x := by
    intro h; have hh := congrArg isSet h; simp at hh
  cases φ <;> cases ψ <;> simp [Form.value_atom,atom_injective.eq_iff,hn]

omit R I A B V G H s S T ef e2 in
theorem represented_base.{uDecl1, uDecl2, uDecl3, uDecl4, uDecl5, uDecl6, uDecl7}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {B : Type uDecl4}
    {V : Type uDecl5}
    {G : Type uDecl6}
    {H : Type uDecl7}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Fintype B]
    [Nonempty A]
    [Nonempty B]
    [Fintype V]
    [DecidableEq V]
    [Group G]
    [MulAction G A]
    [Group H]
    [MulAction H B]
    {s : ℕ}
    (S : Counting.Structure R A)
    (T : Counting.Structure R B)
    (ef : V × Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (r : R) (i j : V) :
    (hfStructure S).rel (.base r) (v i) (v j) ↔ (hfStructure T).rel (.base r) (w i) (w j) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  change (∃ x y, (v i).1 = Hereditary.atom x ∧ (v j).1 = Hereditary.atom y ∧ S.rel r x y) ↔
    (∃ x y, (w i).1 = Hereditary.atom x ∧ (w j).1 = Hereditary.atom y ∧ T.rel r x y)
  rw [←ha i,←ha j,←hb i,←hb j,base_value S e2,base_value T e2]
  cases hi : φ i with
  | set n child label => simp
  | atom k =>
    cases hj : φ j with
    | set n child label => simp
    | atom l =>
      have he := (typeOf_eq_iff S T (tupleNames ef) _ _).mp ht
        (.relation r (ef (i,k)) (ef (j,l))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply] using he

omit V s in
@[simp] theorem splitBlock_symm_new.{uDecl5}
    {V : Type uDecl5}
    [Fintype V]
    [DecidableEq V]
    {s : ℕ} (i : V) (k : Fin s) :
    (splitBlock (s := s) i).symm (i,k) = .inr k := by simp [splitBlock]

omit V s in
@[simp] theorem splitBlock_symm_old.{uDecl5}
    {V : Type uDecl5}
    [Fintype V]
    [DecidableEq V]
    {s : ℕ} (i j : V) (h : j ≠ i) (k : Fin s) :
    (splitBlock (s := s) i).symm (j,k) = .inl (⟨j,h⟩,k) := by simp [splitBlock,h]

omit R I A G in
private theorem homogeneity_reindex.{uDecl1, uDecl2, uDecl3, uDecl6, uDecl8, uDecl9}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {G : Type uDecl6}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Group G]
    [MulAction G A] {J : Type uDecl8} {K : Type uDecl9} [Fintype J] [Fintype K]
    (S : Structure R A) (e : J ↪ I) (f : K ↪ I) (u : K ≃ J)
    (hh : ∀ a b : J → A, tupleType S e a = tupleType S e b →
      ∃ g : G, ∀ j, g • a j = b j) :
    ∀ a b : K → A, tupleType S f a = tupleType S f b → ∃ g : G, ∀ j, g • a j = b j := by
  intro a b hab
  have h := tupleType_project S S f e u.symm.toEmbedding a b hab
  obtain ⟨g,hg⟩ := hh _ _ h
  exact ⟨g,fun j => by simpa using hg (u j)⟩

variable (eplus : (V × Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

include eplus e3 e4 hAutA hAutB in

theorem represented_extension (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, Represented S T ef e2 (Function.update v i x) (Function.update w i (f x)) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  let P := {j : V // j ≠ i} × Fin s
  let u : P ⊕ Fin s ≃ V × Fin s := splitBlock i
  let ep := u.toEmbedding.trans ef
  let epp := (Equiv.sumCongr u (Equiv.refl (Fin s))).toEmbedding.trans eplus
  let e0 := Function.Embedding.inl.trans ep
  let keep : P ↪ V × Fin s := Function.Embedding.inl.trans u.toEmbedding
  let p : P → A := a ∘ keep
  let q : P → B := b ∘ keep
  have hp : tupleType S e0 p = tupleType T e0 q :=
    tupleType_project S T ef e0 keep a b ht
  have homA := homogeneity_reindex S ef ep u hHomA
  have homB := homogeneity_reindex T ef ep u hHomB
  obtain ⟨f,hf⟩ := supported_domain_bijection S T ep epp e2 e3 e4
    hAutA hAutB hs e0 hHomA2 hHomB2 homA homB p q hp
  refine ⟨f,fun x => ?_⟩
  obtain ⟨ψ,c,d,hc,hd,hcd⟩ := hf x
  let a' := Sum.elim p c ∘ u.symm
  let b' := Sum.elim q d ∘ u.symm
  refine ⟨Function.update φ i ψ,a',b',?_,?_,?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [a',u,Function.comp_def,splitBlock] using hc
    · simpa [a',u,p,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using ha j
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [b',u,Function.comp_def,splitBlock] using hd
    · simpa [b',u,q,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using hb j
  · exact tupleType_project S T ep ef u.symm.toEmbedding _ _ hcd

include eplus e3 e4 hAutA hAutB in

theorem supported_eval_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (φ : Formula (HFRelation R) V)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  apply Formula.eval_of_bijectionSystem (hfStructure S) (hfStructure T)
    (Represented S T ef e2) _ _ _ φ v w h
  · exact represented_equal S T ef e2 e3 e4
  · intro v w h r i j
    cases r with
    | mem => exact represented_mem S T ef e2 e3 e4 v w h i j
    | atom => exact represented_atom S T ef e2 v w h i
    | base r => exact represented_base S T ef e2 v w h r i j
  · exact represented_extension S T ef e2 e3 e4 eplus hAutA hAutB hs
      hHomA2 hHomB2 hHomA hHomB

include eplus e3 e4 hAutA hAutB in

theorem supported_sentences_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim)
    (φ : Formula (HFRelation R) V) (hφ : φ.free = ∅)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  let a : V × Fin s → A := fun _ => Classical.choice inferInstance
  have he : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I)
      (a ∘ (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s)) =
        tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim := by
    convert hbase using 1
    congr 1; funext x; exact x.elim
  obtain ⟨b,_,hab⟩ := tupleType_extend S T
    (Function.Embedding.ofIsEmpty : Empty ↪ I) ef
    (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s) a Empty.elim he
  let emptyForm : Form (Fin s) (Set (Formula R I)) := .set 0 Fin.elim0 Fin.elim0
  let v' : V → Domain (A := A) G s := fun i =>
    ⟨Form.value S e2 emptyForm (fun j => a (i,j)),
      value_hereditarily_supported S e2 hAutA emptyForm _⟩
  let w' : V → Domain (A := B) H s := fun i =>
    ⟨Form.value T e2 emptyForm (fun j => b (i,j)),
      value_hereditarily_supported T e2 hAutB emptyForm _⟩
  have hr : Represented S T ef e2 v' w' :=
    ⟨(fun _ => emptyForm),a,b,(fun _ => rfl),(fun _ => rfl),hab⟩
  have hh := supported_eval_transfer S T ef e2 e3 e4 eplus hAutA hAutB hs
    hHomA2 hHomB2 hHomA hHomB φ v' w' hr
  exact (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)).trans
    (hh.trans (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)))

def namesOfCard {J : Type*} [Fintype J] {M : ℕ} (h : Fintype.card J ≤ M) : J ↪ Fin M :=
  (Fintype.equivFin J).toEmbedding.trans (Fin.castLEEmb h)

def HomogeneousThrough (S : Structure R A) (G : Type*) [Group G] [MulAction G A]
    (M r : ℕ) : Prop :=
  ∀ k ≤ r, ∀ e : Fin k ↪ Fin M, ∀ a b : Fin k → A,
    tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j

omit R A in
private theorem homogeneous_tuple.{uDecl1, uDecl3, uDecl8, uDecl9}
    {R : Type uDecl1}
    {A : Type uDecl3}
    [Fintype A]
    [Nonempty A] {J : Type uDecl8} [Fintype J] {M r : ℕ}
    (S : Structure R A) (G : Type uDecl9) [Group G] [MulAction G A]
    (h : HomogeneousThrough S G M r) (e : J ↪ Fin M)
    (hc : Fintype.card J ≤ r) :
    ∀ a b : J → A, tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j := by
  exact homogeneity_reindex S ((Fintype.equivFin J).symm.toEmbedding.trans e) e
    (Fintype.equivFin J) (h _ hc _)

theorem hf_transfer {m M : ℕ} (hs : 0 < s) (_ : 0 < m) (hM : 0 < M)
    (hwidth : max 4 (m+1) * s ≤ M)
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : HomogeneousThrough S G M (max 2 m * s))
    (hHomB : HomogeneousThrough T H M (max 2 m * s))
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim)
    (φ : Formula (HFRelation R) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Domain (A := A) G s) (w : Fin m → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  have h4 : 4*s ≤ M := (Nat.mul_le_mul_right s (le_max_left _ _)).trans hwidth
  have hp : (m+1)*s ≤ M := (Nat.mul_le_mul_right s (le_max_right _ _)).trans hwidth
  have h2 : Fintype.card (Fin s ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h3 : Fintype.card ((Fin s ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h4' : Fintype.card (((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have hpf : Fintype.card ((Fin m × Fin s) ⊕ Fin s) ≤ M := by simpa [Nat.add_mul] using hp
  have hfull : Fintype.card (Fin m × Fin s) ≤ M := by simp only [Fintype.card_prod,Fintype.card_fin]; nlinarith
  have hom2 : Fintype.card (Fin s ⊕ Fin s) ≤ max 2 m*s := by
    simpa [two_mul] using Nat.mul_le_mul_right s (le_max_left 2 m)
  have homf : Fintype.card (Fin m × Fin s) ≤ max 2 m*s := by
    simpa using Nat.mul_le_mul_right s (le_max_right 2 m)
  exact supported_sentences_transfer S T (namesOfCard hfull) (namesOfCard h2)
    (namesOfCard h3) (namesOfCard h4') (namesOfCard hpf) hAutA hAutB hs
    (homogeneous_tuple S G hHomA _ hom2) (homogeneous_tuple T H hHomB _ hom2)
    (homogeneous_tuple S G hHomA _ homf) (homogeneous_tuple T H hHomB _ homf)
    hbase φ hφ v w

end CPTSeparation.Forms

namespace CPTSeparation.Hereditary

variable {A G : Type*} [Group G] [MulAction G A]

theorem supports_pad {k s : ℕ} (hks : k ≤ s) (a₀ : A) (alpha : Fin k → A)
    {x : HF A} (h : Supports (G := G) alpha x) : Supported (G := G) s x := by
  classical
  let beta (i : Fin s) : A := if hi : i.val < k then alpha ⟨i.val,hi⟩ else a₀
  refine ⟨beta,?_⟩
  intro g hg
  apply h g
  intro i
  have hi := hg (i.castLE hks)
  simpa only [beta, Fin.val_castLE, dite_eq_left i.isLt] using hi

end CPTSeparation.Hereditary

namespace CPTSeparation.Grid

section

open Support Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] theorem central_smul_HF (k : CentralGroup n) (x : HF (Atom b)) :
    k • x = centralHom k • x := rfl

theorem small_orbit_supported (hn : 1 ≤ n) (x : HF (Atom b))
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (horbit : (Nat.card (MulAction.orbit (BoxGroup n) x) : ℝ) ≤ (N : ℝ)^q) :
    Supported (G := CentralGroup n) ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  classical
  obtain ⟨T,hT,hfix⟩ := small_orbit_support_edges x N hN q hq horbit
  obtain ⟨alpha,ha⟩ := edge_support_tuple (b := b) T x hfix
  have hsupport : Supports (G := CentralGroup n) alpha x := by
    intro k hk
    exact ha k hk
  have hlen : T.card ≤ ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ := by
    exact_mod_cast le_trans hT (Nat.le_ceil _)
  let a₀ : Atom b := zeroEdgeAtom b (ex ⟨0,by omega⟩ 0 0)
  exact supports_pad hlen a₀ alpha hsupport

theorem orbit_card_le_invariant_family (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F) {x : HF (Atom b)} (hx : x ∈ F) :
    Nat.card (MulAction.orbit (BoxGroup n) x) ≤ F.card := by
  classical
  let f : MulAction.orbit (BoxGroup n) x → {y // y ∈ F} := fun y =>
    ⟨y.val,by obtain ⟨g,hg⟩ := y.property; rw [← hg]; exact hF g x hx⟩
  have hf : Function.Injective f := by
    intro a c h
    exact Subtype.ext (congrArg (fun z : {y // y ∈ F} => z.val) h)
  have hn := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hn

theorem invariant_family_hereditarily_supported (hn : 1 ≤ n)
    (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F)
    (htrans : ∀ x ∈ F, ∀ y, y ∈ x → y ∈ F)
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (hsize : (F.card : ℝ) ≤ (N : ℝ)^q) :
    ∀ x ∈ F, HereditarilySupported (G := CentralGroup n)
      ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  intro x hx y hy
  have hymem : y ∈ F := by
    induction hy with
    | refl => exact hx
    | @tail z w hpath hmem ih => exact ih (htrans w hx z hmem)
  apply small_orbit_supported hn y N hN q hq
  exact le_trans (by exact_mod_cast orbit_card_le_invariant_family F hF hymem) hsize

end

open Classical Finset

variable {n M m s : ℕ} {b : Vertex n → Scalar}

theorem atom_nonempty (hn : 1 ≤ n) (b : Vertex n → Scalar) : Nonempty (Atom b) :=
  ⟨.inr ⟨(0,0,0),someConfiguration hn b (0,0,0)⟩⟩

instance atom_nonempty_succ (b : Vertex (n+1) → Scalar) : Nonempty (Atom b) := atom_nonempty (by omega) b

theorem central_analysis_isomorphism (k : CentralGroup n) (r : AnalysisSymbol) (x y : Atom b) :
    (analysisStructure b).rel r (k • x) (k • y) ↔ (analysisStructure b).rel r x y :=
  ((central_atomShift k x).analysisRelation (central_atomShift k y) r).symm

theorem homogeneous_through_numeric (hn : 1 ≤ n) [Nonempty (Atom b)] (R : ℕ)
    (hw : (7*R:ℝ)+7*((6*R:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M) :
    Forms.HomogeneousThrough (analysisStructure b) (CentralGroup n) M R := by
  intro k hk names a a' ht
  apply quantitative_homogeneity hn names a a' _ ht
  simp only [Fintype.card_fin]
  have hkr : (k:ℝ) ≤ R := by exact_mod_cast hk
  have hp : ((6*k:ℝ)/boxConstant)^((3:ℝ)/2) ≤ ((6*R:ℝ)/boxConstant)^((3:ℝ)/2) := by
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith) boxConstant_pos.le
  linarith

theorem base_empty_type (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    [Nonempty (Atom (0 : Vertex n → Scalar))] [Nonempty (Atom (Pi.single vstar 1))] :
    Counting.tupleType (analysisStructure (0 : Vertex n → Scalar))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
    Counting.tupleType (analysisStructure (Pi.single vstar 1))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim := by
  apply (Counting.typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hφ
  have he : φ.free = ∅ := by
    apply subset_empty.mp
    simpa only [Counting.tupleNames,Finset.univ_eq_empty,Finset.map_empty] using hφ
  exact base_equivalence_numeric hn hbound vstar φ he _ _

theorem grid_hf_transfer (hn : 1 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (vstar : Vertex n) [Nonempty (Atom (0 : Vertex n → Scalar))]
    [Nonempty (Atom (Pi.single vstar 1))]
    (hwidth : max 4 (m+1)*s ≤ M)
    (hhom : (7*(max 2 m*s):ℝ)+7*((6*(max 2 m*s):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M)
    (φ : Counting.Formula (Forms.HFRelation AnalysisSymbol) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Forms.Domain (A := Atom (0 : Vertex n → Scalar)) (CentralGroup n) s)
    (w : Fin m → Forms.Domain (A := Atom (Pi.single vstar 1)) (CentralGroup n) s) :
    φ.eval (Forms.hfStructure (analysisStructure (0 : Vertex n → Scalar))) v ↔
      φ.eval (Forms.hfStructure (analysisStructure (Pi.single vstar 1))) w := by
  have hM : 0 < M := lt_of_lt_of_le (Nat.mul_pos (by omega) hs) hwidth
  exact Forms.hf_transfer _ _ hs hm hM hwidth
    (fun g r a b => central_analysis_isomorphism g r a b)
    (fun g r a b => central_analysis_isomorphism g r a b)
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (base_empty_type hn hgiant vstar) φ hφ v w

end CPTSeparation.Grid

end

end OAI
