import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.TemplateHierarchy

namespace OAI

section
universe u v w
namespace SourceBurnside.WordAlgebra

noncomputable section
open Classical

abbrev Word (α : Type u) := FreeMonoid α
abbrev Polynomial (K : Type v) (α : Type u) [Semiring K] := MonoidAlgebra K (Word α)

structure Table (α : Type u) where
  rep : Word α → Word α → Prop
  zero : Set (Word α)

variable {α : Type u} {K : Type v} [Ring K]

noncomputable def monomial (w : Word α) : Polynomial K α := MonoidAlgebra.single w 1

@[simp] theorem monomial_one : monomial (K := K) (1 : Word α) = 1 := rfl
@[simp] theorem monomial_mul (u v : Word α) :
    monomial (K := K) (u * v) = monomial u * monomial v := by
  simp [monomial, MonoidAlgebra.single_mul_single]

namespace Table

variable (T : Table α)

abbrev Reach : Word α → Word α → Prop := conGen T.rep

def Vanishes (w : Word α) : Prop :=
  ∃ p z s, z ∈ T.zero ∧ T.Reach w (p * z * s)

lemma reach_context {v w : Word α} (h : T.Reach v w) (p s : Word α) :
    T.Reach (p * v * s) (p * w * s) :=
  (conGen T.rep).mul ((conGen T.rep).mul ((conGen T.rep).refl p) h)
    ((conGen T.rep).refl s)

lemma vanishes_of_reach {v w : Word α} (h : T.Reach v w) (hw : T.Vanishes w) :
    T.Vanishes v := by
  obtain ⟨p, z, s, hz, hr⟩ := hw
  exact ⟨p, z, s, hz, (conGen T.rep).trans h hr⟩

def relations : Set (Polynomial K α) :=
  {f | (∃ v w, T.rep v w ∧ f = monomial v - monomial w) ∨
    (∃ z ∈ T.zero, f = monomial z)}

abbrev ideal : TwoSidedIdeal (Polynomial K α) := TwoSidedIdeal.span T.relations

abbrev Algebra := (T.ideal (K := K)).ringCon.Quotient

noncomputable abbrev quotient : Polynomial K α →+* T.Algebra (K := K) :=
  (T.ideal (K := K)).ringCon.mk'

noncomputable def word (w : Word α) : T.Algebra (K := K) := T.quotient (monomial w)

@[simp] theorem word_one : T.word (K := K) 1 = 1 := map_one T.quotient

@[simp] theorem word_mul (v w : Word α) :
    T.word (K := K) (v * w) = T.word v * T.word w := by
  rw [word, monomial_mul, map_mul]; rfl

lemma word_rep {v w : Word α} (h : T.rep v w) : T.word (K := K) v = T.word w := by
  apply ((T.ideal (K := K)).ringCon.eq).mpr
  apply ((T.ideal (K := K)).rel_iff _ _).mpr
  exact TwoSidedIdeal.subset_span (Or.inl ⟨v, w, h, rfl⟩)

lemma word_reach {v w : Word α} (h : T.Reach v w) : T.word (K := K) v = T.word w := by
  let f : Word α →* T.Algebra (K := K) :=
    { toFun := T.word
      map_one' := T.word_one
      map_mul' := T.word_mul }
  have hc : conGen T.rep ≤ Con.ker f := by
    apply Con.conGen_le.mpr
    intro a b hab
    exact T.word_rep hab
  exact hc h

lemma word_zero {z : Word α} (hz : z ∈ T.zero) : T.word (K := K) z = 0 := by
  apply ((T.ideal (K := K)).ringCon.eq).mpr
  exact TwoSidedIdeal.subset_span (Or.inr ⟨z, hz, rfl⟩)

lemma word_eq_zero_of_vanishes {w : Word α} (h : T.Vanishes w) : T.word (K := K) w = 0 := by
  obtain ⟨p, z, s, hz, hr⟩ := h
  rw [T.word_reach hr, word_mul, word_mul, T.word_zero hz, mul_zero, zero_mul]

noncomputable def detect (target : Word α) : Polynomial K α →+ K := by
  classical
  exact (Finsupp.liftAddHom (fun w : Word α =>
    if T.Reach target w then AddMonoidHom.id K else 0)).comp
      MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] lemma detect_single (target w : Word α) (a : K) :
    T.detect target (MonoidAlgebra.single w a) = if T.Reach target w then a else 0 := by
  classical
  change (Finsupp.liftAddHom (fun v : Word α =>
    if T.Reach target v then AddMonoidHom.id K else 0)) (Finsupp.single w a) = _
  rw [Finsupp.liftAddHom_apply_single]
  split <;> simp_all

@[simp] lemma detect_self (w : Word α) : T.detect w (monomial (K := K) w) = 1 := by
  rw [monomial, detect_single, ite_eq_left ((conGen T.rep).refl w)]

lemma detect_eq_of_reach (target : Word α) {v w : Word α} (h : T.Reach v w) (a : K) :
    T.detect target (MonoidAlgebra.single v a) =
      T.detect target (MonoidAlgebra.single w a) := by
  classical
  have he : T.Reach target v ↔ T.Reach target w :=
    ⟨fun ht => (conGen T.rep).trans ht h,
     fun ht => (conGen T.rep).trans ht ((conGen T.rep).symm h)⟩
  simp only [detect_single, he]

def annihilator (L : Polynomial K α →+ K) : TwoSidedIdeal (Polynomial K α) :=
  TwoSidedIdeal.mk' {f | ∀ a b, L (a * f * b) = 0}
    (by intro a b; simp)
    (by intro f g hf hg a b; simp [mul_add, add_mul, hf a b, hg a b])
    (by intro f hf a b; simp [hf a b])
    (by intro f g hg a b; simpa only [mul_assoc] using hg (a * f) b)
    (by intro f g hf a b; simpa only [mul_assoc] using hf a (g * b))

@[simp] lemma mem_annihilator (L : Polynomial K α →+ K) (f : Polynomial K α) :
    f ∈ annihilator L ↔ ∀ a b, L (a * f * b) = 0 := by simp [annihilator]

lemma relation_in_annihilator (target : Word α) (hnz : ¬ T.Vanishes target)
    {f : Polynomial K α} (hf : f ∈ T.relations) : f ∈ annihilator (T.detect target) := by
  classical
  apply (mem_annihilator _ _).mpr
  intro A B
  induction A using MonoidAlgebra.induction_linear with
  | zero => simp
  | add A₁ A₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single p a =>
    induction B using MonoidAlgebra.induction_linear with
    | zero => simp
    | add B₁ B₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | single s b =>
      rcases hf with ⟨v, w, hvw, rfl⟩ | ⟨z, hz, rfl⟩
      · simp only [monomial, mul_sub, sub_mul, MonoidAlgebra.single_mul_single,
          mul_one, map_sub]
        exact sub_eq_zero.mpr (T.detect_eq_of_reach target
          (T.reach_context (ConGen.Rel.of _ _ hvw) p s) (a * b))
      · simp only [monomial, MonoidAlgebra.single_mul_single, mul_one, detect_single]
        apply ite_eq_right
        intro hr
        exact hnz ⟨p, z, s, hz, hr⟩

lemma ideal_le_annihilator (target : Word α) (hnz : ¬ T.Vanishes target) :
    T.ideal (K := K) ≤ annihilator (T.detect target) :=
  TwoSidedIdeal.span_le.mpr (fun _ hf => T.relation_in_annihilator target hnz hf)

theorem word_ne_zero [Nontrivial K] {w : Word α} (hw : ¬ T.Vanishes w) :
    T.word (K := K) w ≠ 0 := by
  intro h
  have hm : monomial (K := K) w ∈ T.ideal := ((T.ideal (K := K)).ringCon.eq).mp h
  have hd := (mem_annihilator (T.detect w) _).mp (T.ideal_le_annihilator w hw hm) 1 1
  simp only [one_mul, mul_one, detect_self] at hd
  exact one_ne_zero hd

theorem word_eq_zero_iff [Nontrivial K] (w : Word α) :
    T.word (K := K) w = 0 ↔ T.Vanishes w :=
  ⟨fun h => by by_contra hn; exact T.word_ne_zero hn h, T.word_eq_zero_of_vanishes⟩

theorem word_eq_word_iff [Nontrivial K] (v w : Word α) :
    T.word (K := K) v = T.word w ↔
      T.Reach v w ∨ (T.Vanishes v ∧ T.Vanishes w) := by
  constructor
  · intro h
    by_cases hv : T.Vanishes v
    · right
      exact ⟨hv, (T.word_eq_zero_iff w).mp (h.symm.trans (T.word_eq_zero_of_vanishes hv))⟩
    · left
      by_contra hr
      have hm : monomial (K := K) v - monomial w ∈ T.ideal :=
        ((T.ideal (K := K)).rel_iff _ _).mp (((T.ideal (K := K)).ringCon.eq).mp h)
      have hd := (mem_annihilator (T.detect v) _).mp
        (T.ideal_le_annihilator v hv hm) 1 1
      simp only [one_mul, mul_one, map_sub, monomial, detect_single,
        ite_eq_left ((conGen T.rep).refl v), ite_eq_right hr, sub_zero] at hd
      exact one_ne_zero hd
  · rintro (hr | ⟨hv, hw⟩)
    · exact T.word_reach hr
    · exact (T.word_eq_zero_of_vanishes hv).trans (T.word_eq_zero_of_vanishes hw).symm

def Homogeneous : Prop := ∀ v w, T.rep v w → v.length = w.length

lemma length_eq_of_reach (hh : T.Homogeneous) {v w : Word α} (h : T.Reach v w) :
    v.length = w.length := by
  let C : Con (Word α) :=
    { r := fun v w => v.length = w.length
      iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
      mul' := by intro a b c d h₁ h₂; simp only [FreeMonoid.length_mul, h₁, h₂] }
  have hC : conGen T.rep ≤ C := Con.conGen_le.mpr hh
  exact hC h

lemma not_vanishes_one (hh : T.Homogeneous) (hz : ∀ z ∈ T.zero, z ≠ 1) :
    ¬ T.Vanishes 1 := by
  rintro ⟨p, z, s, hzero, hreach⟩
  have hl := T.length_eq_of_reach hh hreach
  simp only [FreeMonoid.length_one, FreeMonoid.length_mul] at hl
  have : z.length = 0 := by omega
  exact hz z hzero (FreeMonoid.length_eq_zero.mp this)

theorem nontrivial_algebra [Nontrivial K] (hh : T.Homogeneous)
    (hz : ∀ z ∈ T.zero, z ≠ 1) : Nontrivial (T.Algebra (K := K)) := by
  have h := T.word_ne_zero (K := K) (T.not_vanishes_one hh hz)
  rw [word_one] at h
  exact ⟨⟨1, 0, h⟩⟩

theorem infinite_algebra [Nontrivial K] (hh : T.Homogeneous)
    (hw : ∀ N : ℕ, ∃ w : Word α, N < w.length ∧ ¬ T.Vanishes w) :
    Infinite (T.Algebra (K := K)) := by
  obtain ⟨φ, hφ, hwφ⟩ := Nat.exists_strictMono_subsequence
    (P := fun n => ∃ w : Word α, w.length = n ∧ ¬ T.Vanishes w)
    (fun N => by obtain ⟨w, hn, hsurv⟩ := hw N; exact ⟨w.length, hn, w, rfl, hsurv⟩)
  choose w hwlen hwsurv using hwφ
  apply Infinite.of_injective (fun n => T.word (K := K) (w n))
  intro m n he
  rcases (T.word_eq_word_iff _ _).mp he with hreach | hzero
  · apply hφ.injective
    simpa only [hwlen] using T.length_eq_of_reach hh hreach
  · exact (hwsurv m hzero.1).elim

end Table

end

end SourceBurnside.WordAlgebra

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma step_context {v w : List (Raw h)} (he : Step hh S d v w) (p s : List (Raw h)) :
    Step hh S d (p++v++s) (p++w++s) := by
  obtain ⟨a,b,c,e,rfl,rfl,he⟩ := he
  exact ⟨p++a,b++s,c,e,by simp [List.append_assoc],by simp [List.append_assoc],he⟩
lemma reach_context {v w : List (Raw h)} (he : Reach hh S d v w) (p s : List (Raw h)) :
    Reach hh S d (p++v++s) (p++w++s) := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (step_context e p s)
lemma reach_symm {v w : List (Raw h)} (he : Reach hh S d v w) : Reach hh S d w v := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact (Relation.ReflTransGen.single (step_symm e)).trans ih

def algebraTable (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) : WordAlgebra.Table (Raw h) where
  rep := fun v w => replacement hh S d v.toList w.toList
  zero := {w | zero hh S d w.toList}
def reachCon (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) : Con (FreeMonoid (Raw h)) where
  r v w := Reach hh S d v.toList w.toList
  iseqv := ⟨fun _ => .refl,fun h => reach_symm h,fun h k => h.trans k⟩
  mul' := by
    intro a b c e hab hce
    change Reach hh S d (a.toList++c.toList) (b.toList++e.toList)
    have h₁ : Reach hh S d (a.toList++c.toList) (b.toList++c.toList) := by
      simpa using reach_context hab [] c.toList
    have h₂ : Reach hh S d (b.toList++c.toList) (b.toList++e.toList) := by
      simpa using reach_context hce b.toList []
    exact h₁.trans h₂
lemma reach_iff_table {v w : List (Raw h)} :
    Reach hh S d v w ↔ (algebraTable hh S d).Reach (FreeMonoid.ofList v) (FreeMonoid.ofList w) := by
  constructor
  · intro hr
    induction hr with
    | refl => exact (conGen (algebraTable hh S d).rep).refl _
    | tail h e ih =>
      obtain ⟨p,s,a,b,rfl,rfl,he⟩ := e
      apply (conGen (algebraTable hh S d).rep).trans ih
      exact (conGen (algebraTable hh S d).rep).mul
        ((conGen (algebraTable hh S d).rep).mul ((conGen (algebraTable hh S d).rep).refl (FreeMonoid.ofList p))
          (ConGen.Rel.of (FreeMonoid.ofList a) (FreeMonoid.ofList b) he))
        ((conGen (algebraTable hh S d).rep).refl (FreeMonoid.ofList s))
  · intro h
    have hle : conGen (algebraTable hh S d).rep ≤ reachCon hh S d := by
      apply Con.conGen_le.mpr
      intro a b he
      exact Relation.ReflTransGen.single ⟨[],[],a.toList,b.toList,by simp,by simp,he⟩
    exact hle h
lemma survives_iff_not_vanishes (w : List (Raw h)) :
    Survives hh S d w ↔ ¬(algebraTable hh S d).Vanishes (FreeMonoid.ofList w) := by
  constructor
  · intro hw ⟨p,z,s,hz,hr⟩
    have he : Reach hh S d w (p.toList++z.toList++s.toList) := reach_iff_table.mpr hr
    exact hw p.toList z.toList s.toList he hz
  · intro hw p z s hr hz
    exact hw ⟨FreeMonoid.ofList p,FreeMonoid.ofList z,FreeMonoid.ofList s,hz,reach_iff_table.mp hr⟩
lemma algebraTable_homogeneous (hh4 : 4≤h) : (algebraTable hh S d).Homogeneous := by
  intro v w he
  exact (replacement_lengths hh4 S d v.toList w.toList he).1
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
def table (h : ℕ) (hh : A.threshold≤h) :=
  Codec.algebraTable (A.height_pos hh) (A.schedule h hh) (10000*(D*h))

abbrev Algebra (K : Type*) [Ring K] (h : ℕ) (hh : A.threshold≤h) := (A.table h hh).Algebra (K:=K)

theorem infinite_algebra (K : Type*) [Ring K] [Nontrivial K] (h : ℕ) (hh : A.threshold≤h) :
    Infinite (A.Algebra K h hh) := by
  apply (A.table h hh).infinite_algebra
  · exact Codec.algebraTable_homogeneous (A.threshold_four.trans hh)
  · intro N
    obtain ⟨w,hw,hs⟩ := A.unbounded_survivors N h hh
    exact ⟨FreeMonoid.ofList w,hw,Codec.survives_iff_not_vanishes w |>.mp hs⟩
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.Cancellation

open scoped BigOperators

variable {K : Type u} [CommRing K] [CharP K 2]

noncomputable def alternatingSum {d m : ℕ} (X : Fin m → Matrix (Fin d) (Fin d) K) :
    Matrix (Fin d) (Fin d) K :=
  ∑ σ : Equiv.Perm (Fin m), (List.ofFn (X ∘ σ)).prod

theorem alternating_eq_zero_of_card_lt {S : Type u} [CommSemiring S]
    {V : Type v} [AddCommMonoid V] [Module S V]
    {W : Type w} [AddCommMonoid W] [Module S W]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ S V) (f : AlternatingMap S V W ι)
    (h : Fintype.card κ < Fintype.card ι) : f = 0 := by
  apply b.ext_alternating
  intro t ht
  exact ((not_le_of_gt h) (Fintype.card_le_of_injective t ht)).elim

lemma sign_smul_matrix {d : ℕ} (σ : ℤˣ) (X : Matrix (Fin d) (Fin d) K) :
    σ • X = X := by
  rcases Int.units_eq_one_or σ with h | h
  · rw [h, one_smul]
  · rw [h, Units.smul_def]
    change (-1 : ℤ) • X = X
    rw [neg_one_zsmul]
    ext i j
    exact CharTwo.neg_eq (X i j)

theorem alternatingSum_eq_zero {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) K) (h : d ^ 2 < m) :
    alternatingSum X = 0 := by
  let f := MultilinearMap.mkPiAlgebraFin K m (Matrix (Fin d) (Fin d) K)
  have hz : MultilinearMap.alternatization f = 0 :=
    alternating_eq_zero_of_card_lt (Matrix.stdBasis K (Fin d) (Fin d)) _ (by
      simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h)
  have hv := congrArg (fun F : AlternatingMap K
    (Matrix (Fin d) (Fin d) K) (Matrix (Fin d) (Fin d) K) (Fin m) => F X) hz
  simpa only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    sign_smul_matrix, MultilinearMap.mkPiAlgebraFin_apply, AlternatingMap.zero_apply,
    alternatingSum, Function.comp_def, f] using hv

end SourceBurnside.Cancellation

namespace SourceBurnside.Cancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ : Type*} {K : Type*} [CommRing K] [CharP K 2]

def chunkWeight {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K) (s : List Γ) :=
  (s.map W).prod

omit [CharP K 2] in
lemma chunkWeight_append {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K) (s t : List Γ) :
    chunkWeight W (s ++ t) = chunkWeight W s * chunkWeight W t := by
  simp [chunkWeight]

structure Packet (Γ : Type*) where
  before : List Γ
  inside : List Γ
  after : List Γ

def Packet.join (p : Packet Γ) : List Γ := p.before ++ p.inside ++ p.after

def Packet.key (p : Packet Γ) : List Γ × List Γ × Multiset Γ :=
  (p.before, p.after, p.inside)

lemma perm_of_key_eq {p q : Packet Γ} (h : p.key = q.key) :
    p.before = q.before ∧ p.after = q.after ∧ p.inside.Perm q.inside := by
  have hp := congrArg Prod.fst h
  have hq := congrArg (fun x => x.2.1) h
  have hi := congrArg (fun x => x.2.2) h
  exact ⟨hp, hq, Quotient.exact hi⟩

lemma packet_perm_exists (s : List Γ) (hs : s.Nodup) (t : List Γ) (ht : t.Perm s) :
    ∃ σ : Equiv.Perm (Fin s.length), List.ofFn (s.get ∘ σ) = t := by
  let f : Fin t.length → Γ := t.get
  have hlen := ht.length_eq
  let e : Fin t.length ≃ Fin s.length := finCongr hlen
  have hf : Function.Injective f := List.nodup_iff_injective_get.mp (ht.nodup_iff.mpr hs)
  have hg : Function.Injective s.get := List.nodup_iff_injective_get.mp hs
  let τ : Fin t.length ≃ Fin s.length := Equiv.ofBijective
    (fun i => ⟨s.idxOf (t.get i), List.idxOf_lt_length_iff.mpr (ht.mem_iff.mp (List.get_mem t i))⟩)
    (by
      constructor
      · intro i j hij
        apply hf
        have hij' := congrArg (fun x : Fin s.length => s.get x) hij
        simpa [f] using hij'
      · intro j
        have hm : s.get j ∈ t := ht.mem_iff.mpr (List.get_mem s j)
        refine ⟨⟨t.idxOf (s.get j), List.idxOf_lt_length_iff.mpr hm⟩, ?_⟩
        apply hg
        simp)
  refine ⟨e.symm.trans τ, ?_⟩
  apply List.ext_getElem
  · simp
    exact hlen.symm
  · intro i hi hj
    simp only [List.getElem_ofFn, Function.comp_apply, Equiv.trans_apply]
    simp [τ, e]

lemma packet_perm_injective (s : List Γ) (hs : s.Nodup) :
    Function.Injective (fun σ : Equiv.Perm (Fin s.length) => List.ofFn (s.get ∘ σ)) := by
  intro σ τ h
  have he := List.ofFn_injective h
  apply Equiv.ext
  intro i
  exact List.nodup_iff_injective_get.mp hs (congrFun he i)

lemma sum_packet_permutations {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K)
    (s : List Γ) (hm : d^2 < s.length) :
    (∑ σ : Equiv.Perm (Fin s.length), chunkWeight W (List.ofFn (s.get ∘ σ))) = 0 := by
  simpa only [chunkWeight, List.map_ofFn, Function.comp_def, alternatingSum] using
    (alternatingSum_eq_zero (fun i : Fin s.length => W (s.get i)) hm)

def Packet.reorder (p : Packet Γ) (σ : Equiv.Perm (Fin p.inside.length)) : List Γ :=
  p.before ++ List.ofFn (p.inside.get ∘ σ) ++ p.after

lemma Packet.reorder_injective (p : Packet Γ) (hp : p.inside.Nodup) :
    Function.Injective p.reorder := by
  intro σ τ h
  apply packet_perm_injective p.inside hp
  exact List.append_cancel_left (List.append_cancel_right h)

lemma Packet.reorder_one (p : Packet Γ) : p.reorder 1 = p.join := by
  simp [Packet.reorder, Packet.join]

lemma sum_reorder_weight {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K)
    (p : Packet Γ) (hm : d^2 < p.inside.length) :
    (∑ σ : Equiv.Perm (Fin p.inside.length), chunkWeight W (p.reorder σ)) = 0 := by
  simp only [Packet.reorder, chunkWeight_append]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_packet_permutations W p.inside hm,
    mul_zero, zero_mul]

theorem packet_cancellation {d : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (S : Finset (List Γ)) (W : Γ → Matrix (Fin d) (Fin d) K)
    (value : List Γ → V) (pick : List Γ → Packet Γ)
    (joins : ∀ s ∈ S, (pick s).join = s)
    (nodup : ∀ s ∈ S, (pick s).inside.Nodup)
    (long : ∀ s ∈ S, d^2 < (pick s).inside.length)
    (closed : ∀ s ∈ S, ∀ σ, (pick s).reorder σ ∈ S)
    (stable : ∀ s ∈ S, ∀ σ, (pick ((pick s).reorder σ)).key = (pick s).key)
    (same_value : ∀ s ∈ S, ∀ σ, value ((pick s).reorder σ) = value s)
    (i j : Fin d) :
    (∑ s ∈ S, chunkWeight W s i j • value s) = 0 := by
  let key := fun s => (pick s).key
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image key)
    (fun s hs => Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    (fun s => chunkWeight W s i j • value s)]
  apply Finset.sum_eq_zero
  intro z hz
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
  have hfiber : S.filter (fun t => key t = key s) =
      Finset.univ.image (pick s).reorder := by
    ext t
    constructor
    · intro ht
      obtain ⟨htS,htkey⟩ := Finset.mem_filter.mp ht
      obtain ⟨hb,ha,hp⟩ := perm_of_key_eq htkey
      obtain ⟨σ,hσ⟩ := packet_perm_exists (pick s).inside (nodup s hs) (pick t).inside hp
      refine Finset.mem_image.mpr ⟨σ,Finset.mem_univ _,?_⟩
      rw [Packet.reorder, hσ, ← hb, ← ha]
      exact joins t htS
    · intro ht
      obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_filter.mpr ⟨closed s hs σ, stable s hs σ⟩
  rw [hfiber, Finset.sum_image]
  · simp_rw [same_value s hs]
    rw [← Finset.sum_smul]
    have hw := congrArg (fun A : Matrix (Fin d) (Fin d) K => A i j)
      (sum_reorder_weight W (pick s) (long s hs))
    simp only [Matrix.sum_apply, Matrix.zero_apply] at hw
    rw [hw, zero_smul]
  · exact (Packet.reorder_injective (pick s) (nodup s hs)).injOn

end
end SourceBurnside.Cancellation

end

end OAI
