import OAI.GroupTheory.UniversalGroup.CentralHNN

namespace OAI

universe u v w x

namespace Higman
open Monoid Coprod

lemma commute_of_free_generators {ι : Type u} {κ : Type v}
    {G : Type w} {H : Type x} {K : Type*} [Group G] [Group H] [Group K]
    (p : FreeGroup ι →* G) (hp : Function.Surjective p)
    (q : FreeGroup κ →* H) (hq : Function.Surjective q)
    (f : G →* K) (g : H →* K)
    (hc : ∀ i j, Commute (f (p (FreeGroup.of i))) (g (q (FreeGroup.of j)))) :
    ∀ a b, Commute (f a) (g b) := by
  intro a b
  obtain ⟨a,rfl⟩ := hp a
  obtain ⟨b,rfl⟩ := hq b
  have hgen (i : ι) (b : FreeGroup κ) :
      Commute (f (p (FreeGroup.of i))) (g (q b)) := by
    induction b using FreeGroup.induction_on with
    | one => simp
    | of j => exact hc i j
    | inv_of b hb => simpa only [map_inv] using hb.inv_right
    | mul b c hb hc => simpa only [map_mul] using hb.mul_right hc
  induction a using FreeGroup.induction_on with
  | one => simp
  | of i => exact hgen i b
  | inv_of a ha => simpa only [map_inv] using ha.inv_left
  | mul a c ha hc => simpa only [map_mul] using ha.mul_left hc

theorem finitelyPresented_prod {G : Type u} {H : Type v} [Group G] [Group H]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  classical
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := G)
  obtain ⟨m,q,hq,_⟩ := Group.IsFinitelyPresented.out (G := H)
  let relation : Fin n × Fin m → G ∗ H := fun ij ↦
    (inl (p (FreeGroup.of ij.1)) * inr (q (FreeGroup.of ij.2))) *
      (inr (q (FreeGroup.of ij.2)) * inl (p (FreeGroup.of ij.1)))⁻¹
  let N := Subgroup.normalClosure (Set.range relation)
  let Q := (G ∗ H) ⧸ N
  let proj : G ∗ H →* Q := QuotientGroup.mk' N
  let f : G →* Q := proj.comp inl
  let g : H →* Q := proj.comp inr
  have hcomm : ∀ a b, Commute (f a) (g b) := by
    apply commute_of_free_generators p hp q hq
    intro i j
    have h : proj (relation (i,j)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨(i,j),rfl⟩)
    exact mul_inv_eq_one.mp (by simpa only [f,g,MonoidHom.comp_apply,relation,map_mul,map_inv] using h)
  let π : G ∗ H →* G × H := Coprod.lift (MonoidHom.inl G H) (MonoidHom.inr G H)
  let s : G × H →* Q := MonoidHom.noncommCoprod f g hcomm
  have hs : s.comp π = proj := by
    apply Coprod.hom_ext <;> ext z <;> simp [s,π,f,g]
  have hker : π.ker = N := by
    apply le_antisymm
    · intro z hz
      apply (QuotientGroup.eq_one_iff _).mp
      change proj z = 1
      rw [← hs]
      change s (π z) = 1
      rw [show π z = 1 from hz,map_one]
    · apply Subgroup.normalClosure_le_normal
      rintro z ⟨⟨i,j⟩,rfl⟩
      change π (relation (i,j)) = 1
      simp [π,relation]
  apply Group.IsFinitelyPresented.of_surjective π
  · rintro ⟨a,b⟩
    exact ⟨inl a * inr b,by simp [π]⟩
  · exact ⟨Set.range relation,Set.finite_range _,hker.symm⟩

end Higman

namespace Higman.RopeTrick

section
open Monoid Coprod Multiplicative

section Container
variable {ι : Type u} {K : Type v} [Group K]

abbrev Raw := (K × FreeGroup ι) ∗ Multiplicative ℤ

def rawK : K →* Raw (ι := ι) (K := K) := Coprod.inl.comp (MonoidHom.inl K (FreeGroup ι))
def rawF : FreeGroup ι →* Raw (ι := ι) (K := K) := Coprod.inl.comp (MonoidHom.inr K (FreeGroup ι))
def rawT : Raw (ι := ι) (K := K) := Coprod.inr (ofAdd 1)

def relation (α β : FreeGroup ι →* K) : ι ⊕ ι → Raw (ι := ι) (K := K)
  | .inl j => (rawT * rawK (α (FreeGroup.of j))) *
      (rawK (α (FreeGroup.of j)) * rawT)⁻¹
  | .inr j => (rawT * rawK (β (FreeGroup.of j))) *
      (rawK (β (FreeGroup.of j)) * rawF (FreeGroup.of j) * rawT)⁻¹

abbrev relations (α β : FreeGroup ι →* K) := Subgroup.normalClosure (Set.range (relation α β))
abbrev Container (α β : FreeGroup ι →* K) := Raw (ι := ι) (K := K) ⧸ relations α β

def proj (α β : FreeGroup ι →* K) : Raw (ι := ι) (K := K) →* Container α β :=
  QuotientGroup.mk' (relations α β)
def kMap (α β : FreeGroup ι →* K) : K →* Container α β := (proj α β).comp rawK
def fMap (α β : FreeGroup ι →* K) : FreeGroup ι →* Container α β := (proj α β).comp rawF
def stable (α β : FreeGroup ι →* K) : Container α β := proj α β rawT

theorem finitelyPresented [Finite ι] [Group.IsFinitelyPresented K]
    (α β : FreeGroup ι →* K) : Group.IsFinitelyPresented (Container α β) := by
  let := Higman.finitelyPresented_prod (G := K) (H := FreeGroup ι)
  exact Group.IsFinitelyPresented.quotient _ ⟨Set.range (relation α β),Set.finite_range _,rfl⟩

lemma relation_zero (α β : FreeGroup ι →* K) (j : ι ⊕ ι) :
    proj α β (relation α β j) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j,rfl⟩)

lemma generator_zero (α β : FreeGroup ι →* K) (j : ι) :
    stable α β * kMap α β (α (FreeGroup.of j)) =
      kMap α β (α (FreeGroup.of j)) * stable α β := by
  apply mul_inv_eq_one.mp
  simpa only [proj,relation,map_mul,map_inv,kMap,stable,MonoidHom.comp_apply] using
    relation_zero α β (.inl j)

lemma generator_one (α β : FreeGroup ι →* K) (j : ι) :
    stable α β * kMap α β (β (FreeGroup.of j)) =
      kMap α β (β (FreeGroup.of j)) * fMap α β (FreeGroup.of j) * stable α β := by
  apply mul_inv_eq_one.mp
  simpa only [proj,relation,map_mul,map_inv,kMap,fMap,stable,MonoidHom.comp_apply] using
    relation_zero α β (.inr j)

lemma conjugate_zero (α β : FreeGroup ι →* K) (w : FreeGroup ι) :
    stable α β * kMap α β (α w) * (stable α β)⁻¹ = kMap α β (α w) := by
  have hh : (MulAut.conj (stable α β)).toMonoidHom.comp ((kMap α β).comp α) =
      (kMap α β).comp α := by
    apply FreeGroup.ext_hom
    intro j
    change stable α β * kMap α β (α (FreeGroup.of j)) * (stable α β)⁻¹ = _
    rw [generator_zero,mul_inv_cancel_right]
    rfl
  exact DFunLike.congr_fun hh w

lemma pair_eq (α β : FreeGroup ι →* K) (k : K) (w : FreeGroup ι) :
    proj α β (Coprod.inl (k,w)) = kMap α β k * fMap α β w := by
  change proj α β (Coprod.inl (k,w)) =
    proj α β (Coprod.inl (k,1)) * proj α β (Coprod.inl (1,w))
  rw [← map_mul,← map_mul]
  simp

lemma conjugate_one (α β : FreeGroup ι →* K) (w : FreeGroup ι) :
    stable α β * kMap α β (β w) * (stable α β)⁻¹ =
      kMap α β (β w) * fMap α β w := by
  let p : FreeGroup ι →* Container α β :=
    ((proj α β).comp Coprod.inl).comp (β.prod (MonoidHom.id _))
  have hh : (MulAut.conj (stable α β)).toMonoidHom.comp ((kMap α β).comp β) = p := by
    apply FreeGroup.ext_hom
    intro j
    change stable α β * kMap α β (β (FreeGroup.of j)) * (stable α β)⁻¹ =
      proj α β (Coprod.inl (β (FreeGroup.of j),FreeGroup.of j))
    rw [generator_one,mul_inv_cancel_right,pair_eq]
  have h := DFunLike.congr_fun hh w
  change stable α β * kMap α β (β w) * (stable α β)⁻¹ =
    proj α β (Coprod.inl (β w,w)) at h
  rwa [pair_eq] at h

lemma kills_relation (α β : FreeGroup ι →* K) (w : FreeGroup ι) (hw : α w = β w) :
    fMap α β w = 1 := by
  have h0 := conjugate_zero α β w
  rw [hw,conjugate_one] at h0
  exact mul_left_cancel (h0.trans (mul_one _).symm)

end Container

variable {A : Type u} {K : Type v} {G : Type w} [Group A] [Group K] [Group G]
variable (i : A →* K) (hi : Function.Injective i) (r : A →* G)

def left : A →* K × G := i.prod 1
def right : A →* K × G := i.prod r

include hi in
lemma left_injective : Function.Injective (left i (G := G)) := by
  intro a b h
  exact hi (congrArg Prod.fst h)
include hi in
lemma right_injective : Function.Injective (right i r) := by
  intro a b h
  exact hi (congrArg Prod.fst h)

noncomputable def associated : (left i (G := G)).range ≃* (right i r).range :=
  (MonoidHom.ofInjective (left_injective i hi)).symm.trans
    (MonoidHom.ofInjective (right_injective i hi r))

abbrev Model := HNNExtension (K × G) (left i (G := G)).range (right i r).range (associated i hi r)

lemma associated_left (a : A) : associated i hi r ⟨left i a,⟨a,rfl⟩⟩ =
    ⟨right i r a,⟨a,rfl⟩⟩ := by
  change (MonoidHom.ofInjective (right_injective i hi r))
    ((MonoidHom.ofInjective (left_injective i hi)).symm
      ((MonoidHom.ofInjective (left_injective i hi)) a)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

lemma model_relation (a : A) :
    (HNNExtension.t : Model i hi r) * HNNExtension.of (i a,1) =
      HNNExtension.of (i a,r a) * HNNExtension.t := by
  have h := HNNExtension.t_mul_of (φ := associated i hi r) ⟨left i a,⟨a,rfl⟩⟩
  rw [associated_left] at h
  exact h

end

open Monoid Coprod Multiplicative
noncomputable section
variable {ι : Type u} {A : Type v} {K : Type w} {G : Type x}
variable [Group A] [Group K] [Group G]
variable (i : A →* K) (hi : Function.Injective i) (r : A →* G)
variable (q : FreeGroup ι →* G)

def evaluate : Raw (ι := ι) (K := K) →* Model i hi r :=
  Coprod.lift (HNNExtension.of.comp ((MonoidHom.id K).prodMap q))
    (zpowersHom _ HNNExtension.t)

@[simp] lemma evaluate_rawK (k : K) :
    evaluate i hi r q (rawK k) = HNNExtension.of (k,1) := by
  simp [evaluate,rawK]
@[simp] lemma evaluate_rawF (w : FreeGroup ι) :
    evaluate i hi r q (rawF w) = HNNExtension.of (1,q w) := by
  simp [evaluate,rawF]
@[simp] lemma evaluate_rawT :
    evaluate i hi r q rawT = HNNExtension.t := by
  simp [evaluate,rawT]

variable (p₀ p₁ : FreeGroup ι →* A)
variable (h₀ : ∀ w, r (p₀ w) = 1) (h₁ : ∀ w, r (p₁ w) = q w)

include h₀ h₁ in
lemma evaluate_relation (j : ι ⊕ ι) :
    evaluate i hi r q (relation (i.comp p₀) (i.comp p₁) j) = 1 := by
  cases j with
  | inl j =>
    simp only [relation,map_mul,map_inv,evaluate_rawK,evaluate_rawT]
    apply mul_inv_eq_one.mpr
    simpa only [MonoidHom.comp_apply,h₀] using model_relation i hi r (p₀ (FreeGroup.of j))
  | inr j =>
    simp only [relation,map_mul,map_inv,evaluate_rawK,evaluate_rawF,evaluate_rawT]
    apply mul_inv_eq_one.mpr
    rw [← map_mul]
    simpa only [MonoidHom.comp_apply,Prod.mk_mul_mk,mul_one,one_mul,h₁] using
      model_relation i hi r (p₁ (FreeGroup.of j))

def detect : Container (i.comp p₀) (i.comp p₁) →* Model i hi r :=
  QuotientGroup.lift _ (evaluate i hi r q) (by
    apply Subgroup.normalClosure_le_normal
    rintro z ⟨j,rfl⟩
    exact evaluate_relation i hi r q p₀ p₁ h₀ h₁ j)

@[simp] lemma detect_fMap (w : FreeGroup ι) :
    detect i hi r q p₀ p₁ h₀ h₁ (fMap (i.comp p₀) (i.comp p₁) w) =
      HNNExtension.of (1,q w) := by
  change evaluate i hi r q (rawF w) = _
  exact evaluate_rawF i hi r q w

include hi h₀ h₁ in

theorem embeds_quotient [Finite ι] [Group.IsFinitelyPresented K]
    (hq : Function.Surjective q)
    (hident : ∀ w ∈ q.ker, i (p₀ w) = i (p₁ w)) :
    ∃ (Q : Type (max u w)) (_ : Group Q) (_ : Group.IsFinitelyPresented Q),
      ∃ j : G →* Q, Function.Injective j := by
  let α := i.comp p₀
  let β := i.comp p₁
  have hk : q.ker ≤ (fMap α β).ker := by
    intro w hw
    exact kills_relation α β w (hident w hw)
  let j : G →* Container α β := q.liftOfSurjective hq ⟨fMap α β,hk⟩
  have hj (w : FreeGroup ι) : j (q w) = fMap α β w := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let d := detect i hi r q p₀ p₁ h₀ h₁
  have hd (g : G) : d (j g) = HNNExtension.of (1,g) := by
    obtain ⟨w,rfl⟩ := hq g
    rw [hj]
    exact detect_fMap i hi r q p₀ p₁ h₀ h₁ w
  refine ⟨Container α β,inferInstance,finitelyPresented α β,j,?_⟩
  intro g h he
  have hh := congrArg d he
  rw [hd,hd] at hh
  exact congrArg Prod.snd (HNNExtension.of_injective (φ := associated i hi r) hh)

end
end Higman.RopeTrick

namespace Higman
variable {G : Type u} [Group G]

def IsBenign (A : Subgroup G) : Prop :=
  ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
    (i : G →* K), Function.Injective i ∧
    ∃ B : Subgroup K, B.FG ∧ B.comap i = A

namespace Double
lemma firstIn_eq_secondIn {A : Subgroup G} {g : G} (hg : g ∈ A) :
    firstIn A g = secondIn A g := by
  apply Subtype.ext
  exact HNNExtension.equiv_eq_conj (φ := MulEquiv.refl A) ⟨g,hg⟩
end Double

theorem embeds_of_benign_kernel {ι : Type u} [Finite ι]
    {D : Type v} [Group D] (q : FreeGroup ι →* D) (hq : Function.Surjective q)
    (hben : IsBenign q.ker) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : D →* K), Function.Injective i := by
  obtain ⟨K,_,_,i,hi,B,hB,hBi⟩ := hben
  let E := CentralExtension K B
  have : Group.IsFinitelyPresented E := CentralExtension.finitelyPresented hB
  let j := CentralExtension.map i (le_of_eq hBi.symm)
  have hj : Function.Injective j := CentralExtension.map_injective i hi hBi
  let A := Double.subgroup q.ker
  let jA : A →* E := j.comp A.subtype
  have hjA : Function.Injective jA := hj.comp Subtype.val_injective
  let r := Double.read q (le_refl q.ker)
  exact RopeTrick.embeds_quotient jA hjA r q
    (Double.firstIn q.ker) (Double.secondIn q.ker)
    (Double.read_first q (le_refl q.ker))
    (Double.read_second q (le_refl q.ker)) hq
    (fun w hw ↦ congrArg jA (Double.firstIn_eq_secondIn hw))

namespace IsBenign
variable {A B : Subgroup G}

theorem of_fg [Group.IsFinitelyPresented G] (hA : A.FG) : IsBenign A := by
  refine ⟨G,inferInstance,inferInstance,MonoidHom.id G,Function.injective_id,A,hA,?_⟩
  rfl

theorem inf (hA : IsBenign A) (hB : IsBenign B) : IsBenign (A ⊓ B) := by
  obtain ⟨K,_,_,i,hi,L,hL,hLi⟩ := hA
  obtain ⟨K',_,_,j,_,L',hL',hLj⟩ := hB
  refine ⟨K × K',inferInstance,finitelyPresented_prod,i.prod j,?_,L.prod L',
    hL.prod hL',?_⟩
  · intro x y h
    exact hi (congrArg Prod.fst h)
  · ext x
    change i x ∈ L ∧ j x ∈ L' ↔ x ∈ A ∧ x ∈ B
    change x ∈ L.comap i ∧ x ∈ L'.comap j ↔ _
    rw [hLi,hLj]

theorem comap {D : Type u} [Group D] [Group.IsFinitelyPresented D]
    (hA : IsBenign A) (f : D →* G) : IsBenign (A.comap f) := by
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := D)
  have : Group.FG D := Group.fg_of_surjective hp
  obtain ⟨K,_,_,i,_,L,hL,hLi⟩ := hA
  refine ⟨D × K,inferInstance,finitelyPresented_prod,
    (MonoidHom.id D).prod (i.comp f),?_,(⊤ : Subgroup D).prod L,
    Group.FG.out.prod hL,?_⟩
  · intro x y h
    exact congrArg Prod.fst h
  · ext x
    change (x ∈ (⊤ : Subgroup D) ∧ i (f x) ∈ L) ↔ f x ∈ A
    simpa only [Subgroup.mem_top,true_and,Subgroup.mem_comap] using
      (show f x ∈ L.comap i ↔ f x ∈ A by rw [hLi])

end IsBenign

end Higman

end OAI
