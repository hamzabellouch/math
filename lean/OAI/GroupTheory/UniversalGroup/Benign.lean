import OAI.GroupTheory.UniversalGroup.RopeTrick

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.HNN
open HNNExtension
variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

theorem conj_mem_range_iff (g : G) :
    (t * of g * t⁻¹ : HNNExtension G A B φ) ∈ of.range ↔ g ∈ A := by
  constructor
  · intro h
    by_contra hg
    let w : NormalWord.ReducedWord G A B :=
      { head := 1
        toList := [(1,g),(-1,1)]
        chain := by simp [hg] }
    have hp : w.prod φ = t * of g * t⁻¹ := by
      simp [NormalWord.ReducedWord.prod,w]
    have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ w (hp ▸ h)
    simp [w] at hn
  · intro hg
    rw [← equiv_eq_conj (φ := φ) ⟨g,hg⟩]
    exact ⟨_,rfl⟩

theorem commute_t_iff (g : G) :
    Commute (t : HNNExtension G A A (MulEquiv.refl A)) (of g) ↔ g ∈ A := by
  constructor
  · intro h
    apply (conj_mem_range_iff (MulEquiv.refl A) g).mp
    rw [h.eq,mul_inv_cancel_right]
    exact ⟨g,rfl⟩
  · intro hg
    exact t_mul_of (φ := MulEquiv.refl A) ⟨g,hg⟩

end Higman.HNN

namespace Higman
variable {G : Type u} [Group G] {A : Subgroup G}

theorem benign_iff_centralExtension_embeds : IsBenign A ↔
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (j : CentralExtension G A →* K), Function.Injective j := by
  constructor
  · rintro ⟨K,_,_,i,hi,B,hB,hBi⟩
    exact ⟨CentralExtension K B,inferInstance,CentralExtension.finitelyPresented hB,
      CentralExtension.map i (le_of_eq hBi.symm),
      CentralExtension.map_injective i hi hBi⟩
  · rintro ⟨K,_,_,j,hj⟩
    obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := K)
    have : Group.FG K := Group.fg_of_surjective hp
    let i : G →* K := j.comp HNNExtension.of
    let t : K := j HNNExtension.t
    let k : G →* K × K := i.prod ((MulAut.conj t).toMonoidHom.comp i)
    let d : K →* K × K := (MonoidHom.id K).prod (MonoidHom.id K)
    have hd : d.range.FG := by
      rw [MonoidHom.range_eq_map]
      obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup K).FG)
      refine (Subgroup.fg_iff _).mpr ⟨d '' (S : Set K),?_,S.finite_toSet.image d⟩
      rw [← MonoidHom.map_closure,hS]
    refine ⟨K × K,inferInstance,finitelyPresented_prod,k,?_,d.range,hd,?_⟩
    · intro x y he
      exact HNNExtension.of_injective (φ := MulEquiv.refl A)
        (hj (congrArg Prod.fst he))
    · ext g
      change (∃ z, d z = k g) ↔ g ∈ A
      constructor
      · rintro ⟨z,hz⟩
        have h₀ : z = i g := congrArg Prod.fst hz
        have h₁ : z = t * i g * t⁻¹ := congrArg Prod.snd hz
        have he : (HNNExtension.t : CentralExtension G A) * HNNExtension.of g *
            HNNExtension.t⁻¹ = HNNExtension.of g := by
          apply hj
          simpa only [i,t,MonoidHom.comp_apply,map_mul,map_inv] using h₁.symm.trans h₀
        apply (HNN.commute_t_iff g).mp
        change HNNExtension.t * HNNExtension.of g = HNNExtension.of g * HNNExtension.t
        calc
          HNNExtension.t * HNNExtension.of g =
              ((HNNExtension.t * HNNExtension.of g) * HNNExtension.t⁻¹) *
                (HNNExtension.t : CentralExtension G A) := (inv_mul_cancel_right _ _).symm
          _ = HNNExtension.of g * HNNExtension.t := congrArg (fun x : CentralExtension G A ↦
            x * HNNExtension.t) he
      · intro hg
        refine ⟨i g,?_⟩
        apply Prod.ext
        · rfl
        · change i g = t * i g * t⁻¹
          have he := HNNExtension.equiv_eq_conj (φ := MulEquiv.refl A) ⟨g,hg⟩
          simpa only [i,t,MonoidHom.comp_apply,map_mul,map_inv,MulEquiv.refl_apply] using
            congrArg j he

theorem embeds_of_benign_kernel_fp {D : Type v} [Group D]
    [Group.IsFinitelyPresented G] (q : G →* D) (hq : Function.Surjective q)
    (hben : IsBenign q.ker) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : D →* K), Function.Injective i := by
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := G)
  let p' : FreeGroup (ULift.{u} (Fin n)) →* G := p.comp (FreeGroup.map ULift.down)
  have hp' : Function.Surjective p' := hp.comp
    (FreeGroup.map_surjective (fun a ↦ ⟨ULift.up a,rfl⟩))
  apply embeds_of_benign_kernel (q.comp p') (hq.comp hp')
  exact hben.comap p'

end Higman

namespace Higman.CentralExtension
open Monoid Coprod Multiplicative
variable {G : Type u} [Group G] (A : Subgroup G)

abbrev rawProjection : G ∗ Multiplicative ℤ →* CentralExtension G A :=
  (HNNExtension.con G A A (MulEquiv.refl A)).mk'

theorem rawProjection_ker : (rawProjection A).ker =
    Subgroup.normalClosure (relation '' (A : Set G)) := by
  let C := HNNExtension.con G A A (MulEquiv.refl A)
  let N := Subgroup.normalClosure (relation '' (A : Set G))
  let q := QuotientGroup.mk' N
  have hC : C ≤ Con.ker q := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨a,rfl,rfl⟩
    apply mul_inv_eq_one.mp
    have hh : q (relation (a : G)) = 1 := (QuotientGroup.eq_one_iff (relation (a : G))).mpr
      (Subgroup.subset_normalClosure (show relation (a : G) ∈ relation '' (A : Set G) from
        ⟨a,a.2,rfl⟩))
    simpa only [relation,map_mul,map_inv,MulEquiv.refl_apply] using hh
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    apply (hC ?_).trans (map_one q)
    apply (Con.eq C).mp
    exact hx.trans (map_one C.mk').symm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨g,hg,rfl⟩
    change rawProjection A (relation g) = 1
    change (HNNExtension.t * HNNExtension.of g) *
      (HNNExtension.of g * (HNNExtension.t : CentralExtension G A))⁻¹ = 1
    rw [HNNExtension.t_mul_of (φ := MulEquiv.refl A) ⟨g,hg⟩]
    exact mul_inv_cancel _

variable {H : Type u} [Group H]

theorem rawMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (Coprod.map f (MonoidHom.id (Multiplicative ℤ))) := by
  apply MonoidHom.range_eq_top.mp
  rw [Coprod.range_eq]
  have h₀ : ((Coprod.map f (MonoidHom.id (Multiplicative ℤ))).comp inl).range =
      (inl : H →* H ∗ Multiplicative ℤ).range := by
    change ((inl : H →* H ∗ Multiplicative ℤ).comp f).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,← MonoidHom.range_eq_map]
  rw [h₀]
  exact Coprod.range_inl_sup_range_inr

theorem rawProjection_ker_map (f : G →* H) (hf : Function.Surjective f) :
    (rawProjection A).ker.map (Coprod.map f (MonoidHom.id (Multiplicative ℤ))) =
      (rawProjection (A.map f)).ker := by
  rw [rawProjection_ker,rawProjection_ker,
    Subgroup.map_normalClosure _ _ (rawMap_surjective f hf)]
  congr 1
  ext x
  constructor
  · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
    refine ⟨f g,⟨g,hg,rfl⟩,?_⟩
    simp [relation]
  · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
    refine ⟨relation g,⟨g,hg,rfl⟩,?_⟩
    simp [relation]

end Higman.CentralExtension

namespace Higman.IsBenign
open Monoid Coprod Multiplicative
variable {G H : Type u} [Group G] [Group H]
  [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H]
  {A : Subgroup G}

theorem map_surjective (hA : IsBenign A) (f : G →* H) (hf : Function.Surjective f) :
    IsBenign (A.map f) := by
  obtain ⟨K,_,_,j,hj⟩ := benign_iff_centralExtension_embeds.mp hA
  let π := CentralExtension.rawProjection A
  let F := Coprod.map f (MonoidHom.id (Multiplicative ℤ))
  let k : G ∗ Multiplicative ℤ →* K × (H ∗ Multiplicative ℤ) := (j.comp π).prod F
  let i : H ∗ Multiplicative ℤ →* K × (H ∗ Multiplicative ℤ) :=
    (1 : H ∗ Multiplicative ℤ →* K).prod (MonoidHom.id _)
  have hi : Function.Injective i := by
    intro x y he
    exact congrArg Prod.snd he
  have hk : k.range.FG := by
    obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := G ∗ Multiplicative ℤ)
    have : Group.FG (G ∗ Multiplicative ℤ) := Group.fg_of_surjective hp
    obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup (G ∗ Multiplicative ℤ)).FG)
    refine (Subgroup.fg_iff _).mpr ⟨k '' (S : Set (G ∗ Multiplicative ℤ)),?_,
      S.finite_toSet.image k⟩
    rw [← MonoidHom.map_closure,hS,← MonoidHom.range_eq_map]
  have hker : k.range.comap i = (CentralExtension.rawProjection (A.map f)).ker := by
    rw [← CentralExtension.rawProjection_ker_map A f hf]
    ext x
    change (∃ y, k y = i x) ↔ ∃ y, π y = 1 ∧ F y = x
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨y,?_,congrArg Prod.snd hy⟩
      apply hj
      exact (congrArg Prod.fst hy).trans (map_one j).symm
    · rintro ⟨y,hy,hxy⟩
      refine ⟨y,Prod.ext ?_ hxy⟩
      change j (π y) = 1
      rw [hy,map_one]
  have hben : IsBenign (CentralExtension.rawProjection (A.map f)).ker :=
    ⟨K × (H ∗ Multiplicative ℤ),inferInstance,finitelyPresented_prod,i,hi,k.range,hk,hker⟩
  apply benign_iff_centralExtension_embeds.mpr
  exact embeds_of_benign_kernel_fp (CentralExtension.rawProjection (A.map f))
    Con.mk'_surjective hben

end Higman.IsBenign

namespace Higman.HNNTransport
open HNNExtension
variable {G : Type u} [Group G] {K : Type v} [Group K]
  {A B : Subgroup G} {C D : Subgroup K} (φ : A ≃* B) (ψ : C ≃* D)
  (i : G →* K) (hA : C.comap i = A) (hB : D.comap i = B)
  (hφ : ∀ a : A, i (φ a) = ψ ⟨i a,show i a ∈ C from hA.symm ▸ a.2⟩)

def map : HNNExtension G A B φ →* HNNExtension K C D ψ :=
  HNNExtension.lift (HNNExtension.of.comp i) HNNExtension.t (by
    intro a
    simpa only [MonoidHom.comp_apply,hφ a] using
      HNNExtension.t_mul_of (φ := ψ) ⟨i a,show i a ∈ C from hA.symm ▸ a.2⟩)

@[simp] theorem map_of (g : G) : map φ ψ i hA hφ (HNNExtension.of g) =
    HNNExtension.of (i g) := by simp [map]

@[simp] theorem map_t : map φ ψ i hA hφ HNNExtension.t = HNNExtension.t := by simp [map]

def mapWord (r : NormalWord.ReducedWord G A B) : NormalWord.ReducedWord K C D where
  head := i r.head
  toList := r.toList.map (fun p ↦ (p.1,i p.2))
  chain := by
    apply (List.isChain_map _).mpr
    apply r.chain.imp
    intro a b hab hmem
    apply hab
    rcases Int.units_eq_one_or a.1 with ha | ha
    · have hm : i a.2 ∈ C := by simpa [ha,HNNExtension.toSubgroup] using hmem
      have hm' : a.2 ∈ A := hA ▸ hm
      simpa [ha,HNNExtension.toSubgroup] using hm'
    · have hm : i a.2 ∈ D := by simpa [ha,HNNExtension.toSubgroup] using hmem
      have hm' : a.2 ∈ B := hB ▸ hm
      simpa [ha,HNNExtension.toSubgroup] using hm'

@[simp] theorem mapWord_prod (r : NormalWord.ReducedWord G A B) :
    (mapWord i hA hB r).prod ψ = map φ ψ i hA hφ (r.prod φ) := by
  simp [NormalWord.ReducedWord.prod,mapWord,map_list_prod,List.map_map,Function.comp_def]

include hB

theorem mem_base_of_map_mem_base (x : HNNExtension G A B φ)
    (hx : map φ ψ i hA hφ x ∈ (HNNExtension.of : K →* HNNExtension K C D ψ).range) :
    x ∈ (HNNExtension.of : G →* HNNExtension G A B φ).range := by
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A B
  let r := NormalWord.equiv φ d x
  have hr : r.prod φ = x := (NormalWord.equiv φ d).symm_apply_apply x
  have hm : (mapWord i hA hB r.toReducedWord).prod ψ ∈ HNNExtension.of.range := by
    rw [mapWord_prod φ ψ i hA hB hφ]
    rw [hr]
    exact hx
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range ψ
    (mapWord i hA hB r.toReducedWord) hm
  have hnil : r.toList = [] := by simpa [mapWord] using hn
  refine ⟨r.head,?_⟩
  rw [← hr]
  simp [NormalWord.ReducedWord.prod,hnil]

theorem map_injective (hi : Function.Injective i) : Function.Injective (map φ ψ i hA hφ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hm : map φ ψ i hA hφ x ∈ HNNExtension.of.range := by
    change map φ ψ i hA hφ x = 1 at hx
    rw [hx]
    exact Subgroup.one_mem _
  obtain ⟨g,rfl⟩ := mem_base_of_map_mem_base φ ψ i hA hB hφ x hm
  change map φ ψ i hA hφ (HNNExtension.of g) = 1 at hx
  rw [map_of] at hx
  have hg : i g = 1 := HNNExtension.of_injective (φ := ψ) (hx.trans (map_one _).symm)
  have hg' : g = 1 := hi (hg.trans (map_one i).symm)
  rw [Subgroup.mem_bot,hg',map_one]

theorem range_comap_of : (map φ ψ i hA hφ).range.comap HNNExtension.of = i.range := by
  ext k
  constructor
  · rintro ⟨x,hx⟩
    have hm : map φ ψ i hA hφ x ∈ HNNExtension.of.range := ⟨k,hx.symm⟩
    obtain ⟨g,rfl⟩ := mem_base_of_map_mem_base φ ψ i hA hB hφ x hm
    refine ⟨g,?_⟩
    apply HNNExtension.of_injective (φ := ψ)
    simpa using hx
  · rintro ⟨g,rfl⟩
    exact ⟨HNNExtension.of g,map_of φ ψ i hA hφ g⟩

end Higman.HNNTransport

namespace Higman.HNNSubgroup
open HNNExtension
variable {G : Type u} [Group G] {A B : Subgroup G} (φ : A ≃* B)
  (S : Subgroup G) (hS : ∀ a : A, (φ a : G) ∈ S ↔ (a : G) ∈ S)

def restricted : A.comap S.subtype ≃* B.comap S.subtype where
  toFun a := ⟨⟨φ ⟨a,a.2⟩,(hS ⟨a,a.2⟩).mpr a.1.2⟩,(φ ⟨a,a.2⟩).2⟩
  invFun b := ⟨⟨φ.symm ⟨b,b.2⟩,(hS (φ.symm ⟨b,b.2⟩)).mp (by simp)⟩,
    (φ.symm ⟨b,b.2⟩).2⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : A ↦ (z : G)) (φ.symm_apply_apply ⟨a,a.2⟩)
  right_inv b := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : B ↦ (z : G)) (φ.apply_symm_apply ⟨b,b.2⟩)
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : B ↦ (z : G)) (φ.map_mul ⟨a,a.2⟩ ⟨b,b.2⟩)

def inclusion : HNNExtension S (A.comap S.subtype) (B.comap S.subtype)
    (restricted φ S hS) →* HNNExtension G A B φ :=
  HNNTransport.map (restricted φ S hS) φ S.subtype rfl (fun _ ↦ rfl)

@[simp] theorem inclusion_of (s : S) :
    inclusion φ S hS (HNNExtension.of s) = HNNExtension.of (s : G) := by
  exact HNNTransport.map_of _ _ _ _ _ s

@[simp] theorem inclusion_t : inclusion φ S hS HNNExtension.t = HNNExtension.t := by
  exact HNNTransport.map_t _ _ _ _ _

theorem range_comap_of : (inclusion φ S hS).range.comap HNNExtension.of = S := by
  exact (HNNTransport.range_comap_of (restricted φ S hS) φ S.subtype rfl rfl
    (fun _ ↦ rfl)).trans (Subgroup.range_subtype S)

include hS

theorem closure_comap_of :
    (Subgroup.closure (HNNExtension.of '' (S : Set G) ∪
      {(HNNExtension.t : HNNExtension G A B φ)})).comap HNNExtension.of = S := by
  apply le_antisymm
  · have hle : Subgroup.closure (HNNExtension.of '' (S : Set G) ∪
        {(HNNExtension.t : HNNExtension G A B φ)}) ≤ (inclusion φ S hS).range := by
      apply (Subgroup.closure_le _).mpr
      rintro _ (⟨s,hs,rfl⟩ | ht)
      · exact ⟨HNNExtension.of ⟨s,hs⟩,inclusion_of φ S hS ⟨s,hs⟩⟩
      · obtain rfl := Set.mem_singleton_iff.mp ht
        exact ⟨HNNExtension.t,inclusion_t φ S hS⟩
    exact (Subgroup.comap_mono hle).trans_eq (range_comap_of φ S hS)
  · intro s hs
    exact Subgroup.subset_closure (Or.inl ⟨s,hs,rfl⟩)

end Higman.HNNSubgroup

end UniversalFinitelyPresentedProof

end OAI
