import Mathlib
import OAI.Probability.ThorpRouting.Adaptive.TailShapes

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.ButterflyReverse
open scoped BigOperators

lemma site_surjective (d : ℕ) : Function.Surjective (site d) := by
  induction d with
  | zero => intro t; exact Fin.elim0 t.1.1
  | succ d ih =>
    rintro ⟨⟨i,x⟩,hx⟩
    refine Fin.cases ?_ (fun j => ?_) i hx
    · intro hx0
      refine ⟨Sum.inl (Fin.tail x), ?_⟩
      apply Subtype.ext
      simp only [site, Prod.mk.injEq, true_and]
      rw [←hx0,Fin.cons_self_tail]
    · intro hxj
      obtain ⟨t,ht⟩ := ih ⟨(j,Fin.tail x),hxj⟩
      refine ⟨Sum.inr (x 0,t), ?_⟩
      apply Subtype.ext
      simp only [site,ht,Fin.cons_self_tail]

noncomputable def siteEquiv (d : ℕ) : SwitchIndex d ≃ Site d :=
  Equiv.ofBijective (site d) ⟨site_injective d,site_surjective d⟩

def reverseCard (d : ℕ) : Equiv.Perm (Card d) where
  toFun x := fun i => x i.rev
  invFun x := fun i => x i.rev
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] lemma reverseCard_apply (d : ℕ) (x : Card d) (i : Fin d) :
    reverseCard d x i = x i.rev := rfl

@[simp] lemma reverseCard_involutive (d : ℕ) (x : Card d) :
    reverseCard d (reverseCard d x) = x := by funext i; simp

def mirrorSite (d : ℕ) : Equiv.Perm (Site d) where
  toFun s := ⟨(s.1.1.rev,reverseCard d s.1.2),by simpa using s.2⟩
  invFun s := ⟨(s.1.1.rev,reverseCard d s.1.2),by simpa using s.2⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

noncomputable def mirrorSwitch (d : ℕ) : Equiv.Perm (SwitchIndex d) :=
  (siteEquiv d).trans ((mirrorSite d).trans (siteEquiv d).symm)

lemma site_mirrorSwitch (d : ℕ) (t : SwitchIndex d) :
    site d (mirrorSwitch d t) = mirrorSite d (site d t) := by
  exact (siteEquiv d).apply_symm_apply _

lemma routeDomain_site (d : ℕ) (x y : Card d) (t : SwitchIndex d) :
    t ∈ routeDomain d x y ↔
      ∀ j : Fin d, j ≠ (site d t).1.1 →
      (site d t).1.2 j = if j < (site d t).1.1 then x j else y j := by
  classical
  induction d with
  | zero => exact Empty.elim t
  | succ d ih =>
    cases t with
    | inl z =>
      change Sum.inl z ∈ (insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
        Finset (Sum (Card d) (Bool × SwitchIndex d))) ↔ _
      simp only [Finset.mem_insert, Sum.inl.injEq,Finset.mem_image,
        reduceCtorEq,and_false,exists_false,or_false]
      constructor
      · intro hz j hj
        subst z
        have hj0 : j ≠ 0 := hj
        obtain ⟨i,rfl⟩ := Fin.eq_succ_of_ne_zero hj0
        simp [site,Fin.tail]
      · intro h
        funext j
        have he := h j.succ (by simp [site])
        simpa [site,Fin.tail] using he
    | inr z =>
      obtain ⟨b,t⟩ := z
      change Sum.inr (b,t) ∈ (insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
        Finset (Sum (Card d) (Bool × SwitchIndex d))) ↔ _
      simp only [Finset.mem_insert,reduceCtorEq,false_or,Finset.mem_image,Sum.inr.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨s,hs,hb,ht⟩
        subst s
        have hst := (ih (Fin.tail x) (Fin.tail y) t).mp hs
        intro j hj
        refine Fin.cases ?_ (fun i => ?_) j hj
        · intro _
          simp [site,hb]
        · intro hi
          have hi' : i ≠ (site d t).1.1 := by simpa [site] using hi
          simpa [site,Fin.tail] using hst i hi'
      · intro h
        have hb := h 0 (by simpa only [site] using (Fin.succ_ne_zero (site d t).1.1).symm)
        have hb' : x 0 = b := by simpa [site] using hb.symm
        refine ⟨t,?_,hb',rfl⟩
        apply (ih (Fin.tail x) (Fin.tail y) t).mpr
        intro j hj
        have he := h j.succ (by simpa [site] using hj)
        simpa [site,Fin.tail] using he

lemma routeValue_site (d : ℕ) (x y : Card d) (t : SwitchIndex d) :
    routeValue d x y t = Bool.xor (x (site d t).1.1) (y (site d t).1.1) := by
  induction d with
  | zero => exact Empty.elim t
  | succ d ih =>
    cases t with
    | inl z => rfl
    | inr z => exact ih (Fin.tail x) (Fin.tail y) z.2

lemma mirrorSwitch_involutive (d : ℕ) (t : SwitchIndex d) :
    mirrorSwitch d (mirrorSwitch d t) = t := by
  apply site_injective d
  rw [site_mirrorSwitch,site_mirrorSwitch]
  apply Subtype.ext
  simp [mirrorSite]

lemma mirror_routeDomain (d : ℕ) (x y : Card d) (t : SwitchIndex d)
    (ht : t ∈ routeDomain d x y) :
    mirrorSwitch d t ∈ routeDomain d (reverseCard d y) (reverseCard d x) := by
  rw [routeDomain_site,site_mirrorSwitch]
  intro j hj
  have hj' : j.rev ≠ (site d t).1.1 := by
    intro h
    apply hj
    change j = (site d t).1.1.rev
    rw [←h,Fin.rev_rev]
  have he := (routeDomain_site d x y t).mp ht j.rev hj'
  change (site d t).1.2 j.rev =
    if j < (site d t).1.1.rev then y j.rev else x j.rev
  rw [he]
  have hord : j < (site d t).1.1.rev ↔ ¬j.rev < (site d t).1.1 := by
    rw [Fin.lt_rev_iff]
    constructor
    · intro h
      exact not_lt_of_ge h.le
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hj')
  by_cases h : j.rev < (site d t).1.1 <;> simp [h,hord]

lemma mirror_routeValue (d : ℕ) (x y : Card d) (t : SwitchIndex d) :
    routeValue d (reverseCard d y) (reverseCard d x) (mirrorSwitch d t) =
      routeValue d x y t := by
  rw [routeValue_site,routeValue_site,site_mirrorSwitch]
  simp only [mirrorSite,Equiv.coe_fn_mk,reverseCard_apply,Fin.rev_rev]
  exact Bool.xor_comm _ _

noncomputable def mirrorCoins (d : ℕ) : Equiv.Perm (SwitchIndex d → Bool) where
  toFun ω := fun t => ω (mirrorSwitch d t)
  invFun ω := fun t => ω (mirrorSwitch d t)
  left_inv ω := by funext t; change ω (mirrorSwitch d (mirrorSwitch d t)) = ω t; rw [mirrorSwitch_involutive]
  right_inv ω := by funext t; change ω (mirrorSwitch d (mirrorSwitch d t)) = ω t; rw [mirrorSwitch_involutive]

lemma mirror_endpoint (d : ℕ) (ω : SwitchIndex d → Bool) (x y : Card d)
    (hxy : butterflyPerm d (decodeButterfly d ω) x = y) :
    butterflyPerm d (decodeButterfly d (mirrorCoins d ω)) (reverseCard d y) =
      reverseCard d x := by
  apply (butterfly_endpoint_iff d _ _ _).mpr
  intro t ht
  have ht' := mirror_routeDomain d (reverseCard d y) (reverseCard d x) t ht
  simp only [reverseCard_involutive] at ht'
  have he := (butterfly_endpoint_iff d ω x y).mp hxy (mirrorSwitch d t) ht'
  change ω (mirrorSwitch d t) = _
  rw [he]
  have hv := mirror_routeValue d x y (mirrorSwitch d t)
  rw [mirrorSwitch_involutive] at hv
  exact hv.symm

lemma butterfly_mirror (d : ℕ) (ω : SwitchIndex d → Bool) :
    butterflyPerm d (decodeButterfly d (mirrorCoins d ω)) =
      reverseCard d * (butterflyPerm d (decodeButterfly d ω))⁻¹ * reverseCard d := by
  apply Equiv.ext
  intro x
  have he := mirror_endpoint d ω
    ((butterflyPerm d (decodeButterfly d ω))⁻¹ (reverseCard d x)) (reverseCard d x)
    (Equiv.apply_symm_apply _ _)
  simpa only [reverseCard_involutive,Equiv.Perm.mul_apply] using he

def reverseOrder (d : ℕ) : Equiv.Perm (Fin d) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

lemma relabel_mul (d : ℕ) (a b : Equiv.Perm (Fin d)) :
    StrongSmoothing.coordinateRelabel d (a*b) =
      StrongSmoothing.coordinateRelabel d a * StrongSmoothing.coordinateRelabel d b := rfl

lemma relabel_reverse (d : ℕ) :
    StrongSmoothing.coordinateRelabel d (reverseOrder d) = reverseCard d := rfl

lemma reverseCard_sq (d : ℕ) : reverseCard d * reverseCard d = 1 := by
  ext x i
  simp

lemma sweep_mirror (d : ℕ) (order : Equiv.Perm (Fin d)) (ω : SwitchIndex d → Bool) :
    StrongSmoothing.sweep d (order*reverseOrder d) (mirrorCoins d ω) =
      (StrongSmoothing.sweep d order ω)⁻¹ := by
  simp only [StrongSmoothing.sweep,relabel_mul,relabel_reverse,butterfly_mirror,mul_inv_rev]
  have hR : (reverseCard d)⁻¹ = reverseCard d := by
    exact inv_eq_of_mul_eq_one_right (reverseCard_sq d)
  rw [hR]
  calc
    _ = StrongSmoothing.coordinateRelabel d order *
        (reverseCard d*reverseCard d) *
        (butterflyPerm d (decodeButterfly d ω))⁻¹ *
        (reverseCard d*reverseCard d) * (StrongSmoothing.coordinateRelabel d order)⁻¹ := by group
    _ = _ := by rw [reverseCard_sq]; group

lemma sweepKernel_reverse (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    StrongSmoothing.sweepKernel d l (order*reverseOrder d) =
      (StrongSmoothing.sweepKernel d l order).transpose := by
  classical
  rw [StrongSmoothing.sweepKernel_law,StrongSmoothing.sweepKernel_law,
    ←StrongSmoothing.PermLaw.inverse]
  ext x y
  unfold StrongSmoothing.PermLaw.kernel
  rw [finiteMean_equiv (mirrorCoins d)]
  apply finiteMean_congr
  intro ω
  change (if StrongSmoothing.tuplePerm
      (StrongSmoothing.sweep d (order*reverseOrder d) (mirrorCoins d ω)) x = y then (1:ℝ) else 0) = _
  rw [sweep_mirror,StrongSmoothing.tuplePerm_inverse]

lemma reflectedKernel_reverse (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    StrongSmoothing.reflectedKernel d l order true =
      StrongSmoothing.reflectedKernel d l (order*reverseOrder d) false := by
  simp only [StrongSmoothing.reflectedKernel,Bool.false_eq_true,
    ↓reduceIte,sweepKernel_reverse,Matrix.transpose_transpose]

end Thorp.ButterflyReverse

namespace Thorp.StrongTail
open scoped BigOperators Classical

section
open Specht

def tailDiagram (μ : YoungDiagram) : YoungDiagram :=
  YoungDiagram.ofRowLens μ.rowLens.tail μ.rowLens_sorted.pairwise.tail.sortedGE

lemma mem_tailDiagram (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ tailDiagram μ ↔ (i+1,j) ∈ μ := by
  rw [tailDiagram, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨hi,hj⟩
    rw [List.getElem_tail,YoungDiagram.get_rowLens] at hj
    exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  · intro h
    have hi : i+1 < μ.colLen 0 :=
      (YoungDiagram.mem_iff_lt_colLen.mp h).trans_le (μ.colLen_anti 0 j (Nat.zero_le _))
    have hi' : i < μ.rowLens.tail.length := by simp only [List.length_tail,YoungDiagram.length_rowLens]; omega
    refine ⟨hi', ?_⟩
    simpa only [List.getElem_tail,YoungDiagram.get_rowLens] using YoungDiagram.mem_iff_lt_rowLen.mp h

lemma tail_height (μ : YoungDiagram) : (tailDiagram μ).colLen 0 = μ.colLen 0 - 1 := by
  rw [←YoungDiagram.length_rowLens]
  exact (YoungDiagram.rowLens_length_ofRowLens (fun x hx => μ.pos_of_mem_rowLens x (List.mem_of_mem_tail hx))).trans
    (by simp only [List.length_tail,YoungDiagram.length_rowLens])

noncomputable def tailCellEquiv (μ : YoungDiagram) : Cell (tailDiagram μ) ≃ Tail μ where
  toFun x := ⟨⟨(x.1.1+1,x.1.2),(mem_tailDiagram μ _ _).mp x.2⟩,by simp [row]⟩
  invFun x := ⟨(row x.1-1,col x.1),(mem_tailDiagram μ _ _).mpr (by
    have he : row x.1-1+1 = row x.1 := by have := x.2; omega
    change (row x.1-1+1,col x.1) ∈ μ
    rw [he]
    exact x.1.2)⟩
  left_inv x := by apply Subtype.ext; simp [row,col]
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · change row x.1-1+1 = row x.1
      have := x.2; omega
    · rfl

noncomputable abbrev upCell (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : Cell μ := (tailCellEquiv μ x).1

@[simp] lemma upCell_row (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : row (upCell μ x) = row x+1 := rfl
@[simp] lemma upCell_col (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : col (upCell μ x) = col x := rfl

lemma tail_card_eq (μ : YoungDiagram) : (tailDiagram μ).card = μ.card-μ.rowLen 0 := by
  rw [←card_cell, Fintype.card_congr (tailCellEquiv μ), tail_card]

noncomputable def extendPerm (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    Equiv.Perm (Cell μ) := p.extendDomain (tailCellEquiv μ)

@[simp] lemma extendPerm_up (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (x : Cell (tailDiagram μ)) : extendPerm μ p (upCell μ x) = upCell μ (p x) :=
  Equiv.Perm.extendDomain_apply_image p (tailCellEquiv μ) x

lemma extendPerm_top (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (x : Cell μ) (hx : row x=0) : extendPerm μ p x = x :=
  Equiv.Perm.extendDomain_apply_not_subtype p (tailCellEquiv μ) (not_not.mpr hx)

@[simp] lemma extendPerm_inv (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    (extendPerm μ p)⁻¹ = extendPerm μ p⁻¹ := Equiv.Perm.extendDomain_symm _ _

@[simp] lemma extendPerm_sign (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    permSign (extendPerm μ p) = permSign p := by
  simp [extendPerm,permSign,Equiv.Perm.sign_extendDomain]

noncomputable def liftRows (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) (x : Cell μ) : Fin (μ.colLen 0) :=
  if hx : row x ≠ 0 then
    ⟨(f.1 ((tailCellEquiv μ).symm ⟨x,hx⟩)).val+1,by
      have h := (f.1 ((tailCellEquiv μ).symm ⟨x,hx⟩)).isLt
      have hh := tail_height μ
      omega⟩
  else rowIndex x

@[simp] lemma liftRows_up (μ : YoungDiagram) (f : Tabloid (tailDiagram μ))
    (x : Cell (tailDiagram μ)) : (liftRows μ f (upCell μ x)).val = (f.1 x).val+1 := by
  simp [liftRows,upCell]

lemma liftRows_top (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) (x : Cell μ) (hx : row x=0) :
    liftRows μ f x = rowIndex x := by simp [liftRows,hx]

lemma liftRows_perm (μ : YoungDiagram) (f : Tabloid (tailDiagram μ))
    (p : Equiv.Perm (Cell (tailDiagram μ))) (hf : f.1 = rowIndex ∘ p) :
    liftRows μ f = rowIndex ∘ extendPerm μ p := by
  funext x
  by_cases hx : row x = 0
  · simp [liftRows_top μ f x hx,extendPerm_top μ p x hx]
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he]
    apply Fin.ext
    simp [hf,Function.comp_apply,rowIndex]

noncomputable def liftTabloid (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) : Tabloid μ :=
  ⟨liftRows μ f, by obtain ⟨p,hp⟩ := f.2; exact ⟨extendPerm μ p,liftRows_perm μ f p hp⟩⟩

@[simp] lemma liftTabloid_base (μ : YoungDiagram) :
    liftTabloid μ (baseTabloid (tailDiagram μ)) = baseTabloid μ := by
  apply Subtype.ext
  funext x
  by_cases hx : row x=0
  · exact liftRows_top μ _ x hx
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he]
    apply Fin.ext
    exact liftRows_up μ _ y

lemma liftTabloid_action (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (f : Tabloid (tailDiagram μ)) :
    liftTabloid μ (tabloidAct p f) = tabloidAct (extendPerm μ p) (liftTabloid μ f) := by
  apply Subtype.ext
  funext x
  change liftRows μ (tabloidAct p f) x = liftRows μ f ((extendPerm μ p)⁻¹ x)
  rw [extendPerm_inv]
  by_cases hx : row x=0
  · rw [extendPerm_top μ p⁻¹ x hx,liftRows_top μ _ x hx,liftRows_top μ _ x hx]
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he,extendPerm_up]
    apply Fin.ext
    simp only [liftRows_up,tabloidAct_apply]

noncomputable def restrictTabloids (μ : YoungDiagram) :
    (Tabloid μ → ℂ) →ₗ[ℂ] (Tabloid (tailDiagram μ) → ℂ) where
  toFun v := fun f => v (liftTabloid μ f)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma restrict_action (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (v : Tabloid μ → ℂ) :
    restrictTabloids μ (tabloidRep μ (extendPerm μ p) v) =
      tabloidRep (tailDiagram μ) p (restrictTabloids μ v) := by
  ext f
  change v (tabloidAct (extendPerm μ p)⁻¹ (liftTabloid μ f)) = v (liftTabloid μ (tabloidAct p⁻¹ f))
  rw [extendPerm_inv,liftTabloid_action]

lemma extend_colGroup (μ : YoungDiagram) (c : colGroup (tailDiagram μ)) :
    extendPerm μ c ∈ colGroup μ := by
  intro x
  by_cases hx : row x=0
  · rw [extendPerm_top μ c x hx]
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he,extendPerm_up,upCell_col,upCell_col]
    exact c.2 y

lemma restrict_polytabloid (μ : YoungDiagram) :
    restrictTabloids μ (polytabloid μ) = polytabloid (tailDiagram μ) := by
  let v := restrictTabloids μ (polytabloid μ)
  have hv (c : colGroup (tailDiagram μ)) :
      tabloidRep (tailDiagram μ) c v = permSign (c:Equiv.Perm (Cell (tailDiagram μ))) • v := by
    rw [←restrict_action]
    rw [polytabloid_col_action μ ⟨extendPerm μ c,extend_colGroup μ c⟩]
    simp only [map_smul,extendPerm_sign]
    rfl
  have ha : alternator (colGroup (tailDiagram μ)) (tabloidRep (tailDiagram μ)) v =
      (Fintype.card (colGroup (tailDiagram μ)):ℂ) • v := by
    simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,hv,smul_smul,permSign_sq,one_smul]
    ext f
    simp
  have hb : v (baseTabloid (tailDiagram μ)) = 1 := by
    change polytabloid μ (liftTabloid μ (baseTabloid (tailDiagram μ))) = 1
    rw [liftTabloid_base, polytabloid_base]
  have he := alternator_rank_one_exact (tailDiagram μ) v
  rw [ha] at he
  simp only [Pi.smul_apply,hb,smul_eq_mul,mul_one] at he
  have hc : (Fintype.card (colGroup (tailDiagram μ)):ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (smul_right_injective _ hc) he

lemma tail_space_le_image (μ : YoungDiagram) :
    space (tailDiagram μ) ≤ (space μ).map (restrictTabloids μ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  refine ⟨tabloidRep μ (extendPerm μ p) (polytabloid μ), orbit_mem_space μ _, ?_⟩
  rw [restrict_action,restrict_polytabloid]

theorem tail_dimension_le (μ : YoungDiagram) :
    Module.finrank ℂ (space (tailDiagram μ)) ≤ Module.finrank ℂ (space μ) :=
  (Submodule.finrank_mono (tail_space_le_image μ)).trans (Submodule.finrank_map_le _ _)

end
open StrongSmoothing

def DensityAt (p C : ℝ) : Prop :=
  ∀ (d l : ℕ), l ≤ 2^d → ∀ (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x : StrongSmoothing.Tuples d l),
    let H := StrongSmoothing.reflectedKernel d l order rev
    (Thorp.finiteMean (fun y => ((Fintype.card (StrongSmoothing.Tuples d l):ℝ)*H x y)^p)
      ≤ Real.exp (C*l)) ∧
    (Thorp.finiteMean (fun y => ((Fintype.card (StrongSmoothing.Tuples d l):ℝ)*H y x)^p)
      ≤ Real.exp (C*l)) ∧
    (((2:ℝ)^d)^l)⁻¹ * (∑ y, ((((2:ℝ)^d)^l)*H x y)^p) ≤ Real.exp (C*l) ∧
    (((2:ℝ)^d)^l)⁻¹ * (∑ y, ((((2:ℝ)^d)^l)*H y x)^p) ≤ Real.exp (C*l)

lemma reflected_nonneg_both (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x y : Tuples d l) : 0 ≤ reflectedKernel d l order rev x y := by
  cases rev
  · exact reflected_nonneg _ _ _ _ _
  · rw [ButterflyReverse.reflectedKernel_reverse]
    exact reflected_nonneg _ _ _ _ _

lemma reflected_symm_both (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool) :
    (reflectedKernel d l order rev).IsSymm := by
  cases rev
  · exact reflected_symmetric _ _ _
  · rw [ButterflyReverse.reflectedKernel_reverse]
    exact reflected_symmetric _ _ _

lemma reflected_moment_both (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x : Tuples d l) :
    finiteMean (fun y : Tuples d l =>
      ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y)^(1+(1/1000:ℝ))) ≤
      Real.exp (l*(1+heightDecay 1)) := by
  cases rev
  · exact reflected_moment _ _ _ _
  · rw [ButterflyReverse.reflectedKernel_reverse]
    exact reflected_moment _ _ _ _

lemma reflected_moment_small (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x : Tuples d l) {p : ℝ} (hp : 0 < p) (hpq : p ≤ 1+(1/1000:ℝ)) :
    finiteMean (fun y : Tuples d l =>
      ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y)^p) ≤
      Real.exp (l*(1+heightDecay 1)) := by
  let : Nonempty (Tuples d l) := ⟨x⟩
  let q : ℝ := 1+1/1000
  let f := fun y : Tuples d l => (Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y
  have hf : ∀ y, 0 ≤ f y := fun y => mul_nonneg (Nat.cast_nonneg _) (reflected_nonneg_both _ _ _ _ _ _)
  have hq : 0 < q := by norm_num [q]
  have hr : 0 ≤ p/q := (div_pos hp hq).le
  have hr1 : p/q ≤ 1 := (div_le_one hq).mpr hpq
  have he (y) : (f y)^p = ((f y)^q)^(p/q) := by
    rw [←Real.rpow_mul (hf y)]
    congr 1
    field_simp
  simp_rw [show (fun y : Tuples d l => ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y)^p)
    = fun y => ((f y)^q)^(p/q) from funext he]
  apply (mean_rpow_concave _ (fun y => Real.rpow_nonneg (hf y) _) hr hr1).trans
  apply (Real.rpow_le_rpow (finiteMean_nonneg (fun y => Real.rpow_nonneg (hf y) _))
    (reflected_moment_both d l order rev x) hr).trans
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  apply Real.exp_le_exp.mpr
  have hA : 0 ≤ (l:ℝ)*(1+heightDecay 1) := by
    have hh := heightDecay_nonneg 1
    positivity
  nlinarith

lemma log_factorial_le_power (n N : ℕ) (hn : n ≤ N) (_hN : 0 < N) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log N := by
  have hb : (n.factorial:ℝ) ≤ (N:ℝ)^n := by
    exact_mod_cast (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hn n)
  simpa only [Real.log_pow] using Real.log_le_log (by positivity : (0:ℝ)<n.factorial) hb

lemma log_normalization_le (N l : ℕ) (hN : 0 < N) (hl : l ≤ N) :
    Real.log ((N:ℝ)^l/(N.descFactorial l:ℝ)) ≤ 2*l := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hMp : (0:ℝ)<N.descFactorial l := by exact_mod_cast Nat.descFactorial_pos.mpr hl
  rw [Real.log_div (by positivity) hMp.ne',Real.log_pow]
  by_cases hlow : 2*l ≤ N
  · have hhalf : (N:ℝ)/2 ≤ (N+1-l:ℕ) := by
      have hNat : N ≤ 2*(N+1-l) := by omega
      exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by simpa only [mul_comm] using (show (N:ℝ) ≤ 2*(N+1-l:ℕ) by exact_mod_cast hNat))
    have hb : ((N:ℝ)/2)^l ≤ (N.descFactorial l:ℝ) := by
      apply (pow_le_pow_left₀ (by positivity) hhalf l).trans
      exact_mod_cast Nat.pow_sub_le_descFactorial N l
    have hh := Real.log_le_log (pow_pos (by positivity : (0:ℝ)<(N:ℝ)/2) l) hb
    rw [Real.log_pow,Real.log_div hNp.ne' (by norm_num)] at hh
    have ht : Real.log (2:ℝ) ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    nlinarith [(show (0:ℝ) ≤ l by positivity)]
  · have he : (N.descFactorial l:ℝ)*(Nat.factorial (N-l):ℝ) = N.factorial := by
      have he := Nat.factorial_mul_descFactorial hl
      exact_mod_cast (by simpa only [mul_comm] using he : N.descFactorial l * (N-l).factorial = N.factorial)
    have hh := congrArg Real.log he
    rw [Real.log_mul hMp.ne' (by positivity)] at hh
    have hfull := log_factorial_lower (show 1 ≤ N by omega)
    have hrem := log_factorial_le_power (N-l) N (Nat.sub_le _ _) hN
    rw [Nat.cast_sub hl] at hrem
    have hNle : (N:ℝ) ≤ 2*l := by exact_mod_cast (by omega : N ≤ 2*l)
    linarith

lemma normalized_moment_identity {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) {N : ℝ} (hN : 0 < N) (p : ℝ) :
    N⁻¹*(∑ x, (N*f x)^p) =
     (N/(Fintype.card X:ℝ))^(p-1) * finiteMean (fun x => ((Fintype.card X:ℝ)*f x)^p) := by
  let M : ℝ := Fintype.card X
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have he (x) : (N*f x)^p = (N/M)^p*(M*f x)^p := by
    rw [←Real.mul_rpow (div_nonneg hN.le hM.le) (mul_nonneg hM.le (hf x))]
    congr 1
    field_simp
  simp_rw [he]
  rw [←Finset.mul_sum,Real.rpow_sub (div_pos hN hM),Real.rpow_one]
  unfold finiteMean
  dsimp [M] at hM ⊢
  field_simp

lemma density_at_small_exponent {p : ℝ} (hp : 1 < p) (hpq : p ≤ 1+(1/1000:ℝ)) :
    DensityAt p (3+heightDecay 1) := by
  intro d l hl order rev x
  dsimp only
  let : Nonempty (Tuples d l) := ⟨x⟩
  let H := reflectedKernel d l order rev
  have hm := reflected_moment_small d l order rev x (by linarith : 0<p) hpq
  have hb : Real.exp ((l:ℝ)*(1+heightDecay 1)) ≤ Real.exp ((3+heightDecay 1)*l) := by
    apply Real.exp_le_exp.mpr
    nlinarith [(show (0:ℝ) ≤ l by positivity)]
  have hs (y) : reflectedKernel d l order rev y x = reflectedKernel d l order rev x y := (reflected_symm_both d l order rev).apply _ _
  have hpow : (((2:ℝ)^d)^l)⁻¹ * (∑ y, ((((2:ℝ)^d)^l)*H x y)^p) ≤
      Real.exp ((3+heightDecay 1)*l) := by
    rw [normalized_moment_identity (fun y => H x y) (reflected_nonneg_both d l order rev x)
      (by positivity) p]
    have hrat : ((2:ℝ)^d)^l/(Fintype.card (Tuples d l):ℝ) ≤ Real.exp (2*l) := by
      apply (Real.log_le_iff_le_exp (by positivity)).mp
      rw [tuples_card]
      exact_mod_cast log_normalization_le (2^d) l (by positivity) hl
    have hr : 0 ≤ ((2:ℝ)^d)^l/(Fintype.card (Tuples d l):ℝ) := by positivity
    have hrp : (((2:ℝ)^d)^l/(Fintype.card (Tuples d l):ℝ))^(p-1) ≤ Real.exp (2*l) := by
      apply (Real.rpow_le_rpow hr hrat (by linarith)).trans
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hpl : p-1 ≤ 1 := by linarith
      nlinarith [(show (0:ℝ) ≤ l by positivity)]
    apply (mul_le_mul hrp hm (finiteMean_nonneg (fun y => Real.rpow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (reflected_nonneg_both d l order rev x y)) _)) (Real.exp_pos _).le).trans
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    rfl
  dsimp [H] at hpow
  refine ⟨hm.trans hb,?_,hpow,?_⟩
  · simpa only [hs] using hm.trans hb
  · simpa only [hs] using hpow

end Thorp.StrongTail

namespace Thorp.Casimir
open scoped BigOperators Classical

section
open Filter

noncomputable def K (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ)
    (Specht.relabelledUnitary μ e) (palindromePerm d)

noncomputable def traceMoment (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (r : ℕ) : ℝ :=
  (LinearMap.trace ℂ (Specht.hilbertSpace μ) ((K d μ e)^r).toLinearMap).re

noncomputable def fromDistance (d t : ℕ) (σ : Equiv.Perm (Card d)) : ℝ :=
  (1/2:ℝ) * ∑ g : Equiv.Perm (Card d),
    |law d t (g*σ⁻¹) - 1/(Nat.factorial (2^d):ℝ)|

def MainStatement : Prop :=
  ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    (∀ d k : ℕ, 1 ≤ k → k ≤ 2^d → ∀ x : Fin k ↪ Card d,
      (palindromeRowMoment d x (1/64))^(64/65:ℝ) ≤
        Real.exp (C*levelScale (2^d) k)) ∧
    (∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0 < μ.card-μ.rowLen 0 →
        ‖K d μ e‖ ≤ Real.exp (-a*levelScale (2^d) (μ.card-μ.rowLen 0)) ∧
        (Module.finrank ℂ (Specht.space μ):ℝ) * traceMoment d μ e 65 ≤
          Real.exp (C*levelScale (2^d) (μ.card-μ.rowLen 0))) ∧
    (∃ l : ℕ, 0 < l ∧ ∀ starts : (d : ℕ) → Equiv.Perm (Card d),
      Tendsto (fun d => fromDistance d (l*d) (starts d)) atTop (nhds 0))

end

theorem cycleCoefficient_decay (l r : ℕ) (hr : (l:ℝ)/2 ≤ r)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ (l:ℝ)/16) :
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
  have hqE : q ≤ Real.exp ((l:ℝ)/16) := by
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
      _ ≤ (4*Real.exp ((l:ℝ)/16)*E)/Real.exp ((l:ℝ)/8) := by
        apply div_le_div₀ (by positivity) _ (Real.exp_pos _) hden
        have hs := hsqJ.trans hJE
        have hm := mul_le_mul hqE hs (Real.sqrt_nonneg _) (Real.exp_nonneg _)
        nlinarith
      _ = 4*Real.exp ((l:ℝ)/16+(l:ℝ)/32-(l:ℝ)/8) := by
        dsimp [E]
        rw [mul_assoc,←Real.exp_add,mul_div_assoc,←Real.exp_sub]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
        linarith
  change Real.log q / (J:ℝ) + 2*q*Real.sqrt J / Real.sqrt ((2:ℝ)^r) ≤ _
  linarith

theorem palindrome_slab_partial_mgf (r s l : ℕ) (hl : 0 < l) (hs : 2*s ≤ l)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r)) (X : SwitchIndex (s+r) → Bool)
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
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

lemma palindrome_slab_adapted_mul_le (d s l : ℕ) (hsd : s ≤ d) (hl : 0 < l)
    (hs : 2*s ≤ l) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (X : SwitchIndex d → Bool) (F : (SwitchIndex d → Bool) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted d s F) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
    finiteMean (fun Y => F Y*q^(palindromeSlabCost l d e (Y,X))) ≤
      finiteMean F * Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hsd
  exact adapted_mul_mean_le r s F _ hF hA _
    (fun lo => palindrome_slab_partial_mgf r s l hl hs e X lo q hq hlog)

theorem palindrome_family_mgf (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
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

lemma palindrome_family_mgf_decay (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*heightDecay L) := by
  apply (palindrome_family_mgf L n d hL e X q hq hlog).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using h

theorem palindrome_high_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/32) :
    finiteMean (fun Y => q^(palindromeFamilyCost H n d e (Y,X)+
      palindromeFamilyCost (2*H) n d e (Y,X))) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/16 := by rw [Real.log_pow]; norm_num; linarith
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
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/32) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeFamilyCost H n d e ω+
      palindromeFamilyCost (2*H) n d e ω)) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  rw [finiteMean_prod,finiteMean_comm]
  calc
    _ ≤ finiteMean (fun _X : SwitchIndex d → Bool => Real.exp (Fintype.card ι*heightDecay H)) := by
      apply finiteMean_mono
      intro X
      exact palindrome_high_mgf H n d hH e X q hq hlog
    _ = _ := finiteMean_const _

theorem palindrome_cost_mgf_coarse (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/32) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤
      Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  have hd : d ≤ 1*4^d := by have hh := pow_four_ge d; omega
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost 1 d e ω+
      (palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω) := by
    have hh := palindromeCost_family 1 d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hlow (ω : BenesCoins d) : q^(palindromeLowCost 1 d e ω) ≤ Real.exp (Fintype.card ι) := by
    calc
      _ ≤ q^(Fintype.card ι) := pow_le_pow_right₀ hq (by simpa using palindromeLowCost_le 1 d e ω)
      _ = Real.exp (Fintype.card ι*Real.log q) := by rw [Real.exp_nat_mul,Real.exp_log hqp]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)])
  calc
    _ ≤ finiteMean (fun ω : BenesCoins d => Real.exp (Fintype.card ι)*
        q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) := by
      apply finiteMean_mono
      intro ω
      rw [hcost,pow_add]
      exact mul_le_mul_of_nonneg_right (hlow ω) (pow_nonneg hqp.le _)
    _ = Real.exp (Fintype.card ι)*finiteMean (fun ω : BenesCoins d =>
        q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) := by simpa only [mul_comm] using finiteMean_mul_const (fun ω : BenesCoins d => q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) (Real.exp (Fintype.card ι))
    _ ≤ Real.exp (Fintype.card ι)*Real.exp (Fintype.card ι*heightDecay 1) := by
      exact mul_le_mul_of_nonneg_left
        (palindrome_high_full_mgf 1 d d (by decide) e q hq hlog) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

lemma row_moment_coarse (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (a : ℝ) (ha : 0 < a) (ha32 : a ≤ 1/32) :
    palindromeRowMoment d e a ≤ Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  let q : ℝ := (2:ℝ)^a
  have hq : 1 ≤ q := Real.one_le_rpow (by norm_num) ha.le
  have hlog : Real.log q ≤ 1/32 := by
    dsimp [q]
    rw [Real.log_rpow (by norm_num)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    nlinarith
  have hn : (0:ℝ) < ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn0 : (0:ℝ) ≤ ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn1 : ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.descFactorial_le_pow (2^d) (Fintype.card ι)
  have hpow := Real.rpow_le_one hn0 hn1 ha.le
  have hm := palindrome_row_density_moment d e a ha.le
  have he (c : ℕ) : q^c = (2:ℝ)^((c:ℝ)*a) := by
    rw [mul_comm,Real.rpow_mul_natCast (by norm_num)]
  simp_rw [←he] at hm
  exact (hm.trans (mul_le_of_le_one_left (finiteMean_nonneg (fun _ =>
    pow_nonneg (le_trans (by norm_num) hq) _)) hpow)).trans
      (palindrome_cost_mgf_coarse d e q hq hlog)

end Thorp.Casimir


end ThorpNine.Adaptive

end OAI
