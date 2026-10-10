import Mathlib
import OAI.GroupTheory.PeriodicGroups.Presentation.SmallSwapActions

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

instance columnAction : MulAction (Group (ι := ι) (R := R)) (ColumnFrames.Vertex (ι := ι) ε) :=
  MulAction.compHom _ evaluate

@[simp] lemma column_smul (g : Group (ι := ι) (R := R)) (v : ColumnFrames.Vertex (ι := ι) ε) :
    g • v = evaluate g • v := rfl

lemma parabolic_fix (t : ι) {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) :
    g • ColumnFrames.standard ε t = ColumnFrames.standard ε t := by
  apply (ColumnFrames.mem_fixer_iff_standard ε {t} (evaluate g)).mp
    (evaluate_parabolic_le t ⟨g,hg,rfl⟩) t (by simp)

lemma swap_smul (t a : ι) (hta : t≠a) (i : ι) :
    swap (R := R) t a hta • ColumnFrames.standard ε i = ColumnFrames.standard ε (Equiv.swap t a i) := by
  rw [column_smul,evaluate_swap,ColumnFrames.permutation_standard]

variable (hI : MatrixNilKernel ε.toRingHom)

def cosetData (o a b : ι) (hoa : o≠a) (hob : o≠b) (hab : a≠b)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase o}) (R := R))) :
    CosetTransport.Data (H := Group (ι := ι) (R := R)) (F := ZMod 2) (ColumnFrames.rho (ι := ι) ε) where
  P := parabolic o
  o := ColumnFrames.standard ε o
  a := ColumnFrames.standard ε a
  b := ColumnFrames.standard ε b
  s := swap o a hoa
  t := swap a b hab
  fix _ hg := parabolic_fix ε o hg
  sa := by simpa only [Equiv.swap_apply_left] using swap_smul ε o a hoa o
  ss := swap_square o a hoa
  sb := by simpa only [Equiv.swap_apply_of_ne_of_ne hob.symm hab.symm] using swap_smul ε o a hoa b
  tm := swap_mem_parabolic o a b hab hoa.symm hob.symm
  ta := by simpa only [Equiv.swap_apply_left] using swap_smul ε a b hab a
  braid := swap_braid o a b hoa hob hab
  base := ColumnFrames.standard_triangle ε o a b
  oa := ColumnFrames.standard_edge ε o a hoa
  edge_map g u v h := ColumnFrames.edge_map ε (evaluate g) u v h
  tri_map g u v w h := ColumnFrames.triangle_map ε (evaluate g) u v w h
  edge_trans v hv := by
    obtain ⟨U,hU,he⟩ := ColumnFrames.edge_transitive ε hI o a hoa v hv
    rw [←evaluate_parabolic ε hI] at hU
    obtain ⟨p,hp,rfl⟩ := hU
    exact ⟨p,hp,he⟩
  tri_trans v w h₁ h₂ h₃ h := by
    obtain ⟨U,hU,hv,hw⟩ := ColumnFrames.triangle_transitive ε hI o a b hoa hob hab v w h₁ h₂ h₃ h
    rw [←evaluate_parabolic ε hI] at hU
    obtain ⟨p,hp,rfl⟩ := hU
    exact ⟨p,hp,hv,hw⟩
  qnorm g hg ha := by
    apply swap_normalizes_double_fixer ε hI o a hoa ih hg
    rw [ColumnFrames.mem_fixer_iff_standard ε]
    intro k hk
    rcases Finset.mem_insert.mp hk with hko | hk
    · simpa only [hko,column_smul] using parabolic_fix ε o hg
    · have hka : k=a := by simpa using hk
      subst k
      exact ha
  generates := parabolic_swap_generates o a hoa

include ε hI in
lemma evaluate_injective_step (hι : 5 < Fintype.card ι) (o a b : ι)
    (hoa : o≠a) (hob : o≠b) (hab : a≠b)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase o}) (R := R))) :
    Function.Injective (evaluate (ι := ι) (R := R)) := by
  let D := cosetData ε hI o a b hoa hob hab ih
  have hinj := CosetTransport.point_injective (ColumnFrames.rho ε) D
    (fun v => v.property) (ColumnFrames.cones ε hι)
  apply (MonoidHom.ker_eq_bot_iff evaluate).mp
  apply le_antisymm _ bot_le
  intro g hg
  have he : evaluate g=1 := hg
  have hp : CosetTransport.point (ColumnFrames.rho ε) D (QuotientGroup.mk g) =
      CosetTransport.point (ColumnFrames.rho ε) D (QuotientGroup.mk 1) := by
    simp only [CosetTransport.point_mk,column_smul,he,map_one]
  have hcos := hinj hp
  have hmem : g∈parabolic o := by
    change g∈D.P
    have hh := QuotientGroup.eq.mp hcos.symm
    simpa only [inv_one,one_mul] using hh
  exact parabolic_kernel_trivial o ih hmem he

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical
universe u v
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]

theorem evaluate_injective (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
    (ι : Type v) [Fintype ι] [DecidableEq ι] : Function.Injective (evaluate (ι := ι) (R := R)) := by
  suffices h : ∀n : ℕ, ∀(κ : Type v) [Fintype κ] [DecidableEq κ],
      Fintype.card κ=n → Function.Injective (evaluate (ι := κ) (R := R)) from h _ ι rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro κ _ _ hn
    by_cases hs : Fintype.card κ ≤ 5
    · exact evaluate_injective_small hs
    · have hb : 5 < Fintype.card κ := by omega
      obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 3) (β := κ) (by simpa using (by omega : 3 ≤ Fintype.card κ))
      apply evaluate_injective_step ε hI hb (j 0) (j 1) (j 2)
        (j.injective.ne (by decide)) (j.injective.ne (by decide)) (j.injective.ne (by decide))
      apply ih (Fintype.card {i : κ // i∈Finset.univ.erase (j 0)}) ?_ _ rfl
      rw [←hn]
      exact Fintype.card_subtype_lt (x := j 0) (Finset.notMem_erase _ _)

def equivalence (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
    (ι : Type v) [Fintype ι] [DecidableEq ι] : Group (ι := ι) (R := R) ≃* (Matrix ι ι R)ˣ :=
  MulEquiv.ofBijective evaluate ⟨evaluate_injective ε hI ι,evaluate_surjective ε hI⟩

@[simp] lemma equivalence_apply (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
    (ι : Type v) [Fintype ι] [DecidableEq ι] (g : Group (ι := ι) (R := R)) :
    equivalence ε hI ι g = evaluate g := rfl

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def elementaryGroup : Subgroup (Group (ι := ι) (R := R)) :=
  Subgroup.closure {g | ∃i j h a, g = root i j h a}

lemma root_mem_elementary (i j : ι) (h : i≠j) (a : R) :
    root i j h a ∈ elementaryGroup := Subgroup.subset_closure ⟨i,j,h,a,rfl⟩

lemma diag_normalizes_elementary (i : ι) (u : Rˣ) :
    diag i u ∈ Subgroup.normalizer (elementaryGroup (ι := ι) (R := R) : Set _) := by
  have hh (u : Rˣ) : elementaryGroup ≤
      elementaryGroup.comap (MulAut.conj (diag i u)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨t,j,h,b,rfl⟩
    change diag i u * root t j h b * (diag i u)⁻¹ ∈ elementaryGroup
    rw [diag_conjugate_root]
    exact root_mem_elementary _ _ _ _
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact hh u hx
  · intro hx
    have he := hh u⁻¹ hx
    change diag i u⁻¹ * (diag i u * x * (diag i u)⁻¹) * (diag i u⁻¹)⁻¹ ∈ elementaryGroup at he
    simpa only [diag_inv,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,
      inv_mul_cancel,mul_one] using he

instance elementary_normal : (elementaryGroup (ι := ι) (R := R)).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← supported_gen_all]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g,rfl⟩
  cases g with
  | root i j h a => exact elementaryGroup.le_normalizer (root_mem_elementary i j h a)
  | diag i u => exact diag_normalizes_elementary i u

abbrev K1 := Group (ι := ι) (R := R) ⧸ elementaryGroup

def toK1 : Group (ι := ι) (R := R) →* K1 (ι := ι) (R := R) :=
  QuotientGroup.mk' elementaryGroup

@[simp] lemma toK1_root (i j : ι) (h : i≠j) (a : R) : toK1 (root i j h a) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (root_mem_elementary i j h a)

@[simp] lemma diag_one (i : ι) : diag i (1 : Rˣ) = 1 := by
  apply local_faithful {i} (by simp)
    (diag_mem_local _ _ _ (by simp)) (localGroup _).one_mem
  simp [MatrixGenerators.singleDiagonal]

variable [Algebra (ZMod 2) R]

lemma minus_one_unit : (-1 : Rˣ) = 1 := by
  apply Units.ext
  change (-1 : R) = 1
  have h := congrArg (algebraMap (ZMod 2) R) (show (-1 : ZMod 2) = 1 by decide)
  simpa only [map_neg, map_one] using h

@[simp] lemma toK1_swap (i j : ι) (h : i≠j) : toK1 (swap (R := R) i j h) = 1 := by
  simp [swap,minus_one_unit]

lemma toK1_diag_eq (i j : ι) (u : Rˣ) : toK1 (diag i u) = toK1 (diag j u) := by
  by_cases h : i=j
  · subst j; rfl
  have he := congrArg (toK1 (R := R)) (swap_conjugate_diag i j h i u)
  simpa using he

variable [Fintype κ] [DecidableEq κ]

omit [Algebra (ZMod 2) R] in
lemma elementary_inclusion (e : ι ↪ κ) : elementaryGroup (R := R) ≤
    elementaryGroup.comap (inclusion e) := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i,j,h,a,rfl⟩
  change inclusion e (root i j h a) ∈ elementaryGroup
  change inclusion e (gen (.root i j h a)) ∈ elementaryGroup
  rw [inclusion_gen]
  exact root_mem_elementary _ _ _ _

def K1map (e : ι ↪ κ) : K1 (ι := ι) (R := R) →* K1 (ι := κ) (R := R) :=
  QuotientGroup.map _ _ (inclusion e) (elementary_inclusion e)

omit [Algebra (ZMod 2) R] in
@[simp] lemma K1map_mk (e : ι ↪ κ) (g : Group (ι := ι) (R := R)) :
    K1map e (toK1 g) = toK1 (inclusion e g) := rfl

omit [Fintype ι] [Algebra (ZMod 2) R] in
lemma supported_range (S : Finset ι) : supported (R := R) S ≤
    (FreeGroup.map (Generator.map (Function.Embedding.subtype (·∈S)))).range := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  cases g with
  | root i j h a =>
    obtain ⟨hi,hj⟩ := Finset.insert_subset_iff.mp hg
    have hj := Finset.singleton_subset_iff.mp hj
    refine ⟨FreeGroup.of (.root ⟨i,hi⟩ ⟨j,hj⟩ (fun he => h (congrArg Subtype.val he)) a),?_⟩
    rw [FreeGroup.map.of]
    rfl
  | diag i u =>
    refine ⟨FreeGroup.of (.diag ⟨i,Finset.singleton_subset_iff.mp hg⟩ u),?_⟩
    rw [FreeGroup.map.of]
    rfl

def unitWord (i : κ) : FreeGroup (Generator ι R) →* K1 (ι := κ) (R := R) :=
  FreeGroup.lift fun g => match g with
    | .root _ _ _ _ => 1
    | .diag _ u => toK1 (diag i u)

lemma unitWord_map (i : κ) (e : ι ↪ κ) : unitWord (R := R) i =
    (toK1.comp (inclusion e)).comp (PresentedGroup.mk relations) := by
  apply FreeGroup.ext_hom
  intro g
  cases g with
  | root a b h r =>
    change 1 = toK1 (inclusion e (gen (.root a b h r)))
    rw [inclusion_gen]
    exact (toK1_root _ _ _ _).symm
  | diag a u =>
    change toK1 (diag i u) = toK1 (inclusion e (gen (.diag a u)))
    rw [inclusion_gen]
    exact toK1_diag_eq _ _ _

lemma unitWord_relation (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (w : FreeGroup (Generator ι R)) (hw : w ∈ relations) : unitWord (R := R) i w = 1 := by
  obtain ⟨S,hS,hwS⟩ := hw.2
  obtain ⟨v,hv⟩ := supported_range S hwS
  let eS := Function.Embedding.subtype (·∈S)
  have hvmat : matrixWord v = 1 := by
    apply embed_injective eS
    rw [map_one]
    have hh := congrArg matrixWord hv
    rw [← MonoidHom.comp_apply,matrixWord_map,MonoidHom.comp_apply,hw.1] at hh
    exact hh
  have hvr : v∈relations := ⟨hvmat,Finset.univ,by simpa using hS,by rw [supported_univ]; trivial⟩
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le
    (α := {x : ι // x∈S}) (β := κ) (by simpa using hS.trans hκ)
  have he : (unitWord (R := R) i).comp (FreeGroup.map (Generator.map eS)) =
      unitWord (R := R) (ι := {x : ι // x∈S}) i := by
    apply FreeGroup.ext_hom
    intro g
    cases g <;> rfl
  rw [← hv, ← MonoidHom.comp_apply, he, unitWord_map i j]
  change toK1 (inclusion j (PresentedGroup.mk relations v)) = 1
  rw [PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure hvr),map_one,map_one]

def collapseGroup (i : κ) (hκ : 5 ≤ Fintype.card κ) :
    Group (ι := ι) (R := R) →* K1 (ι := κ) (R := R) :=
  PresentedGroup.toGroup (unitWord_relation i hκ)

@[simp] lemma collapseGroup_root (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (a b : ι) (h : a≠b) (r : R) : collapseGroup i hκ (root a b h r) = 1 :=
  PresentedGroup.toGroup.of _

@[simp] lemma collapseGroup_diag (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (a : ι) (u : Rˣ) : collapseGroup i hκ (diag a u) = toK1 (diag i u) :=
  PresentedGroup.toGroup.of _

lemma collapseGroup_kills (i : κ) (hκ : 5 ≤ Fintype.card κ) :
    elementaryGroup (ι := ι) (R := R) ≤ (collapseGroup i hκ).ker := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a,b,h,r,rfl⟩
  exact collapseGroup_root i hκ a b h r

def collapse (i : κ) (hκ : 5 ≤ Fintype.card κ) :
    K1 (ι := ι) (R := R) →* K1 (ι := κ) (R := R) :=
  QuotientGroup.lift _ (collapseGroup i hκ) (collapseGroup_kills i hκ)

@[simp] lemma collapse_mk (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (g : Group (ι := ι) (R := R)) : collapse i hκ (toK1 g) = collapseGroup i hκ g := rfl

lemma collapse_left (e : ι ↪ κ) (i : ι) (hι : 5 ≤ Fintype.card ι) :
    (collapse (R := R) i hι).comp (K1map e) = MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext
  change (collapseGroup i hι).comp (inclusion e) = toK1
  apply PresentedGroup.ext
  intro g
  cases g with
  | root a b h r =>
    change collapseGroup i hι (inclusion e (gen (.root a b h r))) = toK1 (root a b h r)
    rw [inclusion_gen]
    exact (collapseGroup_root _ _ _ _ _ _).trans (toK1_root _ _ _ _).symm
  | diag a u =>
    change collapseGroup i hι (inclusion e (gen (.diag a u))) = toK1 (diag a u)
    rw [inclusion_gen]
    exact (collapseGroup_diag _ _ _ _).trans (toK1_diag_eq _ _ _)

lemma collapse_right (e : ι ↪ κ) (i : ι) (hι : 5 ≤ Fintype.card ι) :
    (K1map (R := R) e).comp (collapse i hι) = MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext
  change (K1map e).comp (collapseGroup i hι) = toK1
  apply PresentedGroup.ext
  intro g
  cases g with
  | root a b h r =>
    change K1map e (collapseGroup i hι (root a b h r)) = toK1 (root a b h r)
    simp
  | diag a u =>
    change K1map e (collapseGroup i hι (diag a u)) = toK1 (diag a u)
    rw [collapseGroup_diag,K1map_mk]
    change toK1 (inclusion e (gen (.diag i u))) = _
    rw [inclusion_gen]
    exact toK1_diag_eq _ _ _

def K1equivalence (e : ι ↪ κ) (hι : 5 ≤ Fintype.card ι) :
    K1 (ι := ι) (R := R) ≃* K1 (ι := κ) (R := R) := by
  have hnon : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let i := Classical.choice hnon
  exact
    { toFun := K1map e
      invFun := collapse i hι
      left_inv := DFunLike.congr_fun (collapse_left e i hι)
      right_inv := DFunLike.congr_fun (collapse_right e i hι)
      map_mul' := (K1map e).map_mul }

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
