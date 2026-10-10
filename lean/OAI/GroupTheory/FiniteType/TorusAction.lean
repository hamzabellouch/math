import Mathlib
import OAI.GroupTheory.FiniteType.SequentialLimit
import OAI.GroupTheory.FiniteType.StageConstruction

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace TorusAction
open SequentialLimit SequentialAction AscendingHNN
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

def basePerm : U →* Equiv.Perm (Limit s) := by
  letI := limitAction f s heq
  exact (MulAction.toPermHom (Limit f) (Limit s)).comp (ofGroup f 0)

lemma basePerm_apply (g : U) (x : Limit s) :
    basePerm f s heq g x = act f s heq (of f 0 g) x := rfl

lemma basePerm_of (g : U) (i : ℕ) (x : X) :
    basePerm f s heq g (of s i x) = of s i ((f : U → U)^[i] g • x) := by
  rw [basePerm_apply,of_advance f 0 i (Nat.zero_le i),Nat.sub_zero,act_of]

lemma base_shift (g : U) :
    basePerm f s heq g * shift s = shift s * basePerm f s heq (f g) := by
  ext x
  have h := shift_equivariant f s heq (of f 0 (f g)) x
  simpa only [shiftGroup_of,of_succ,Equiv.Perm.mul_apply,basePerm_apply] using h.symm

lemma inverse_shift_base (g : U) :
    (shift s)⁻¹ * basePerm f s heq g = basePerm f s heq (f g) * (shift s)⁻¹ := by
  calc
    _ = (shift s)⁻¹ * (basePerm f s heq g * shift s) * (shift s)⁻¹ := by group
    _ = _ := by rw [base_shift]; group

def representation : Torus f hf →* Equiv.Perm (Limit s) :=
  HNNExtension.lift (basePerm f s heq) (shift s)⁻¹
    (fun a => inverse_shift_base f s heq a)

@[simp] lemma representation_embed (g : U) :
    representation f hf s heq (embed f hf g) = basePerm f s heq g := by
  exact HNNExtension.lift_of _ _ _ g

@[simp] lemma representation_stable :
    representation f hf s heq (stable f hf) = shift s := by
  change (HNNExtension.lift (basePerm f s heq) (shift s)⁻¹
    (fun a : (⊤ : Subgroup U) => inverse_shift_base f s heq a)) HNNExtension.t⁻¹ = _
  rw [map_inv]
  exact (congrArg Inv.inv (HNNExtension.lift_t _ _ _)).trans (inv_inv _)

lemma basePerm_stage (g : U) (i : ℕ) :
    basePerm f s heq g '' stage s i = stage s i := by
  ext x
  constructor
  · rintro ⟨_,⟨y,rfl⟩,rfl⟩
    exact ⟨(f : U → U)^[i] g • y,(basePerm_of f s heq g i y).symm⟩
  · rintro ⟨y,rfl⟩
    refine ⟨of s i (((f : U → U)^[i] g)⁻¹ • y),⟨_,rfl⟩,?_⟩
    rw [basePerm_of,smul_inv_smul]

lemma shift_pow_stage (i n : ℕ) : ((shift s)^n) '' stage s i = stage s (i+n) := by
  ext x
  constructor
  · rintro ⟨_,⟨y,rfl⟩,rfl⟩
    exact ⟨y,(shift_pow_of s n i y).symm⟩
  · rintro ⟨y,rfl⟩
    exact ⟨of s i y,⟨y,rfl⟩,shift_pow_of s n i y⟩

lemma representation_injective [FaithfulSMul U X] (hs : Function.Injective s)
    (hn : ¬ Function.Surjective s) : Function.Injective (representation f hf s heq) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨a,b,u,rfl⟩ := normal_form f hf g
  simp only [map_mul,map_pow,map_inv,representation_stable,representation_embed] at hg
  have he : (shift s)^a * basePerm f s heq u = (shift s)^b := by
    apply mul_right_cancel (b := ((shift s)^b)⁻¹)
    rw [hg,mul_inv_cancel]
  have hst : stage s a = stage s b := by
    have hh := congrArg (fun e : Equiv.Perm (Limit s) => e '' stage s 0) he
    change (fun x => ((shift s)^a) (basePerm f s heq u x)) '' stage s 0 =
      ((shift s)^b) '' stage s 0 at hh
    rw [← Set.image_image,basePerm_stage,shift_pow_stage,shift_pow_stage] at hh
    simpa only [Nat.zero_add] using hh
  have hab : a=b := (strictMono_nat_of_lt_succ (stage_strict s hs hn)).injective hst
  subst b
  have hu : basePerm f s heq u = 1 := by
    apply mul_left_cancel (a := (shift s)^a)
    simpa only [mul_one] using he
  have hu' : u=1 := by
    apply eq_of_smul_eq_smul (α := X)
    intro x
    apply of_injective s hs 0
    have hux := congrArg (fun e : Equiv.Perm (Limit s) => e (of s 0 x)) hu
    simpa only [basePerm_of,Function.iterate_zero,id_eq,Equiv.Perm.one_apply,one_smul] using hux
  simp [hu']

lemma tuple_transitivity (ht : HasImageTupleTransitivity (U := U) s)
    (n : ℕ) (v w : Fin n → Limit s) (hv : Function.Injective v)
    (hw : Function.Injective w) :
    ∃ g : Torus f hf, ∀ a, representation f hf s heq g (v a) = w a := by
  obtain ⟨i,z,hz⟩ := tuple_rep s (Sum.elim v w)
  let x : Fin n → X := fun a => z (.inl a)
  let y : Fin n → X := fun a => z (.inr a)
  have hx (a : Fin n) : v a = of s i (x a) := hz (.inl a)
  have hy (a : Fin n) : w a = of s i (y a) := hz (.inr a)
  have hxi : Function.Injective x := by
    intro a b hab
    apply hv
    rw [hx a,hx b,hab]
  have hyi : Function.Injective y := by
    intro a b hab
    apply hw
    rw [hy a,hy b,hab]
  obtain ⟨u,hu⟩ := ht n x y hxi hyi
  refine ⟨(stable f hf)^(i+1) * embed f hf u * ((stable f hf)^(i+1))⁻¹,fun a => ?_⟩
  simp only [map_mul,map_pow,map_inv,representation_stable,representation_embed]
  have h₀ (x : X) : ((shift s)^(i+1)) (of s 0 x) = of s (i+1) x := by
    simpa only [Nat.zero_add] using shift_pow_of s (i+1) 0 x
  rw [hx,hy,← of_succ s i (x a),← of_succ s i (y a),← h₀ (s (x a))]
  simp only [Equiv.Perm.mul_apply]
  simp only [Equiv.Perm.inv_def,Equiv.symm_apply_apply,basePerm_of]
  simp only [Function.iterate_zero,id_eq,hu,h₀]

end TorusAction

namespace StageConstruction
variable {R : Type*} [Ring R]

instance columnMulAction : MulAction (Q R) (X R) := MulAction.compHom _ action

@[simp] lemma smul_eq_action (q : Q R) (x : X R) : q • x=action q x := rfl

instance columnFaithful : FaithfulSMul (Q R) (X R) where
  eq_of_smul_eq_smul h := action_injective (Equiv.ext h)

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable {Y W : Type*} [DecidableEq Y] [Group W] [MulAction W Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point)

abbrev LimitGroup := AscendingHNN.Torus (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
abbrev LimitPoints := SequentialLimit.Limit (sigma φ S point)

def limitRepresentation : LimitGroup φ D ρ ι hφ hρ hι →* Equiv.Perm (LimitPoints φ S point) :=
  TorusAction.representation (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
    (sigma φ S point) (fun q x => (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm)

include hTS hpt in
                                                                                  
lemma limitRepresentation_injective [Nontrivial R] (he : e≠0) :
    Function.Injective (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) := by
  exact @TorusAction.representation_injective (Q R) (X R) _ columnMulAction
    (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
    (sigma φ S point) (fun q x => (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm)
    columnFaithful (sigma_injective φ e S T hTS point he hφ hpt)
    (sigma_not_surjective φ S point)

include hTS hSe hpt in
                                                                                    
lemma limit_tuple_transitivity (n : ℕ) (x y : Fin n → LimitPoints φ S point)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ q : LimitGroup φ D ρ ι hφ hρ hι,
      ∀ j, limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι q (x j)=y j :=
  TorusAction.tuple_transitivity (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
    (sigma φ S point) (fun q x => (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm)
    (sigma_tuple_transitivity φ D e S T hTS hSe point hpt) n x y hx hy

omit [DecidableEq Y] in
lemma limitPoints_countable [Countable R] : Countable (LimitPoints φ S point) := by
  dsimp [LimitPoints,SequentialLimit.Limit]
  infer_instance

include φ point hφ hpt hTS in
lemma stagePoints_infinite [Nontrivial R] (he : e≠0) : Infinite (X R) := by
  apply not_finite_iff_infinite.mp
  intro h
  let : Finite (X R) := h
  exact sigma_not_surjective φ S point
    (Finite.injective_iff_surjective.mp (sigma_injective φ e S T hTS point he hφ hpt))

include hφ hpt hTS in
lemma limitPoints_infinite [Nontrivial R] (he : e≠0) : Infinite (LimitPoints φ S point) := by
  let := stagePoints_infinite φ e S T hTS point hφ hpt he
  exact Infinite.of_injective (SequentialLimit.of (sigma φ S point) 0)
    (SequentialLimit.of_injective (sigma φ S point) (sigma_injective φ e S T hTS point he hφ hpt) 0)

end StageConstruction

end

namespace Steinberg
section
variable {n R : Type*} [Ring R]
variable (spare : ∀ i j : n, i≠j → ∃ k, i≠k ∧ k≠j)

def coefficients (N : Subgroup (Group n R)) [N.Normal] : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {a | ∀ i j hij, root i j hij a∈N}
    (by intro i j hij; rw [root_zero]; exact N.one_mem)
    (by intro a b ha hb i j hij; rw [← root_add]; exact N.mul_mem (ha _ _ _) (hb _ _ _))
    (by intro a ha i j hij; rw [root_neg]; exact N.inv_mem (ha _ _ _))
    (by
      intro a b hb i j hij
      obtain ⟨k,hik,hkj⟩ := spare i j hij
      rw [← root_commutator i k j hik hkj hij]
      exact Subgroup.commutator_le_right ⊤ N
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (hb k j hkj)))
    (by
      intro a b ha i j hij
      obtain ⟨k,hik,hkj⟩ := spare i j hij
      rw [← root_commutator i k j hik hkj hij]
      exact Subgroup.commutator_le_left N ⊤
        (Subgroup.commutator_mem_commutator (ha i k hik) (Subgroup.mem_top _)))

@[simp] lemma mem_coefficients (N : Subgroup (Group n R)) [N.Normal] (a : R) :
    a∈coefficients spare N ↔ ∀ i j hij, root i j hij a∈N := by
  simp [coefficients]

def rootSet (s : Set R) : Set (Group n R) :=
  {g | ∃ i j hij a, a∈s ∧ g=root i j hij a}

include spare in
lemma root_mem_normalClosure_span (s : Set R) {a : R} (ha : a∈TwoSidedIdeal.span s)
    (i j : n) (hij : i≠j) : root i j hij a∈Subgroup.normalClosure (rootSet (n:=n) s) := by
  have h : TwoSidedIdeal.span s≤coefficients spare (Subgroup.normalClosure (rootSet (n:=n) s)) := by
    apply TwoSidedIdeal.span_le.mpr
    intro r hr
    apply (mem_coefficients spare _ r).mpr
    intro i j hij
    exact Subgroup.subset_normalClosure ⟨i,j,hij,r,hr,rfl⟩
  exact (mem_coefficients _ _ a).mp (h ha) i j hij

variable {S : Type*} [Ring S]
lemma map_surjective (φ : R →ₙ+* S) (hφ : Function.Surjective φ) :
    Function.Surjective (map (n:=n) φ) := by
  intro g
  have h : g∈(map (n:=n) φ).range := by
    apply PresentedGroup.generated_by (relations n S) (map φ).range _ g
    intro r
    obtain ⟨a,ha⟩ := hφ r.coefficient
    refine ⟨root r.i r.j r.different a, ?_⟩
    rw [map_root,ha]
    rfl
  exact h

lemma normalClosure_kernel_le (φ : R →ₙ+* S) :
    Subgroup.normalClosure (rootSet (n:=n) {a | φ a=0})≤(map (n:=n) φ).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i,j,hij,a,ha,rfl⟩
  change map φ (root i j hij a)=1
  rw [map_root,ha,root_zero]

end

section
variable {n R S H : Type*} [Ring R] [Ring S] [_root_.Group H]

lemma root_sub (i j : n) (hij : i≠j) (a b : R) :
    root i j hij (a-b)=root i j hij a*(root i j hij b)⁻¹ := by
  rw [sub_eq_add_neg,← root_add,root_neg]

lemma root_image_eq (φ : R →ₙ+* S) (f : Group n R →* H)
    (hker : ∀ i j hij a, φ a=0 → f (root i j hij a)=1)
    (i j : n) (hij : i≠j) {a b : R} (hab : φ a=φ b) :
    f (root i j hij a)=f (root i j hij b) := by
  have h := hker i j hij (a-b) (by rw [map_sub,hab,sub_self])
  rw [root_sub,map_mul,map_inv] at h
  exact eq_of_mul_inv_eq_one h

def descendCoefficients (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (f : Group n R →* H)
    (hker : ∀ i j hij a, φ a=0 → f (root i j hij a)=1) : Group n S →* H :=
  lift (fun i j hij a => f (root i j hij (Function.surjInv hφ a)))
    (by
      intro i j hij a b
      rw [← map_mul,root_add]
      apply root_image_eq φ f hker
      simp only [map_add,Function.surjInv_eq])
    (by
      intro i j k hij hjk hik a b
      rw [← map_commutatorElement,root_commutator i j k hij hjk hik]
      apply root_image_eq φ f hker
      simp only [map_mul,Function.surjInv_eq])
    (by
      intro i j k l hij hkl hil hjk a b
      exact (root_commute i j k l hij hkl hil hjk _ _).map f)

lemma descendCoefficients_comp (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (f : Group n R →* H)
    (hker : ∀ i j hij a, φ a=0 → f (root i j hij a)=1) :
    (descendCoefficients φ hφ f hker).comp (map φ)=f := by
  apply hom_ext
  intro i j hij a
  simp only [MonoidHom.comp_apply,map_root,descendCoefficients,lift_root]
  apply root_image_eq φ f hker
  exact Function.surjInv_eq hφ _

theorem ker_map (φ : R →ₙ+* S) (hφ : Function.Surjective φ) :
    (map (n:=n) φ).ker=Subgroup.normalClosure (rootSet (n:=n) {a | φ a=0}) := by
  apply le_antisymm _ (normalClosure_kernel_le φ)
  let N := Subgroup.normalClosure (rootSet (n:=n) {a | φ a=0})
  let f := QuotientGroup.mk' N
  have hk : ∀ i j hij a, φ a=0 → f (root i j hij a)=1 := by
    intro i j hij a ha
    exact QuotientGroup.eq_one_iff _ |>.mpr (Subgroup.subset_normalClosure ⟨i,j,hij,a,ha,rfl⟩)
  have hd := descendCoefficients_comp φ hφ f hk
  intro w hw
  have he : f w=1 := by
    rw [← hd,MonoidHom.comp_apply,MonoidHom.mem_ker.mp hw,map_one]
  exact (QuotientGroup.eq_one_iff _).mp he

variable (spare : ∀ i j : n, i≠j → ∃ k, i≠k ∧ k≠j)

include spare in
                                                                              
theorem ker_map_span (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (s : Set R) (hs : {a | φ a=0}=(TwoSidedIdeal.span s : Set R)) :
    (map (n:=n) φ).ker=Subgroup.normalClosure (rootSet (n:=n) s) := by
  rw [ker_map φ hφ,hs]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i,j,hij,a,ha,rfl⟩
    exact root_mem_normalClosure_span spare s ha i j hij
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨i,j,hij,a,ha,rfl⟩
    exact ⟨i,j,hij,a,TwoSidedIdeal.subset_span ha,rfl⟩

end

variable {n R S : Type*} [Ring R] [Ring S]
variable (spare : ∀ i j : n, i≠j → ∃ k, i≠k ∧ k≠j)

lemma rootSet_finite [Finite n] (s : Set R) (hs : s.Finite) : (rootSet (n:=n) s).Finite := by
  have he : rootSet (n:=n) s=⋃ i, ⋃ j, ⋃ hij : i≠j, root i j hij '' s := by
    ext g
    simp only [rootSet,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_image]
    constructor
    · rintro ⟨i,j,hij,a,ha,rfl⟩; exact ⟨i,j,hij,a,ha,rfl⟩
    · rintro ⟨i,j,hij,a,ha,rfl⟩; exact ⟨i,j,hij,a,ha,rfl⟩
  rw [he]
  exact Set.finite_iUnion (fun i => Set.finite_iUnion (fun j =>
    Set.finite_iUnion (fun hij => hs.image (root i j hij))))

include spare in

theorem finitelyPresented_quotient [Finite n] [_root_.Group.IsFinitelyPresented (Group n R)]
    (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (s : Set R) (hs : s.Finite) (hker : {a | φ a=0}=(TwoSidedIdeal.span s : Set R)) :
    _root_.Group.IsFinitelyPresented (Group n S) := by
  apply _root_.Group.IsFinitelyPresented.of_surjective (map φ) (map_surjective φ hφ)
  exact ⟨rootSet s,rootSet_finite s hs,(ker_map_span spare φ hφ s hker).symm⟩

def coefficientSubring (H : Subgroup (Group n R))
    (h1 : ∀ i j hij, root i j hij (1:R)∈H) : Subring R where
  carrier := {a | ∀ i j hij, root i j hij a∈H}
  zero_mem' := by intro i j hij; rw [root_zero]; exact H.one_mem
  one_mem' := h1
  add_mem' := by intro a b ha hb i j hij; rw [← root_add]; exact H.mul_mem (ha _ _ _) (hb _ _ _)
  neg_mem' := by intro a ha i j hij; rw [root_neg]; exact H.inv_mem (ha _ _ _)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k,hik,hkj⟩ := spare i j hij
    rw [← root_commutator i k j hik hkj hij,commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (ha _ _ _) (hb _ _ _))
      (H.inv_mem (ha _ _ _))) (H.inv_mem (hb _ _ _))

include spare in
lemma closure_roots_eq_top (s : Set R) (hs : Subring.closure s=⊤) :
    Subgroup.closure (rootSet (n:=n) (insert 1 s))=⊤ := by
  let H := Subgroup.closure (rootSet (n:=n) (insert 1 s))
  have h1 : ∀ i j hij, root i j hij (1:R)∈H :=
    fun i j hij => Subgroup.subset_closure ⟨i,j,hij,1,Set.mem_insert _ _,rfl⟩
  have hr : Subring.closure s ≤ coefficientSubring spare H h1 := by
    apply Subring.closure_le.mpr
    intro a ha i j hij
    exact Subgroup.subset_closure ⟨i,j,hij,a,Set.mem_insert_of_mem 1 ha,rfl⟩
  rw [hs] at hr
  have hroot (r : Root n R) : PresentedGroup.of r∈H := hr (Subring.mem_top _) r.i r.j r.different
  apply top_unique
  intro g _
  exact PresentedGroup.generated_by (relations n R) H hroot g

include spare in
                                                                   
theorem finitelyGenerated [Finite n] (s : Set R) (hs : s.Finite) (hgen : Subring.closure s=⊤) :
    _root_.Group.FG (Group n R) :=
  _root_.Group.fg_iff.mpr ⟨rootSet (insert 1 s),closure_roots_eq_top spare s hgen,
    rootSet_finite _ (hs.insert 1)⟩

end Steinberg

end

end OAI
