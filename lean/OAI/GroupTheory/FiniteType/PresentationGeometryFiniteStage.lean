import Mathlib
import OAI.GroupTheory.FiniteType.CWWhitehead
import OAI.GroupTheory.FiniteType.CoreDeckLeftQuotientCovering

namespace OAI

noncomputable section
namespace PresentationGeometry.FiniteStage
open Set Topology CategoryTheory CategoryTheory.Limits
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, IsZero (groupHomology (RegularProductR.rep ℤ Q I) m))
abbrev finalSpace := SequentialColimit.Space (stageX S₀ hzero) (stageMap S₀ hzero)
@[instance_reducible] noncomputable def finalCW : CWComplex (univ : Set (finalSpace S₀ hzero)) :=
  SequentialCW.cwComplex (stageX S₀ hzero) (stageMap S₀ hzero) (stageMap_closed S₀ hzero)
    (stageCell S₀ hzero) (fun i j h d c v _ => stageMap_chart S₀ hzero i j h d c v)
lemma finalFiniteType :
    letI := finalCW S₀ hzero
    RelCWComplex.FiniteType (univ : Set (finalSpace S₀ hzero)) :=
  SequentialCW.finiteType (stageX S₀ hzero) (stageMap S₀ hzero) (stageMap_closed S₀ hzero)
    (stageCell S₀ hzero) (fun i j h d c v _ => stageMap_chart S₀ hzero i j h d c v)
    (fun d => ⟨d,stageCell_stable S₀ hzero d⟩)
noncomputable def finalCore :=
  SequentialCoreTower.core (stageX S₀ hzero) (stageMap S₀ hzero)
    (stageI S₀ hzero) (stageIndex S₀ hzero) (fun n => (stages S₀ hzero n).core)
    (fun n => (stages S₀ hzero n).pot) (stage_base S₀ hzero) (stage_pot S₀ hzero)
    (fun n => (stages S₀ hzero n).coord)
lemma finalCore_contractible : ContractibleSpace (finalCore S₀ hzero).TotalSpace := by
  let := finalCW S₀ hzero
  exact SequentialCoreTower.contractible (stageX S₀ hzero) (stageMap S₀ hzero)
    (stageI S₀ hzero) (stageIndex S₀ hzero) (fun n => (stages S₀ hzero n).core)
    (fun n => (stages S₀ hzero n).pot) (stage_base S₀ hzero) (stage_pot S₀ hzero)
    (fun n => (stages S₀ hzero n).coord) (stageMap_closed S₀ hzero)
    (fun n p hp z => (stages S₀ hzero n).connectivity p (by omega) z)
lemma finalCore_regular (i j x a q) :
    (finalCore S₀ hzero).coordChange i j x (a*q) =
      (finalCore S₀ hzero).coordChange i j x a * q := by
  change _ * (a*q) = (_ * a) * q
  exact (mul_assoc _ a q).symm
include S₀ hzero in

lemma geometric_of_initial : SimpleFInftyOvergroups.HasTypeFInfty Q := by
  let X := finalSpace S₀ hzero
  let W := finalCore S₀ hzero
  let := finalCW S₀ hzero
  let : T2Space X := SequentialColimit.hausdorff (stageX S₀ hzero)
    (stageMap S₀ hzero) (stageMap_closed S₀ hzero)
  let : ContractibleSpace W.TotalSpace := finalCore_contractible S₀ hzero
  have hsur : Function.Surjective W.proj := fun x => ⟨⟨x,(1:Q)⟩,rfl⟩
  let : PathConnectedSpace X := hsur.pathConnectedSpace W.continuous_proj
  let x : X := SequentialColimit.incl (stageX S₀ hzero) (stageMap S₀ hzero) 0 S₀.point
  refine ⟨X,inferInstance,finalCW S₀ hzero,inferInstance,inferInstance,
    finalFiniteType S₀ hzero,x,?_,W.TotalSpace,inferInstance,W.proj,
    DiscreteCoverCharts.covering W,hsur,inferInstance⟩
  exact ⟨CoreDeck.leftFundamentalEquiv W (finalCore_regular S₀ hzero) x⟩
end PresentationGeometry.FiniteStage

namespace SimpleFInftyOvergroups
open CategoryTheory.Limits

theorem geometric_product_criterion (Q : Type) [Group Q] [Group.IsFinitelyPresented Q]
    (hzero : ∀ I : Type, ∀ n ≥ 2, IsZero (groupHomology (RegularProductR.rep ℤ Q I) n)) :
    HasTypeFInfty Q := by
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  obtain ⟨S₀⟩ := PresentationGeometry.FiniteStage.initialStage_exists Q
  exact PresentationGeometry.FiniteStage.geometric_of_initial S₀ hzero
end SimpleFInftyOvergroups

namespace ListChains

variable (G : Type*)

abbrev Simplex := G × List G
abbrev Chain := Simplex G →₀ ℤ

def simplexVertex (a : G) : Simplex G := (a, [])
def simplexCone (a : G) (s : Simplex G) : Simplex G := (a, s.1 :: s.2)
def vertex (a : G) : Chain G := Finsupp.single (simplexVertex G a) 1

def cone (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lmapDomain ℤ ℤ (simplexCone G a)

@[simp] lemma cone_single (a : G) (s : Simplex G) (r : ℤ) :
    cone G a (Finsupp.single s r) = Finsupp.single (simplexCone G a s) r := by
  simp [cone]

lemma single_cons (a b : G) (l : List G) (r : ℤ) :
    Finsupp.single (a,b::l) r = cone G a (Finsupp.single (b,l) r) :=
  (cone_single G a (b,l) r).symm

def augmentation : Chain G →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun s : Simplex G => if s.2 = [] then 1 else 0)

@[simp] lemma augmentation_single (s : Simplex G) (r : ℤ) :
    augmentation G (Finsupp.single s r) = if s.2 = [] then r else 0 := by
  simp only [augmentation, Finsupp.linearCombination_single, smul_eq_mul]
  split_ifs <;> simp

@[simp] lemma augmentation_vertex (a : G) : augmentation G (vertex G a) = 1 := by
  simp [vertex, simplexVertex]

@[simp] lemma augmentation_cone (a : G) (c : Chain G) :
    augmentation G (cone G a c) = 0 := by
  have h : augmentation G ∘ₗ cone G a = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

def K (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lsingle (simplexVertex G a) ∘ₗ augmentation G

@[simp] lemma K_apply (a : G) (c : Chain G) : K G a c = augmentation G c • vertex G a := by
  simp [K, vertex]

@[simp] lemma augmentation_K (a : G) (c : Chain G) :
    augmentation G (K G a c) = augmentation G c := by
  simp

private def boundaryAux (a : G) : List G → Chain G
  | [] => 0
  | b :: l => Finsupp.single (b,l) 1 - cone G a (boundaryAux b l) -
    (if l = [] then vertex G a else 0)

def boundary : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s => boundaryAux G s.1 s.2)

@[simp] lemma boundary_single (s : Simplex G) (r : ℤ) :
    boundary G (Finsupp.single s r) = r • boundaryAux G s.1 s.2 := by
  simp [boundary]

@[simp] lemma boundary_vertex (a : G) : boundary G (vertex G a) = 0 := by
  simp [vertex, simplexVertex, boundaryAux]

@[simp] lemma boundary_K (a : G) (c : Chain G) : boundary G (K G a c) = 0 := by
  simp

lemma boundary_cone (a : G) (c : Chain G) :
    boundary G (cone G a c) = c - cone G a (boundary G c) - K G a c := by
  have h : boundary G ∘ₗ cone G a = LinearMap.id - cone G a ∘ₗ boundary G - K G a := by
    apply Finsupp.lhom_ext
    rintro ⟨b,l⟩ r
    simp only [LinearMap.comp_apply, cone_single, boundary_single, simplexCone, boundaryAux,
      LinearMap.sub_apply, LinearMap.id_apply, K_apply, augmentation_single, map_smul]
    split_ifs <;> simp [smul_sub, Finsupp.smul_single]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_boundary (c : Chain G) : augmentation G (boundary G c) = 0 := by
  have h : augmentation G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    rintro ⟨a,l⟩ r
    cases l with
    | nil => simp [boundaryAux]
    | cons b l =>
      change augmentation G (boundary G (Finsupp.single (a,b::l) r)) = 0
      rw [single_cons]
      rw [boundary_cone]
      simp only [map_sub, augmentation_cone, augmentation_K, sub_zero, sub_self]
  exact LinearMap.congr_fun h c

@[simp] lemma K_boundary (a : G) (c : Chain G) : K G a (boundary G c) = 0 := by
  simp

@[simp] lemma boundary_boundary (c : Chain G) : boundary G (boundary G c) = 0 := by
  have hb (l : List G) (a : G) :
      boundary G (boundary G (Finsupp.single (a,l) 1)) = 0 := by
    induction l generalizing a with
    | nil =>
      change boundary G (boundary G (vertex G a)) = 0
      rw [boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [boundary_cone, map_sub, map_sub, boundary_cone, ih b]
      simp only [map_zero, K_boundary, boundary_K, sub_zero, sub_self]
  have h : boundary G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hr, map_smul, hb s.2 s.1,
      smul_zero]
  exact LinearMap.congr_fun h c

def degree (s : Simplex G) : ℕ := s.2.length

def Homogeneous (n : ℕ) (c : Chain G) : Prop :=
  ∀ s ∈ c.support, degree G s = n

def mapChain {H : Type*} (f : G → H) : Chain G →ₗ[ℤ] Chain H :=
  Finsupp.lmapDomain ℤ ℤ (fun s => (f s.1, s.2.map f))

@[simp] lemma mapChain_single {H : Type*} (f : G → H) (s : Simplex G) (r : ℤ) :
    mapChain G f (Finsupp.single s r) = Finsupp.single (f s.1, s.2.map f) r := by
  simp [mapChain]

@[simp] lemma mapChain_vertex {H : Type*} (f : G → H) (a : G) :
    mapChain G f (vertex G a) = vertex H (f a) := by
  simp [vertex, simplexVertex]

lemma mapChain_cone {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (cone G a c) = cone H (f a) (mapChain G f c) := by
  have h : mapChain G f ∘ₗ cone G a = cone H (f a) ∘ₗ mapChain G f := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    augmentation H (mapChain G f c) = augmentation G c := by
  have h : augmentation H ∘ₗ mapChain G f = augmentation G := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  exact LinearMap.congr_fun h c

lemma mapChain_K {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (K G a c) = K H (f a) (mapChain G f c) := by
  simp

lemma boundary_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    boundary H (mapChain G f c) = mapChain G f (boundary G c) := by
  have hb (l : List G) (a : G) :
      boundary H (mapChain G f (Finsupp.single (a,l) 1)) =
        mapChain G f (boundary G (Finsupp.single (a,l) 1)) := by
    induction l generalizing a with
    | nil =>
      change boundary H (mapChain G f (vertex G a)) = mapChain G f (boundary G (vertex G a))
      rw [mapChain_vertex, boundary_vertex, boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [mapChain_cone, boundary_cone, boundary_cone, map_sub, map_sub,
        mapChain_cone, mapChain_K, ih b]
  have he : boundary H ∘ₗ mapChain G f = mapChain G f ∘ₗ boundary G := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, hr, map_smul, hb s.2 s.1]
  exact LinearMap.congr_fun he c

def sign : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s : Simplex G => (-1 : ℤ) ^ degree G s • Finsupp.single s 1)

@[simp] lemma sign_single (s : Simplex G) (r : ℤ) :
    sign G (Finsupp.single s r) = (-1 : ℤ) ^ degree G s • Finsupp.single s r := by
  simp [sign, mul_comm]

@[simp] lemma sign_vertex (a : G) : sign G (vertex G a) = vertex G a := by
  simp [vertex, degree, simplexVertex]

lemma sign_cone (a : G) (c : Chain G) : sign G (cone G a c) = -cone G a (sign G c) := by
  have h : sign G ∘ₗ cone G a = -(cone G a ∘ₗ sign G) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, cone_single, sign_single,
      map_smul, degree, simplexCone, List.length_cons, pow_succ, mul_neg_one, neg_smul]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_sign (c : Chain G) : augmentation G (sign G c) = augmentation G c := by
  have h : augmentation G ∘ₗ sign G = augmentation G := by
    apply Finsupp.lhom_ext
    rintro ⟨a,l⟩ r
    simp only [LinearMap.comp_apply, sign_single, map_smul, augmentation_single]
    cases l <;> simp [degree]
  exact LinearMap.congr_fun h c

@[simp] lemma sign_K (a : G) (c : Chain G) : sign G (K G a c) = K G a c := by
  simp

@[simp] lemma K_sign (a : G) (c : Chain G) : K G a (sign G c) = K G a c := by
  simp

lemma boundary_sign (c : Chain G) : boundary G (sign G c) = -sign G (boundary G c) := by
  have hb (l : List G) (a : G) : boundary G (sign G (Finsupp.single (a,l) 1)) =
      -sign G (boundary G (Finsupp.single (a,l) 1)) := by
    induction l generalizing a with
    | nil =>
      change boundary G (sign G (vertex G a)) = -sign G (boundary G (vertex G a))
      rw [sign_vertex, boundary_vertex, map_zero, neg_zero]
    | cons b l ih =>
      rw [single_cons, sign_cone, map_neg, boundary_cone, boundary_cone,
        map_sub, map_sub, ih b, map_neg, K_sign, sign_cone, sign_K]
  have h : boundary G ∘ₗ sign G = -(sign G ∘ₗ boundary G) := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, hr, map_smul,
      hb s.2 s.1, smul_neg]
  exact LinearMap.congr_fun h c

def Supported (P : Simplex G → Prop) (c : Chain G) : Prop := ∀ s ∈ c.support, P s

lemma supported_zero (P : Simplex G → Prop) : Supported G P 0 := by simp [Supported]

lemma supported_add {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c+d) := by
  classical
  intro s hs
  obtain hs | hs := Finset.mem_union.mp (Finsupp.support_add hs)
  · exact hc s hs
  · exact hd s hs

lemma supported_neg {P : Simplex G → Prop} {c : Chain G}
    (hc : Supported G P c) : Supported G P (-c) := by
  simpa only [Supported, Finsupp.support_neg] using hc

lemma supported_sub {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c-d) := by
  rw [sub_eq_add_neg]
  exact supported_add G hc (supported_neg G hd)

lemma supported_smul {P : Simplex G → Prop} {c : Chain G}
    (r : ℤ) (hc : Supported G P c) : Supported G P (r • c) :=
  fun s hs => hc s (Finsupp.support_smul hs)

lemma supported_single {P : Simplex G → Prop} {s : Simplex G} (hs : P s) (r : ℤ) :
    Supported G P (Finsupp.single s r) := by
  classical
  intro t ht
  have h : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  simpa only [h] using hs

lemma supported_mono {P Q : Simplex G → Prop} (hPQ : ∀ s, P s → Q s) {c : Chain G}
    (hc : Supported G P c) : Supported G Q c := fun s hs => hPQ s (hc s hs)

lemma supported_sum {ι : Type*} (t : Finset ι) {P : Simplex G → Prop}
    (c : ι → Chain G) (hc : ∀ i ∈ t, Supported G P (c i)) :
    Supported G P (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supported_zero G P
  | @insert i t hit ih =>
    rw [Finset.sum_insert hit]
    exact supported_add G (hc i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj)))

lemma supported_linearMap {H : Type*} {P : Simplex G → Prop} {Q : Simplex H → Prop}
    (T : Chain G →ₗ[ℤ] Chain H)
    (hT : ∀ s, P s → Supported H Q (T (Finsupp.single s 1)))
    {c : Chain G} (hc : Supported G P c) : Supported H Q (T c) := by
  classical
  have he : T c = ∑ s ∈ c.support, (c s) • T (Finsupp.single s 1) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he]
  exact supported_sum H c.support _ (fun s hs => supported_smul H _ (hT s (hc s hs)))

end ListChains

end

end OAI
