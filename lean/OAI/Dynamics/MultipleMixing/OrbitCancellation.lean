import OAI.Dynamics.MultipleMixing.FibreMeasures

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))

def localProjectiveGroup (a : U) : Subgroup (ProjectiveCircle (κ a)) :=
  Subgroup.closure {g | ∃ q, (a,q) ∈ S ∧ HilbertCode.projective a q = g}

omit [DecidableEq I] in
lemma localProjectiveGroup_eq (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    localProjectiveGroup κ S (u p i) = (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := by
  unfold localProjectiveGroup
  have he : {g : ProjectiveCircle (κ (u p i)) | ∃ q, (u p i,q) ∈ S ∧ HilbertCode.projective (u p i) q = g} =
      {g | ∃ q : ExactCodeSlot κ Λ u p i, HilbertCode.projective (u p i) q.val = g} := by
    ext g
    constructor
    · rintro ⟨q,hq,he⟩
      exact ⟨⟨q,(Set.ext_iff.mp hS q).mpr hq⟩,he⟩
    · rintro ⟨q,he⟩
      exact ⟨q.val,(Set.ext_iff.mp hS q.val).mp q.property,he⟩
  rw [he,codeSlot_projective_range κ Λ u p hm i,Subgroup.closure_eq]

omit [DecidableEq I] in
def localCodeEquivSlot (p : P) (i : I)
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    {q // (u p i,q) ∈ S} ≃ ExactCodeSlot κ Λ u p i := Set.equivOfEq hS.symm

omit [DecidableEq I] in

def localCodeEquivGroup (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    {q // (u p i,q) ∈ S} ≃ localProjectiveGroup κ S (u p i) :=
  (localCodeEquivSlot κ Λ u S p i hS).trans ((codeSlotEquivProjective κ Λ u p hm i).trans
    (MulEquiv.subgroupCongr (localProjectiveGroup_eq κ Λ u S p i hm hS).symm).toEquiv)

omit [DecidableEq I] in
lemma localCodeEquivGroup_val (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (q : {q // (u p i,q) ∈ S}) :
    (localCodeEquivGroup κ Λ u S p i hm hS q).val = HilbertCode.projective (u p i) q.val := rfl

def localProjectiveMatching (hk : 3 ≤ Fintype.card I) (p : P)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p)) (i j : I)
    (hSi : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (hSj : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a j = q} = {q | (u p j,q) ∈ S}) :
    localProjectiveGroup κ S (u p i) ≃* localProjectiveGroup κ S (u p j) :=
  (MulEquiv.subgroupCongr (localProjectiveGroup_eq κ Λ u S p i hm hSi)).trans
    ((exactProjectiveMatching hk (Λ p) (fun j => κ (u p j)) hm hind i j).trans
      (MulEquiv.subgroupCongr (localProjectiveGroup_eq κ Λ u S p j hm hSj).symm))
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
    (S : Set (U × HilbertCode κ)) (a b : U)
    (e : {q // (a,q) ∈ S} ≃ {q // (b,q) ∈ S})
    (F : ProjectiveCircle (κ a) ≃* ProjectiveCircle (κ b))
    (he : ∀ q, F (HilbertCode.projective a q.val) = HilbertCode.projective b (e q).val)
include he in
lemma localProjectiveGroup_map :
    (localProjectiveGroup κ S a).map F.toMonoidHom = localProjectiveGroup κ S b := by
  unfold localProjectiveGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨f,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨(e ⟨q,hq⟩).val,(e ⟨q,hq⟩).property,(he ⟨q,hq⟩).symm⟩
  · rintro ⟨q,hq,rfl⟩
    refine ⟨HilbertCode.projective a (e.symm ⟨q,hq⟩).val,
      ⟨(e.symm ⟨q,hq⟩).val,(e.symm ⟨q,hq⟩).property,rfl⟩,?_⟩
    change F (HilbertCode.projective a (e.symm ⟨q,hq⟩).val) = _
    simpa only [e.apply_symm_apply] using he (e.symm ⟨q,hq⟩)

def localProjectiveTransport : localProjectiveGroup κ S a ≃* localProjectiveGroup κ S b :=
  (F.subgroupMap (localProjectiveGroup κ S a)).trans
    (MulEquiv.subgroupCongr (localProjectiveGroup_map κ S a b e F he))

lemma localProjectiveTransport_val (g : localProjectiveGroup κ S a) :
    (localProjectiveTransport κ S a b e F he g).val = F g.val := rfl
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))
lemma localProjectiveMatching_code (hk : 3 ≤ Fintype.card I) (p : P)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p)) (i j : I)
    (hSi : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (hSj : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a j = q} = {q | (u p j,q) ∈ S})
    (a : I → HilbertCode κ) (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    localProjectiveMatching κ Λ u S hk p hm hind i j hSi hSj
      (localCodeEquivGroup κ Λ u S p i hm hSi
        ⟨a i,(Set.ext_iff.mp hSi _).mp ⟨a,ha,rfl⟩⟩) =
    localCodeEquivGroup κ Λ u S p j hm hSj
        ⟨a j,(Set.ext_iff.mp hSj _).mp ⟨a,ha,rfl⟩⟩ := by
  let v : exactProjectiveTuples (Λ p) (fun t => κ (u p t)) :=
    ⟨fun t => HilbertCode.projective (u p t) (a t),exact_code_projective_mem κ Λ u hm ha⟩
  let ei := MonoidHom.ofInjective (exactProjectiveSlot_injective hk (Λ p) (fun t => κ (u p t)) hm hind i)
  let ej := MonoidHom.ofInjective (exactProjectiveSlot_injective hk (Λ p) (fun t => κ (u p t)) hm hind j)
  apply Subtype.ext
  change (ej (ei.symm (ei v))).val = (ej v).val
  rw [ei.symm_apply_apply]
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {U Y C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
    (S : Set (U × HilbertCode κ))

def localGroupCode (a : U) (g : localProjectiveGroup κ S a) : HilbertCode κ :=
  if h : ∃ q, (a,q) ∈ S ∧ HilbertCode.projective a q = g.val then h.choose
  else HilbertCode.encode a 0

lemma localGroupCode_equiv (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (q : {q // (a,q) ∈ S}) : localGroupCode κ S a (e q) = q.val := by
  have h : ∃ r, (a,r) ∈ S ∧ HilbertCode.projective a r = (e q).val := ⟨q.val,q.property,(he q).symm⟩
  rw [localGroupCode,dite_eq_left h]
  have hh := h.choose_spec
  have heq : e ⟨h.choose,hh.1⟩ = e q := Subtype.ext ((he _).trans hh.2)
  exact congrArg Subtype.val (e.injective heq)

def localGroupBlock (ψ : U × HilbertCode κ → C) (a : U) (g : localProjectiveGroup κ S a) : C :=
  ψ (a,localGroupCode κ S a g)

lemma localGroupBlock_equiv (ψ : U × HilbertCode κ → C) (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (q : {q // (a,q) ∈ S}) : localGroupBlock κ S ψ a (e q) = ψ (a,q.val) := by
  unfold localGroupBlock
  rw [localGroupCode_equiv κ S a e he q]

lemma localProjectiveTransport_block (ψ : U × HilbertCode κ → C) (a b : U)
    (e : {q // (a,q) ∈ S} ≃ {q // (b,q) ∈ S})
    (F : ProjectiveCircle (κ a) ≃* ProjectiveCircle (κ b))
    (he : ∀ q, F (HilbertCode.projective a q.val) = HilbertCode.projective b (e q).val)
    (ea : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (ha : ∀ q, (ea q).val = HilbertCode.projective a q.val)
    (eb : {q // (b,q) ∈ S} ≃ localProjectiveGroup κ S b)
    (hb : ∀ q, (eb q).val = HilbertCode.projective b q.val)
    (D : C → C) (hψ : ∀ q : {q // (a,q) ∈ S}, ψ (b,(e q).val) = D (ψ (a,q.val))) :
    ∀ g, localGroupBlock κ S ψ b (localProjectiveTransport κ S a b e F he g) =
      D (localGroupBlock κ S ψ a g) := by
  intro g
  obtain ⟨q,rfl⟩ := ea.surjective g
  have hh : localProjectiveTransport κ S a b e F he (ea q) = eb (e q) := by
    apply Subtype.ext
    rw [localProjectiveTransport_val,ha,he,hb]
  rw [hh,localGroupBlock_equiv κ S ψ b eb hb,localGroupBlock_equiv κ S ψ a ea ha]
  exact hψ q

variable {P I : Type*} [MeasurableSpace P] [Fintype I] [DecidableEq I]
    (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ] (u : P → I → U)
lemma localProjectiveMatching_block (hk : 3 ≤ Fintype.card I) (p : P)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p)) (i j : I)
    (hSi : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (hSj : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a j = q} = {q | (u p j,q) ∈ S})
    (ψ : U × HilbertCode κ → C) (D : C → C)
    (hψ : ∀ a, (p,a) ∈ exactCodeSet κ Λ u → ψ (u p j,a j) = D (ψ (u p i,a i))) :
    ∀ g, localGroupBlock κ S ψ (u p j)
      (localProjectiveMatching κ Λ u S hk p hm hind i j hSi hSj g) =
      D (localGroupBlock κ S ψ (u p i) g) := by
  intro g
  let e := localCodeEquivGroup κ Λ u S p i hm hSi
  obtain ⟨q,rfl⟩ := e.surjective g
  obtain ⟨a,ha,hai⟩ := (Set.ext_iff.mp hSi _).mpr q.property
  have hq : q = ⟨a i,(Set.ext_iff.mp hSi _).mp ⟨a,ha,rfl⟩⟩ := Subtype.ext hai.symm
  subst q
  change localGroupBlock κ S ψ (u p j)
    (localProjectiveMatching κ Λ u S hk p hm hind i j hSi hSj
      (localCodeEquivGroup κ Λ u S p i hm hSi _)) = _
  rw [localProjectiveMatching_code κ Λ u S hk p hm hind i j hSi hSj a ha]
  rw [localGroupBlock_equiv κ S ψ (u p j) _ (localCodeEquivGroup_val κ Λ u S p j hm hSj)]
  rw [localGroupBlock_equiv κ S ψ (u p i) _ (localCodeEquivGroup_val κ Λ u S p i hm hSi)]
  exact hψ a ha
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {Y : Type*} [MeasurableSpace Y]

def measurableCircleTime (E : Y ≃ᵐ Y) : MeasurableCircle Y ≃* MeasurableCircle Y where
  toFun f := ⟨(f : Y → Circle) ∘ E.symm,(measurableCircle_measurable Y f).comp E.symm.measurable⟩
  invFun f := ⟨(f : Y → Circle) ∘ E,(measurableCircle_measurable Y f).comp E.measurable⟩
  left_inv f := Subtype.ext (by funext y; exact congrArg f (E.symm_apply_apply y))
  right_inv f := Subtype.ext (by funext y; exact congrArg f (E.apply_symm_apply y))
  map_mul' f g := rfl

lemma measurableCircleTime_phase (E : Y ≃ᵐ Y) (μ ν : Measure Y)
    (hE : MeasurePreserving E μ ν) : (phaseSubgroup μ).map (measurableCircleTime E) = phaseSubgroup ν := by
  ext f
  constructor
  · rintro ⟨g,⟨c,hg⟩,rfl⟩
    exact ⟨c,(MeasurePreserving.symm E hE).quasiMeasurePreserving.ae_eq_comp hg⟩
  · rintro ⟨c,hf⟩
    refine ⟨(measurableCircleTime E).symm f,⟨c,hE.quasiMeasurePreserving.ae_eq_comp hf⟩,
      (measurableCircleTime E).apply_symm_apply f⟩

def projectiveTime (E : Y ≃ᵐ Y) (μ ν : Measure Y) (hE : MeasurePreserving E μ ν) :
    ProjectiveCircle μ ≃* ProjectiveCircle ν :=
  QuotientGroup.congr (phaseSubgroup μ) (phaseSubgroup ν) (measurableCircleTime E) (measurableCircleTime_phase E μ ν hE)

lemma projectiveTime_apply (E : Y ≃ᵐ Y) (μ ν : Measure Y) (hE : MeasurePreserving E μ ν)
    (f : Y → Circle) (hf : Measurable f) :
    projectiveTime E μ ν hE (projectiveCircle μ f hf) =
      projectiveCircle ν (f ∘ E.symm) (hf.comp E.symm.measurable) := rfl

namespace HilbertCode
variable {U : Type*} [MeasurableSpace U] [MeasurableSpace.CountablyGenerated Y]
  {κ : Kernel U Y} [IsMarkovKernel κ]
lemma projective_transport (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ)
    (hq : q.IsUnimodular) (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    projective (F q.base) (transport F E q) =
      projectiveTime E (κ q.base) (κ (F q.base)) hE (projective q.base q) := by
  rw [projective,projective,projectiveTime_apply,projectiveCircle_eq_iff]
  obtain ⟨c,hc,hr⟩ := transport_representative F E q hq hE
  let d : Circle := ⟨c,mem_sphere_zero_iff_norm.mpr hc⟩
  refine ⟨d,?_⟩
  have ht := circleRep_ae (transport F E q) (transport_unimodular F E q)
  have hs := (MeasurePreserving.symm E hE).quasiMeasurePreserving.ae_eq_comp (circleRep_ae q hq)
  filter_upwards [ht,hr,hs] with y hty hry hsy
  apply Circle.coe_injective
  exact hty.trans (hry.trans (congrArg (c * ·) hsy.symm))
end HilbertCode
end

section
open MeasureTheory Set
variable {U P B : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace P] [StandardBorelSpace P]
  (ν : Measure U) [IsProbabilityMeasure ν] (π : Measure P) [IsProbabilityMeasure π]
  (s t : P → U) (hst : MeasurePreserving (fun p => (s p,t p)) π (ν.prod ν))
  (A : U → Type*) [∀ u, Group (A u)] (block : ∀ u, A u → B) (D : B ≃ B)

include hst in

lemma exists_block_preserving_trivialization
    (h : ∀ᵐ p ∂π, ∃ e : A (s p) ≃* A (t p), ∀ a, block (t p) (e a) = D (block (s p) a)) :
    ∃ u₀ : U, ∀ᵐ u ∂ν, ∃ J : A u₀ ≃* A u, ∀ a, block u (J a) = block u₀ a := by
  have hp : ∀ᵐ z ∂ν.prod ν, ∃ e : A z.1 ≃* A z.2,
      ∀ a, block z.2 (e a) = D (block z.1 a) := by
    rw [←hst.map_eq]
    exact ae_map_descent π hst.measurable h
  obtain ⟨uS,huS⟩ := (Measure.ae_ae_of_ae_prod hp).exists
  obtain ⟨u₀,e₀,he₀⟩ := huS.exists
  refine ⟨u₀,huS.mono ?_⟩
  intro u hu
  obtain ⟨e,he⟩ := hu
  refine ⟨e₀.symm.trans e,fun a => ?_⟩
  change block u (e (e₀.symm a)) = block u₀ a
  rw [he,←he₀,e₀.apply_symm_apply]

include hst in
lemma exists_good_block_preserving_trivialization (Q : U → Prop) (hQ : ∀ᵐ u ∂ν, Q u)
    (h : ∀ᵐ p ∂π, ∃ e : A (s p) ≃* A (t p), ∀ a, block (t p) (e a) = D (block (s p) a)) :
    ∃ u₀ : U, Q u₀ ∧ ∀ᵐ u ∂ν, ∃ J : A u₀ ≃* A u, ∀ a, block u (J a) = block u₀ a := by
  obtain ⟨v,hv⟩ := exists_block_preserving_trivialization ν π s t hst A block D h
  obtain ⟨u₀,hu₀,e,he⟩ := (hQ.and hv).exists
  refine ⟨u₀,hu₀,hv.mono ?_⟩
  intro u hu
  obtain ⟨e',he'⟩ := hu
  refine ⟨e.symm.trans e',fun a => ?_⟩
  change block u (e' (e.symm a)) = _
  rw [he',←he,e.apply_symm_apply]

omit [StandardBorelSpace U] in

lemma exists_block_automorphism
    (u₀ : U) (hJ : ∀ᵐ u ∂ν, ∃ J : A u₀ ≃* A u, ∀ a, block u (J a) = block u₀ a)
    (T : U → U) (hT : MeasurePreserving T ν ν) (S : B ≃ B)
    (ht : ∀ᵐ u ∂ν, ∃ τ : A u ≃* A (T u), ∀ a, block (T u) (τ a) = S (block u a)) :
    ∃ G : A u₀ ≃* A u₀, ∀ a, block u₀ (G a) = S.symm (block u₀ a) := by
  obtain ⟨u,hu,htu,htime⟩ := (hJ.and ((hT.quasiMeasurePreserving.ae hJ).and ht)).exists
  obtain ⟨J,hJ₁⟩ := hu
  obtain ⟨J',hJ₂⟩ := htu
  obtain ⟨τ,hτ⟩ := htime
  let V : A u₀ ≃* A u₀ := J.trans (τ.trans J'.symm)
  have hV (a) : block u₀ (V a) = S (block u₀ a) := by
    change block u₀ (J'.symm (τ (J a))) = _
    rw [←hJ₂,J'.apply_symm_apply,hτ,hJ₁]
  refine ⟨V.symm,fun a => ?_⟩
  apply S.injective
  rw [S.apply_symm_apply,←hV,V.apply_symm_apply]
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})

include hm hS in
omit [DecidableEq I] in
lemma localGraph_group_equiv (i : I) :
    ∀ᵐ a ∂M.parameterLaw 0, ∃ e : {q // (a,q) ∈ S} ≃ localProjectiveGroup (M.ownKernel 0) S a,
      ∀ q, (e q).val = HilbertCode.projective a q.val := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1,
      ∃ e : {q // (tupleParameter M p i,q) ∈ S} ≃
        localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p i),
        ∀ q, (e q).val = HilbertCode.projective (tupleParameter M p i) q.val := by
    filter_upwards [hS] with p hp
    exact ⟨localCodeEquivGroup (M.ownKernel 0) Λ (tupleParameter M) S p i (hm p) (hp i),
      localCodeEquivGroup_val (M.ownKernel 0) Λ (tupleParameter M) S p i (hm p) (hp i)⟩
  have hd := ae_map_descent (P := fun a =>
    ∃ e : {q // (a,q) ∈ S} ≃ localProjectiveGroup (M.ownKernel 0) S a,
      ∀ q, (e q).val = HilbertCode.projective a q.val)
    (M.parameterLaw 1) (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd

include hm hS in
lemma localGraph_matching_blocks {C : Type*} (hk : 3 ≤ Fintype.card I)
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (s t : I)
    (ψ : RawLabel M → C) (D : C → C)
    (hψ : ∀ᵐ p ∂M.parameterLaw 1, ∀ a, (p,a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ψ (tupleParameter M p t,a t) = D (ψ (tupleParameter M p s,a s))) :
    ∀ᵐ p ∂M.parameterLaw 1,
      ∃ e : localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p s) ≃*
          localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p t),
        ∀ g, localGroupBlock (M.ownKernel 0) S ψ (tupleParameter M p t) (e g) =
          D (localGroupBlock (M.ownKernel 0) S ψ (tupleParameter M p s) g) := by
  filter_upwards [hS,hψ] with p hp hψ
  exact ⟨localProjectiveMatching (M.ownKernel 0) Λ (tupleParameter M) S hk p (hm p) (hind p) s t (hp s) (hp t),
    localProjectiveMatching_block (M.ownKernel 0) S Λ (tupleParameter M) hk p (hm p) (hind p) s t
      (hp s) (hp t) ψ D hψ⟩

include hm hS in
omit [DecidableEq I] in
lemma localGraph_time_blocks {C : Type*} (i : I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (ψ : RawLabel M → C) (D : C → C)
    (hψ : ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S → ψ (rawLabelTime M (a,q)) = D (ψ (a,q))) :
    ∀ᵐ a ∂M.parameterLaw 0,
      ∃ τ : localProjectiveGroup (M.ownKernel 0) S a ≃*
          localProjectiveGroup (M.ownKernel 0) S (amap M.timeU 0 a),
        ∀ g, localGroupBlock (M.ownKernel 0) S ψ (amap M.timeU 0 a) (τ g) =
          D (localGroupBlock (M.ownKernel 0) S ψ a g) := by
  classical
  have heq := localGraph_group_equiv M Λ hm S hS i
  filter_upwards [localGraph_time_equiv M Λ i hL hm S hS,
    M.ownKernel_time_preserving 0,localGraph_code_properties M Λ i S hS,
    heq,(M.parameterLaw_invariant 0).quasiMeasurePreserving.ae heq,hψ]
      with a hcode htime hprop hea heb hψ
  obtain ⟨e,he⟩ := hcode
  obtain ⟨ea,ha⟩ := hea
  obtain ⟨eb,hb⟩ := heb
  let F := projectiveTime (amapEquiv M.timeY 0) (M.ownKernel 0 a)
    (M.ownKernel 0 (amap M.timeU 0 a)) htime
  have hf (q : {q // (a,q) ∈ S}) : F (HilbertCode.projective a q.val) =
      HilbertCode.projective (amap M.timeU 0 a) (e q).val := by
    rw [he]
    have hq := hprop q.val q.property
    have hh (b : Arr I M.U 0) (hb : q.val.base = b)
        (ht : MeasurePreserving (amapEquiv M.timeY 0) (M.ownKernel 0 b)
          (M.ownKernel 0 (amap M.timeU 0 b))) :
        projectiveTime (amapEquiv M.timeY 0) (M.ownKernel 0 b)
          (M.ownKernel 0 (amap M.timeU 0 b)) ht (HilbertCode.projective b q.val) =
        HilbertCode.projective (amap M.timeU 0 b)
          (HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val) := by
      subst b
      exact (HilbertCode.projective_transport (amap M.timeU 0) (amapEquiv M.timeY 0)
        q.val hq.2.2 ht).symm
    exact hh a hq.1 htime
  refine ⟨localProjectiveTransport (M.ownKernel 0) S a (amap M.timeU 0 a) e F hf,?_⟩
  apply localProjectiveTransport_block (M.ownKernel 0) S ψ a (amap M.timeU 0 a) e F hf ea ha eb hb D
  intro q
  rw [he]
  exact hψ q.val q.property
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {U Y C : Type*} [MeasurableSpace U] [StandardBorelSpace U]
    [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
    (κ : Kernel U Y) [IsMarkovKernel κ] (S : Set (U × HilbertCode κ))
    (E : BorelFibreEnumeration S)

include E in
omit [StandardBorelSpace U] in
lemma localGroup_countable (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a) :
    Countable (localProjectiveGroup κ S a) := by
  have hc : {q | (a,q) ∈ S}.Countable := by
    apply (Set.countable_range (fun n => E.section_ n a)).mono
    intro q hq
    obtain ⟨n,_,hn⟩ := E.cover a q hq
    exact ⟨n,hn⟩
  let : Countable {q // (a,q) ∈ S} := hc.to_subtype
  exact e.symm.injective.countable

omit [StandardBorelSpace U] in
lemma localGroupBlock_symm (ψ : U × HilbertCode κ → C) (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (g : localProjectiveGroup κ S a) :
    localGroupBlock κ S ψ a g = ψ (a,(e.symm g).val) := by
  have h := localGroupBlock_equiv κ S ψ a e he (e.symm g)
  simpa only [e.apply_symm_apply] using h

omit [StandardBorelSpace U] in
lemma localGroupBlock_finite (ψ : U × HilbertCode κ → C) (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val) (b : C)
    (hb : {q | (a,q) ∈ S ∧ ψ (a,q) = b}.Finite) :
    {g | localGroupBlock κ S ψ a g = b}.Finite := by
  apply Set.Finite.of_injOn (f := fun g => (e.symm g).val) _ _ hb
  · intro g hg
    exact ⟨(e.symm g).property,(localGroupBlock_symm κ S ψ a e he g).symm.trans hg⟩
  · intro g _ h _ heq
    exact e.symm.injective (Subtype.ext heq)

variable (ν : Measure U) [IsProbabilityMeasure ν] (ψ : U × HilbertCode κ → C)
    (a₀ : U)
    (hJ : ∀ᵐ a ∂ν, ∃ J : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a,
      ∀ g, localGroupBlock κ S ψ a (J g) = localGroupBlock κ S ψ a₀ g)
    (he : ∀ᵐ a ∂ν, ∃ e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a,
      ∀ q, (e q).val = HilbertCode.projective a q.val)

include hJ he in
lemma localGroupBlock_nonempty (b : positiveLevels (E.measure ν) ψ) :
    {g | localGroupBlock κ S ψ a₀ g = b.val}.Nonempty := by
  by_contra hn
  have hz : ∀ᵐ z ∂E.measure ν, ψ z ≠ b.val := by
    filter_upwards [E.ae_mem ν,E.ae_base ν hJ,E.ae_base ν he] with z hz hj he
    obtain ⟨J,hj⟩ := hj
    obtain ⟨e,he⟩ := he
    intro hzb
    apply hn
    refine ⟨J.symm (e ⟨z.2,hz⟩),?_⟩
    change localGroupBlock κ S ψ a₀ (J.symm (e ⟨z.2,hz⟩)) = b.val
    rw [←hj,J.apply_symm_apply,localGroupBlock_equiv κ S ψ z.1 e he]
    exact hzb
  exact b.property (by simpa only [ae_iff,not_not] using hz)
end

section
open MeasureTheory ProbabilityTheory Set
variable {U Y C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (κ : Kernel U Y) [IsMarkovKernel κ] (S : Set (U × HilbertCode κ))
    (ψ : U × HilbertCode κ → C)

lemma localBlock_card_le (a₀ a : U) (b : C)
    (hb : {g : localProjectiveGroup κ S a₀ | localGroupBlock κ S ψ a₀ g = b}.Finite)
    (J : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a)
    (hJ : ∀ g, localGroupBlock κ S ψ a (J g) = localGroupBlock κ S ψ a₀ g)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val) :
    ∃ h : {q | (a,q) ∈ S ∧ ψ (a,q) = b}.Finite, h.toFinset.card ≤ hb.toFinset.card := by
  classical
  let A : Set (HilbertCode κ) := {q | (a,q) ∈ S ∧ ψ (a,q) = b}
  let B : Set (localProjectiveGroup κ S a₀) := {g | localGroupBlock κ S ψ a₀ g = b}
  let map : A → B := fun q => ⟨J.symm (e ⟨q.val,q.property.1⟩),by
    change localGroupBlock κ S ψ a₀ (J.symm (e ⟨q.val,q.property.1⟩)) = b
    rw [←hJ,J.apply_symm_apply,localGroupBlock_equiv κ S ψ a e he]
    exact q.property.2⟩
  have hi : Function.Injective map := by
    intro q r h
    have h' := J.symm.injective (congrArg Subtype.val h)
    have hh : (⟨q.val,q.property.1⟩ : {q // (a,q) ∈ S}) = ⟨r.val,r.property.1⟩ := e.injective h'
    exact Subtype.ext (Subtype.mk.inj hh)
  let : Finite B := hb.to_subtype
  let : Finite A := Finite.of_injective map hi
  have hf : A.Finite := Set.toFinite A
  refine ⟨hf,?_⟩
  have h := Nat.card_le_card_of_injective map hi
  change A.ncard ≤ B.ncard at h
  rw [Set.ncard_eq_toFinset_card A hf,Set.ncard_eq_toFinset_card B hb] at h
  exact h
end

namespace ArrayObjects.Object.Rolled

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

section FiniteBlocks
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)

include hM hk hL hm hind hS Eπ Eσ hst in
lemma exists_raw_finite_blocks :
    ∃ (ψ : RawLabel M → LabelOrbitVector) (a₀ : Arr I M.U 0),
      Measurable ψ ∧
      (positiveLevels (E.measure (M.parameterLaw 0)) ψ).Countable ∧
      Countable (localProjectiveGroup (M.ownKernel 0) S a₀) ∧
      (∀ g : localProjectiveGroup (M.ownKernel 0) S a₀,
        localGroupBlock (M.ownKernel 0) S ψ a₀ g ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
      (∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        {g | localGroupBlock (M.ownKernel 0) S ψ a₀ g = b.val}.Finite ∧
        {g | localGroupBlock (M.ownKernel 0) S ψ a₀ g = b.val}.Nonempty) ∧
      (∀ᵐ a ∂M.parameterLaw 0,
        ∃ J : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a,
          ∀ g, localGroupBlock (M.ownKernel 0) S ψ a (J g) = localGroupBlock (M.ownKernel 0) S ψ a₀ g) ∧
      (∃ G : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a₀,
        ∀ g, localGroupBlock (M.ownKernel 0) S ψ a₀ (G g) =
          labelShiftSecond.symm (localGroupBlock (M.ownKernel 0) S ψ a₀ g)) ∧
      (∀ᵐ a ∂M.parameterLaw 0, ∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        {q | (a,q) ∈ S ∧ ψ (a,q) = b.val}.Finite) ∧
      (∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
        ψ (a,q) ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
      (∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
        ψ (rawLabelTime M (a,q)) = labelShiftSecond (ψ (a,q))) := by
  obtain ⟨ψ,hψ,hBc,hpos,hfinite,hfib,hD,hV,htr,ht⟩ :=
    exists_raw_finite_levels M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  let A : Arr I M.U 0 → Type _ := fun a => localProjectiveGroup (M.ownKernel 0) S a
  let block := localGroupBlock (M.ownKernel 0) S ψ
  have heq := localGraph_group_equiv M Λ hm S hS s
  let Q : Arr I M.U 0 → Prop := fun a =>
    (∃ e : {q // (a,q) ∈ S} ≃ A a, ∀ q, (e q).val = HilbertCode.projective a q.val) ∧
    (∀ q, (a,q) ∈ S → ψ (a,q) ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
    (∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
      {q | (a,q) ∈ S ∧ ψ (a,q) = b.val}.Finite)
  have hQ : ∀ᵐ a ∂M.parameterLaw 0, Q a := heq.and (hpos.and hfib)
  obtain ⟨a₀,ha₀,hJ⟩ := exists_good_block_preserving_trivialization
    (M.parameterLaw 0) (M.parameterLaw 1) (fun p => tupleParameter M p s) (fun p => tupleParameter M p t)
    (parameter_pair_preserving M hk s t hst) A block labelShiftFirst.toEquiv Q hQ
    (localGraph_matching_blocks M Λ hm S hS hk hind s t ψ labelShiftFirst htr)
  obtain ⟨e,he⟩ := ha₀.1
  refine ⟨ψ,a₀,hψ,hBc,localGroup_countable (M.ownKernel 0) S E a₀ e,?_,?_,hJ,?_,hfib,hpos,ht⟩
  · intro g
    rw [localGroupBlock_symm (M.ownKernel 0) S ψ a₀ e he]
    exact ha₀.2.1 _ (e.symm g).property
  · intro b
    exact ⟨localGroupBlock_finite (M.ownKernel 0) S ψ a₀ e he b.val (ha₀.2.2 b),
      localGroupBlock_nonempty (M.ownKernel 0) S E (M.parameterLaw 0) ψ a₀ hJ heq b⟩
  · exact exists_block_automorphism (M.parameterLaw 0) A block a₀ hJ
      (amap M.timeU 0) (M.parameterLaw_invariant 0) labelShiftSecond.toEquiv
      (localGraph_time_blocks M Λ hm S hS s hL ψ labelShiftSecond ht)
end FiniteBlocks


attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def slotExact (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    Set (Lp ℂ 2 ν) := {v | ∃ (f : Cell M i → Circle) (hf : Measurable f) (d : ℂ),
      v = d • circleLp ν f hf ∧ ∃ (a : ↥(({i} : Finset I)ᶜ) → Arr I M.Y 0 → Circle) (c : Circle),
      (∀ j, Measurable (a j)) ∧ ∀ᵐ y ∂M.ownKernel 1 p,
        f (slotCell M i y) = c * ∏ j : ↥(({i} : Finset I)ᶜ), a j (plane 0 0 j y)}

def slotExactSpan (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    Submodule ℂ (Lp ℂ 2 ν) := (Submodule.span ℂ (slotExact M i ν p)).topologicalClosure

lemma slotExactSpan_closed (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    IsClosed (slotExactSpan M i ν p : Set (Lp ℂ 2 ν)) := Submodule.isClosed_topologicalClosure _

lemma slotExactSpan_le_active (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1)
    (hx : MeasurePreserving (slotCell M i) (M.ownKernel 1 p) ν) :
    slotExactSpan M i ν p ≤ slotActive M i ν p := by
  apply Submodule.topologicalClosure_minimal _ _ (slotActive_closed M i ν p)
  apply Submodule.span_le.mpr
  rintro v ⟨f,hf,d,rfl,a,c,ha,he⟩
  rw [slotActive_eq M i ν p hx]
  apply Submodule.smul_mem
  apply Submodule.le_topologicalClosure
  let g : (↥(({i} : Finset I)ᶜ) → Arr I M.Y 0) → Circle := fun z => c * ∏ j, a j (z j)
  have hg : Measurable g := measurable_const.mul (Finset.measurable_prod _ fun j _ => (ha j).comp (measurable_pi_apply j))
  refine ⟨circleLp ((M.ownKernel 1 p).map (slotRest M i)) g hg,?_⟩
  exact JoiningOperator.circleLp_operator hx (MeasurePreserving.mk (measurable_slotRest M i) rfl) f g hf hg he

omit [DecidableEq I] in
lemma oneColumn_single_row (i j : I) (y : Arr I M.Y 2) :
    oneColumn M {i} 0 j y = fun _ => plane 0 0 j (plane 1 0 i y) := by
  funext r
  have hr : (r : I) = i := Finset.mem_singleton.mp r.property
  simp only [oneColumn,missingRow,hr]
  rfl

lemma fullExact_subset_slot_row (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ e ∂M.parameterLaw 2, fullExact M {i} {i} 0 e ⊆
      slotExact M i (cellLaw M {i} {i} 0 e) (plane 1 0 i e) := by
  filter_upwards [row_marginal_fibre M hM hI i] with e hr
  rintro v ⟨f,hf,d,hv,⟨a,c,ha,he⟩,_⟩
  refine ⟨f,hf,d,hv,(fun j y => a j (fun _ => y)),c,?_,?_⟩
  · intro j
    exact (ha j).comp (Measurable.of_eval fun _ => measurable_id)
  · rw [←hr.map_eq]
    apply ae_map_descent _ hr.measurable
    filter_upwards [he] with y hy
    simpa only [cells_single_row,Function.comp_apply,oneColumn_single_row] using hy
section PairTransport
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

private lemma transport_pair (i : I) (ν ρ : Measure (Cell M i))
    [IsFiniteMeasure ν] [IsFiniteMeasure ρ] (p q : Arr I M.U 1) (h : ν = ρ)
    (hp : (slotActive M i ν p).starProjection ∘L (slotActive M i ν q).starProjection =
      (slotActive M i ν q).starProjection ∘L (slotActive M i ν p).starProjection ∧
      slotActive M i ν p ⊓ slotActive M i ν q ≤ slotExactSpan M i ν p) :
    (slotActive M i ρ p).starProjection ∘L (slotActive M i ρ q).starProjection =
      (slotActive M i ρ q).starProjection ∘L (slotActive M i ρ p).starProjection ∧
      slotActive M i ρ p ⊓ slotActive M i ρ q ≤ slotExactSpan M i ρ p := by
  subst ρ
  exact hp

lemma slot_pair_on_square (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ e ∂M.parameterLaw 2,
      let ν := slotLocal M i (plane 0 0 i (plane 1 0 i e))
      let p := plane 1 0 i e
      let q := plane 1 (Fin.last 1) i e
      (slotActive M i ν p).starProjection ∘L (slotActive M i ν q).starProjection =
        (slotActive M i ν q).starProjection ∘L (slotActive M i ν p).starProjection ∧
      slotActive M i ν p ⊓ slotActive M i ν q ≤ slotExactSpan M i ν p := by
  filter_upwards [singleton_cellLaw M hM hI i,rowActive_single_slot M hM hI i s,
    columnActive_single_slot M hM hI i s,grouped_active_commutes M hM s.partition s.partition 0,
    commonActive_le_fullExact_span M hM {i} {i} s s 0,fullExact_subset_slot_row M hM hI i]
    with e hν hr hc hcomm hex hfull
  have hsub : slotActive M i (cellLaw M {i} {i} 0 e) (plane 1 0 i e) ⊓
      slotActive M i (cellLaw M {i} {i} 0 e) (plane 1 (Fin.last 1) i e) ≤
      slotExactSpan M i (cellLaw M {i} {i} 0 e) (plane 1 0 i e) := by
    rw [←hr,←hc]
    exact hex.trans (Submodule.topologicalClosure_mono (Submodule.span_mono hfull))
  simp only [hr,hc] at hcomm
  exact transport_pair M i _ _ _ _ hν ⟨hcomm,hsub⟩

lemma slot_conditional_pairs (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ pq ∂(M.parameterCoordinateKernel i u).prod (M.parameterCoordinateKernel i u),
      (slotActive M i (slotLocal M i u) pq.1).starProjection ∘L
        (slotActive M i (slotLocal M i u) pq.2).starProjection =
      (slotActive M i (slotLocal M i u) pq.2).starProjection ∘L
        (slotActive M i (slotLocal M i u) pq.1).starProjection ∧
      slotActive M i (slotLocal M i u) pq.1 ⊓ slotActive M i (slotLocal M i u) pq.2 ≤
        slotExactSpan M i (slotLocal M i u) pq.1 := by
  let P : Arr I M.U 0 → (Arr I M.U 1 × Arr I M.U 1) → Prop := fun u pq =>
    (slotActive M i (slotLocal M i u) pq.1).starProjection ∘L
      (slotActive M i (slotLocal M i u) pq.2).starProjection =
    (slotActive M i (slotLocal M i u) pq.2).starProjection ∘L
      (slotActive M i (slotLocal M i u) pq.1).starProjection ∧
    slotActive M i (slotLocal M i u) pq.1 ⊓ slotActive M i (slotLocal M i u) pq.2 ≤
      slotExactSpan M i (slotLocal M i u) pq.1
  have h := conditional_ae_descent (P := P) ((measurable_plane 0 0 i).comp (measurable_plane 1 0 i))
    ((measurable_plane 1 0 i).prodMk (measurable_plane 1 (Fin.last 1) i))
    (M.diagonal_parameter_product hM hI i) (slot_pair_on_square M hM hI i s)
  rw [←Measure.map_map (measurable_plane 0 0 i) (measurable_plane 1 0 i),
    M.parameterLaw_consistent 1 0 i,M.parameterLaw_consistent 0 0 i] at h
  simpa only [Kernel.prod_apply] using h

theorem slot_conditional_exactness (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      slotActive M i (slotLocal M i u) p ≤ slotExactSpan M i (slotLocal M i u) p := by
  filter_upwards [slot_conditional_pairs M hM hI i s] with u hu
  let V := fun p => slotActive M i (slotLocal M i u) p
  let C := fun p => V p ⊓ slotExactSpan M i (slotLocal M i u) p
  have hc (p) : IsClosed (C p : Set (Lp ℂ 2 (slotLocal M i u))) :=
    (slotActive_closed M i _ p).inter (slotExactSpan_closed M i _ p)
  have h := random_projection_exactness (M.parameterCoordinateKernel i u) V C hc
    (fun _ => inf_le_left) (hu.mono fun pq h => ⟨h.1,le_inf inf_le_left h.2⟩)
  filter_upwards [h] with p hp
  have hle : V p ≤ slotExactSpan M i (slotLocal M i u) p := hp.le.trans inf_le_right
  exact hle
end PairTransport

def unpadCell (i : I) (y : Cell M i) : Arr I M.Y 0 :=
  y ⟨i,Finset.mem_singleton_self i⟩ ⟨i,Finset.mem_singleton_self i⟩
omit [DecidableEq I] in
@[fun_prop] lemma measurable_unpadCell (i : I) : Measurable (unpadCell M i) :=
  (measurable_pi_apply _).comp (measurable_pi_apply _)
omit [DecidableEq I] in
lemma unpad_pad (i : I) (y : Arr I M.Y 0) : unpadCell M i (padCell M i y) = y := rfl
omit [DecidableEq I] in
lemma pad_unpad (i : I) (y : Cell M i) : padCell M i (unpadCell M i y) = y := by
  funext a b
  have ha : a = ⟨i,Finset.mem_singleton_self i⟩ := Subtype.ext (Finset.mem_singleton.mp a.property)
  have hb : b = ⟨i,Finset.mem_singleton_self i⟩ := Subtype.ext (Finset.mem_singleton.mp b.property)
  subst a; subst b; rfl

lemma slotExactSpan_le_codeSpan (i : I) (p : Arr I M.U 1)
    (hm : ∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
      (slotLocal M i (tupleParameter M p j))) :
    slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p ≤
      exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i := by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro v ⟨f,hf,d,rfl,a,c,ha,he⟩
  let b : ↥(({i} : Finset I)ᶜ) → Cell M i → Circle := fun j z => a j (unpadCell M i z)
  have hb (j) : Measurable (b j) := (ha j).comp (measurable_unpadCell M i)
  have hc : ∀ᵐ z ∂slotTupleKernel M i p, ∏ j, circleComplete i f b j (z j) = c := by
    rw [slotTupleKernel,Kernel.map_apply _ (measurable_slotTuple M i)]
    apply ae_map_descent _ (measurable_slotTuple M i)
    filter_upwards [he] with y hy
    apply circleComplete_prod i f b _ c
    exact hy
  have hv := exactCircle_mem_codeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i hm
    (circleComplete i f b) (measurable_circleComplete i f b hf hb) c hc d
  change d • circleLp (slotLocal M i (tupleParameter M p i)) f hf ∈
    exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i
  simpa only [circleComplete_self] using hv

lemma codeSpan_le_slotExactSpan (i : I) (p : Arr I M.U 1)
    (hm : ∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
      (slotLocal M i (tupleParameter M p j))) :
    exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i ≤
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p := by
  apply Submodule.topologicalClosure_minimal _ _ (slotExactSpan_closed M i _ p)
  apply Submodule.span_le.mpr
  intro v hv
  obtain ⟨f,hf,c,hv,he⟩ := exactVector_circle_tuple (slotLocal M i) (slotTupleKernel M i)
    (tupleParameter M) p i hm hv
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨f i,hf i,1,?_,(fun j y => (f j (padCell M i y))⁻¹),c,?_,?_⟩
  · simpa only [one_smul] using hv
  · intro j
    exact ((hf j).comp (measurable_padCell M i)).inv
  · have hmap : MeasurePreserving (slotTuple M i) (M.ownKernel 1 p) (slotTupleKernel M i p) :=
      ⟨measurable_slotTuple M i,(Kernel.map_apply _ (measurable_slotTuple M i) _).symm⟩
    filter_upwards [hmap.quasiMeasurePreserving.ae he] with y hy
    exact prod_equation_solve i _ c hy

lemma slotExactSpan_eq_codeSpan (i : I) (p : Arr I M.U 1)
    (hm : ∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
      (slotLocal M i (tupleParameter M p j))) :
    slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p =
      exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i :=
  le_antisymm (slotExactSpan_le_codeSpan M i p hm) (codeSpan_le_slotExactSpan M i p hm)
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I Ω Z : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (hu : Measurable u)
  (L : Kernel P Ω) [IsMarkovKernel L] (x : Ω → Y) (z : Ω → Z)

include hu in
lemma measurableSet_code_tests (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    MeasurableSet {p | ∀ n, posteriorTest L x z κ (fun p => u p i) n p ∈ exactCodeSpan κ Λ u p i} := by
  obtain ⟨s,hs,he⟩ := exactCodeSpan_sections κ Λ u hu hk hm hind i
  have hv (n) := measurableSection_posteriorTest L x z κ (fun p => u p i)
    ((measurable_pi_apply i).comp hu) n
  simp only [he,Set.ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    measurableSet_section_mem_span ((measurable_pi_apply i).comp hu) hs (hv n)

omit [StandardBorelSpace P] [StandardBorelSpace U] [DecidableEq I] [IsMarkovKernel Λ] in
lemma code_tests_iff_range (hz : Measurable z) (p : P) (i : I)
    (hx : MeasurePreserving x (L p) (κ (u p i))) :
    (∀ n, posteriorTest L x z κ (fun p => u p i) n p ∈ exactCodeSpan κ Λ u p i) ↔
      (LinearMap.range (JoiningOperator.operator hx (MeasurePreserving.mk hz rfl)).toLinearMap).topologicalClosure ≤
        exactCodeSpan κ Λ u p i := by
  simp only [posteriorTest_eq_operator L x z κ (fun p => u p i) hz p hx]
  exact (operator_range_le_iff_tests _ _ (hilbertTests_dense _) _
    (Submodule.isClosed_topologicalClosure _)).symm
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma slot_global_exactness (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ p ∂M.parameterLaw 1, slotActive M i (slotLocal M i (tupleParameter M p i)) p =
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p := by
  have hI : 2 ≤ Fintype.card I := by omega
  obtain ⟨L,hL,hLe,hm,hi⟩ := exists_good_tuple_kernel (slotLocal M i) (slotTupleKernel M i)
    (tupleParameter M) (measurable_tupleParameter M) (M.parameterLaw 1)
    (slotTuple_marginal M hI i) (slotTuple_proper M i)
  let : IsMarkovKernel L := hL
  let E := {p | ∀ n, posteriorTest (M.ownKernel 1) (slotCell M i) (slotRest M i)
    (slotLocal M i) (fun p => tupleParameter M p i) n p ∈
      exactCodeSpan (slotLocal M i) L (tupleParameter M) p i}
  have hEm : MeasurableSet E := measurableSet_code_tests (slotLocal M i) L (tupleParameter M)
    (measurable_tupleParameter M) (M.ownKernel 1) (slotCell M i) (slotRest M i) hk hm hi i
  have hκ : HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 i)
      (M.parameterCoordinateKernel i) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib (by fun_prop) measurable_id.aemeasurable).symm⟩
  have hgood : ∀ᵐ p ∂M.parameterLaw 1,
      L p = slotTupleKernel M i p ∧
      (∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
        (slotLocal M i (tupleParameter M p j))) ∧
      MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
        (slotLocal M i (tupleParameter M p i)) :=
    hLe.and ((slotTuple_marginal M hI i).and (slotCell_marginal M hI i))
  have hcond := conditional_ae_descent (κ := M.parameterCoordinateKernel i)
    (P := fun u p => plane 0 0 i p = u ∧ L p = slotTupleKernel M i p ∧
      (∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
        (slotLocal M i (tupleParameter M p j))) ∧
      MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
        (slotLocal M i (tupleParameter M p i)))
    (measurable_plane 0 0 i) measurable_id hκ
    (hgood.mono fun p hp => ⟨rfl,hp⟩)
  rw [M.parameterLaw_consistent 0 0 i] at hcond
  have hE : ∀ᵐ p ∂M.parameterLaw 1, p ∈ E := by
    apply conditional_ae_lift (κ := M.parameterCoordinateKernel i) (measurable_plane 0 0 i) measurable_id hκ hEm
    rw [M.parameterLaw_consistent 0 0 i]
    filter_upwards [slot_conditional_exactness M hM hI i s,hcond] with u hu hg
    filter_upwards [hu,hg] with p hp hg
    rcases hg with ⟨hu,heq,hpm,hxm⟩
    subst u
    apply (code_tests_iff_range (slotLocal M i) L (tupleParameter M) (M.ownKernel 1)
      (slotCell M i) (slotRest M i) (measurable_slotRest M i) p i hxm).mpr
    rw [←slotActive_eq M i _ p hxm]
    change slotActive M i (slotLocal M i (tupleParameter M p i)) p ≤ _ at hp
    rw [exactCodeSpan_congr_kernel (slotLocal M i) L (tupleParameter M) (slotTupleKernel M i) p i heq,
      ←slotExactSpan_eq_codeSpan M i p hpm]
    exact hp
  filter_upwards [hE,hgood] with p hp hg
  apply le_antisymm _ (slotExactSpan_le_active M i _ p hg.2.2)
  have hr := (code_tests_iff_range (slotLocal M i) L (tupleParameter M) (M.ownKernel 1)
    (slotCell M i) (slotRest M i) (measurable_slotRest M i) p i hg.2.2).mp hp
  rw [←slotActive_eq M i _ p hg.2.2,
    exactCodeSpan_congr_kernel (slotLocal M i) L (tupleParameter M) (slotTupleKernel M i) p i hg.1,
    ←slotExactSpan_eq_codeSpan M i p hg.2.1] at hr
  exact hr
end ArrayObjects.Object.Rolled

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

def projectiveRep (g : ProjectiveCircle μ) : MeasurableCircle Y :=
  if g = 1 then 1 else Quotient.out g

lemma projectiveRep_class (g : ProjectiveCircle μ) :
    projectiveCircle μ (projectiveRep μ g) (measurableCircle_measurable Y _) = g := by
  by_cases hg : g = 1
  · subst g
    simp only [projectiveRep]
    exact projectiveCircle_one μ
  · rw [projectiveRep,ite_eq_right hg]
    exact Quotient.out_eq g

lemma projectiveRep_one : projectiveRep μ 1 = 1 := by simp [projectiveRep]

def projectiveCharacter (g : ProjectiveCircle μ) (y : Y) : ℂ := projectiveRep μ g y

lemma projectiveCharacter_measurable (g : ProjectiveCircle μ) :
    Measurable (projectiveCharacter μ g) :=
  measurable_subtype_coe.comp (measurableCircle_measurable Y _)

lemma projectiveCharacter_mul (g h : ProjectiveCircle μ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (fun y => projectiveCharacter μ g y * projectiveCharacter μ h y) =ᵐ[μ]
        fun y => c * projectiveCharacter μ (g*h) y := by
  have he : projectiveCircle μ (fun y => projectiveRep μ g y * projectiveRep μ h y)
      ((measurableCircle_measurable Y _).mul (measurableCircle_measurable Y _)) =
      projectiveCircle μ (projectiveRep μ (g*h)) (measurableCircle_measurable Y _) := by
    rw [projectiveCircle_mul _ _ _ (measurableCircle_measurable Y _)
      (measurableCircle_measurable Y _),projectiveRep_class,projectiveRep_class,projectiveRep_class]
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff μ _ _ _ _).mp he
  refine ⟨(c : ℂ),Circle.norm_coe c,?_⟩
  filter_upwards [hc] with y hy
  exact congrArg (fun c : Circle => (c : ℂ)) hy

lemma projectiveCharacters_of_zero_mean (L : Subgroup (ProjectiveCircle μ))
    (hm : ∀ g : L, g ≠ 1 → ∫ y, projectiveCharacter μ g.val y ∂μ = 0) :
    ProjectiveCharacters μ (fun g : Additive L => projectiveCharacter μ g.toMul.val) where
  measurable g := (projectiveCharacter_measurable μ _).aestronglyMeasurable
  modulus _ := Filter.Eventually.of_forall fun _ => Circle.norm_coe _
  zero := Filter.Eventually.of_forall fun _ => by
    change (projectiveRep μ 1 _ : ℂ) = 1
    rw [projectiveRep_one]; rfl
  mul g h := projectiveCharacter_mul μ g.toMul.val h.toMul.val
  mean g hg := hm g.toMul hg
end

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]

def absoluteCoefficient (f : Y → ℂ) (z : U × HilbertCode κ) : ℝ :=
  ‖∫ y, f y * conj (HilbertCode.circleRep z.2 y : ℂ) ∂κ z.1‖

lemma measurable_absoluteCoefficient (f : Y → ℂ) (hf : Measurable f) :
    Measurable (absoluteCoefficient κ f) := by
  have hm : Measurable (fun p : (U × HilbertCode κ) × Y => (p.1.2,p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hrep : Measurable (fun p : (U × HilbertCode κ) × Y =>
      HilbertCode.representative (κ := κ) (p.1.2,p.2)) :=
    (HilbertCode.measurable_representative (κ := κ)).comp hm
  have hr : Measurable (fun p : (U × HilbertCode κ) × Y =>
      (HilbertCode.circleRep p.1.2 p.2 : ℂ)) :=
    measurable_subtype_coe.comp (measurable_circleOfValue.comp hrep)
  exact ((hf.comp measurable_snd).mul (continuous_star.measurable.comp hr)).stronglyMeasurable.integral_kernel_prod_right
    (κ := κ.comap Prod.fst measurable_fst) |>.norm.measurable

lemma absoluteCoefficient_nonneg (f : Y → ℂ) (z : U × HilbertCode κ) :
    0 ≤ absoluteCoefficient κ f z := norm_nonneg _

lemma absoluteCoefficient_le (f : Y → ℂ) (C : ℝ) (z : U × HilbertCode κ)
    (hf : ∀ᵐ y ∂κ z.1, ‖f y‖ ≤ C) : absoluteCoefficient κ f z ≤ C := by
  have hb : ∀ᵐ y ∂κ z.1, ‖f y * conj (HilbertCode.circleRep z.2 y : ℂ)‖ ≤ C := by
    filter_upwards [hf] with y hy
    simpa only [norm_mul,Complex.norm_conj,Circle.norm_coe,mul_one] using hy
  simpa [absoluteCoefficient, Measure.real] using
    norm_integral_le_of_norm_le_const hb

omit [MeasurableSpace.CountablyGenerated Y] in
lemma norm_integral_mul_conj_of_phase {μ : Measure Y} (f g h : Y → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (he : g =ᵐ[μ] fun y => c * h y) :
    ‖∫ y, f y * conj (g y) ∂μ‖ = ‖∫ y, f y * conj (h y) ∂μ‖ := by
  have ht : (fun y => f y * conj (g y)) =ᵐ[μ]
      fun y => conj c * (f y * conj (h y)) := he.mono fun y hy => by
    dsimp only at hy ⊢
    rw [hy,map_mul]; ring
  rw [integral_congr_ae ht,integral_const_mul,norm_mul,Complex.norm_conj,hc,one_mul]

lemma absoluteCoefficient_projective (f : Y → ℂ) (a : U) (q : HilbertCode κ) :
    absoluteCoefficient κ f (a,q) =
      ‖∫ y, f y * conj (projectiveCharacter (κ a) (HilbertCode.projective a q) y) ∂κ a‖ := by
  have he : projectiveCircle (κ a) (HilbertCode.circleRep q)
      (HilbertCode.measurable_circleRep_fixed q) =
      projectiveCircle (κ a) (projectiveRep (κ a) (HilbertCode.projective a q))
        (measurableCircle_measurable Y _) := by
    rw [projectiveRep_class]
    rfl
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff _ _ _ _ _).mp he
  apply norm_integral_mul_conj_of_phase _ _ _ (c : ℂ) (Circle.norm_coe c)
  filter_upwards [hc] with y hy
  exact congrArg (fun z : Circle => (z : ℂ)) hy
lemma absoluteCoefficient_encode_smul (f : Y → ℂ) (a : U)
    (g : Y → Circle) (hg : Measurable g) (d : ℂ) (hd : ‖d‖ = 1) :
    absoluteCoefficient κ f (a,HilbertCode.encode a (d • circleLp (κ a) g hg)) =
      ‖∫ y, f y * conj (g y : ℂ) ∂κ a‖ := by
  let q := HilbertCode.encode a (d • circleLp (κ a) g hg)
  have hr : (fun y => HilbertCode.representative (q,y)) =ᵐ[κ a]
      (fun y => d * (g y : ℂ)) := by
    have h := HilbertCode.representative_eq_decode q
    change (fun y => HilbertCode.representative (q,y)) =ᵐ[κ a]
      (HilbertCode.decode (HilbertCode.encode a (d • circleLp (κ a) g hg)) : Y → ℂ) at h
    rw [HilbertCode.decode_encode] at h
    filter_upwards [h,Lp.coeFn_smul d (circleLp (κ a) g hg),circleLp_coe (κ a) g hg]
      with y h1 h2 h3
    exact h1.trans (h2.trans (congrArg (d * ·) h3))
  have hu : q.IsUnimodular := hr.mono fun y hy => by
    dsimp only at hy
    rw [hy,norm_mul,hd,Circle.norm_coe,mul_one]
  exact norm_integral_mul_conj_of_phase _ _ _ d hd ((HilbertCode.circleRep_ae q hu).trans hr)

omit [MeasurableSpace.CountablyGenerated Y] in
lemma inner_circle_toLp {ν : Measure Y} [IsFiniteMeasure ν]
    (f : Y → ℂ) (hf : MemLp f 2 ν) (g : Y → Circle) (hg : Measurable g) :
    inner ℂ (circleLp ν g hg) (hf.toLp f) = ∫ y, f y * conj (g y : ℂ) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleLp_coe ν g hg,hf.coeFn_toLp] with y h1 h2
  rw [h1,h2]
  rfl
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] in
lemma raw_exact_coefficient_zero (p : Arr I M.U 1) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (f : Arr I M.Y 0 → ℂ)
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) f (tupleParameter M p i,q) = 0)
    (g : I → Arr I M.Y 0 → Circle) (hg : ∀ j, Measurable (g j)) (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ j, g j (y j) = c) :
    ∫ y, f y * conj (g i y : ℂ) ∂M.ownKernel 0 (tupleParameter M p i) = 0 := by
  obtain ⟨a,d,ha,hd⟩ := normalized_exact_codes (M.ownKernel 0) Λ (tupleParameter M)
    p hm g hg c he
  have hz := hzero (a i) ⟨a,ha,rfl⟩
  rw [(hd i).2,absoluteCoefficient_encode_smul _ _ _ _ _ _ (hd i).1] at hz
  exact norm_eq_zero.mp hz

lemma slotExact_coefficient_zero (p : Arr I M.U 1) (i : I)
    (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (f : Arr I M.Y 0 → ℂ)
    (hf : MemLp (f ∘ unpadCell M i) 2 (slotLocal M i (tupleParameter M p i)))
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) f (tupleParameter M p i,q) = 0)
    {v : Lp ℂ 2 (slotLocal M i (tupleParameter M p i))}
    (hv : v ∈ slotExact M i (slotLocal M i (tupleParameter M p i)) p) :
    inner ℂ v (hf.toLp (f ∘ unpadCell M i)) = 0 := by
  obtain ⟨g,hg,d,rfl,a,c,ha,he⟩ := hv
  let b : ↥(({i} : Finset I)ᶜ) → Arr I M.Y 0 → Circle := fun j y => a j y
  have hb (j) : Measurable (b j) := ha j
  let g₀ : Arr I M.Y 0 → Circle := g ∘ padCell M i
  have hg₀ : Measurable g₀ := hg.comp (measurable_padCell M i)
  have ht : ∀ᵐ y ∂Λ p, ∏ j, circleComplete i g₀ b j (y j) = c := by
    rw [hL,rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)]
    apply ae_map_descent _ (measurable_rawTuple M)
    filter_upwards [he] with y hy
    apply circleComplete_prod i g₀ b _ c
    exact hy
  have hz := raw_exact_coefficient_zero M Λ p i hm f hzero
    (circleComplete i g₀ b) (measurable_circleComplete i g₀ b hg₀ hb) c ht
  simp only [circleComplete_self] at hz
  rw [inner_smul_left,inner_circle_toLp]
  suffices hh : ∫ y, (f ∘ unpadCell M i) y * conj (g y : ℂ)
      ∂slotLocal M i (tupleParameter M p i) = 0 by rw [hh,mul_zero]
  rw [slotLocal,Kernel.map_apply _ (measurable_padCell M i),integral_map
    (measurable_padCell M i).aemeasurable]
  · exact hz
  · have hmeas : AEStronglyMeasurable (fun y => (f ∘ unpadCell M i) y * conj (g y : ℂ))
        (slotLocal M i (tupleParameter M p i)) := by
      apply hf.aestronglyMeasurable.mul
      exact (continuous_star.measurable.comp (measurable_subtype_coe.comp hg)).aestronglyMeasurable
    simpa only [slotLocal,Kernel.map_apply _ (measurable_padCell M i)] using hmeas

lemma slotActive_orthogonal_of_coefficients_zero (p : Arr I M.U 1) (i : I)
    (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (he : slotActive M i (slotLocal M i (tupleParameter M p i)) p =
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p)
    (f : Arr I M.Y 0 → ℂ)
    (hf : MemLp (f ∘ unpadCell M i) 2 (slotLocal M i (tupleParameter M p i)))
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) f (tupleParameter M p i,q) = 0) :
    hf.toLp (f ∘ unpadCell M i) ∈ (slotActive M i (slotLocal M i (tupleParameter M p i)) p)ᗮ := by
  rw [he]
  let K : Submodule ℂ (Lp ℂ 2 (slotLocal M i (tupleParameter M p i))) :=
    (ℂ ∙ hf.toLp (f ∘ unpadCell M i))ᗮ
  have hk : slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p ≤ K := by
    apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _)
    apply Submodule.span_le.mpr
    intro v hv
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    exact slotExact_coefficient_zero M Λ p i hL hm f hf hzero hv
  rw [Submodule.mem_orthogonal]
  intro v hv
  exact (Submodule.mem_orthogonal_singleton_iff_inner_left).mp (hk hv)
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
variable {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure Y} {η : Measure Z} {x : Ω → Y} {z : Ω → Z}
lemma correlation_zero_of_orthogonal (hx : MeasurePreserving x μ ν) (hz : MeasurePreserving z μ η)
    (f : Y → ℂ) (hf : MemLp f 2 ν) (g : Z → ℂ) (hg : MemLp g 2 η)
    (horth : hf.toLp f ∈ (LinearMap.range (operator hx hz).toLinearMap).topologicalClosureᗮ) :
    ∫ ω, f (x ω) * conj (g (z ω)) ∂μ = 0 := by
  have hv : operator hx hz (hg.toLp g) ∈
      (LinearMap.range (operator hx hz).toLinearMap).topologicalClosure :=
    Submodule.le_topologicalClosure _ ⟨hg.toLp g,rfl⟩
  have he := Submodule.inner_right_of_mem_orthogonal hv horth
  rw [←inner_conj_symm,inner_operator,←integral_conj] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards [hx.quasiMeasurePreserving.ae hf.coeFn_toLp,
    hz.quasiMeasurePreserving.ae hg.coeFn_toLp] with ω h1 h2
  rw [h1,h2]
  simp only [RCLike.inner_apply,starRingEnd_apply,map_mul,star_star]
  ring
end JoiningOperator

namespace ConditionalFibres
open MeasureTheory ProbabilityTheory
variable {Ω U Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {x : Ω → U} {y : Ω → Y}
  {κ : Kernel U Y} [IsMarkovKernel κ]
lemma integral_integral_of_bound (h : HasCondDistrib y x κ μ)
    (f : Y → ℂ) (hf : Measurable f) (C : ℝ) (hb : ∀ y, ‖f y‖ ≤ C) :
    ∫ u, ∫ z, f z ∂κ u ∂μ.map x = ∫ ω, f (y ω) ∂μ := by
  have hi : Integrable (fun p : U × Y => f p.2) (μ.map x ⊗ₘ κ) :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hb p.2)
  rw [←Measure.integral_compProd hi,←h.map_eq]
  exact integral_map h.aemeasurable (hf.comp measurable_snd).aestronglyMeasurable
end ConditionalFibres

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

lemma slot_product_zero (p : Arr I M.U 1) (i : I)
    (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hx : MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
      (slotLocal M i (tupleParameter M p i)))
    (he : slotActive M i (slotLocal M i (tupleParameter M p i)) p =
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p)
    (f : I → Arr I M.Y 0 → ℂ) (hf : ∀ j, Measurable (f j))
    (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) (f i) (tupleParameter M p i,q) = 0) :
    ∫ y, ∏ j, f j (plane 0 0 j y) ∂M.ownKernel 1 p = 0 := by
  let g : (↥(({i} : Finset I)ᶜ) → Arr I M.Y 0) → ℂ :=
    fun z => conj (∏ j : ↥(({i} : Finset I)ᶜ), f j (z j))
  have hgm : Measurable g := continuous_star.measurable.comp
    (Finset.measurable_prod _ fun j _ => (hf j).comp (measurable_pi_apply j))
  have hgb (z) : ‖g z‖ ≤ 1 := by
    dsimp [g]
    rw [Complex.norm_conj, norm_prod]
    exact Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => hb j _)
  let hfi : MemLp (f i ∘ unpadCell M i) 2 (slotLocal M i (tupleParameter M p i)) :=
    MemLp.of_bound ((hf i).comp (measurable_unpadCell M i)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => hb i _)
  have ho := slotActive_orthogonal_of_coefficients_zero M Λ p i hL hm he (f i) hfi hzero
  rw [slotActive_eq M i _ p hx] at ho
  have hz := JoiningOperator.correlation_zero_of_orthogonal hx
    (MeasurePreserving.mk (measurable_slotRest M i) rfl) (f i ∘ unpadCell M i) hfi g
    (MemLp.of_bound hgm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hgb)) ho
  convert hz using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp [g,slotCell,slotRest,unpadCell,padCell]
  rw [Complex.conj_conj]
  rw [Fintype.prod_eq_mul_prod_compl i]
  congr 1
  exact (Finset.prod_attach _ (fun j : I => f j (plane 0 0 j y))).symm

lemma raw_correlation_forces_coefficient (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ j, {q | (p,q) ∈ rawLineGraph M Λ j} =
      {q | (tupleParameter M p j,q) ∈ S})
    (i : I) (f : I → Arr I M.Y 0 → ℂ) (hf : ∀ j, Measurable (f j))
    (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hpos : (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) ≠ 0) :
    ¬ ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
      absoluteCoefficient (M.ownKernel 0) (f i) (a,q) = 0 := by
  intro hz
  have hpa : MeasurePreserving (fun p => tupleParameter M p i)
      (M.parameterLaw 1) (M.parameterLaw 0) :=
    ⟨measurable_plane 0 0 i,M.parameterLaw_consistent 0 0 i⟩
  have hzero : ∀ᵐ p ∂M.parameterLaw 1,
      (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.ownKernel 1 p) = 0 := by
    filter_upwards [hL,hS,hpa.quasiMeasurePreserving.ae hz,
      slot_global_exactness M hM hk i (singletonSplit hk i),
      slotCell_marginal M (by omega) i] with p hp hs hz he hx
    apply slot_product_zero M Λ p i hp (hm p) hx he f hf hb
    intro q hq
    exact hz q (by change q ∈ {q | (tupleParameter M p i,q) ∈ S}; rw [←hs i]; exact hq)
  apply hpos
  have hpm : Measurable (fun y : Arr I M.Y 1 => ∏ j, f j (plane 0 0 j y)) :=
    Finset.measurable_prod _ fun j _ => (hf j).comp (measurable_plane _ _ _)
  have hpb (y : Arr I M.Y 1) : ‖∏ j, f j (plane 0 0 j y)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => hb j _)
  have ht := ConditionalFibres.integral_integral_of_bound (M.ownKernel_conditional 1) _ hpm 1 hpb
  exact ht.symm.trans (integral_eq_zero_of_ae hzero)
end ArrayObjects.Object.Rolled

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped BigOperators

section
attribute [local instance] Classical.propDecidable
variable {U Z W : Type*} [MeasurableSpace U] [MeasurableSpace Z] [MeasurableSpace W]
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def sumFibreEquiv (a : U) : {n : ℕ // a ∈ E.domain n} ≃ {z : Z // (a,z) ∈ S} :=
  Equiv.ofBijective (fun n => ⟨E.section_ n.val a,E.mem n.val a n.property⟩) (by
    constructor
    · intro n m h
      exact Subtype.ext (E.unique a n.val m.val n.property m.property (congrArg Subtype.val h))
    · intro z
      obtain ⟨n,hn,he⟩ := E.cover a z.val z.property
      exact ⟨⟨n,hn⟩,Subtype.ext he⟩)

def fibreSum (F : U × Z → ℝ) (a : U) : ℝ :=
  ∑' n : ℕ, if a ∈ E.domain n then F (a,E.section_ n a) else 0

lemma measurable_fibreSum (F : U × Z → ℝ) (hF : Measurable F) :
    Measurable (E.fibreSum F) := by
  apply Measurable.tsum
  intro n
  exact Measurable.ite (E.measurable_domain n)
    (hF.comp (measurable_id.prodMk (E.measurable_section n))) measurable_const

lemma fibreSum_eq_tsum (F : U × Z → ℝ) (a : U) :
    E.fibreSum F a = ∑' z : {z : Z // (a,z) ∈ S}, F (a,z.val) := by
  rw [fibreSum,←(E.sumFibreEquiv a).tsum_eq]
  exact (tsum_subtype {n | a ∈ E.domain n} (fun n => F (a,E.section_ n a))).symm

lemma fibreSum_eq_finite_sum (F : U × Z → ℝ) (a : U) (h : {z | (a,z) ∈ S}.Finite) :
    E.fibreSum F a = ∑ z ∈ h.toFinset, F (a,z) := by
  rw [E.fibreSum_eq_tsum]
  let : Fintype {z : Z // (a,z) ∈ S} := h.fintype
  rw [tsum_fintype]
  exact (Finset.sum_subtype h.toFinset (fun z => h.mem_toFinset (a := z)) (fun z => F (a,z))).symm

lemma fibreSum_nonneg (F : U × Z → ℝ) (hF : ∀ z, 0 ≤ F z) (a : U) :
    0 ≤ E.fibreSum F a := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact hF _
  · exact le_rfl

lemma fibreSum_eq_zero_iff (F : U × Z → ℝ) (hF : ∀ z, 0 ≤ F z)
    (a : U) (h : {z | (a,z) ∈ S}.Finite) :
    E.fibreSum F a = 0 ↔ ∀ z, (a,z) ∈ S → F (a,z) = 0 := by
  rw [E.fibreSum_eq_finite_sum F a h,Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hF (a,z))]
  simp only [h.mem_toFinset,Set.mem_ofPred_eq]

lemma fibreSum_eq_sum_equiv {K : Type*} [Fintype K] (a : U)
    (e : K ≃ {z : Z // (a,z) ∈ S}) (F : U × Z → ℝ) :
    E.fibreSum F a = ∑ k, F (a,(e k).val) := by
  rw [E.fibreSum_eq_tsum,←e.tsum_eq,tsum_fintype]

variable {R : Set (U × W)} (D : BorelFibreEnumeration R)
lemma fibreSum_transport (a b : U) (e : {z : Z // (a,z) ∈ S} ≃ {w : W // (b,w) ∈ R})
    (F : U × Z → ℝ) (G : U × W → ℝ)
    (he : ∀ z, F (a,z.val) = G (b,(e z).val)) : E.fibreSum F a = D.fibreSum G b := by
  rw [E.fibreSum_eq_tsum,D.fibreSum_eq_tsum,←e.tsum_eq]
  exact tsum_congr he

variable {C : Type*} [MeasurableSpace C] [MeasurableSingletonClass C]

def restrictLevel (ψ : U × Z → C) (hψ : Measurable ψ) (b : C) :
    BorelFibreEnumeration {z | z ∈ S ∧ ψ z = b} where
  domain n := {a | a ∈ E.domain n ∧ ψ (a,E.section_ n a) = b}
  section_ := E.section_
  measurable_domain n := (E.measurable_domain n).inter
    ((hψ.comp (measurable_id.prodMk (E.measurable_section n))) (measurableSet_singleton b))
  measurable_section := E.measurable_section
  mem n a ha := ⟨E.mem n a ha.1,ha.2⟩
  cover a z hz := by
    obtain ⟨n,hn,he⟩ := E.cover a z hz.1
    exact ⟨n,⟨hn,he ▸ hz.2⟩,he⟩
  unique a n m hn hm he := E.unique a n m hn.1 hm.1 he
end

variable {U Z C : Type*} [MeasurableSpace U] [MeasurableSpace Z]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma fibreSum_le_card_mul (F : U × Z → ℝ) (c : ℝ) (a : U)
    (h : {z | (a,z) ∈ S}.Finite) (hF : ∀ z, (a,z) ∈ S → F (a,z) ≤ c) :
    E.fibreSum F a ≤ h.toFinset.card * c := by
  rw [E.fibreSum_eq_finite_sum F a h]
  calc
    _ ≤ ∑ _z ∈ h.toFinset, c := Finset.sum_le_sum fun z hz => hF z (h.mem_toFinset.mp hz)
    _ = _ := by simp

lemma exists_positive_block (ν : Measure U) [IsFiniteMeasure ν]
    (ψ : U × Z → C) (hψ : Measurable ψ) (B : Set C) (hB : B.Countable)
    (F : U × Z → ℝ) (hF : Measurable F) (hF0 : ∀ z, 0 ≤ F z)
    (c : ℝ) (hc : 0 ≤ c) (hFc : ∀ z, F z ≤ c)
    (hcover : ∀ᵐ a ∂ν, ∀ z, (a,z) ∈ S → ψ (a,z) ∈ B)
    (hfinite : ∀ b ∈ B, ∃ N : ℕ, ∀ᵐ a ∂ν,
      ∃ h : {z | (a,z) ∈ S ∧ ψ (a,z) = b}.Finite, h.toFinset.card ≤ N)
    (hn : ¬ (∀ᵐ a ∂ν, ∀ z, (a,z) ∈ S → F (a,z) = 0)) :
    ∃ b ∈ B, 0 < ∫ a, (E.restrictLevel ψ hψ b).fibreSum F a ∂ν := by
  classical
  let : Countable B := hB.to_subtype
  by_contra hh
  have hz (b : B) : ∀ᵐ a ∂ν, (E.restrictLevel ψ hψ b.val).fibreSum F a = 0 := by
    obtain ⟨N,hN⟩ := hfinite b.val b.property
    have h0 : ∀ a, 0 ≤ (E.restrictLevel ψ hψ b.val).fibreSum F a :=
      (E.restrictLevel ψ hψ b.val).fibreSum_nonneg F hF0
    have hi : Integrable ((E.restrictLevel ψ hψ b.val).fibreSum F) ν := by
      apply Integrable.mono' (integrable_const ((N : ℝ) * c))
        ((E.restrictLevel ψ hψ b.val).measurable_fibreSum F hF).aestronglyMeasurable
      filter_upwards [hN] with a ha
      obtain ⟨h,hcard⟩ := ha
      rw [Real.norm_eq_abs,abs_of_nonneg (h0 a)]
      exact ((E.restrictLevel ψ hψ b.val).fibreSum_le_card_mul F c a h
        (fun z _ => hFc (a,z))).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hc)
    have he : ∫ a, (E.restrictLevel ψ hψ b.val).fibreSum F a ∂ν = 0 := by
      apply le_antisymm
      · exact not_lt.mp (fun h => hh ⟨b.val,b.property,h⟩)
      · exact integral_nonneg h0
    exact (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall h0) hi).mp he
  apply hn
  have hf (b : B) : ∀ᵐ a ∂ν, {z | (a,z) ∈ S ∧ ψ (a,z) = b.val}.Finite := by
    obtain ⟨N,hN⟩ := hfinite b.val b.property
    exact hN.mono fun a ha => ha.choose
  filter_upwards [hcover,ae_all_iff.mpr hz,ae_all_iff.mpr hf] with a ha hz hf
  intro z hzS
  let b : B := ⟨ψ (a,z),ha z hzS⟩
  exact ((E.restrictLevel ψ hψ b.val).fibreSum_eq_zero_iff F hF0 a (hf b)).mp
    (hz b) z ⟨hzS,rfl⟩

end BorelFibreEnumeration

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

structure PositiveRawBlock (S : Set (RawLabel M)) (E : BorelFibreEnumeration S)
    (f : Arr I M.Y 0 → ℂ) where
  ψ : RawLabel M → LabelOrbitVector
  measurable_ψ : Measurable ψ
  a₀ : Arr I M.U 0
  b : LabelOrbitVector
  finite_block : {g : localProjectiveGroup (M.ownKernel 0) S a₀ |
    localGroupBlock (M.ownKernel 0) S ψ a₀ g = b}.Finite
  G : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a₀
  block_shift : ∀ g, localGroupBlock (M.ownKernel 0) S ψ a₀ (G g) =
    labelShiftSecond.symm (localGroupBlock (M.ownKernel 0) S ψ a₀ g)
  identifications : ∀ᵐ a ∂M.parameterLaw 0,
    ∃ J : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a,
      ∀ g, localGroupBlock (M.ownKernel 0) S ψ a (J g) = localGroupBlock (M.ownKernel 0) S ψ a₀ g
  time_labels : ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
    ψ (rawLabelTime M (a,q)) = labelShiftSecond (ψ (a,q))
  positive : 0 < ∫ a, (E.restrictLevel ψ measurable_ψ b).fibreSum
    (absoluteCoefficient (M.ownKernel 0) f) a ∂M.parameterLaw 0

variable (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)

include hM hk hL hm hind hS Eπ Eσ hst in
lemma exists_positive_raw_block (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hpos : (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) ≠ 0) :
    Nonempty (PositiveRawBlock M S E (f i)) := by
  obtain ⟨ψ,a₀,hψ,hBc,hcount,hall,hfinite,hJ,⟨G,hG⟩,hfib,hcover,ht⟩ :=
    exists_raw_finite_blocks M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  have he := localGraph_group_equiv M Λ hm S hS i
  have hfin : ∀ b ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ, ∃ N : ℕ,
      ∀ᵐ a ∂M.parameterLaw 0,
      ∃ h : {q | (a,q) ∈ S ∧ ψ (a,q) = b}.Finite, h.toFinset.card ≤ N := by
    intro b hb
    have hB := (hfinite ⟨b,hb⟩).1
    refine ⟨hB.toFinset.card,?_⟩
    filter_upwards [he,hJ] with a he hJ
    obtain ⟨e,he⟩ := he
    obtain ⟨J,hJ⟩ := hJ
    exact localBlock_card_le (M.ownKernel 0) S ψ a₀ a b hB J hJ e he
  have hh := E.exists_positive_block (M.parameterLaw 0) ψ hψ
    (positiveLevels (E.measure (M.parameterLaw 0)) ψ) hBc
    (absoluteCoefficient (M.ownKernel 0) (f i))
    (measurable_absoluteCoefficient (M.ownKernel 0) (f i) (hf i))
    (absoluteCoefficient_nonneg (M.ownKernel 0) (f i)) 1 zero_le_one
    (fun z => absoluteCoefficient_le _ _ 1 z (Filter.Eventually.of_forall (hb i)))
    hcover hfin (raw_correlation_forces_coefficient M Λ hM hk hL hm S hS i f hf hb hpos)
  obtain ⟨b,hb,hpos⟩ := hh
  exact ⟨⟨ψ,hψ,a₀,b,(hfinite ⟨b,hb⟩).1,G,hG,hJ,ht,hpos⟩⟩
end ArrayObjects.Object.Rolled

section
open MeasureTheory Set
variable {U Z C : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    {S : Set (U × Z)} (E : BorelFibreEnumeration S)
    (ψ : U × Z → C) (hψ : Measurable ψ)

def fibreLevelEquiv (a b : U) (e : {z // (a,z) ∈ S} ≃ {z // (b,z) ∈ S})
    (D : C ≃ C) (he : ∀ z, ψ (b,(e z).val) = D (ψ (a,z.val))) (c : C) :
    {z // (a,z) ∈ S ∧ ψ (a,z) = D.symm c} ≃ {z // (b,z) ∈ S ∧ ψ (b,z) = c} :=
  Equiv.ofBijective (fun z => ⟨(e ⟨z.val,z.property.1⟩).val,⟨(e _).property,by
    rw [he,z.property.2,D.apply_symm_apply]⟩⟩) (by
    constructor
    · intro z w h
      have hv : (e ⟨z.val,z.property.1⟩).val = (e ⟨w.val,w.property.1⟩).val := congrArg (fun w : {z // (b,z) ∈ S ∧ ψ (b,z) = c} => w.val) h
      have hh : e ⟨z.val,z.property.1⟩ = e ⟨w.val,w.property.1⟩ := Subtype.ext hv
      have h' := e.injective hh
      exact Subtype.ext (Subtype.mk.inj h')
    · intro w
      let z := e.symm ⟨w.val,w.property.1⟩
      have hz : ψ (a,z.val) = D.symm c := by
        apply D.injective
        rw [D.apply_symm_apply,←he,e.apply_symm_apply]
        exact w.property.2
      refine ⟨⟨z.val,⟨z.property,hz⟩⟩,?_⟩
      apply Subtype.ext
      have hv : (e z).val = w.val := congrArg Subtype.val (e.apply_symm_apply ⟨w.val,w.property.1⟩)
      exact hv)

lemma fibreLevelSum_transport (a b : U) (e : {z // (a,z) ∈ S} ≃ {z // (b,z) ∈ S})
    (D : C ≃ C) (he : ∀ z, ψ (b,(e z).val) = D (ψ (a,z.val))) (c : C)
    (F G : U × Z → ℝ) (hFG : ∀ z, F (a,z.val) = G (b,(e z).val)) :
    (E.restrictLevel ψ hψ (D.symm c)).fibreSum F a =
      (E.restrictLevel ψ hψ c).fibreSum G b := by
  apply BorelFibreEnumeration.fibreSum_transport _ _ a b (fibreLevelEquiv ψ a b e D he c)
  intro z
  exact hFG ⟨z.val,z.property.1⟩
end

section
open MeasureTheory Set Filter
open scoped Topology
variable {U Z C : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    {S : Set (U × Z)} (E : BorelFibreEnumeration S)
    (ψ : U × Z → C) (hψ : Measurable ψ) (D : C ≃ C) (b : C)
    (F : ℕ → U × Z → ℝ)
def movingFibreSum (n : ℕ) (a : U) : ℝ :=
  (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum (F n) a

lemma measurable_movingFibreSum (hm : ∀ n, Measurable (F n)) (n : ℕ) :
    Measurable (movingFibreSum E ψ hψ D b F n) :=
  (E.restrictLevel ψ hψ _).measurable_fibreSum _ (hm n)

variable (ν : Measure U) (T : U → U) (hT : MeasurePreserving T ν ν)
lemma movingFibreSum_step
    (h : ∀ᵐ a ∂ν, ∃ e : {z // (a,z) ∈ S} ≃ {z // (T a,z) ∈ S},
      (∀ z, ψ (T a,(e z).val) = D (ψ (a,z.val))) ∧
      (∀ n z, F (n+1) (a,z.val) = F n (T a,(e z).val))) (n : ℕ) :
    movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T := by
  filter_upwards [h] with a ha
  obtain ⟨e,he,hF⟩ := ha
  change (E.restrictLevel ψ hψ _).fibreSum _ a = (E.restrictLevel ψ hψ _).fibreSum _ (T a)
  rw [Function.iterate_succ_apply']
  exact fibreLevelSum_transport E ψ hψ a (T a) e D he _ _ _ (hF n)

include hT in
lemma movingFibreSum_iterate
    (hstep : ∀ n, movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T) (n : ℕ) :
    movingFibreSum E ψ hψ D b F n =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F 0) ∘ T^[n] := by
  induction n with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ n ih =>
    filter_upwards [hstep n,hT.quasiMeasurePreserving.ae_eq_comp ih] with a h1 h2
    exact h1.trans h2

include hT in
lemma movingFibreSum_integral [IsFiniteMeasure ν]
    (hm : ∀ n, Measurable (F n))
    (hstep : ∀ n, movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T) (n : ℕ) :
    ∫ a, movingFibreSum E ψ hψ D b F n a ∂ν =
      ∫ a, movingFibreSum E ψ hψ D b F 0 a ∂ν := by
  rw [integral_congr_ae (movingFibreSum_iterate E ψ hψ D b F ν T hT hstep n)]
  have hmap := integral_map (hT.iterate n).measurable.aemeasurable
    ((measurable_movingFibreSum E ψ hψ D b F hm 0).aestronglyMeasurable (μ := ν.map (T^[n])))
  rw [(hT.iterate n).map_eq] at hmap
  exact hmap.symm

include hT in
lemma movingFibreSum_bound
    (hstep : ∀ n, movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T) (c : ℝ)
    (hb : ∀ᵐ a ∂ν, 0 ≤ movingFibreSum E ψ hψ D b F 0 a ∧
      movingFibreSum E ψ hψ D b F 0 a ≤ c) (n : ℕ) :
    ∀ᵐ a ∂ν, 0 ≤ movingFibreSum E ψ hψ D b F n a ∧ movingFibreSum E ψ hψ D b F n a ≤ c := by
  filter_upwards [movingFibreSum_iterate E ψ hψ D b F ν T hT hstep n,
    (hT.iterate n).quasiMeasurePreserving.ae hb] with a he ha
  rwa [he]
end

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
lemma absoluteCoefficient_transport (F : U → U) (E : Y ≃ᵐ Y)
    (f : Y → ℂ) (q : HilbertCode κ) (hq : q.IsUnimodular)
    (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    absoluteCoefficient κ f (F q.base,HilbertCode.transport F E q) =
      absoluteCoefficient κ (f ∘ E) (q.base,q) := by
  obtain ⟨d,hd,hr⟩ := HilbertCode.transport_representative F E q hq hE
  have ht := HilbertCode.circleRep_ae (HilbertCode.transport F E q)
    (HilbertCode.transport_unimodular F E q)
  have hs := (MeasurePreserving.symm E hE).quasiMeasurePreserving.ae_eq_comp (HilbertCode.circleRep_ae q hq)
  have he : (fun y => (HilbertCode.circleRep (HilbertCode.transport F E q) y : ℂ)) =ᵐ[κ (F q.base)]
      fun y => d * (HilbertCode.circleRep q (E.symm y) : ℂ) := by
    filter_upwards [ht,hr,hs] with y h1 h2 h3
    exact h1.trans (h2.trans (congrArg (d * ·) h3.symm))
  rw [absoluteCoefficient,norm_integral_mul_conj_of_phase _ _ _ d hd he]
  rw [←hE.integral_comp E.measurableEmbedding (fun y => f y * conj (HilbertCode.circleRep q (E.symm y) : ℂ))]
  simp only [E.symm_apply_apply,absoluteCoefficient,Function.comp_apply]
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [retained14 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (i : I) (E : BorelFibreEnumeration S)
    (ψ : RawLabel M → LabelOrbitVector) (hψ : Measurable ψ)
    (ht : ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
      ψ (rawLabelTime M (a,q)) = labelShiftSecond (ψ (a,q)))

include hL hm hS ht i in
include retained14 in
lemma raw_moving_sum_step (b : LabelOrbitVector) (f : Arr I M.Y 0 → ℂ) (n : ℕ) :
    movingFibreSum E ψ hψ labelShiftSecond.toEquiv b
      (fun n => absoluteCoefficient (M.ownKernel 0) (f ∘ (amap M.timeY 0)^[n])) (n+1) =ᵐ[M.parameterLaw 0]
      (movingFibreSum E ψ hψ labelShiftSecond.toEquiv b
        (fun n => absoluteCoefficient (M.ownKernel 0) (f ∘ (amap M.timeY 0)^[n])) n) ∘ amap M.timeU 0 := by
  let _ := retained14
  apply movingFibreSum_step
  filter_upwards [localGraph_time_equiv M Λ i hL hm S hS,
    localGraph_code_properties M Λ i S hS, M.ownKernel_time_preserving 0,ht] with a he hq htime ht
  obtain ⟨e,he⟩ := he
  refine ⟨e,?_,?_⟩
  · intro q
    rw [he]
    exact ht q q.property
  · intro n q
    rw [he]
    obtain ⟨hb,_,hu⟩ := hq q q.property
    have H := absoluteCoefficient_transport (M.ownKernel 0) (amap M.timeU 0)
      (amapEquiv M.timeY 0) (f ∘ (amap M.timeY 0)^[n]) q.val hu (by rw [hb]; exact htime)
    rw [hb] at H
    rw [H]
    congr 1
end ArrayObjects.Object.Rolled

section
open MeasureTheory Set
variable {U Z C H : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    {S : Set (U × Z)} (E : BorelFibreEnumeration S)
    (ψ : U × Z → C) (hψ : Measurable ψ) (D : C ≃ C)
    (τ : H → C) (G : H ≃ H)
    (hG : ∀ h, τ (G h) = D.symm (τ h))
include hG in
omit [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma block_iterate (n : ℕ) (l : H) :
    τ ((G^[n]) l) = (D.symm^[n]) (τ l) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',hG,ih,Function.iterate_succ_apply']

def movingBlockCodeEquiv (a : U) (e : H ≃ {z // (a,z) ∈ S})
    (he : ∀ l, ψ (a,(e l).val) = τ l) (b : C) (n : ℕ) :
    {l // τ l = b} ≃ {z // (a,z) ∈ S ∧ ψ (a,z) = (D.symm^[n]) b} :=
  (Equiv.subtypeEquiv (p := fun l => τ l = b)
    (q := fun z : {z // (a,z) ∈ S} => ψ (a,z.val) = (D.symm^[n]) b) ((G^n).trans e) (by
    intro l
    change τ l = b ↔ ψ (a,(e ((G^n) l)).val) = (D.symm^[n]) b
    rw [he,Equiv.Perm.coe_pow,block_iterate D τ G hG]
    exact (Function.Injective.iterate D.symm.injective n).eq_iff.symm)).trans
      { toFun := fun z => ⟨z.val.val,z.val.property,z.property⟩
        invFun := fun z => ⟨⟨z.val,z.property.1⟩,z.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

include hG in
lemma movingBlock_sum (a : U) (e : H ≃ {z // (a,z) ∈ S})
    (he : ∀ l, ψ (a,(e l).val) = τ l) (b : C)
    (hb : {l | τ l = b}.Finite) (n : ℕ) (F : U × Z → ℝ) :
    (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum F a =
      ∑ l ∈ hb.toFinset, F (a,(e ((G^[n]) l)).val) := by
  classical
  let : Fintype {l : H // τ l = b} := hb.fintype
  rw [(E.restrictLevel ψ hψ _).fibreSum_eq_sum_equiv a
    (movingBlockCodeEquiv ψ D τ G hG a e he b n) F]
  change (∑ k : {l : H // τ l = b}, F (a,(e ((G^[n]) k.val)).val)) = _
  exact (Finset.sum_subtype hb.toFinset (fun l => hb.mem_toFinset (a := l))
    (fun l => F (a,(e ((G^[n]) l)).val))).symm
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {Y I : Type*} [MeasurableSpace Y] [Fintype I] [DecidableEq I]
lemma exactCircleTuples_mean_zero (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (f : I → MeasurableCircle Y) (hf : f ∈ exactCircleTuples μ)
    (i : I) (hi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) ≠ 1) :
    ∫ y, (f i y : ℂ) ∂ν i = 0 := by
  have hfm (j : I) : Measurable (fun y : Y => (f j y : ℂ)) :=
    measurable_subtype_coe.comp (measurableCircle_measurable Y (f j))
  have hpm (j : I) : Measurable (fun y : I → Y => (f j (y j) : ℂ)) :=
    (hfm j).comp (measurable_pi_apply j)
  have hpn (j : I) : ∀ᵐ y ∂μ, ‖(f j (y j) : ℂ)‖ = 1 :=
    Filter.Eventually.of_forall fun _ => Circle.norm_coe _
  have hpi (j : I) : iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => (f t (y t) : ℂ)) μ :=
    (hind j).comp (fun t y => (f t y : ℂ)) (fun t => hfm t)
  obtain ⟨c,hc⟩ := hf
  have hc' : ∀ᵐ y ∂μ, ∏ j, (f j (y j) : ℂ) = (c : ℂ) := by
    filter_upwards [hc] with y hy
    exact (map_prod Circle.coeHom _ _).symm.trans (congrArg (fun a : Circle => (a : ℂ)) hy)
  have hx := exact_tuple_dichotomy hk (fun j (y : I → Y) => (f j (y j) : ℂ))
    (fun j => (hpm j).aestronglyMeasurable) hpn hpi (c : ℂ) (Circle.norm_coe c) hc'
  rcases hx with hz | he
  · rw [←(hm i).map_eq,integral_map (hm i).aemeasurable (hfm i).aestronglyMeasurable]
    exact hz i
  · exfalso
    apply hi
    let a : Circle := ⟨∫ y, (f i (y i) : ℂ) ∂μ,mem_sphere_zero_iff_norm.mpr (he i).2⟩
    have hj : ∀ᵐ y ∂μ, f i (y i) = a :=
      (he i).1.mono fun _ h => Circle.coe_injective h
    have hj' : (f i : Y → Circle) =ᵐ[ν i] fun _ => a := by
      rw [←(hm i).map_eq]
      apply (ae_map_iff (hm i).measurable.aemeasurable
        (measurableSet_eq_fun (measurableCircle_measurable Y (f i)) measurable_const)).mpr
      exact hj
    rw [←projectiveCircle_one (ν i),projectiveCircle_eq_iff]
    exact ⟨a,by simpa only [mul_one] using hj'⟩

lemma exactProjectiveSlot_mean_zero (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ) (i : I)
    (g : ProjectiveCircle (ν i)) (hg : g ∈ (exactProjectiveSlot μ ν i).range) (hne : g ≠ 1) :
    ∫ y, projectiveCharacter (ν i) g y ∂ν i = 0 := by
  obtain ⟨a,ha⟩ := hg
  obtain ⟨f,hf,hfa⟩ := a.property
  have hfi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) = g := by
    change tupleProjectivize ν f i = g
    rw [hfa]
    exact ha
  have hz := exactCircleTuples_mean_zero hk μ ν hm hind f hf i (fun h => hne (hfi.symm.trans h))
  have he : projectiveCircle (ν i) (projectiveRep (ν i) g) (measurableCircle_measurable Y _) =
      projectiveCircle (ν i) (f i) (measurableCircle_measurable Y _) :=
    (projectiveRep_class (ν i) g).trans hfi.symm
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff (ν i) _ _ _ _).mp he
  have hc' : projectiveCharacter (ν i) g =ᵐ[ν i] fun y => (c : ℂ) * (f i y : ℂ) :=
    hc.mono fun _ h => congrArg (fun c : Circle => (c : ℂ)) h
  rw [integral_congr_ae hc',integral_const_mul,hz,mul_zero]
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))
lemma localProjectiveCharacters (hk : 3 ≤ Fintype.card I) (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    ProjectiveCharacters (κ (u p i))
      (fun g : Additive (localProjectiveGroup κ S (u p i)) =>
        projectiveCharacter (κ (u p i)) g.toMul.val) := by
  apply projectiveCharacters_of_zero_mean
  intro g hg
  apply exactProjectiveSlot_mean_zero hk (Λ p) (fun j => κ (u p j)) hm hind i g.val
  · rw [←localProjectiveGroup_eq κ Λ u S p i hm hS]
    exact g.property
  · intro he
    apply hg
    exact Subtype.ext he
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
include hk hm hind hS in
lemma localGraph_projectiveCharacters (i : I) :
    ∀ᵐ a ∂M.parameterLaw 0, ProjectiveCharacters (M.ownKernel 0 a)
      (fun g : Additive (localProjectiveGroup (M.ownKernel 0) S a) =>
        projectiveCharacter (M.ownKernel 0 a) g.toMul.val) := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1, ProjectiveCharacters (M.ownKernel 0 (tupleParameter M p i))
      (fun g : Additive (localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p i)) =>
        projectiveCharacter (M.ownKernel 0 (tupleParameter M p i)) g.toMul.val) := by
    filter_upwards [hS] with p hp
    exact localProjectiveCharacters (M.ownKernel 0) Λ (tupleParameter M) S hk p i (hm p) (hind p) (hp i)
  have hd := ae_map_descent (P := fun a => ProjectiveCharacters (M.ownKernel 0 a)
    (fun g : Additive (localProjectiveGroup (M.ownKernel 0) S a) =>
      projectiveCharacter (M.ownKernel 0 a) g.toMul.val))
    (M.parameterLaw 1) (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd
end ArrayObjects.Object.Rolled

namespace ProjectiveCharacters
open MeasureTheory
variable {Y L K : Type*} [MeasurableSpace Y] [AddCommGroup L] [AddCommGroup K]
    {η : Measure Y} {χ : L → Y → ℂ}
lemma reindex (hχ : ProjectiveCharacters η χ) (e : K ≃+ L) :
    ProjectiveCharacters η (fun k => χ (e k)) where
  measurable k := hχ.measurable _
  modulus k := hχ.modulus _
  zero := by simpa only [map_zero] using hχ.zero
  mul k l := by simpa only [map_add] using hχ.mul (e k) (e l)
  mean k hk := hχ.mean (e k) (by intro h; exact hk (e.injective (h.trans (map_zero e).symm)))
end ProjectiveCharacters

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ComplexConjugate
variable {X Y L A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup L]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ a b z, t (a+b) z = t b (t a z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (a : X → A) (ha : Measurable a) (v : A → ℂ)
    (hcenter : ∫ z, v (a z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => a (t m z)) n / n)
      atTop (𝓝 0))
    {χ : L → Y → ℂ} (hχ : ProjectiveCharacters η χ)
    (G : L ≃ₗ[ℤ] L)

include hx ht htadd hmix ha hcenter hH hχ in
lemma finite_block_cancellation (B : Finset L) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
      ∑ l ∈ B, ‖∫ y, v (a (t m (x y))) * conj (χ ((G ^ m) l) y) ∂η‖)
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum B (fun l _ =>
    orbit_cancellation x hx t ht htadd hmix a ha v hcenter hH hχ G l)
  simp only [Finset.sum_const_zero] at h
  convert h using 1
  funext N
  rw [←Finset.mul_sum,Finset.sum_comm]

variable {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]

lemma constant_integral_zero_of_bounded_cesaro (s : ℕ → U → ℝ) (C c : ℝ)
    (hC : 0 ≤ C) (hs : ∀ n, AEStronglyMeasurable (s n) ν)
    (hb : ∀ n, ∀ᵐ u ∂ν, 0 ≤ s n u ∧ s n u ≤ C)
    (hc : ∀ n, ∫ u, s n u ∂ν = c)
    (hlim : ∀ᵐ u ∂ν, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, s m u)
      atTop (𝓝 0)) : c = 0 := by
  let F : ℕ → U → ℝ := fun N u => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, s m u
  have hsi (n : ℕ) : Integrable (s n) ν :=
    Integrable.mono' (integrable_const C) (hs n) ((hb n).mono fun u hu => by
      rw [Real.norm_eq_abs,abs_of_nonneg hu.1]
      exact hu.2)
  have hfm (N : ℕ) : AEStronglyMeasurable (F N) ν :=
    (Finset.aestronglyMeasurable_fun_sum _ (fun m _ => hs m)).const_mul _
  have hfb (N : ℕ) : ∀ᵐ u ∂ν, ‖F N u‖ ≤ C := by
    filter_upwards [ae_all_iff.mpr hb] with u hu
    have hn : 0 ≤ F N u := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun m _ => (hu m).1)
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    have hle : ∑ m ∈ Finset.range N, s m u ≤ N * C := by
      calc
        _ ≤ ∑ _m ∈ Finset.range N, C := Finset.sum_le_sum fun m _ => (hu m).2
        _ = _ := by simp
    by_cases hN : N=0
    · subst N; simpa [F] using hC
    · unfold F
      calc
        _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * C) := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = C := by rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN),one_mul]
  have hfint (N : ℕ) (hN : N ≠ 0) : ∫ u, F N u ∂ν = c := by
    simp only [F,integral_const_mul,integral_finsetSum _ (fun m _ => hsi m),hc,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN),one_mul]
  have hd := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => C)
    hfm (integrable_const C) hfb hlim
  have he : (fun N : ℕ => ∫ u, F N u ∂ν) =ᶠ[atTop] fun _ => c := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hfint N (by omega)
  have hd' : Tendsto (fun _ : ℕ => c) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using hd.congr' he
  exact tendsto_nhds_unique tendsto_const_nhds hd'
end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ComplexConjugate
variable {U Y X A C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] [MeasurableSpace X]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    (κ : Kernel U Y) [IsMarkovKernel κ] (S : Set (U × HilbertCode κ))
    (E : BorelFibreEnumeration S) (ψ : U × HilbertCode κ → C) (hψ : Measurable ψ)
    (D : C ≃ C) (a₀ a : U) (b : C)
    (hb : {g : localProjectiveGroup κ S a₀ | localGroupBlock κ S ψ a₀ g = b}.Finite)
    (G : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a₀)
    (hG : ∀ g, localGroupBlock κ S ψ a₀ (G g) = D.symm (localGroupBlock κ S ψ a₀ g))
    (J : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a)
    (hJ : ∀ g, localGroupBlock κ S ψ a (J g) = localGroupBlock κ S ψ a₀ g)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (hχ : ProjectiveCharacters (κ a)
      (fun g : Additive (localProjectiveGroup κ S a) => projectiveCharacter (κ a) g.toMul.val))
    {μ : Measure X} [IsProbabilityMeasure μ]
    (x : Y → X) (hx : MeasurePreserving x (κ a) μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ c d z, t (c+d) z = t d (t c z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α (t m z)) n / n)
      atTop (𝓝 0))
    (R : Y → Y) (f : Y → ℂ) (hf : ∀ n y, f ((R^[n]) y) = v (α (t n (x y))))
include hb hG hJ he hχ hx ht htadd hmix hα hcenter hH hf in
lemma local_moving_cancellation :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum
        (absoluteCoefficient κ (f ∘ R^[n])) a) atTop (𝓝 0) := by
  classical
  let H := Additive (localProjectiveGroup κ S a₀)
  let G' : H ≃ₗ[ℤ] H := G.toAdditive.toIntLinearEquiv
  let τ : H → C := fun g => localGroupBlock κ S ψ a₀ g.toMul
  have hb' : {g : H | τ g = b}.Finite := hb
  let e' : H ≃ {q // (a,q) ∈ S} :=
    { toFun := fun g => e.symm (J g.toMul)
      invFun := fun q => Additive.ofMul (J.symm (e q))
      left_inv := by intro g; simp
      right_inv := by intro q; simp }
  have he' (g : H) : ψ (a,(e' g).val) = τ g := by
    dsimp only [e',Equiv.coe_fn_mk]
    rw [←localGroupBlock_equiv κ S ψ a e he,e.apply_symm_apply,hJ]
  have hG' (g : H) : τ (G'.toEquiv g) = D.symm (τ g) := hG _
  have hs (n : ℕ) :
      (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum
        (absoluteCoefficient κ (f ∘ R^[n])) a =
      ∑ l ∈ hb'.toFinset, ‖∫ y, v (α (t n (x y))) *
        conj (projectiveCharacter (κ a) (J ((G'^n) l).toMul).val y) ∂κ a‖ := by
    rw [movingBlock_sum E ψ hψ D τ G'.toEquiv hG' a e' he' b hb' n]
    apply Finset.sum_congr rfl
    intro l hl
    rw [absoluteCoefficient_projective]
    have hq : HilbertCode.projective a (e' ((G'.toEquiv^[n]) l)).val =
        (J ((G'^n) l).toMul).val := by
      rw [←he]
      dsimp only [e',Equiv.coe_fn_mk]
      rw [e.apply_symm_apply]
      rw [LinearEquiv.coe_pow]
      rfl
    rw [hq]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only [Function.comp_apply]
      rw [hf]
  have hc := finite_block_cancellation x hx t ht htadd hmix α hα v hcenter hH
    (hχ.reindex J.toAdditive) G' hb'.toFinset
  simp only [hs]
  convert hc using 1
  rfl
end

namespace ArrayObjects.Object
open MeasureTheory
universe u
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma selected_time_iterate (n : ℕ) (y : Arr I M.Y 0) :
    M.x (zeroEquiv I M.Y ((amap M.timeY 0)^[n] y)) =
      (T^[n]) (M.x (zeroEquiv I M.Y y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have h : M.x (M.timeY (zeroEquiv I M.Y ((amap M.timeY 0)^[n] y))) =
      T (M.x (zeroEquiv I M.Y ((amap M.timeY 0)^[n] y))) := congrFun M.time_x _
    exact h.trans (congrArg T ih)
end ArrayObjects.Object

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

section RawCorrelation
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : M.localLaw.map M.x = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hM hk hL hm hind hS E Eπ Eσ hst hμ hT hmix hα hcenter hH in
lemma raw_correlation_zero (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
    (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0 := by
  classical
  by_contra hn
  obtain ⟨P⟩ := exists_positive_raw_block M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst i f hf hb hn
  let F := fun n => absoluteCoefficient (M.ownKernel 0) (f i ∘ (amap M.timeY 0)^[n])
  let bsum := movingFibreSum E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F
  have hFm (n : ℕ) : Measurable (F n) := measurable_absoluteCoefficient _ _
    ((hf i).comp ((measurable_amap M.timeY.measurable 0).iterate n))
  have hstep (n : ℕ) : bsum (n+1) =ᵐ[M.parameterLaw 0] (bsum n) ∘ amap M.timeU 0 :=
    raw_moving_sum_step M Λ hL hm S hS i E P.ψ P.measurable_ψ P.time_labels P.b (f i) n
  have he := localGraph_group_equiv M Λ hm S hS i
  let C : ℝ := P.finite_block.toFinset.card
  have hbound0 : ∀ᵐ a ∂M.parameterLaw 0, 0 ≤ bsum 0 a ∧ bsum 0 a ≤ C := by
    filter_upwards [he,P.identifications] with a ha hJ
    obtain ⟨e,he⟩ := ha
    obtain ⟨J,hJ⟩ := hJ
    obtain ⟨hfin,hcard⟩ := localBlock_card_le (M.ownKernel 0) S P.ψ P.a₀ a P.b P.finite_block J hJ e he
    constructor
    · exact (E.restrictLevel P.ψ P.measurable_ψ P.b).fibreSum_nonneg _
        (absoluteCoefficient_nonneg _ _) a
    · have h := (E.restrictLevel P.ψ P.measurable_ψ P.b).fibreSum_le_card_mul
        (F 0) 1 a hfin (fun q _ => absoluteCoefficient_le _ _ 1 (a,q)
          (Eventually.of_forall (hb i)))
      exact h.trans (by simpa only [mul_one] using (Nat.cast_le (α := ℝ)).mpr hcard)
  have hzero := constant_integral_zero_of_bounded_cesaro (M.parameterLaw 0) bsum C
    (∫ a, bsum 0 a ∂M.parameterLaw 0) (Nat.cast_nonneg _) (fun n =>
      (measurable_movingFibreSum E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F hFm n).aestronglyMeasurable)
    (movingFibreSum_bound E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F
      (M.parameterLaw 0) (amap M.timeU 0) (M.parameterLaw_invariant 0) hstep C hbound0)
    (movingFibreSum_integral E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F
      (M.parameterLaw 0) (amap M.timeU 0) (M.parameterLaw_invariant 0) hFm hstep) ?_
  · exact (ne_of_gt P.positive) hzero
  · filter_upwards [he,P.identifications,localGraph_projectiveCharacters M Λ hk hm hind S hS i,
      M.ownKernel_zero_image] with a ha hJ hχ hxa
    obtain ⟨e,he⟩ := ha
    obtain ⟨J,hJ⟩ := hJ
    have hx : MeasurePreserving (M.x ∘ zeroEquiv I M.Y) (M.ownKernel 0 a) μ :=
      ⟨M.measurable_x.comp (zeroEquiv I M.Y).measurable,hxa.trans hμ⟩
    apply local_moving_cancellation (M.ownKernel 0) S E P.ψ P.measurable_ψ
      labelShiftSecond.toEquiv P.a₀ a P.b P.finite_block P.G P.block_shift J hJ e he hχ
      (M.x ∘ zeroEquiv I M.Y) hx (fun n => T^[n]) (fun n => hT.iterate n)
      (fun c d z => by rw [Nat.add_comm,Function.iterate_add_apply]) hmix α hα v hcenter hH
      (amap M.timeY 0) (f i)
    intro n y
    rw [hi,M.selected_time_iterate]
    rfl
end RawCorrelation
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : M.localLaw.map M.x = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hM hk hμ hT hmix hα hcenter hH in
lemma saturated_correlation_zero (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
    (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0 := by
  classical
  obtain ⟨Λ,hΛ,hL,hm,hind⟩ := raw_good_tuple_kernel M (by omega)
  let := hΛ
  obtain ⟨S,hSm,hSb,hSs,hS⟩ := exists_commonLocalLineGraph M hM hk Λ hL hm hind
  obtain ⟨E⟩ := separated_family_enumeration (M.ownKernel 0) S hSm (fun u q hq => (hSb u q hq).1) hSs
  obtain ⟨Eπ⟩ := exactCode_enumeration (M.ownKernel 0) Λ (tupleParameter M)
    (measurable_tupleParameter M) hk hm hind
  obtain ⟨Eσ⟩ := exactSquare_enumeration (M.ownKernel 0) Λ (tupleParameter M)
    (fun e a => plane 1 0 a e) (fun e s => plane 1 (Fin.last 1) s e)
    (measurable_tupleParameter M) (Measurable.of_eval fun _ => measurable_plane _ _ _)
    (Measurable.of_eval fun _ => measurable_plane _ _ _) hk hm hind
  have : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t,ht⟩ := exists_ne i
  exact raw_correlation_zero M Λ hM hk hL hm hind S hS E Eπ Eσ i t ht.symm
    hμ hT hmix α hα v hcenter hH i f hf hb hi
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
