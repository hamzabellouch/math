import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import OAI.Analysis.FactorGeneration.SpectralTruncation
import OAI.Analysis.FactorGeneration.TraceHilbert

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/
section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}
  {T : StarSubalgebra ℂ (K →L[ℂ] K)}

/-- The carrier equipped with the subspace topology from ambient WOT. -/
abbrev WOTCarrier (S : StarSubalgebra ℂ (H →L[ℂ] H)) :=
  {a : H →WOT[ℂ] H // a.toCLM ∈ S}

/-- A homomorphism viewed on the WOT carrier, with ambient WOT codomain. -/
def wotMap (φ : S →⋆ₐ[ℂ] T) (a : WOTCarrier S) : K →WOT[ℂ] K :=
  ContinuousLinearMapWOT.ofCLM (φ ⟨a.val.toCLM, a.property⟩).val

/-- Ambient concrete inverse image, contained in S. -/
def concretePreimage (φ : S →⋆ₐ[ℂ] T)
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (Q.comap (T.subtype.comp φ)).map S.subtype

theorem concretePreimage_le (φ : S →⋆ₐ[ℂ] T)
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) : concretePreimage φ Q ≤ S := by
  rintro a ⟨b, _, rfl⟩
  exact b.property

theorem mem_concretePreimage (φ : S →⋆ₐ[ℂ] T)
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) (a : S) :
    a.val ∈ concretePreimage φ Q ↔ (φ a).val ∈ Q := by
  constructor
  · rintro ⟨b, hb, hab⟩
    have h : b = a := Subtype.ext hab
    subst b
    exact hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem concretePreimage_wotClosed (φ : S →⋆ₐ[ℂ] T)
    (hS : WOTClosed S) (hφ : Continuous (wotMap φ))
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) (hQ : WOTClosed Q) :
    WOTClosed (concretePreimage φ Q) := by
  have hc := hS.isClosedMap_subtype_val _ (hQ.preimage hφ)
  have heq : Subtype.val '' (wotMap φ ⁻¹' {a : K →WOT[ℂ] K | a.toCLM ∈ Q}) =
      {a : H →WOT[ℂ] H | a.toCLM ∈ concretePreimage φ Q} := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (mem_concretePreimage φ Q ⟨b.val.toCLM, b.property⟩).mpr hb
    · intro ha
      have hs := concretePreimage_le φ Q ha
      exact ⟨⟨a, hs⟩, (mem_concretePreimage φ Q ⟨a.toCLM, hs⟩).mp ha, rfl⟩
  exact (congrArg IsClosed heq).mp hc

/-- WOT continuity suffices for the forward inclusion on generated algebras. -/
theorem map_mem_wstar (φ : S →⋆ₐ[ℂ] T)
    (hS : WOTClosed S) (hφ : Continuous (wotMap φ))
    (s : Set S) (a : S) (ha : a.val ∈ wstar (Subtype.val '' s)) :
    (φ a).val ∈ wstar ((fun b : S => (φ b).val) '' s) := by
  apply (mem_concretePreimage φ _ a).mp
  apply wstar_le (concretePreimage_wotClosed φ hS hφ _ (wstar_closed _)) _ ha
  rintro b ⟨c, hc, rfl⟩
  exact (mem_concretePreimage φ _ c).mpr (subset_wstar _ ⟨c, hc, rfl⟩)

/-- An algebra isomorphism continuous in both directions for the concrete weak operator topologies. -/
structure WOTStarAlgEquiv (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : StarSubalgebra ℂ (K →L[ℂ] K)) where
  toStarAlgEquiv : S ≃⋆ₐ[ℂ] T
  continuous_toFun : Continuous (wotMap toStarAlgEquiv.toStarAlgHom)
  continuous_invFun : Continuous (wotMap toStarAlgEquiv.symm.toStarAlgHom)

namespace WOTStarAlgEquiv
variable (e : WOTStarAlgEquiv S T)

def symm : WOTStarAlgEquiv T S where
  toStarAlgEquiv := e.toStarAlgEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

theorem mem_wstar_iff (hS : WOTClosed S) (hT : WOTClosed T)
    (s : Set S) (a : S) :
    (e.toStarAlgEquiv a).val ∈ wstar ((fun b : S => (e.toStarAlgEquiv b).val) '' s) ↔
      a.val ∈ wstar (Subtype.val '' s) := by
  constructor
  · intro ha
    have hs : ((fun b : T => (e.toStarAlgEquiv.symm b).val) ''
        (e.toStarAlgEquiv '' s)) = Subtype.val '' s := by
      ext b
      simp only [Set.mem_image]
      constructor
      · rintro ⟨c, ⟨d, hd, rfl⟩, rfl⟩
        exact ⟨d, hd, by simp⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨e.toStarAlgEquiv c, ⟨c, hc, rfl⟩, by simp⟩
    have hi : Subtype.val '' (e.toStarAlgEquiv '' s) =
        (fun b : S => (e.toStarAlgEquiv b).val) '' s := Set.image_image _ _ _
    have hr := map_mem_wstar e.toStarAlgEquiv.symm.toStarAlgHom hT
      e.continuous_invFun (e.toStarAlgEquiv '' s) (e.toStarAlgEquiv a) (hi ▸ ha)
    change (e.toStarAlgEquiv.symm (e.toStarAlgEquiv a)).val ∈
      wstar ((fun b : T => (e.toStarAlgEquiv.symm b).val) '' (e.toStarAlgEquiv '' s)) at hr
    simpa only [hs, StarAlgEquiv.symm_apply_apply] using hr
  · exact map_mem_wstar e.toStarAlgEquiv.toStarAlgHom hS e.continuous_toFun s a

theorem wstar_image_eq (hS : WOTClosed S) (hT : WOTClosed T) (s : Set S) :
    wstar ((fun b : S => (e.toStarAlgEquiv b).val) '' s) =
      ((wstar (Subtype.val '' s)).comap S.subtype).map
        (T.subtype.comp e.toStarAlgEquiv.toStarAlgHom) := by
  ext b
  constructor
  · intro hb
    have hbt : b ∈ T := wstar_le hT (by rintro _ ⟨a, _, rfl⟩; exact (e.toStarAlgEquiv a).property) hb
    let a := e.toStarAlgEquiv.symm ⟨b, hbt⟩
    have he : e.toStarAlgEquiv a = ⟨b, hbt⟩ := e.toStarAlgEquiv.apply_symm_apply _
    exact ⟨a, (e.mem_wstar_iff hS hT s a).mp (by simpa only [he] using hb),
      congrArg Subtype.val he⟩
  · rintro ⟨a, ha, rfl⟩
    exact (e.mem_wstar_iff hS hT s a).mpr ha

theorem wstar_singleton_eq (hS : WOTClosed S) (hT : WOTClosed T)
    (a : S) (ha : wstar {a.val} = S) :
    wstar {(e.toStarAlgEquiv a).val} = T := by
  apply le_antisymm (wstar_le hT (by simp))
  intro b hb
  have hg : (e.toStarAlgEquiv (e.toStarAlgEquiv.symm ⟨b, hb⟩)).val ∈
      wstar ((fun c : S => (e.toStarAlgEquiv c).val) '' {a}) :=
    (e.mem_wstar_iff hS hT {a} _).mpr (by simpa only [Set.image_singleton, ha] using
      (e.toStarAlgEquiv.symm ⟨b, hb⟩).property)
  simpa only [Set.image_singleton, StarAlgEquiv.apply_symm_apply] using hg

include e in
theorem singlyGenerated_iff (hS : WOTClosed S) (hT : WOTClosed T) :
    SinglyGenerated S ↔ SinglyGenerated T := by
  constructor
  · rintro ⟨a, ha, hg⟩
    exact ⟨(e.toStarAlgEquiv ⟨a, ha⟩).val, (e.toStarAlgEquiv ⟨a, ha⟩).property,
      e.wstar_singleton_eq hS hT ⟨a, ha⟩ hg⟩
  · rintro ⟨b, hb, hg⟩
    exact ⟨(e.toStarAlgEquiv.symm ⟨b, hb⟩).val, (e.toStarAlgEquiv.symm ⟨b, hb⟩).property,
      e.symm.wstar_singleton_eq hT hS ⟨b, hb⟩ hg⟩

end WOTStarAlgEquiv

/-! Transport of the unchanged finite diffuse factor predicate.
The algebraic fields use the actual star isomorphism; target WOT closedness
is explicit. No trace or separability conclusion is inferred. -/

theorem isII1Factor_of_starAlgEquiv (e : S ≃⋆ₐ[ℂ] T)
    (hS : IsII1Factor S) (hT : WOTClosed T) : IsII1Factor T where
  nonzero := by
    intro h
    have ht : (0 : T) = 1 := Subtype.ext h
    have hs : (0 : S) = 1 := e.injective (by simpa only [map_zero, map_one] using ht)
    exact hS.nonzero (congrArg Subtype.val hs)
  weaklyClosed := hT
  factor := by
    intro x hx
    have hc : ∀ y : S, y * e.symm x = e.symm x * y := by
      intro y
      apply e.injective
      change e (y * e.symm x) = e (e.symm x * y)
      simpa only [map_mul, e.apply_symm_apply] using hx (e y)
    obtain ⟨c, hc⟩ := hS.factor (e.symm x) hc
    refine ⟨c, ?_⟩
    calc x = e (e.symm x) := (e.apply_symm_apply x).symm
         _ = e (algebraMap ℂ S c) := congrArg e hc
         _ = algebraMap ℂ T c := e.toAlgEquiv.commutes c
  finite := by
    intro v hv
    have h : star (e.symm v) * e.symm v = 1 := by
      simpa only [map_mul, map_star, map_one] using congrArg e.symm hv
    have hf := hS.finite (e.symm v) h
    simpa only [map_mul, map_star, map_one, e.apply_symm_apply] using congrArg e hf
  diffuse := by
    intro p hp hp0
    have hsp : IsStarProjection (e.symm p) := hp.map e.symm
    have hsp0 : e.symm p ≠ 0 := by
      intro hz
      apply hp0
      simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
    obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hS.diffuse (e.symm p) hsp hsp0
    refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
    · intro hz
      apply hq0
      apply e.injective
      change e q = e 0
      simpa only [map_zero] using hz
    · intro heq
      apply hqp
      apply e.injective
      change e q = e (e.symm p)
      simpa only [e.apply_symm_apply] using heq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

theorem WOTStarAlgEquiv.isII1Factor_iff (e : WOTStarAlgEquiv S T)
    (hS : WOTClosed S) (hT : WOTClosed T) : IsII1Factor S ↔ IsII1Factor T :=
  ⟨fun h => isII1Factor_of_starAlgEquiv e.toStarAlgEquiv h hT,
   fun h => isII1Factor_of_starAlgEquiv e.toStarAlgEquiv.symm h hS⟩

end

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertImageCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertImageOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertImageStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertImageOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local instance traceHilbertImageClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

def traceFreeHilbertVectorBall (C : ℝ) : Set K :=
  {x | ∃ a : M.toStarSubalgebra, ‖a‖ ≤ C ∧ π a Ω = x}

theorem traceFreeHilbertVectorBall_isClosed (C : ℝ) :
    IsClosed (traceFreeHilbertVectorBall hfactor hdiff hfinite hunit C) := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  choose a ha he using hv
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T,hT,ht⟩ := (traceFreeHilbertWeakBall_isCompact hfactor hdiff hfinite hunit C).ultrafilter_le_nhds
    (ω.map (fun n => ContinuousLinearMapWOT.ofCLM (π (a n)))) (by
      apply le_principal_iff.mpr
      change ∀ᶠ n in (ω : Filter ℕ), ContinuousLinearMapWOT.ofCLM (π (a n)) ∈
        traceFreeHilbertWeakBall hfactor hdiff hfinite hunit C
      exact Eventually.of_forall (fun n => ⟨a n,ha n,rfl⟩))
  obtain ⟨b,hb,rfl⟩ := hT
  refine ⟨b,hb,?_⟩
  apply ext_inner_left ℂ
  intro y
  have hw := (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp ht) Ω y
  change Tendsto (fun n => inner ℂ y (π (a n) Ω)) (ω : Filter ℕ)
    (𝓝 (inner ℂ y (π b Ω))) at hw
  have hn := (innerSL ℂ y).continuous.continuousAt.tendsto.comp
    (hx.mono_left (Ultrafilter.of_le atTop))
  exact tendsto_nhds_unique hw (by simpa only [Function.comp_def,innerSL_apply_apply,he] using hn)

theorem traceFreeHilbertIntoClosure_symmetrize (a : M.toStarSubalgebra) :
    ρ (traceSymmetrize a) = traceSymmetrize (ρ a) := by
  simp only [traceSymmetrize,map_smul,map_add,map_star]

theorem traceFreeHilbertIntoClosure_clip (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    ρ (traceClip a C) = traceClip (ρ a) C := by
  rw [traceClip_cfc a ha C,traceClip_cfc _ (ha.map ρ) C]
  exact (ρ).map_cfc (fun t : ℝ => -min (-min t C) C) a
    (by fun_prop) (by fun_prop) ha (ha.map ρ)

theorem traceFreeHilbertClosure_selfAdjoint_approximation
    (x : (N).toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : M.toStarSubalgebra, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖x‖ ∧ (σ).norm₂ (ρ a-x) < ε := by
  obtain ⟨v,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp
    (traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit (x.val Ω)) ε hε
  have ha' : (σ).norm₂ (ρ a-x) < ε := by
    change ‖π a Ω-x.val Ω‖ < ε
    simpa only [dist_eq_norm,norm_sub_rev] using ha
  let b := traceSymmetrize a
  have hb : IsSelfAdjoint b := traceSymmetrize_selfAdjoint a
  have hb' : (σ).norm₂ (ρ b-x) ≤ (σ).norm₂ (ρ a-x) := by
    have he : ρ b-x = traceSymmetrize (ρ a-x) := by
      rw [traceSymmetrize_sub,traceSymmetrize_eq_self x hx]
      exact congrArg (fun z => z-x) (traceFreeHilbertIntoClosure_symmetrize hfactor hdiff hfinite hunit a)
    rw [he]
    exact traceSymmetrize_norm₂_le σ _
  refine ⟨traceClip b ‖x‖,traceClip_selfAdjoint b hb _,traceClip_norm_le b hb _ (norm_nonneg _),?_⟩
  rw [traceFreeHilbertIntoClosure_clip hfactor hdiff hfinite hunit b hb]
  exact (traceClip_distance σ (ρ b) x (hb.map ρ) hx).trans_lt (hb'.trans_lt ha')

theorem traceFreeHilbertClosure_selfAdjoint_preimage (x : (N).toStarSubalgebra)
    (hx : IsSelfAdjoint x) : ∃ a : M.toStarSubalgebra, ρ a = x := by
  have hm : x.val Ω ∈ traceFreeHilbertVectorBall hfactor hdiff hfinite hunit ‖x‖ := by
    apply (traceFreeHilbertVectorBall_isClosed hfactor hdiff hfinite hunit ‖x‖).closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,ha,hax⟩ := traceFreeHilbertClosure_selfAdjoint_approximation hfactor hdiff hfinite hunit x hx ε hε
    exact ⟨π a Ω,⟨a,ha,rfl⟩,by
      change ‖π a Ω-x.val Ω‖ < ε at hax
      simpa only [dist_eq_norm,norm_sub_rev] using hax⟩
  obtain ⟨a,_,ha⟩ := hm
  refine ⟨a,?_⟩
  apply sub_eq_zero.mp
  apply (σ).separating
  change π a Ω-x.val Ω = 0
  exact sub_eq_zero.mpr ha

theorem traceFreeHilbertIntoClosure_surjective : Function.Surjective ρ := by
  intro x
  obtain ⟨a,ha⟩ := traceFreeHilbertClosure_selfAdjoint_preimage hfactor hdiff hfinite hunit (ℜ x) (ℜ x).property
  obtain ⟨b,hb⟩ := traceFreeHilbertClosure_selfAdjoint_preimage hfactor hdiff hfinite hunit (ℑ x) (ℑ x).property
  refine ⟨a+Complex.I • b,?_⟩
  rw [map_add,map_smul,ha,hb]
  exact realPart_add_I_smul_imaginaryPart x

theorem traceFreeHilbertIntoClosure_injective : Function.Injective ρ := by
  intro a b hab
  exact traceFreeHilbertAction_injective hfactor hdiff hfinite hunit (congrArg Subtype.val hab)

def traceFreeHilbertEquiv : M.toStarSubalgebra ≃⋆ₐ[ℂ] (N).toStarSubalgebra :=
  StarAlgEquiv.ofBijective ρ ⟨traceFreeHilbertIntoClosure_injective hfactor hdiff hfinite hunit,
    traceFreeHilbertIntoClosure_surjective hfactor hdiff hfinite hunit⟩

theorem traceFreeHilbertAction_range_eq : (π).range = (N).toStarSubalgebra := by
  ext T
  constructor
  · rintro ⟨a,rfl⟩
    exact traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit a
  · intro hT
    obtain ⟨a,ha⟩ := traceFreeHilbertIntoClosure_surjective hfactor hdiff hfinite hunit ⟨T,hT⟩
    exact ⟨a,congrArg Subtype.val ha⟩

theorem traceHilbertVonNeumann_wotClosed {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (P : VonNeumannAlgebra J) : WOTClosed P.toStarSubalgebra := by
  change IsClosed {T : J →WOT[ℂ] J | T.toCLM ∈ (P : Set (J →L[ℂ] J))}
  rw [← P.centralizer_centralizer]
  change IsClosed {T : J →WOT[ℂ] J |
    ∀ S ∈ Set.centralizer (P : Set (J →L[ℂ] J)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : J →WOT[ℂ] J | S*T.toCLM=T.toCLM*S} =
      {T : J →WOT[ℂ] J |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (J →WOT[ℂ] J) ≃ (J →L[ℂ] J) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

theorem traceFreeHilbertAction_range_wotClosed : WOTClosed (π).range := by
  rw [traceFreeHilbertAction_range_eq]
  exact traceHilbertVonNeumann_wotClosed N

end

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertTransportCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertTransportOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertTransportStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertTransportOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local instance traceHilbertTransportClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

theorem traceFreeHilbertEquiv_norm (a : M.toStarSubalgebra) : ‖e a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (e).toStarAlgHom (e).injective a

def traceFreeHilbertIsometry : M.toStarSubalgebra ≃ₗᵢ[ℂ] (N).toStarSubalgebra :=
  { (e).toAlgEquiv.toLinearEquiv with
    norm_map' := traceFreeHilbertEquiv_norm hfactor hdiff hfinite hunit }

theorem traceFreeHilbertClosure_isII1Factor : IsII1Factor (N).toStarSubalgebra := by
  have hM : IsII1Factor M.toStarSubalgebra := {
    nonzero := fun h => hunit (Subtype.ext h.symm)
    weaklyClosed := traceHilbertVonNeumann_wotClosed M
    factor := by
      intro a ha
      obtain ⟨z,hz⟩ := hfactor a ha
      exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z).symm⟩
    finite := hfinite
    diffuse := hdiff }
  exact isII1Factor_of_starAlgEquiv e hM (traceHilbertVonNeumann_wotClosed N)

theorem traceFreeHilbertClosure_hasSeparablePredual
    (hsep : HasSeparablePredual M.toStarSubalgebra) : HasSeparablePredual (N).toStarSubalgebra := by
  obtain ⟨X,g,s,c,hs,⟨d⟩⟩ := hsep
  exact ⟨X,g,s,c,hs,⟨d.trans (traceFreeHilbertIsometry hfactor hdiff hfinite hunit)⟩⟩

end Tracial

section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original exact factor and predual predicates produce a concrete cyclic
tracial representation and an isometric algebra isomorphism. No WOT continuity
of the isomorphism on the whole carrier, or Hilbert separability, is asserted. -/
theorem isII1Factor_cyclic_tracial_representation
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S) (hsep : HasSeparablePredual S) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (N : VonNeumannAlgebra K) (e : S ≃⋆ₐ[ℂ] N.toStarSubalgebra)
      (τ : UltrapowerBridge.TracialRepresentation N),
      IsII1Factor N.toStarSubalgebra ∧ HasSeparablePredual N.toStarSubalgebra ∧
      (∀ a, ‖e a‖ = ‖a‖) ∧ DenseRange (fun a : N.toStarSubalgebra => a.val τ.vector) := by
  let M := vonNeumannOfWOTClosed S hS.weaklyClosed
  have hf : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    obtain ⟨z,hz⟩ := hS.factor c hc
    exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  have hunit : (1 : M.toStarSubalgebra) ≠ 0 := by
    intro h
    exact hS.nonzero (congrArg Subtype.val h).symm
  let E := Tracial.TraceFreePreHilbert hf hS.diffuse hS.finite hunit
  let : NormedAddCommGroup E :=
    Tracial.traceFreePreHilbertNormedAddCommGroup hf hS.diffuse hS.finite hunit
  let : InnerProductSpace ℂ E :=
    Tracial.traceFreePreHilbertInnerProductSpace hf hS.diffuse hS.finite hunit
  let K := Tracial.TraceFreeHilbert hf hS.diffuse hS.finite hunit
  let g : NormedAddCommGroup K := inferInstance
  let i : InnerProductSpace ℂ K := UniformSpace.Completion.innerProductSpace
  let c : CompleteSpace K := inferInstance
  exact ⟨K,g,i,c,
    Tracial.traceFreeHilbertClosure hf hS.diffuse hS.finite hunit,
    Tracial.traceFreeHilbertEquiv hf hS.diffuse hS.finite hunit,
    Tracial.traceFreeHilbertClosureTrace hf hS.diffuse hS.finite hunit,
    Tracial.traceFreeHilbertClosure_isII1Factor hf hS.diffuse hS.finite hunit,
    Tracial.traceFreeHilbertClosure_hasSeparablePredual hf hS.diffuse hS.finite hunit hsep,
    Tracial.traceFreeHilbertEquiv_norm hf hS.diffuse hS.finite hunit,
    Tracial.traceFreeHilbertClosureTrace_cyclic hf hS.diffuse hS.finite hunit⟩

end

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceSubalgebraBallCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceSubalgebraBallOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraBallStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceSubalgebraBallOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local instance traceSubalgebraBallClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

def traceFreeSubalgebraWeakBall (C : ℝ) : Set (K →WOT[ℂ] K) :=
  {T | ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ‖a‖ ≤ C ∧
    ContinuousLinearMapWOT.ofCLM (π a) = T}

theorem traceFreeSubalgebraWeakBall_isCompact (hQ : WOTClosed Q) (C : ℝ) :
    IsCompact (traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  have hc : IsCompact {T : weakOperatorBall M C | T.val.toCLM ∈ Q} :=
    (hQ.preimage continuous_subtype_val).isCompact
  have he : traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C =
      traceFreeHilbertBallMap hfactor hdiff hfinite hunit C ''
        {T : weakOperatorBall M C | T.val.toCLM ∈ Q} := by
    ext T
    constructor
    · rintro ⟨a,ha,hn,rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,hn⟩⟩,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a.val.toCLM,a.property.1⟩,ha,a.property.2,rfl⟩
  rw [he]
  exact hc.image (traceFreeHilbertBallMap_continuous hfactor hdiff hfinite hunit C)

def traceFreeSubalgebraVectorBall (C : ℝ) : Set K :=
  {x | ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ‖a‖ ≤ C ∧ π a Ω = x}

theorem traceFreeSubalgebraVectorBall_isClosed (hQ : WOTClosed Q) (C : ℝ) :
    IsClosed (traceFreeSubalgebraVectorBall hfactor hdiff hfinite hunit Q C) := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  choose a hQmem ha he using hv
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T,hT,ht⟩ := (traceFreeSubalgebraWeakBall_isCompact hfactor hdiff hfinite hunit Q hQ C).ultrafilter_le_nhds
    (ω.map (fun n => ContinuousLinearMapWOT.ofCLM (π (a n)))) (by
      apply le_principal_iff.mpr
      change ∀ᶠ n in (ω : Filter ℕ), ContinuousLinearMapWOT.ofCLM (π (a n)) ∈
        traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C
      exact Eventually.of_forall (fun n => ⟨a n,hQmem n,ha n,rfl⟩))
  obtain ⟨b,hbQ,hb,rfl⟩ := hT
  refine ⟨b,hbQ,hb,?_⟩
  apply ext_inner_left ℂ
  intro y
  have hw := (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp ht) Ω y
  change Tendsto (fun n => inner ℂ y (π (a n) Ω)) (ω : Filter ℕ)
    (𝓝 (inner ℂ y (π b Ω))) at hw
  have hn := (innerSL ℂ y).continuous.continuousAt.tendsto.comp
    (hx.mono_left (Ultrafilter.of_le atTop))
  exact tendsto_nhds_unique hw (by simpa only [Function.comp_def,innerSL_apply_apply,he] using hn)

theorem traceSymmetrize_mem_original (a : M.toStarSubalgebra) (ha : a.val ∈ Q) :
    (traceSymmetrize a).val ∈ Q := by
  have hs : star a.val ∈ Q := star_mem ha
  exact Q.smul_mem (Q.add_mem ha hs) _

theorem traceClip_mem_original (hQ : WOTClosed Q) (a : M.toStarSubalgebra)
    (haQ : a.val ∈ Q) (ha : IsSelfAdjoint a) (C : ℝ) : (traceClip a C).val ∈ Q := by
  let P := Q.comap M.toStarSubalgebra.subtype
  let : IsClosed (P : Set M.toStarSubalgebra) :=
    (hQ.preimage ContinuousLinearMapWOT.continuous_ofCLM).preimage continuous_subtype_val
  change traceClip a C ∈ P
  rw [traceClip_cfc a ha C]
  exact cfc_mem (𝕜' := ℂ) (fun t : ℝ => -min (-min t C) C) haQ

end Tracial

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceSubalgebraImageCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceSubalgebraImageOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraImageStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceSubalgebraImageOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local instance traceSubalgebraImageClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

local notation "P" => StarSubalgebra.map π (StarSubalgebra.comap
  (StarSubalgebra.subtype (VonNeumannAlgebra.toStarSubalgebra M)) Q)

/-- The double commutant of the represented intersection with Q. -/
def traceFreeSubalgebraClosure : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))) =
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    simp only [Set.centralizer_centralizer_centralizer]

local notation "R" => traceFreeSubalgebraClosure hfactor hdiff hfinite hunit Q

theorem traceFreeSubalgebraClosure_mem_iff (T : K →L[ℂ] K) :
    T ∈ R ↔ T ∈ Set.centralizer (Set.centralizer (P : Set (K →L[ℂ] K))) := by
  change T ∈ (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) ↔ _
  simp only [← SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq,Set.union_self]

theorem traceFreeSubalgebraClosure_le : (R).toStarSubalgebra ≤ (N).toStarSubalgebra := by
  intro T hT
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T).mpr
  have ht := (traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q T).mp hT
  intro a ha
  apply ht a
  rintro b ⟨c,_,rfl⟩
  exact ha (π c) ⟨c,rfl⟩

def traceFreeSubalgebraInclusion : (R).toStarSubalgebra →⋆ₐ[ℂ] (N).toStarSubalgebra :=
  StarSubalgebra.inclusion (traceFreeSubalgebraClosure_le hfactor hdiff hfinite hunit Q)

local notation "j" => traceFreeSubalgebraInclusion hfactor hdiff hfinite hunit Q

theorem traceFreeSubalgebra_selfAdjoint_approximation
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) (hx : IsSelfAdjoint x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖j x‖ ∧
      (σ).norm₂ (ρ a-j x) < ε := by
  classical
  obtain ⟨v,hv⟩ := bicommutant_finite_strong_approximation P x.val
    ((traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q x.val).mp x.property)
    {Ω} ε hε
  obtain ⟨a,haQ,ha⟩ := v.property
  change π a = v.val at ha
  have ha' : (σ).norm₂ (ρ a-j x) < ε := by
    change ‖π a Ω-x.val Ω‖ < ε
    have happrox := hv Ω (Finset.mem_singleton_self Ω)
    change ‖x.val Ω-v.val Ω‖ < ε at happrox
    rw [← ha] at happrox
    simpa only [norm_sub_rev] using happrox
  let b := traceSymmetrize a
  have hb : IsSelfAdjoint b := traceSymmetrize_selfAdjoint a
  have hbQ : b.val ∈ Q := traceSymmetrize_mem_original Q a haQ
  have hJ : IsSelfAdjoint (j x) := hx.map j
  have hb' : (σ).norm₂ (ρ b-j x) ≤ (σ).norm₂ (ρ a-j x) := by
    have he : ρ b-j x = traceSymmetrize (ρ a-j x) := by
      rw [traceSymmetrize_sub,traceSymmetrize_eq_self (j x) hJ]
      exact congrArg (fun z => z-j x)
        (traceFreeHilbertIntoClosure_symmetrize hfactor hdiff hfinite hunit a)
    rw [he]
    exact traceSymmetrize_norm₂_le σ _
  refine ⟨traceClip b ‖j x‖,
    traceClip_mem_original Q hQ b hbQ hb _,
    traceClip_selfAdjoint b hb _,traceClip_norm_le b hb _ (norm_nonneg _),?_⟩
  rw [traceFreeHilbertIntoClosure_clip hfactor hdiff hfinite hunit b hb]
  exact (traceClip_distance σ (ρ b) (j x) (hb.map ρ) hJ).trans_lt (hb'.trans_lt ha')

theorem traceFreeSubalgebra_selfAdjoint_preimage
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ρ a = j x := by
  have hm : x.val Ω ∈ traceFreeSubalgebraVectorBall hfactor hdiff hfinite hunit Q ‖j x‖ := by
    apply (traceFreeSubalgebraVectorBall_isClosed hfactor hdiff hfinite hunit Q hQ ‖j x‖).closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,haQ,_,ha,hax⟩ := traceFreeSubalgebra_selfAdjoint_approximation
      hfactor hdiff hfinite hunit Q hQ x hx ε hε
    exact ⟨π a Ω,⟨a,haQ,ha,rfl⟩,by
      change ‖π a Ω-x.val Ω‖ < ε at hax
      simpa only [dist_eq_norm,norm_sub_rev] using hax⟩
  obtain ⟨a,haQ,_,ha⟩ := hm
  refine ⟨a,haQ,?_⟩
  apply sub_eq_zero.mp
  apply (σ).separating
  change π a Ω-x.val Ω = 0
  exact sub_eq_zero.mpr ha

theorem traceFreeSubalgebraClosure_preimage
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ρ a = j x := by
  obtain ⟨a,haQ,ha⟩ := traceFreeSubalgebra_selfAdjoint_preimage hfactor hdiff hfinite hunit Q hQ
    (ℜ x) (ℜ x).property
  obtain ⟨b,hbQ,hb⟩ := traceFreeSubalgebra_selfAdjoint_preimage hfactor hdiff hfinite hunit Q hQ
    (ℑ x) (ℑ x).property
  refine ⟨a+Complex.I • b,Q.add_mem haQ (Q.smul_mem hbQ _),?_⟩
  rw [map_add,map_smul,ha,hb,← map_smul,← map_add]
  exact congrArg j (realPart_add_I_smul_imaginaryPart x)

theorem traceFreeSubalgebraImage_eq_closure (hQ : WOTClosed Q) :
    P = (R).toStarSubalgebra := by
  apply le_antisymm
  · intro T hT
    apply (traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q T).mpr
    exact fun a ha => (ha T hT).symm
  · intro T hT
    obtain ⟨a,haQ,ha⟩ := traceFreeSubalgebraClosure_preimage hfactor hdiff hfinite hunit Q hQ ⟨T,hT⟩
    exact ⟨a,haQ,congrArg Subtype.val ha⟩

/-- Every original WOT-closed subalgebra has WOT-closed represented intersection.
No cyclicity of its orbit, factor hypothesis on Q, or full WOT continuity is used. -/
theorem traceFreeSubalgebraImage_wotClosed (hQ : WOTClosed Q) :
    WOTClosed ((Q.comap M.toStarSubalgebra.subtype).map π) := by
  rw [traceFreeSubalgebraImage_eq_closure hfactor hdiff hfinite hunit Q hQ]
  exact traceHilbertVonNeumann_wotClosed R

end

/-! Generation pullback for the actual constructed trace representation. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceGenerationTransportCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceGenerationTransportOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceGenerationTransportStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceGenerationTransportOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local instance traceGenerationTransportClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

/-- Pull a literal W*-generator back through the constructed representation.
Closed images of the original generated subalgebra replace any unproved
whole-carrier weak-operator continuity assertion. -/
theorem traceFreeHilbert_singlyGenerated_pullback
    (hgen : SinglyGenerated (N).toStarSubalgebra) : SinglyGenerated M.toStarSubalgebra := by
  obtain ⟨b,hb,hgen⟩ := hgen
  let a : M.toStarSubalgebra := (e).symm ⟨b,hb⟩
  let Q := wstar {a.val}
  have hQM : Q ≤ M.toStarSubalgebra :=
    wstar_le (traceHilbertVonNeumann_wotClosed M) (by
      intro c hc
      obtain rfl := Set.mem_singleton_iff.mp hc
      exact a.property)
  let P := (Q.comap M.toStarSubalgebra.subtype).map π
  have hbP : b ∈ P := by
    refine ⟨a,subset_wstar {a.val} (Set.mem_singleton a.val),?_⟩
    exact congrArg Subtype.val ((e).apply_symm_apply ⟨b,hb⟩)
  have hNP : (N).toStarSubalgebra ≤ P := by
    rw [← hgen]
    exact wstar_le (traceFreeSubalgebraImage_wotClosed hfactor hdiff hfinite hunit Q
      (wstar_closed {a.val})) (by
        intro c hc
        obtain rfl := Set.mem_singleton_iff.mp hc
        exact hbP)
  refine ⟨a.val,a.property,le_antisymm hQM ?_⟩
  intro c hc
  obtain ⟨d,hdQ,hd⟩ := hNP (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit ⟨c,hc⟩)
  have hd' : d = (⟨c,hc⟩ : M.toStarSubalgebra) :=
    traceFreeHilbertAction_injective hfactor hdiff hfinite hunit hd
  change d.val ∈ Q at hdQ
  rw [hd'] at hdQ
  exact hdQ

end Tracial

end Generator

end

end OAI
