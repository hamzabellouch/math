import Mathlib
import OAI.Geometry.BallPacking.Forms.ManifoldMapDifferential

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open Set Function
open scoped ContDiff Topology
open scoped Manifold
open Manifold IsManifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem symplecticProjection_natural
    {Ω₀ Ω₁ : E →L[ℝ] E →L[ℝ] ℝ} {i₀ i₁ : F →L[ℝ] E}
    {L : E →L[ℝ] E} {K : F →L[ℝ] F}
    (h₀ : (Ω₀.bilinearComp i₀ i₀).IsInvertible)
    (h₁ : (Ω₁.bilinearComp i₁ i₁).IsInvertible)
    (hK : Surjective K) (hL : ∀ u v, Ω₁ (L u) (L v) = Ω₀ u v)
    (hi : ∀ u, L (i₀ u) = i₁ (K u)) (x : E) :
    symplecticProjection Ω₁ i₁ (L x) = K (symplecticProjection Ω₀ i₀ x) := by
  apply h₁.injective
  ext w
  obtain ⟨u,rfl⟩ := hK w
  change Ω₁ (i₁ (symplecticProjection Ω₁ i₁ (L x))) (i₁ (K u)) =
    Ω₁ (i₁ (K (symplecticProjection Ω₀ i₀ x))) (i₁ (K u))
  rw [symplecticProjection_pairing h₁,←hi,←hi,hL,hL,symplecticProjection_pairing h₀]

theorem normal_annihilation_pullback
    {Ω₀ Ω₁ : E →L[ℝ] E →L[ℝ] ℝ} {i₀ i₁ : F →L[ℝ] E}
    {L : E →L[ℝ] E} {K : F →L[ℝ] F} {β : E →L[ℝ] ℝ}
    (h₀ : (Ω₀.bilinearComp i₀ i₀).IsInvertible)
    (h₁ : (Ω₁.bilinearComp i₁ i₁).IsInvertible)
    (hK : Surjective K) (hL : ∀ u v, Ω₁ (L u) (L v) = Ω₀ u v)
    (hi : ∀ u, L (i₀ u) = i₁ (K u))
    (hβ : ∀ v, β v = β (i₁ (symplecticProjection Ω₁ i₁ v))) (v : E) :
    β (L v) = β (L (i₀ (symplecticProjection Ω₀ i₀ v))) := by
  rw [hβ (L v),symplecticProjection_natural h₀ h₁ hK hL hi,hi]

theorem moser_vector_tangent_of_annihilation
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hΩ : Ω.IsInvertible) (hi : (Ω.bilinearComp i i).IsInvertible)
    (hskew : ∀ u v, Ω u v = -Ω v u) (β : E →L[ℝ] ℝ)
    (hb : ∀ v, β v = β (i (symplecticProjection Ω i v))) :
    -Ω.inverse β = i (-((Ω.bilinearComp i i).inverse (β.comp i))) := by
  have hz : symplecticNormalJet Ω i β = 0 := by
    ext v
    exact sub_eq_zero.mpr (hb v).symm
  simpa only [hz,add_zero] using corrected_moser_vector_tangent hΩ hi hskew β

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def localNormalJet (β : E → E →L[ℝ] ℝ) (r : E → E) (x : E) : ℝ := β x (x-r x)

theorem localNormalJet_contDiffOn {β : E → E →L[ℝ] ℝ} {r : E → E} {U : Set E}
    (hβ : ContDiffOn ℝ ∞ β U) (hr : ContDiffOn ℝ ∞ r U) :
    ContDiffOn ℝ ∞ (localNormalJet β r) U :=
  hβ.clm_apply (contDiffOn_id.sub hr)

theorem localNormalJet_zero {β : E → E →L[ℝ] ℝ} {r : E → E} {x : E}
    (hx : r x = x) : localNormalJet β r x = 0 := by
  simp only [localNormalJet,hx,sub_self,map_zero]

theorem localNormalJet_hasFDerivAt {β : E → E →L[ℝ] ℝ} {r : E → E} {x : E}
    (hβ : DifferentiableAt ℝ β x) (hr : DifferentiableAt ℝ r x)
    (hx : r x = x) (hβr : (β x).comp (fderiv ℝ r x) = 0) :
    HasFDerivAt (localNormalJet β r) (β x) x := by
  apply (hβ.hasFDerivAt.clm_apply ((hasFDerivAt_id x).sub hr.hasFDerivAt)).congr_fderiv
  ext v
  have hz : β x (fderiv ℝ r x v) = 0 :=
    congrArg (fun A : E →L[ℝ] ℝ => A v) hβr
  simp only [ContinuousLinearMap.comp_apply,Pi.sub_apply,id_eq,hx,sub_self,map_zero,add_zero,
    sub_apply,ContinuousLinearMap.id_apply,map_sub,hz,sub_zero]

theorem product_normal_first_jet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {β : E × F → (E × F) →L[ℝ] ℝ} {x : E × F}
    (hβ : DifferentiableAt ℝ β x) (hx : x.2 = 0)
    (htan : ∀ v : E, β x (v,0) = 0) :
    HasFDerivAt (fun y : E × F => β y (0,y.2)) (β x) x := by
  let r : (E × F) →L[ℝ] E × F := (ContinuousLinearMap.fst ℝ E F).prod 0
  have heq : (fun y : E × F => β y (0,y.2)) = localNormalJet β r := by
    ext y
    change β y (0,y.2) = β y (y.1-y.1,y.2-0)
    rw [sub_self,sub_zero]
  rw [heq]
  apply localNormalJet_hasFDerivAt hβ r.differentiableAt
  · exact Prod.ext rfl hx.symm
  · rw [r.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    exact htan v.1

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def splitInclusion (L : (F × G) ≃L[ℝ] E) : F →L[ℝ] E :=
  L.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ F G)

def splitRetraction (L : (F × G) ≃L[ℝ] E) : E →L[ℝ] E :=
  (splitInclusion L).comp ((ContinuousLinearMap.fst ℝ F G).comp L.symm.toContinuousLinearMap)

theorem splitRetraction_eq {L : (F × G) ≃L[ℝ] E} {x : E}
    (hx : (L.symm x).2 = 0) : splitRetraction L x = x := by
  change L ((L.symm x).1,0) = x
  rw [←hx,Prod.mk.eta,L.apply_symm_apply]

def localSymplecticPotential (L : (F × G) ≃L[ℝ] E)
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : ℝ :=
  symplecticNormalJet (Ω p) (splitInclusion L) (α p) (p.2-splitRetraction L p.2)

theorem localSymplecticPotential_zero {L : (F × G) ≃L[ℝ] E}
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ × E → E →L[ℝ] ℝ) {p : ℝ × E}
    (hp : (L.symm p.2).2 = 0) : localSymplecticPotential L Ω α p = 0 := by
  simp only [localSymplecticPotential,splitRetraction_eq hp,sub_self,map_zero]

variable [CompleteSpace F]

theorem symplecticNormalJet_contDiffAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : P → E →L[ℝ] E →L[ℝ] ℝ} {α : P → E →L[ℝ] ℝ}
    {i : P → F →L[ℝ] E} {p : P}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hα : ContDiffAt ℝ ∞ α p) (hi : ContDiffAt ℝ ∞ i p)
    (hinv : ((Ω p).bilinearComp (i p) (i p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun q => symplecticNormalJet (Ω q) (i q) (α q)) p :=
  (hα.clm_comp (hi.clm_comp (symplecticProjection_contDiffAt hΩ hi hinv))).sub hα

theorem localSymplecticPotential_contDiffAt {L : (F × G) ≃L[ℝ] E}
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {α : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hα : ContDiffAt ℝ ∞ α p)
    (hinv : ((Ω p).bilinearComp (splitInclusion L) (splitInclusion L)).IsInvertible) :
    ContDiffAt ℝ ∞ (localSymplecticPotential L Ω α) p :=
  (symplecticNormalJet_contDiffAt hΩ hα contDiffAt_const hinv).clm_apply
    (contDiffAt_snd.sub ((splitRetraction L).contDiff.contDiffAt.comp p contDiffAt_snd))

theorem localSymplecticPotential_hasFDerivAt {L : (F × G) ≃L[ℝ] E}
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {α : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hα : ContDiffAt ℝ ∞ α p)
    (hinv : ((Ω p).bilinearComp (splitInclusion L) (splitInclusion L)).IsInvertible)
    (hp : (L.symm p.2).2 = 0) :
    HasFDerivAt (localSymplecticPotential L Ω α)
      ((symplecticNormalJet (Ω p) (splitInclusion L) (α p)).comp
        (ContinuousLinearMap.snd ℝ ℝ E)) p := by
  let β : ℝ × E → (ℝ × E) →L[ℝ] ℝ := fun q =>
    (symplecticNormalJet (Ω q) (splitInclusion L) (α q)).comp (ContinuousLinearMap.snd ℝ ℝ E)
  let r : (ℝ × E) →L[ℝ] ℝ × E :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod ((splitRetraction L).comp (ContinuousLinearMap.snd ℝ ℝ E))
  have he : localSymplecticPotential L Ω α = localNormalJet β r := rfl
  rw [he]
  apply localNormalJet_hasFDerivAt
    (((symplecticNormalJet_contDiffAt hΩ hα contDiffAt_const hinv).clm_comp
      contDiffAt_const).differentiableAt (by simp)) r.differentiableAt
  · exact Prod.ext rfl (splitRetraction_eq hp)
  · rw [r.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    exact symplecticNormalJet_tangent hinv (α p) ((L.symm v.2).1)

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem maximalChart_inverse_differential {c : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,E) ∞ M) {x : M} (hx : x ∈ c.source) :
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c.symm (c x)).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x) =
      ContinuousLinearMap.id ℝ E ∧
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c.symm (c x)) =
      ContinuousLinearMap.id ℝ E := by
  have hd := (contMDiffAt_of_mem_maximalAtlas hc hx).mdifferentiableAt (by simp)
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hx)).mdifferentiableAt (by simp)
  constructor
  · have hf := (hi.hasMFDerivAt.comp x hd.hasMFDerivAt).mfderiv
    have he : (c.symm ∘ c : M → M) =ᶠ[𝓝 x] id := by
      filter_upwards [c.open_source.mem_nhds hx] with z hz
      exact c.left_inv hz
    rw [he.mfderiv_eq] at hf
    convert! hf.symm using 1
    simp only [mfderiv_id]
    rfl
  · have hid := hi.hasMFDerivAt
    have hd' : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) c (c.symm (c x))
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x) := by
      rw [c.left_inv hx]
      exact hd.hasMFDerivAt
    have hf := (hd'.comp (c x) hid).mfderiv
    have he : (c ∘ c.symm : E → E) =ᶠ[𝓝 (c x)] id := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
      exact c.right_inv hz
    rw [he.mfderiv_eq] at hf
    convert! hf.symm using 1
    simp only [mfderiv_id]
    rfl

def maximalChartLinearEquiv {c : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,E) ∞ M) {x : M} (hx : x ∈ c.source) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse' (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c.symm (c x))
    (maximalChart_inverse_differential hc hx).2 (maximalChart_inverse_differential hc hx).1

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def relativeLocalPotential (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    (d : OpenPartialHomeomorph M E) (L : (F × G) ≃L[ℝ] E) (p : ℝ × M) : ℝ :=
  localSymplecticPotential L (euclideanPullbackTwoForm Ω d.symm)
    (euclideanPullbackOneForm α d.symm) (p.1,d p.2)

def relativeLocalDomain (Ω : ℝ → ManifoldTwoForm E M)
    (d : OpenPartialHomeomorph M E) (L : (F × G) ≃L[ℝ] E) : Set (ℝ × M) :=
  {p | p.2 ∈ d.source ∧ ((euclideanPullbackTwoForm Ω d.symm (p.1,d p.2)).bilinearComp
      (splitInclusion L) (splitInclusion L)).IsInvertible}

variable [CompleteSpace F]

theorem relativeLocalDomain_isOpen {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E) : IsOpen (relativeLocalDomain Ω d L) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hp' : p.2 ∈ d.source := hp.1
  have hform := euclideanPullbackTwoForm_contDiffAt (p := (p.1,d p.2)) hΩ
    (contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hp'))
  have hi : ContDiffAt ℝ ∞ (fun q : ℝ × E => (euclideanPullbackTwoForm Ω d.symm q).bilinearComp
      (splitInclusion L) (splitInclusion L)) (p.1,d p.2) :=
    smooth_bilinear_flip ((smooth_bilinear_flip (hform.clm_comp contDiffAt_const)).clm_comp contDiffAt_const)
  have hc : ContinuousAt (fun q : ℝ × M => (q.1,d q.2)) p :=
    continuousAt_fst.prodMk ((d.continuousOn.continuousAt (d.open_source.mem_nhds hp')).comp
      continuousAt_snd)
  have hn := (hi.continuousAt.comp (f := fun q : ℝ × M => (q.1,d q.2)) hc).preimage_mem_nhds
    (ContinuousLinearEquiv.isOpen.mem_nhds hp.2)
  filter_upwards [hn,continuousAt_snd.preimage_mem_nhds (d.open_source.mem_nhds hp')] with q hq hqs
  exact ⟨hqs,hq⟩

theorem relativeLocalPotential_contMDiffOn {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E) :
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (relativeLocalPotential Ω α d L) (relativeLocalDomain Ω d L) := by
  intro p hp
  have hi := contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hp.1)
  have hf := localSymplecticPotential_contDiffAt
    (euclideanPullbackTwoForm_contDiffAt (p := (p.1,d p.2)) hΩ hi)
    (euclideanPullbackOneForm_contDiffAt (p := (p.1,d p.2)) hα hi) hp.2
  have hc : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ × E) ∞
      (fun q : ℝ × M => (q.1,d q.2)) p := contMDiffAt_fst.prodMk_space
    ((contMDiffAt_of_mem_maximalAtlas hd hp.1).comp p contMDiffAt_snd)
  exact (hf.contMDiffAt.comp p hc).contMDiffWithinAt

end
section

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem symplecticProjection_reparametrize
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E} (D : G ≃L[ℝ] F)
    (hi : (Ω.bilinearComp i i).IsInvertible)
    (hi' : (Ω.bilinearComp (i.comp D.toContinuousLinearMap) (i.comp D.toContinuousLinearMap)).IsInvertible) (x : E) :
    symplecticProjection Ω (i.comp D.toContinuousLinearMap) x = D.symm (symplecticProjection Ω i x) := by
  apply hi'.injective
  apply ContinuousLinearMap.ext
  intro u
  rw [show (Ω.bilinearComp (i.comp D.toContinuousLinearMap) (i.comp D.toContinuousLinearMap))
      (symplecticProjection Ω (i.comp D.toContinuousLinearMap) x) u = Ω x (i (D u)) from
        symplecticProjection_pairing hi' x u]
  change Ω x (i (D u)) = Ω (i (D (D.symm (symplecticProjection Ω i x)))) (i (D u))
  rw [D.apply_symm_apply,symplecticProjection_pairing hi]

theorem symplecticNormalJet_reparametrize
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E} (D : G ≃L[ℝ] F)
    (hi : (Ω.bilinearComp i i).IsInvertible)
    (hi' : (Ω.bilinearComp (i.comp D.toContinuousLinearMap) (i.comp D.toContinuousLinearMap)).IsInvertible) (α : E →L[ℝ] ℝ) :
    symplecticNormalJet Ω (i.comp D.toContinuousLinearMap) α = symplecticNormalJet Ω i α := by
  ext x
  change α (i (D (symplecticProjection Ω (i.comp D.toContinuousLinearMap) x))) - α x =
    α (i (symplecticProjection Ω i x)) - α x
  rw [symplecticProjection_reparametrize D hi hi',D.apply_symm_apply]

theorem symplecticProjection_changeCoordinates (C : E ≃L[ℝ] H)
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) (x : E) :
    symplecticProjection (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap) (C.toContinuousLinearMap.comp i) (C x) =
      symplecticProjection Ω i x := by
  have hB : (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap).bilinearComp
      (C.toContinuousLinearMap.comp i) (C.toContinuousLinearMap.comp i) = Ω.bilinearComp i i := by
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,C.symm_apply_apply]
  simp only [symplecticProjection,hB,ContinuousLinearMap.comp_apply]
  congr 1
  ext u
  simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearEquiv.coe_coe,C.symm_apply_apply]

theorem symplecticNormalJet_changeCoordinates (C : E ≃L[ℝ] H)
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) (α : E →L[ℝ] ℝ) (x : E) :
    symplecticNormalJet (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap)
      (C.toContinuousLinearMap.comp i) (α.comp C.symm.toContinuousLinearMap) (C x) = symplecticNormalJet Ω i α x := by
  change α (C.symm (C (i (symplecticProjection (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap)
    (C.toContinuousLinearMap.comp i) (C x))))) - α (C.symm (C x)) = _
  rw [C.symm_apply_apply,C.symm_apply_apply,symplecticProjection_changeCoordinates]
  rfl

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem adapted_restriction_isInvertible
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E)
    (C : E ≃L[ℝ] E) (D : F ≃L[ℝ] F) (L : (F × G) ≃L[ℝ] E)
    (hsplit : splitInclusion (F := F) (G := G) L = C.toContinuousLinearMap.comp (i.comp D.symm.toContinuousLinearMap))
    (hi : (Ω.bilinearComp i i).IsInvertible) :
    ((Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap).bilinearComp
      (splitInclusion (F := F) (G := G) L) (splitInclusion (F := F) (G := G) L)).IsInvertible := by
  have hB : (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap).bilinearComp
      (splitInclusion (F := F) (G := G) L) (splitInclusion (F := F) (G := G) L) =
        (Ω.bilinearComp i i).bilinearComp D.symm.toContinuousLinearMap D.symm.toContinuousLinearMap := by
    rw [hsplit]
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,C.symm_apply_apply]
  rw [hB]
  exact bilinearComp_isInvertible hi ⟨D.symm,rfl⟩

theorem adapted_normal_jet
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) (α : E →L[ℝ] ℝ)
    (C : E ≃L[ℝ] E) (D : F ≃L[ℝ] F) (L : (F × G) ≃L[ℝ] E)
    (hsplit : splitInclusion (F := F) (G := G) L = C.toContinuousLinearMap.comp (i.comp D.symm.toContinuousLinearMap))
    (hi : (Ω.bilinearComp i i).IsInvertible) (v : E) :
    symplecticNormalJet
      (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap)
      (splitInclusion (F := F) (G := G) L) (α.comp C.symm.toContinuousLinearMap) (C v) =
        symplecticNormalJet Ω i α v := by
  rw [hsplit,symplecticNormalJet_changeCoordinates]
  have hi' : (Ω.bilinearComp (i.comp D.symm.toContinuousLinearMap)
      (i.comp D.symm.toContinuousLinearMap)).IsInvertible := by
    have he : Ω.bilinearComp (i.comp D.symm.toContinuousLinearMap)
        (i.comp D.symm.toContinuousLinearMap) =
        (Ω.bilinearComp i i).bilinearComp D.symm.toContinuousLinearMap D.symm.toContinuousLinearMap := by
      ext u v
      rfl
    rw [he]
    exact bilinearComp_isInvertible hi ⟨D.symm,rfl⟩
  rw [symplecticNormalJet_reparametrize D.symm hi hi']

end

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

private theorem fderiv_eq_of_hasFDerivAt {f : F → E} {f' : F →L[ℝ] E} {x : F}
    (h : HasFDerivAt f f' x) : fderiv ℝ f x = f' := h.fderiv

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem adapted_inclusion_differential {e : N → M}
    {c : OpenPartialHomeomorph N F} {d : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,F) ∞ N) (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E)
    (heq : EqOn (d ∘ e ∘ c.symm) (fun y => L (y,0)) c.target)
    {b : N} (hb : b ∈ c.source) (hdb : e b ∈ d.source)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e b) :
    splitInclusion (E := E) (F := F) (G := G) L =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) : E →L[ℝ] E).comp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b : F →L[ℝ] E).comp
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) c.symm (c b) : F →L[ℝ] F)) := by
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hb)).mdifferentiableAt (by simp)
  have he' : HasMFDerivAt 𝓘(ℝ,F) 𝓘(ℝ,E) e (c.symm (c b))
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b) := by rw [c.left_inv hb]; exact he.hasMFDerivAt
  have hd' : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) d (e (c.symm (c b)))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b)) := by
    rw [c.left_inv hb]
    exact (contMDiffAt_of_mem_maximalAtlas hd hdb).mdifferentiableAt (by simp) |>.hasMFDerivAt
  have hfd : HasFDerivAt (d ∘ e ∘ c.symm)
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) : E →L[ℝ] E).comp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b : F →L[ℝ] E).comp
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) c.symm (c b) : F →L[ℝ] F))) (c b) :=
    hasMFDerivAt_iff_hasFDerivAt.mp (hd'.comp (c b) (he'.comp (c b) hi.hasMFDerivAt))
  have hcomp : fderiv ℝ (d ∘ e ∘ c.symm) (c b) =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) : E →L[ℝ] E).comp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b : F →L[ℝ] E).comp
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) c.symm (c b) : F →L[ℝ] F)) := fderiv_eq_of_hasFDerivAt hfd
  have hloc : (d ∘ e ∘ c.symm) =ᶠ[𝓝 (c b)] fun y => L (y,0) :=
    heq.eventuallyEq_of_mem (c.open_target.mem_nhds (c.map_source hb))
  rw [hloc.fderiv_eq (𝕜 := ℝ)] at hcomp
  have hf : fderiv ℝ (fun y : F => L (y,0)) (c b) = splitInclusion (E := E) (F := F) (G := G) L := by
    exact (splitInclusion (E := E) (F := F) (G := G) L).fderiv
  rw [hf] at hcomp
  exact hcomp

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem maximalChart_pullback_two (Ω : ℝ → ManifoldTwoForm E M)
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    {x : M} (hx : x ∈ d.source) (t : ℝ) :
    euclideanPullbackTwoForm Ω d.symm (t,d x) =
      (Ω t x).bilinearComp (maximalChartLinearEquiv hd hx).symm.toContinuousLinearMap
        (maximalChartLinearEquiv hd hx).symm.toContinuousLinearMap := by
  dsimp [euclideanPullbackTwoForm]
  rw [d.left_inv hx]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem maximalChart_pullback_one (α : ℝ → ManifoldOneForm E M)
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    {x : M} (hx : x ∈ d.source) (t : ℝ) :
    euclideanPullbackOneForm α d.symm (t,d x) =
      (α t x).comp (maximalChartLinearEquiv hd hx).symm.toContinuousLinearMap := by
  dsimp [euclideanPullbackOneForm]
  rw [d.left_inv hx]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem relativeLocalDomain_mem (Ω : ℝ → ManifoldTwoForm E M) {e : N → M}
    {c : OpenPartialHomeomorph N F} {d : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,F) ∞ N) (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E)
    (heq : EqOn (d ∘ e ∘ c.symm) (fun y => L (y,0)) c.target)
    {b : N} (hb : b ∈ c.source) (hdb : e b ∈ d.source)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e b) {t : ℝ}
    (hi : ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) :
    (t,e b) ∈ relativeLocalDomain Ω d L := by
  refine ⟨hdb,?_⟩
  rw [maximalChart_pullback_two Ω hd hdb]
  exact adapted_restriction_isInvertible _ _ (maximalChartLinearEquiv hd hdb)
    (maximalChartLinearEquiv hc hb) L (adapted_inclusion_differential hc hd L heq hb hdb he) hi

variable [CompleteSpace F]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem relativeLocalPotential_hasMFDerivAt
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {c : OpenPartialHomeomorph N F} {d : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,F) ∞ N) (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E)
    (heq : EqOn (d ∘ e ∘ c.symm) (fun y => L (y,0)) c.target)
    {b : N} (hb : b ∈ c.source) (hdb : e b ∈ d.source)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e b) {t : ℝ}
    (hi : ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) :
    HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ)
      (relativeLocalPotential Ω α d L) (t,e b)
      ((symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
        (ContinuousLinearMap.snd ℝ ℝ E)) := by
  have hds := contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hdb)
  have hinv := (relativeLocalDomain_mem Ω hc hd L heq hb hdb he hi).2
  have hzero : (L.symm (d (e b))).2 = 0 := by
    have h := heq (c.map_source hb)
    simp only [Function.comp_apply,c.left_inv hb] at h
    rw [h,L.symm_apply_apply]
  have hf := localSymplecticPotential_hasFDerivAt
    (euclideanPullbackTwoForm_contDiffAt (p := (t,d (e b))) hΩ hds)
    (euclideanPullbackOneForm_contDiffAt (p := (t,d (e b))) hα hds) hinv hzero
  have ha : HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) Prod.fst (t,e b)
      (ContinuousLinearMap.fst ℝ ℝ E) := hasMFDerivAt_fst (t,e b)
  have hb' := ((contMDiffAt_of_mem_maximalAtlas hd hdb).mdifferentiableAt (by simp)).hasMFDerivAt.comp
      (t,e b) (hasMFDerivAt_snd (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,E)) (t,e b))
  have hcoord : HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ × E)
      (fun q : ℝ × M => (q.1,d q.2)) (t,e b)
      ((ContinuousLinearMap.fst ℝ ℝ E).prod
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b)).comp (ContinuousLinearMap.snd ℝ ℝ E))) :=
    ⟨ha.1.prodMk hb'.1,ha.2.prodMk hb'.2⟩
  have hcomp := (hasMFDerivAt_iff_hasFDerivAt.mpr hf).comp (t,e b) hcoord
  apply hcomp.congr_mfderiv
  ext v
  change symplecticNormalJet (euclideanPullbackTwoForm Ω d.symm (t,d (e b)))
    (splitInclusion L) (euclideanPullbackOneForm α d.symm (t,d (e b)))
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) v.2) = _
  rw [maximalChart_pullback_two Ω hd hdb,maximalChart_pullback_one α hd hdb]
  exact adapted_normal_jet _ _ _ (maximalChartLinearEquiv hd hdb)
    (maximalChartLinearEquiv hc hb) L (adapted_inclusion_differential hc hd L heq hb hdb he) hi v.2

end PackingSufficiencySupport.Hamiltonian
end

end OAI
