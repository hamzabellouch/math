import Mathlib
import OAI.Geometry.BallPacking.Normal.CubicToricAmbient

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem exists_compact_exact_fibre_embedding {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
    (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
      manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
    ∃ t∈Ioc (0:ℝ) δ,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w := by
  obtain ⟨ε,hε,_hε1,V,hV,hKV,Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,hΦform⟩ :=
    exists_compact_short_exact_moser hΓ hK hinv
  have hS : IsOpen {p : ℝ × M | p.2∈V ∧ Φ p∈U} :=
    (hV.preimage continuous_snd).inter (hU.preimage hΦ.continuous)
  have hKS : ({0}:Set ℝ)×ˢK⊆{p : ℝ × M | p.2∈V ∧ Φ p∈U} := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    exact ⟨hKV hx,by simpa only [hΦ0] using hKU hx⟩
  obtain ⟨T,W,hT,hW,h0T,hKW,hTW⟩ := generalized_tube_lemma isCompact_singleton hK hS hKS
  obtain ⟨η,hη,hηT⟩ := Metric.isOpen_iff.mp hT 0 (h0T (mem_singleton 0))
  let t : ℝ := min (η/2) (min ε δ)
  have ht : 0<t := lt_min (by positivity) (lt_min hε hδ)
  have htη : t≤η/2 := min_le_left _ _
  have htε : t≤ε := (min_le_right _ _).trans (min_le_left _ _)
  have htδ : t≤δ := (min_le_right _ _).trans (min_le_right _ _)
  have htT : t∈T := hηT (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
    linarith)
  have hstay (x : M) (hx : x∈W) : x∈V ∧ Φ (t,x)∈U :=
    hTW (show (t,x)∈T×ˢW from ⟨htT,hx⟩)
  have hφ := hΦ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  have hψ := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  have hφemb : Topology.IsEmbedding (fun x : M => Φ (t,x)) := by
    apply Topology.IsEmbedding.of_comp hφ.continuous hψ.continuous
    have he : (fun x : M => Ψ (t,Φ (t,x)))=id := funext fun x => (hΦinv t ⟨ht.le,htε⟩ x).1
    change Topology.IsEmbedding (fun x : M => Ψ (t,Φ (t,x)))
    rw [he]
    exact Topology.IsEmbedding.id
  have ha := hA.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  let g : M → N := (fun x => A (t,x)) ∘ (fun x => Φ (t,x))
  refine ⟨t,⟨ht,htδ⟩,g,W,hW,hKW,ha.comp hφ,?_,?_⟩
  · exact (hemb t ⟨ht,htδ⟩).comp
      ((hφemb.comp Topology.IsEmbedding.subtypeVal).codRestrict U (fun x : W => (hstay x.val x.property).2))
  · intro x hx v w
    have hd := mfderiv_comp x (ha.mdifferentiable (by simp) (Φ (t,x)))
      (hφ.mdifferentiable (by simp) x)
    change Ω t (A (t,Φ (t,x))) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=_
    change Ω t (A (t,Φ (t,x)))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ((A ∘ fun y => (t,y)) ∘ (Φ ∘ fun y => (t,y))) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ((A ∘ fun y => (t,y)) ∘ (Φ ∘ fun y => (t,y))) x w)=_
    rw [hd]
    have hf := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
      B (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (t,y)) x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (t,y)) x w))
      (hform t ⟨ht,htδ⟩ (Φ (t,x)) (hstay x hx).2)
    exact hf.symm.trans (hΦform t ⟨ht.le,htε⟩ x (hstay x hx).1 v w)

 theorem exists_compact_exact_fibre_embedding_into {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
    (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
    {T : Set N} (hinto : ∀ t∈Ioc (0:ℝ) δ,MapsTo (fun x => A (t,x)) U T)
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
      manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
    ∃ t∈Ioc (0:ℝ) δ,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      MapsTo g W T ∧ ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w := by
  obtain ⟨ε,hε,_hε1,V,hV,hKV,Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,hΦform⟩ :=
    exists_compact_short_exact_moser hΓ hK hinv
  have hS : IsOpen {p : ℝ × M | p.2∈V ∧ Φ p∈U} :=
    (hV.preimage continuous_snd).inter (hU.preimage hΦ.continuous)
  have hKS : ({0}:Set ℝ)×ˢK⊆{p : ℝ × M | p.2∈V ∧ Φ p∈U} := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    exact ⟨hKV hx,by simpa only [hΦ0] using hKU hx⟩
  obtain ⟨T,W,hT,hW,h0T,hKW,hTW⟩ := generalized_tube_lemma isCompact_singleton hK hS hKS
  obtain ⟨η,hη,hηT⟩ := Metric.isOpen_iff.mp hT 0 (h0T (mem_singleton 0))
  let t : ℝ := min (η/2) (min ε δ)
  have ht : 0<t := lt_min (by positivity) (lt_min hε hδ)
  have htη : t≤η/2 := min_le_left _ _
  have htε : t≤ε := (min_le_right _ _).trans (min_le_left _ _)
  have htδ : t≤δ := (min_le_right _ _).trans (min_le_right _ _)
  have htT : t∈T := hηT (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
    linarith)
  have hstay (x : M) (hx : x∈W) : x∈V ∧ Φ (t,x)∈U :=
    hTW (show (t,x)∈T×ˢW from ⟨htT,hx⟩)
  have hφ := hΦ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  have hψ := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  have hφemb : Topology.IsEmbedding (fun x : M => Φ (t,x)) := by
    apply Topology.IsEmbedding.of_comp hφ.continuous hψ.continuous
    have he : (fun x : M => Ψ (t,Φ (t,x)))=id := funext fun x => (hΦinv t ⟨ht.le,htε⟩ x).1
    change Topology.IsEmbedding (fun x : M => Ψ (t,Φ (t,x)))
    rw [he]
    exact Topology.IsEmbedding.id
  have ha := hA.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  let g : M → N := (fun x => A (t,x)) ∘ (fun x => Φ (t,x))
  refine ⟨t,⟨ht,htδ⟩,g,W,hW,hKW,ha.comp hφ,?_,?_,?_⟩
  · exact (hemb t ⟨ht,htδ⟩).comp
      ((hφemb.comp Topology.IsEmbedding.subtypeVal).codRestrict U (fun x : W => (hstay x.val x.property).2))
  · intro x hx
    exact hinto t ⟨ht,htδ⟩ (hstay x hx).2
  · intro x hx v w
    have hd := mfderiv_comp x (ha.mdifferentiable (by simp) (Φ (t,x)))
      (hφ.mdifferentiable (by simp) x)
    change Ω t (A (t,Φ (t,x))) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=_
    change Ω t (A (t,Φ (t,x)))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ((A ∘ fun y => (t,y)) ∘ (Φ ∘ fun y => (t,y))) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ((A ∘ fun y => (t,y)) ∘ (Φ ∘ fun y => (t,y))) x w)=_
    rw [hd]
    have hf := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
      B (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (t,y)) x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (t,y)) x w))
      (hform t ⟨ht,htδ⟩ (Φ (t,x)) (hstay x hx).2)
    exact hf.symm.trans (hΦform t ⟨ht.le,htε⟩ x (hstay x hx).1 v w)

 theorem exists_compact_exact_fibre_embedding_central_into {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
    (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
    {T : Set N} (hT : IsOpen T) (hinto : MapsTo (fun x => A (0,x)) K T)
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
      manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
    ∃ t∈Ioc (0:ℝ) δ,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      MapsTo g W T ∧ ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w := by
  have hS : IsOpen (A ⁻¹' T) := hT.preimage hA.continuous
  have hKS : ({0}:Set ℝ)×ˢK⊆A ⁻¹' T := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    exact hinto hx
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hS hKS
  obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  let δ' := min δ (η/2)
  have hδ' : 0<δ' := lt_min hδ (by positivity)
  have htδ {t : ℝ} (ht : t∈Ioc (0:ℝ) δ') : t∈Ioc (0:ℝ) δ :=
    ⟨ht.1,ht.2.trans (min_le_left _ _)⟩
  have htV {t : ℝ} (ht : t∈Ioc (0:ℝ) δ') : t∈V := by
    apply hηV
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1]
    have h := ht.2.trans (min_le_right δ (η/2))
    linarith
  obtain ⟨t,ht,g,O,hO,hKO,hg,hge,hgT,hgf⟩ :=
    exists_compact_exact_fibre_embedding_into hΓ hK hinv (hU.inter hW)
      (fun x hx => ⟨hKU hx,hKW hx⟩) hδ' hA
      (fun t ht => (hemb t (htδ ht)).comp (Topology.IsEmbedding.inclusion inter_subset_left))
      (fun t ht x hx => hVW ⟨htV ht,hx.2⟩) Ω
      (fun t ht x hx => hform t (htδ ht) x hx.1)
  exact ⟨t,htδ ht,g,O,hO,hKO,hg,hge,hgT,hgf⟩

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

abbrev CubicPhysicalModel := RealModel × PlanePhase (Fin 2)
abbrev CubicPhysicalSpace := BaseCurve × PlanePhase (Fin 2)

def cubicPhysicalForm {A B : ℕ} (D S : ℕ) (L : ℝ) : ManifoldTwoForm CubicPhysicalModel CubicPhysicalSpace :=
  globalHorizontalCoupling phaseArea (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)

 theorem exists_actual_cubic_normal_transfer_into {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0<L) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hKd : ∀ p∈K,physicalParameter L (planeMoments p.2)∈lowerTrapezoid A B)
    (hinv : ∀ p∈K,(cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible)
    {T : Set CubicAmbient} (hT : IsOpen T)
    (hbase : ∀ x : BaseCurve,∀ z : ℂ,(inclusion x,z)∈T) :
    ∃ t : ℝ,0<t ∧ ∃ g : CubicPhysicalSpace → CubicAmbient,∃ W : Set CubicPhysicalSpace,
      IsOpen W ∧ K⊆W ∧ ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) ∞ g ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧ MapsTo g W T ∧
      ∀ x∈W,∀ v w,cubicAmbientForm (A := A) (B := B) D S (1/(L*Real.pi)) t (g x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x v)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x w)=
        cubicPhysicalForm (A := A) (B := B) D S L x v w := by
  let : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞
      (fun x : BaseCurve => coefficientSquares (cubicCoefficients D S x)) :=
    coefficientSquares_contDiff.contMDiff.comp (cubicCoefficients_smooth D S)
  have hapos (x : BaseCurve) (i : TrapezoidWeight A B) :
      0<coefficientSquares (cubicCoefficients D S x) i := by
    rw [cubicCoefficients_squares]
    exact coefficientNorm_pos _ _ _
  obtain ⟨Ξ,hΞ,hΞfst,V,hV,hKV,hVd,hΞemb,hΞeq⟩ :=
    exists_compact_physical_radial_bridge hA hAB ha hapos hL hK
      (fun p hp => (physicalDiskCoordinates_mem hL.le p.2).mpr (hKd p hp))
  have hIK : IsCompact (Ξ '' K) := hK.image hΞ.continuous
  obtain ⟨Ψ,Γ,δ,hδ,U,hU,hUK,hΨ,hΨ0,hΓ,hΓ0,hΨemb,hΓform⟩ :=
    exists_actual_cubic_exact_family_with_zero (A := A) (B := B) D S (1/(L*Real.pi))
      (hIK.image continuous_fst) (hIK.image continuous_snd)
  have hKU : MapsTo Ξ K U := by
    intro x hx
    exact hUK ⟨⟨Ξ x,⟨x,hx,rfl⟩,rfl⟩,⟨Ξ x,⟨x,hx,rfl⟩,rfl⟩⟩
  let Δ : ℝ → ManifoldOneForm CubicPhysicalModel CubicPhysicalSpace := manifoldPullbackOneForm Γ Ξ
  have hΔ : SmoothOneFormFamily Δ := manifoldPullbackOneForm_smooth hΞ hΓ
  have hΔ0 (x : CubicPhysicalSpace) (hx : x∈V) : Δ 0 x=
      (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)+
        (verticalLiouville : ManifoldOneForm CubicPhysicalModel CubicPhysicalSpace)) x := by
    have h := cubic_radial_primitive hA hAB D S hL hΞ hΞfst
      ((physicalDiskCoordinates_mem hL.le x.2).mp (hVd x hx))
      (by filter_upwards [hV.mem_nhds hx] with y hy; exact hΞeq y hy)
    simpa only [Δ,manifoldPullbackOneForm,hΓ0] using h
  have hΔext (x : CubicPhysicalSpace) (hx : x∈V) :
      manifoldExteriorOneForm (Δ 0) x=cubicPhysicalForm (A := A) (B := B) D S L x := by
    apply coupling_exterior_of_primitive_germ (hΔ.comp (contDiff_const (c := (0:ℝ))))
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hΔ0 y hy
  have hnondeg (x : CubicPhysicalSpace) (hx : x∈K) : (manifoldExteriorOneForm (Δ 0) x).IsInvertible := by
    rw [hΔext x (hKV hx)]
    exact hinv x hx
  let F : ℝ × CubicPhysicalSpace → CubicAmbient := fun p => Ψ (p.1,Ξ p.2)
  have hF : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞ F :=
    hΨ.comp (contMDiff_fst.prodMk (hΞ.comp contMDiff_snd))
  let O := V∩Ξ ⁻¹' U
  have hO : IsOpen O := hV.inter (hU.preimage hΞ.continuous)
  have hKO : K⊆O := fun x hx => ⟨hKV hx,hKU hx⟩
  have htI {t : ℝ} (ht : t∈Ioc (0:ℝ) δ) : t∈Icc (-δ) δ := ⟨by linarith [ht.1],ht.2⟩
  have hFemb (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) : Topology.IsEmbedding (fun x : O => F (t,x.val)) :=
    (hΨemb t (htI ht) (ne_of_gt ht.1)).comp
      (((hΞemb.comp (Topology.IsEmbedding.inclusion inter_subset_left)).codRestrict U)
        (fun x : O => x.property.2))
  have hFform (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) (x : CubicPhysicalSpace) (hx : x∈O) :
      manifoldExteriorOneForm (Δ t) x=(cubicAmbientForm (A := A) (B := B) D S (1/(L*Real.pi)) t (F (t,x))).bilinearComp
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) (fun y => F (t,y)) x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) (fun y => F (t,y)) x) := by
    have hs := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun y : CubicConeSpace => (t,y))
    have he := manifold_pullback_exterior (fun c y hy => (hΓ.spatial_smooth t c hy).contDiffWithinAt) hΞ x
    change manifoldExteriorOneForm (Δ t) x=
      (manifoldExteriorOneForm (Γ t) (Ξ x)).bilinearComp
        (manifoldMapDifferential (E := CubicConeModel) (F := CubicPhysicalModel) Ξ x)
        (manifoldMapDifferential (E := CubicConeModel) (F := CubicPhysicalModel) Ξ x) at he
    rw [he,hΓform t (htI ht) (ne_of_gt ht.1) (Ξ x) hx.2]
    have hdiff := manifoldMapDifferential_comp
      (hs.mdifferentiable (by simp) (Ξ x)) (hΞ.mdifferentiable (by simp) x)
    change manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) (fun y => F (t,y)) x=_ at hdiff
    rw [hdiff]
    rfl
  have hF0 : MapsTo (fun x => F (0,x)) K T := by
    intro x _hx
    change Ψ (0,Ξ x)∈T
    rw [hΨ0]
    exact hbase _ _
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgT,hgform⟩ := exists_compact_exact_fibre_embedding_central_into
    hΔ hK hnondeg hO hKO hδ hF hFemb hT hF0
      (fun t => cubicAmbientForm (A := A) (B := B) D S (1/(L*Real.pi)) t) hFform
  refine ⟨t,ht.1,g,W∩V,hW.inter hV,fun x hx => ⟨hKW hx,hKV hx⟩,hg,
    hgemb.comp (Topology.IsEmbedding.inclusion inter_subset_left),fun x hx => hgT hx.1,?_⟩
  intro x hx v w
  have he := hgform x hx.1 v w
  rw [hΔext x hx.2] at he
  exact he

 theorem exists_actual_cubic_normal_transfer {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0<L) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hKd : ∀ p∈K,physicalParameter L (planeMoments p.2)∈lowerTrapezoid A B)
    (hinv : ∀ p∈K,(cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible) :
    ∃ t : ℝ,0<t ∧ ∃ g : CubicPhysicalSpace → CubicAmbient,∃ W : Set CubicPhysicalSpace,
      IsOpen W ∧ K⊆W ∧ ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) ∞ g ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧
      ∀ x∈W,∀ v w,cubicAmbientForm (A := A) (B := B) D S (1/(L*Real.pi)) t (g x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x v)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x w)=
        cubicPhysicalForm (A := A) (B := B) D S L x v w := by
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,_hgT,hgform⟩ :=
    exists_actual_cubic_normal_transfer_into hA hAB D S hL hK hKd hinv isOpen_univ
      (fun _ _ => mem_univ _)
  exact ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgform⟩

 def cubicAffineDomain : Set CubicAmbient := {p | p.1.1≠0 ∧ p.1.2≠0}

 theorem cubicAffineDomain_isOpen : IsOpen cubicAffineDomain :=
  (isOpen_ne_fun (continuous_fst.fst) continuous_const).inter
    (isOpen_ne_fun (continuous_fst.snd) continuous_const)

 theorem inclusion_mem_cubicAffineDomain (x : BaseCurve) (z : ℂ) :
    (inclusion x,z)∈cubicAffineDomain :=
  ⟨inclusion_fst_ne_zero x,inclusion_snd_ne_zero x⟩

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

 theorem productForm_isInvertible {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {A : V →L[ℝ] V →L[ℝ] ℝ} (hA : A.IsInvertible) :
    (productForm A).IsInvertible := by
  have he : oneCovectorForm A 1 0=productForm A := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp [oneCovectorForm_apply,productForm_apply,planarArea_apply]
    ring
  rw [←he]
  exact oneCovectorForm_isInvertible hA one_ne_zero 0

 theorem successorStandardForm_isInvertible (m : ℕ) : (successorStandardForm m).IsInvertible :=
  bilinearComp_equiv_isInvertible (complexSplitPhase m) (productForm_isInvertible phaseArea_isInvertible)

 theorem isInvertible_of_bilinearComp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E=Module.finrank ℝ F)
    {A : F →L[ℝ] F →L[ℝ] ℝ} {L : E →L[ℝ] F}
    (h : (A.bilinearComp L L).IsInvertible) : A.IsInvertible := by
  obtain ⟨e,he⟩ := h
  have hL : Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    apply e.injective
    change (e : E →L[ℝ] E →L[ℝ] ℝ) v=(e : E →L[ℝ] E →L[ℝ] ℝ) 0
    rw [he]
    ext w
    simp [ContinuousLinearMap.bilinearComp_apply,hv]
  let c : E ≃L[ℝ] F := (L.toLinearMap.linearEquivOfInjective hL hdim).toContinuousLinearEquiv
  have hc : (c : E →L[ℝ] F)=L := by ext v; rfl
  apply (bilinearComp_equiv_isInvertible_iff c).mp
  rw [hc]
  exact ⟨e,he⟩

 theorem FormNeighborhoodEmbedding.target_invertible
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    {K : Set N} {σ : ManifoldTwoForm F N} {Ω : ManifoldTwoForm E M} {f : N → M}
    (hf : FormNeighborhoodEmbedding K σ Ω f) (hdim : Module.finrank ℝ F=Module.finrank ℝ E)
    {x : N} (hx : x∈K) (hσ : (σ x).IsInvertible) : (Ω (f x)).IsInvertible := by
  obtain ⟨U,_hU,hKU,_hs,_he,hform⟩ := hf
  apply isInvertible_of_bilinearComp (E := F) (F := E) hdim
    (L := manifoldMapDifferential (E := E) (F := F) f x)
  have hh : (Ω (f x)).bilinearComp (manifoldMapDifferential (E := E) (F := F) f x)
      (manifoldMapDifferential (E := E) (F := F) f x)=σ x := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact hform x (hKU hx) v w
  rw [hh]
  exact hσ

end PackingSufficiencySupport.Hamiltonian
end

end OAI
