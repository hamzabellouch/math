import Mathlib
import OAI.Geometry.BallPacking.Toric.RadialDiskSmooth
import OAI.Geometry.BallPacking.Normal.MovingPrimitiveNaturality

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

abbrev CubicConeModel := RealModel × DiskPair
abbrev CubicConeSpace := BaseCurve × DiskPair
abbrev CubicConeTarget := PlaneBase × DiskPair
abbrev CubicAmbient := PlaneBase × ℂ

 def ambientWeightedCoefficient (D m : ℕ) (z : PlaneBase) : WeightedHomogeneousIndex → ℂ :=
  complexAffineLift ((complexCartesian (ι := Option (Fin 3))).symm
    (affinePhase 3 (weightedProjection D m z)))

 theorem ambientWeightedCoefficient_smooth (D m : ℕ) :
    ContDiff ℝ ∞ (ambientWeightedCoefficient D m) :=
  complexAffineLift_smooth.comp ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.comp
    ((affinePhase 3).contDiff.comp ((weightedProjection_contDiff D m).restrict_scalars ℝ)))

 theorem ambientWeightedCoefficient_restrict (D m : ℕ) (x : BaseCurve) :
    ambientWeightedCoefficient D m (inclusion x)=weightedCoefficient D m x := rfl

 theorem ambientWeightedCoefficient_none (D m : ℕ) (x : PlaneBase) :
    ambientWeightedCoefficient D m x none=1 := rfl

 def conePolynomial {A B : ℕ} (D S : ℕ) (p : CubicConeTarget) :
    TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  toricLift latticeIndex (fun i => ambientWeightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) p.1) p.2

 theorem conePolynomial_smooth {A B : ℕ} (D S : ℕ) :
    ContDiff ℝ ∞ (conePolynomial (A := A) (B := B) D S) := by
  apply contDiff_pi.mpr
  intro ij
  change ContDiff ℝ ∞ (fun p : CubicConeTarget => p.2.1^(latticeIndex ij.1).1 *
    p.2.2^(latticeIndex ij.1).2 * ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2)
  have hc : ContDiff ℝ ∞ (fun p : CubicConeTarget =>
      ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2) :=
    (contDiff_apply ℝ ℂ ij.2).comp
    ((ambientWeightedCoefficient_smooth (cubicDegree D ij.1) (cubicMarkedOrder S ij.1)).comp contDiff_fst)
  exact (((contDiff_snd.fst).pow _).mul ((contDiff_snd.snd).pow _)).mul hc

 theorem conePolynomial_nonzero {A B : ℕ} (D S : ℕ) (p : CubicConeTarget) :
    complexCartesian (conePolynomial (A := A) (B := B) D S p)≠0 := by
  obtain ⟨i,hi⟩ := lattice_zero A B
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) (i,none)
  have hh : conePolynomial (A := A) (B := B) D S p (i,none)=1 := by
    change p.2.1^(latticeIndex i).1*p.2.2^(latticeIndex i).2*
      ambientWeightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) p.1 none=1
    rw [hi,ambientWeightedCoefficient_none]
    simp
  rw [hh] at he
  exact one_ne_zero he

 def cubicConePrimitive {A B : ℕ} (D S : ℕ) (c : ℝ) : CubicConeTarget → CubicConeTarget →L[ℝ] ℝ :=
  primitivePullback (hopfPrimitive c) (complexCartesian ∘ conePolynomial (A := A) (B := B) D S)

 theorem cubicConePrimitive_smooth {A B : ℕ} (D S : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (cubicConePrimitive (A := A) (B := B) D S c) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact primitivePullback_smoothAt (hopfPrimitive_smoothAt c (conePolynomial_nonzero D S p))
    (((complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).contDiff.comp
      (conePolynomial_smooth D S)).contDiffAt)

 def cubicNormalCoordinates (t : ℝ) (p : CubicAmbient) : CubicConeTarget :=
  (p.1,(p.2,t⁻¹ • polynomial p.1))

 theorem cubicNormalCoordinates_smooth (t : ℝ) : ContDiff ℝ ∞ (cubicNormalCoordinates t) :=
  contDiff_fst.prodMk (contDiff_snd.prodMk (((polynomial_contDiff.restrict_scalars ℝ).comp contDiff_fst).const_smul _))

 def cubicAmbientPrimitive {A B : ℕ} (D S : ℕ) (c t : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
  primitivePullback (cubicConePrimitive (A := A) (B := B) D S c) (cubicNormalCoordinates t)

 def cubicAmbientForm {A B : ℕ} (D S : ℕ) (c t : ℝ) :=
  euclideanExteriorOneForm (cubicAmbientPrimitive (A := A) (B := B) D S c t)

 def centralCubicCoordinates (p : CubicConeSpace) : CubicConeTarget := (inclusion p.1,p.2)

 def centralCubicPrimitive {A B : ℕ} (D S : ℕ) (c : ℝ) : ManifoldOneForm CubicConeModel CubicConeSpace :=
  manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S c) centralCubicCoordinates 0

 theorem centralCubicCoordinates_smooth :
    ContMDiff 𝓘(ℝ,CubicConeModel) 𝓘(ℝ,CubicConeTarget) ∞ centralCubicCoordinates :=
  (inclusion_real_contMDiff.comp (flatProduct_fst_smooth (V := DiskPair))).prodMk_space
    (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve))

 theorem exists_actual_cubic_exact_family_with_zero {A B : ℕ} (D S : ℕ) (c : ℝ)
    {K : Set BaseCurve} {H : Set DiskPair} (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Φ : ℝ × CubicConeSpace → CubicAmbient,
      ∃ Γ : ℝ → ManifoldOneForm CubicConeModel CubicConeSpace,
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set CubicConeSpace,IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicAmbient) ∞ Φ ∧
      (∀ p,Φ (0,p)=(inclusion p.1,p.2.1)) ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralCubicPrimitive (A := A) (B := B) D S c ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Φ (t,p.val))) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        manifoldExteriorOneForm (Γ t) p=
          (cubicAmbientForm (A := A) (B := B) D S c t (Φ (t,p))).bilinearComp
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p)
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p) := by
  obtain ⟨Ψ,ε,hε,O,hO,hKO,hΨ,hΨ0,hEQ,hemb⟩ :=
    exists_actual_cubic_normal_tube hK (hH.image continuous_snd)
  have hxs : ContMDiff 𝓘(ℝ,CubicConeModel) ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ)) ∞
      (fun p : CubicConeSpace => (p.1,p.2.2)) :=
    (flatProduct_fst_smooth (V := DiskPair)).prodMk
      (contDiff_snd.contMDiff.comp (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve)))
  have hν : ContMDiff 𝓘(ℝ,CubicConeModel) 𝓘(ℝ,ℂ) ∞ (fun p : CubicConeSpace => p.2.1) :=
    contDiff_fst.contMDiff.comp (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve))
  let Φ : ℝ × CubicConeSpace → CubicAmbient := fun p => (Ψ (p.1,(p.2.1,p.2.2.2)),p.2.2.1)
  have hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicAmbient) ∞ Φ :=
    (hΨ.comp (contMDiff_fst.prodMk (hxs.comp contMDiff_snd))).prodMk_space (hν.comp contMDiff_snd)
  let g : ℝ × CubicConeSpace → CubicConeTarget := fun p => ((Φ p).1,p.2.2)
  have hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicConeTarget) ∞ g :=
    (contDiff_fst.contMDiff.comp hΦ).prodMk_space
      ((flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := DiskPair)).comp contMDiff_snd)
  let Γ := movingPrimitivePullback (E := CubicConeModel) (cubicConePrimitive (A := A) (B := B) D S c) g
  let U : Set CubicConeSpace := (fun p : CubicConeSpace => (p.1,p.2.2)) ⁻¹' O
  have hU : IsOpen U := hO.preimage hxs.continuous
  refine ⟨Φ,Γ,ε,hε,U,hU,?_,hΦ,?_,movingPrimitivePullback_smooth (cubicConePrimitive_smooth D S c) hg,?_,?_,?_⟩
  · intro p hp
    exact hKO ⟨hp.1,mem_image_of_mem _ hp.2⟩
  · intro p
    change (Ψ (0,(p.1,p.2.2)),p.2.1)=(inclusion p.1,p.2.1)
    rw [hΨ0]
  · have he : (fun p : CubicConeSpace => g (0,p))=centralCubicCoordinates := by
      funext p
      change (Ψ (0,(p.1,p.2.2)),p.2)=(inclusion p.1,p.2)
      rw [hΨ0]
    change manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S c)
      (fun p => g (0,p)) 0=centralCubicPrimitive (A := A) (B := B) D S c
    rw [he]
    rfl
  · intro t ht ht0
    let J : U → O × ℂ := fun p => (⟨(p.val.1,p.val.2.2),p.property⟩,p.val.2.1)
    have hJ : Topology.IsEmbedding J := by
      let e : CubicConeSpace ≃ₜ (BaseCurve × ℂ) × ℂ :=
        { toFun := fun p => ((p.1,p.2.2),p.2.1)
          invFun := fun p => (p.1.1,(p.2,p.1.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          continuous_toFun := (continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst
          continuous_invFun := continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd) }
      have hc : Continuous J :=
        ((continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.snd).subtype_mk
          (fun p => p.property)).prodMk continuous_subtype_val.snd.fst
      exact Topology.IsEmbedding.of_comp hc (continuous_subtype_val.prodMap continuous_id)
        (e.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
    exact ((hemb t ht ht0).prodMap Topology.IsEmbedding.id).comp hJ
  · intro t ht ht0 p hp
    have he : (fun q => g (t,q))=ᶠ[𝓝 p] cubicNormalCoordinates t ∘ (fun q => Φ (t,q)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      change (Ψ (t,(q.1,q.2.2)),q.2)=
        (Ψ (t,(q.1,q.2.2)),(q.2.1,t⁻¹ • polynomial (Ψ (t,(q.1,q.2.2)))))
      rw [hEQ _ hq t ht,smul_smul,inv_mul_cancel₀ ht0,one_smul]
    exact movingPrimitivePullback_exterior_comp (cubicConePrimitive_smooth D S c) hg
      (cubicNormalCoordinates_smooth t) (hΦ.comp (contMDiff_const.prodMk contMDiff_id)) he

 theorem exists_actual_cubic_exact_family {A B : ℕ} (D S : ℕ) (c : ℝ)
    {K : Set BaseCurve} {H : Set DiskPair} (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Φ : ℝ × CubicConeSpace → CubicAmbient,
      ∃ Γ : ℝ → ManifoldOneForm CubicConeModel CubicConeSpace,
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set CubicConeSpace,IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicAmbient) ∞ Φ ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralCubicPrimitive (A := A) (B := B) D S c ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Φ (t,p.val))) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        manifoldExteriorOneForm (Γ t) p=
          (cubicAmbientForm (A := A) (B := B) D S c t (Φ (t,p))).bilinearComp
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p)
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p) := by
  obtain ⟨Φ,Γ,ε,hε,U,hU,hKU,hΦ,_hΦ0,hΓ,hΓ0,hemb,hform⟩ :=
    exists_actual_cubic_exact_family_with_zero (A := A) (B := B) D S c hK hH
  exact ⟨Φ,Γ,ε,hε,U,hU,hKU,hΦ,hΓ,hΓ0,hemb,hform⟩

 def physicalDiskRecovery (L : ℝ) (z : DiskPair) : PlanePhase (Fin 2) :=
  (Real.sqrt (L*Real.pi))⁻¹ • complexCartesian ![z.1,z.2]

 theorem physicalDiskRecovery_smooth (L : ℝ) : ContDiff ℝ ∞ (physicalDiskRecovery L) := by
  apply ContDiff.const_smul
  apply (complexCartesian (ι := Fin 2)).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd

 theorem physicalDiskRecovery_left {L : ℝ} (hL : 0<L) (z : PlanePhase (Fin 2)) :
    physicalDiskRecovery L (physicalDiskCoordinates L z)=z := by
  have hs : Real.sqrt (L*Real.pi)≠0 := (Real.sqrt_pos.mpr (mul_pos hL Real.pi_pos)).ne'
  have he : complexCartesian ![(physicalDiskCoordinates L z).1,(physicalDiskCoordinates L z).2]=
      Real.sqrt (L*Real.pi) • z := by
    funext i
    fin_cases i <;> apply Prod.ext <;> simp [physicalDiskCoordinates_apply,complexCartesian_apply]
  rw [physicalDiskRecovery,he,smul_smul,inv_mul_cancel₀ hs,one_smul]

 theorem physicalDiskRecovery_right {L : ℝ} (hL : 0<L) (z : DiskPair) :
    physicalDiskCoordinates L (physicalDiskRecovery L z)=z := by
  have hs : Real.sqrt (L*Real.pi)≠0 := (Real.sqrt_pos.mpr (mul_pos hL Real.pi_pos)).ne'
  apply Prod.ext <;> apply Complex.ext <;>
    simp [physicalDiskCoordinates_apply,physicalDiskRecovery,complexCartesian_apply,
      hs]

 theorem physicalDiskCoordinates_isEmbedding {L : ℝ} (hL : 0<L) :
    Topology.IsEmbedding (physicalDiskCoordinates L) := by
  apply Topology.IsEmbedding.of_comp (physicalDiskCoordinates L).continuous (physicalDiskRecovery_smooth L).continuous
  have he : physicalDiskRecovery L ∘ physicalDiskCoordinates L=id := funext (physicalDiskRecovery_left hL)
  rw [he]
  exact Topology.IsEmbedding.id

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem exists_compact_physical_radial_bridge {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : M → TrapezoidWeight A B → ℝ}
    (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞ a)
    (hapos : ∀ x i,0<a x i) {L : ℝ} (hL : 0<L)
    {K : Set (M × PlanePhase (Fin 2))} (hK : IsCompact K)
    (hKd : ∀ p∈K,physicalDiskCoordinates L p.2∈diskDomain A B) :
    ∃ Ξ : M × PlanePhase (Fin 2) → M × DiskPair,
      ContMDiff 𝓘(ℝ,E × PlanePhase (Fin 2)) 𝓘(ℝ,E × DiskPair) ∞ Ξ ∧
      (∀ p,(Ξ p).1=p.1) ∧
      ∃ D : Set (M × PlanePhase (Fin 2)),IsOpen D ∧ K⊆D ∧
        (∀ p∈D,physicalDiskCoordinates L p.2∈diskDomain A B) ∧
        Topology.IsEmbedding (fun p : D => Ξ p.val) ∧
        ∀ p∈D,(Ξ p).2=diskInverse latticeIndex (a p.1) (physicalDiskCoordinates L p.2) := by
  let F : M × PlanePhase (Fin 2) → (TrapezoidWeight A B → ℝ) × DiskPair :=
    fun p => (a p.1,physicalDiskCoordinates L p.2)
  have hF : ContMDiff 𝓘(ℝ,E × PlanePhase (Fin 2))
      𝓘(ℝ,(TrapezoidWeight A B → ℝ) × DiskPair) ∞ F :=
    (ha.comp (flatProduct_fst_smooth (V := PlanePhase (Fin 2)))).prodMk_space
      ((physicalDiskCoordinates L).contDiff.contMDiff.comp (flatProduct_snd_smooth (E := E) (M := M)))
  let U : Set ((TrapezoidWeight A B → ℝ) × DiskPair) :=
    {p | (∀ i,0<p.1 i) ∧ p.2∈diskDomain A B}
  have hU : IsOpen U := positiveCoefficients_isOpen.prod (diskDomain_isOpen A B)
  have hFu : F '' K⊆U := by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨hapos p.1,hKd p hp⟩
  have hi : ContDiffOn ℝ ∞ (fun p : (TrapezoidWeight A B → ℝ) × DiskPair =>
      diskInverse latticeIndex p.1 p.2) U :=
    fun p hp => (diskInverse_contDiffAt hA hAB hp.1 hp.2).contDiffWithinAt
  obtain ⟨χ,_hχ,_hχc,_hχU,_hχr,_hχ1,hg,_hgc,hge⟩ :=
    exists_smooth_compact_extension (hK.image hF.continuous) hU hFu hi
  let g : (TrapezoidWeight A B → ℝ) × DiskPair → DiskPair :=
    fun p => χ p • diskInverse latticeIndex p.1 p.2
  obtain ⟨O,hO,hKO,hOg⟩ := mem_nhdsSet_iff_exists.mp hge
  let D : Set (M × PlanePhase (Fin 2)) := F ⁻¹' (O∩U)
  have hD : IsOpen D := (hO.inter hU).preimage hF.continuous
  let Ξ : M × PlanePhase (Fin 2) → M × DiskPair := fun p => (p.1,g (F p))
  have hΞ : ContMDiff 𝓘(ℝ,E × PlanePhase (Fin 2)) 𝓘(ℝ,E × DiskPair) ∞ Ξ := by
    rw [show 𝓘(ℝ,E × DiskPair)=(𝓘(ℝ,E)).prod 𝓘(ℝ,DiskPair) from modelWithCornersSelf_prod]
    exact (flatProduct_fst_smooth (E := E) (M := M) (V := PlanePhase (Fin 2))).prodMk
      (hg.contMDiff.comp hF)
  let R : M × DiskPair → M × PlanePhase (Fin 2) :=
    fun p => (p.1,physicalDiskRecovery L (diskForward latticeIndex (a p.1) p.2))
  have hforward : ContMDiff 𝓘(ℝ,E × DiskPair) 𝓘(ℝ,DiskPair) ∞
      (fun p : M × DiskPair => diskForward latticeIndex (a p.1) p.2) := by
    have hp := (ha.comp (flatProduct_fst_smooth (V := DiskPair))).prodMk_space
      (flatProduct_snd_smooth (E := E) (M := M) (V := DiskPair))
    intro p
    exact (diskForward_contDiffAt (hapos p.1) (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) p.2).contMDiffAt.comp p hp.contMDiffAt
  have hR : Continuous R := continuous_fst.prodMk
    ((physicalDiskRecovery_smooth L).continuous.comp hforward.continuous)
  have he (p : M × PlanePhase (Fin 2)) (hp : p∈D) :
      (Ξ p).2=diskInverse latticeIndex (a p.1) (physicalDiskCoordinates L p.2) := hOg hp.1
  have hRI (p : M × PlanePhase (Fin 2)) (hp : p∈D) : R (Ξ p)=p := by
    change (p.1,physicalDiskRecovery L (diskForward latticeIndex (a p.1) (Ξ p).2))=p
    rw [he p hp,diskForward_inverse (hapos p.1) (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
      (trapezoid_radial_surjective hAB (hapos p.1) (squaredRadii_mem_lower hp.2.2)),
      physicalDiskRecovery_left hL]
  refine ⟨Ξ,hΞ,fun _ => rfl,D,hD,?_,fun p hp => hp.2.2,?_,he⟩
  · intro p hp
    exact ⟨hKO (mem_image_of_mem F hp),hFu (mem_image_of_mem F hp)⟩
  · apply Topology.IsEmbedding.of_comp (hΞ.continuous.comp continuous_subtype_val) hR
    have he : R ∘ (fun p : D => Ξ p.val)=Subtype.val := funext fun p => hRI p.val p.property
    change Topology.IsEmbedding (R ∘ (fun p : D => Ξ p.val))
    rw [he]
    exact Topology.IsEmbedding.subtypeVal

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

 theorem manifoldPullbackOneForm_comp_at {g : N → G} {f : M → N} {x : M}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,G) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x) (α : G → G →L[ℝ] ℝ) :
    manifoldPullbackOneForm (E := F) (F := E)
        (fun _ => manifoldPullbackOneForm (E := G) (F := F) (fun _ => α) g 0) f 0 x=
      manifoldPullbackOneForm (E := G) (F := E) (fun _ => α) (g ∘ f) 0 x := by
  unfold manifoldPullbackOneForm
  rw [manifoldMapDifferential_comp hg hf]
  rfl

 theorem manifoldPullbackOneForm_primitive_at {g : F → G} {f : M → F} {x : M}
    (hg : DifferentiableAt ℝ g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x) (α : G → G →L[ℝ] ℝ) :
    manifoldPullbackOneForm (E := F) (F := E) (fun _ => primitivePullback α g) f 0 x=
      manifoldPullbackOneForm (E := G) (F := E) (fun _ => α) (g ∘ f) 0 x := by
  unfold manifoldPullbackOneForm primitivePullback manifoldMapDifferential
  rw [mfderiv_comp x hg.hasFDerivAt.hasMFDerivAt.mdifferentiableAt hf,mfderiv_eq_fderiv]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubic_radial_primitive {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ)
    {L : ℝ} (hL : 0<L)
    {Ξ : BaseCurve × PlanePhase (Fin 2) → CubicConeSpace}
    (hΞ : ContMDiff 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,CubicConeModel) ∞ Ξ)
    (hΞfst : ∀ p,(Ξ p).1=p.1) {x : BaseCurve × PlanePhase (Fin 2)}
    (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B)
    (he : ∀ᶠ q in 𝓝 x,(Ξ q).2=diskInverse latticeIndex
      (coefficientSquares (cubicCoefficients (A := A) (B := B) D S q.1)) (physicalDiskCoordinates L q.2)) :
    manifoldPullbackOneForm (fun _ => centralCubicPrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Ξ 0 x=
      (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2))
          (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)+
        (verticalLiouville : ManifoldOneForm (RealModel × PlanePhase (Fin 2)) (BaseCurve × PlanePhase (Fin 2)))) x := by
  let P := complexCartesian ∘ conePolynomial (A := A) (B := B) D S
  have hP : ContDiff ℝ ∞ P := (complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).contDiff.comp (conePolynomial_smooth D S)
  let Y := centralCubicCoordinates ∘ Ξ
  have hY : ContMDiff 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,CubicConeTarget) ∞ Y := centralCubicCoordinates_smooth.comp hΞ
  have hh := manifoldPullbackOneForm_comp_at (centralCubicCoordinates_smooth.mdifferentiable (by simp) (Ξ x))
    (hΞ.mdifferentiable (by simp) x) (cubicConePrimitive (A := A) (B := B) D S (1/(L*Real.pi)))
  change manifoldPullbackOneForm (fun _ => centralCubicPrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Ξ 0 x=
    manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Y 0 x at hh
  rw [hh]
  have hpull := manifoldPullbackOneForm_primitive_at (hP.differentiable (by simp) (Y x))
    (hY.mdifferentiable (by simp) x) (hopfPrimitive (1/(L*Real.pi)))
  change manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Y 0 x=_ at hpull
  rw [hpull]
  have heP : P ∘ Y=ᶠ[𝓝 x] complexCartesian ∘ physicalPolynomialLift (A := A) (B := B) D S L := by
    filter_upwards [he] with q hq
    change complexCartesian (toricLift latticeIndex
      (fun i => ambientWeightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) (inclusion (Ξ q).1)) (Ξ q).2)=_
    rw [hΞfst,hq]
    rfl
  have hQ := (physicalPolynomialLift_smoothAt hA hAB D S hL.le hx).mdifferentiableAt (by simp)
  apply ContinuousLinearMap.ext
  intro v
  unfold manifoldPullbackOneForm manifoldMapDifferential
  rw [heP.eq_of_nhds,heP.mfderiv_eq,mfderiv_comp x
    ((complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).hasFDerivAt.hasMFDerivAt.mdifferentiableAt) hQ,
    mfderiv_eq_fderiv,ContinuousLinearEquiv.fderiv]
  exact physicalPolynomialLift_primitive hA hAB D S hL hx v

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
section

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [Fintype ι]

 theorem coupling_exterior_of_primitive_germ
    {α : ManifoldOneForm (E × PlanePhase ι) (M × PlanePhase ι)}
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {Γ : PlanePhase ι → ManifoldOneForm E M} {x : M × PlanePhase ι}
    (he : α=ᶠ[𝓝 x] productHorizontalLift Γ+verticalLiouville) :
    manifoldExteriorOneForm α x=globalHorizontalCoupling phaseArea Γ x := by
  have he' : α-verticalLiouville=ᶠ[𝓝 x] productHorizontalLift Γ := by
    filter_upwards [he] with q hq
    simp only [Pi.sub_apply,hq,Pi.add_apply,add_sub_cancel_right]
  have hd := manifoldExteriorOneForm_congr_germ he'
  rw [manifoldExteriorOneForm_sub_at (hα.spatial_smooth 0 x (mem_extChartAt_target _))
    (verticalLiouville_smooth.spatial_smooth 0 x (mem_extChartAt_target _)),verticalLiouville_exterior] at hd
  change manifoldExteriorOneForm α x=_+manifoldExteriorOneForm (productHorizontalLift Γ) x
  rw [←hd]
  abel

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M] in
 theorem exact_path_local_transport_derivative {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {Φ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (hODE : ∀ x s,s∈Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun r => Φ (r,x)) s ((1:ℝ →L[ℝ] ℝ).smulRight (V (s,Φ (s,x)))))
    {O : Set (ℝ × M)} (hO : IsOpen O)
    (hinv : ∀ p∈O,(manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
    (heq : ∀ p∈O,V p=manifoldMoserField
      (fun t => manifoldExteriorOneForm (Γ t)) (manifoldTimePrimitive Γ) p)
    {t : ℝ} (ht : t∈Ioo (-2:ℝ) 2) {x : M} (hx : (t,Φ (t,x))∈O) (v w : E) :
    HasDerivAt (fun s => manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) s x v w) 0 t := by
  have hΩ : SmoothTwoFormFamily (fun t => manifoldExteriorOneForm (Γ t)) :=
    manifoldExteriorOneForm_path_smooth hΓ
  have hα : SmoothOneFormFamily (manifoldTimePrimitive Γ) := manifoldTimePrimitive_smooth hΓ
  apply local_manifold_form_transport_derivative (Ω := fun t => manifoldExteriorOneForm (Γ t))
    hΦ hV isOpen_Ioo hODE hΩ ht x
  intro c y hy he u z
  have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)∈𝓝 (t,y) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hy⟩
  have htO : (t,(extChartAt 𝓘(ℝ,E) c).symm y)∈O := by rw [he]; exact hx
  exact joint_manifold_moser_PDE (Ω := fun t => manifoldExteriorOneForm (Γ t))
    (α := manifoldTimePrimitive Γ) hV hO hy htO hinv
    (Filter.eventually_of_mem (hO.mem_nhds htO) fun p hp => heq p hp)
    ((hΩ c).contDiffAt hn) ((hα c).contDiffAt hn)
    (fun u z => by
      simp only [chartTwoForm,ContinuousLinearMap.bilinearComp_apply]
      exact manifoldExteriorOneForm_skew (Γ t) _ _ _)
    (manifoldExteriorOneForm_path_closed hΓ t c y hy)
    (manifoldExteriorOneForm_path_time hΓ t c y hy) u z

 theorem exists_compact_short_exact_moser {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible) :
    ∃ ε : ℝ, 0<ε ∧ ε≤1 ∧ ∃ W : Set M, IsOpen W ∧ K⊆W ∧
      ∃ Φ Ψ : ℝ × M → M,
        ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
        ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
        (∀ x,Φ (0,x)=x) ∧
        (∀ t∈Icc (0:ℝ) ε,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
        (∀ t∈Icc (0:ℝ) ε,∀ x∈W,∀ v w,
          manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
            manifoldExteriorOneForm (Γ 0) x v w) := by
  let Ω : ℝ → ManifoldTwoForm E M := fun t => manifoldExteriorOneForm (Γ t)
  let α : ℝ → ManifoldOneForm E M := manifoldTimePrimitive Γ
  have hΩ : SmoothTwoFormFamily (fun t => manifoldExteriorOneForm (Γ t)) :=
    manifoldExteriorOneForm_path_smooth hΓ
  have hα : SmoothOneFormFamily (manifoldTimePrimitive Γ) := manifoldTimePrimitive_smooth hΓ
  let U : Set (ℝ × M) := {p | (Ω p.1 p.2).IsInvertible}
  have hU : IsOpen U := manifoldTwoForm_isOpen_nondegenerate hΩ
  have hKU : ({0}:Set ℝ)×ˢK⊆U := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    exact hinv x hx
  obtain ⟨V,hV,hVe,_hVz,⟨C,hC,hVC⟩,_hVL⟩ :=
    exists_joint_localized_manifold_moser_field (Ω := Ω) (α := α) hΩ hα
      (isCompact_singleton.prod hK) hU hKU (fun _ hp => hp)
  obtain ⟨O,hO,hKO,hOV⟩ := mem_nhdsSet_iff_exists.mp hVe
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hODE,_hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hV hC hVC
  have hgraph : Continuous (fun p : ℝ × M => (p.1,Φ p)) :=
    continuous_fst.prodMk hΦ.continuous
  have hsub : ({0}:Set ℝ)×ˢK ⊆ (fun p : ℝ × M => (p.1,Φ p)) ⁻¹' (O∩U) := by
    rintro ⟨t,x⟩ hp
    rcases hp.1 with rfl
    simp only [mem_preimage,hΦ0]
    exact ⟨hKO hp,hKU hp⟩
  obtain ⟨T,W,hT,hW,h0T,hKW,hTW⟩ := generalized_tube_lemma isCompact_singleton hK
    ((hO.inter hU).preimage hgraph) hsub
  obtain ⟨δ,hδ,hδT⟩ := Metric.isOpen_iff.mp hT 0 (h0T (mem_singleton 0))
  let ε : ℝ := min (δ/2) (1/2)
  have hε : 0<ε := lt_min (by positivity) (by norm_num)
  have hεd : ε≤δ/2 := min_le_left _ _
  have hε1 : ε≤1/2 := min_le_right _ _
  have hstay (t : ℝ) (ht : t∈Icc (0:ℝ) ε) (x : M) (hx : x∈W) :
      (t,Φ (t,x))∈O∩U := by
    change (t,x)∈(fun p : ℝ × M => (p.1,Φ p)) ⁻¹' (O∩U)
    apply hTW
    refine ⟨hδT ?_,hx⟩
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    constructor <;> linarith [ht.1,ht.2]
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) ε) (x : M) (hx : x∈W) (v w : E) :
      HasDerivAt (fun s => manifoldPullback Φ Ω s x v w) 0 t := by
    exact exact_path_local_transport_derivative hΓ hΦ hV hODE (hO.inter hU)
      (fun _ hp => hp.2) (fun p hp => hOV hp.1)
      (show t∈Ioo (-2:ℝ) 2 by constructor <;> linarith [ht.1,ht.2])
      (hstay t ht x hx) v w
  refine ⟨ε,hε,by linarith,W,hW,hKW,Φ,Ψ,hΦ,hΨ,hΦ0,?_,?_⟩
  · intro t ht x
    exact hΦi t ⟨ht.1,by linarith [ht.2]⟩ x
  · intro t ht x hx v w
    have he := (convex_Icc (0:ℝ) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs x hx v w).hasDerivWithinAt)
      (fun _ _ => (by simp : ‖(0:ℝ)‖≤(0:ℝ)))
      (show (0:ℝ)∈Icc (0:ℝ) ε from ⟨le_rfl,hε.le⟩) ht
    have he' : manifoldPullback Φ Ω t x v w=manifoldPullback Φ Ω 0 x v w := by
      simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using he
    rw [he']
    have hid : (fun y => Φ (0,y))=id := funext hΦ0
    have hD : preferredDifferential (fun y => Φ (0,y)) x=ContinuousLinearMap.id ℝ E := by
      change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (0,y)) x=_
      rw [hid]; exact mfderiv_id
    rw [manifoldPullback,hD]
    simp only [hΦ0,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply,Ω]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
