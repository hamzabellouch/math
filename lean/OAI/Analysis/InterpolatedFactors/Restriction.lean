import OAI.Analysis.InterpolatedFactors.Ultraweak

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

section
namespace FreeGroupFactorMain.FullReducingCorner
open Amplification GaussianRecognition ReducingSubspace
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

def transport (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) (t : Set B) (he : Φ '' s=t) :
    bicomm s ≃⋆ₐ[ℂ] bicomm t where
  toFun T := ⟨Φ T,by
    rw [← he]
    exact (bicommutant_transport Φ s T).mpr T.property⟩
  invFun T := ⟨Φ.symm T,by
    apply (bicommutant_transport Φ s (Φ.symm T)).mp
    rw [StarAlgEquiv.apply_symm_apply,he]
    exact T.property⟩
  left_inv T := Subtype.ext (StarAlgEquiv.symm_apply_apply Φ (T:A))
  right_inv T := Subtype.ext (StarAlgEquiv.apply_symm_apply Φ (T:B))
  map_mul' T U := Subtype.ext (Φ.map_mul (T:A) (U:A))
  map_add' T U := Subtype.ext (Φ.map_add (T:A) (U:A))
  map_smul' c T := Subtype.ext (map_smul Φ c (T:A))
  map_star' T := Subtype.ext (Φ.map_star' (T:A))

variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]

theorem representation_compress (T : E →L[ℂ] E) :
    cornerRepresentation K (compress K.starProjection isStarProjection_starProjection T)=reduce K T := by
  apply ContinuousLinearMap.ext
  intro ξ
  change K.orthogonalProjectionOnto (K.starProjection (T (K.starProjection (ξ:E))))=
    K.orthogonalProjectionOnto (T ξ)
  rw [K.starProjection_mem_subspace_eq_self ξ,K.orthogonalProjectionOnto_starProjection_of_le le_rfl]

def reductionImage (s : Set (E →L[ℂ] E)) : Set (K →L[ℂ] K) := reduce K '' s

theorem representation_compressedSet (s : Set (E →L[ℂ] E)) :
    cornerRepresentation K '' compressedSet K.starProjection isStarProjection_starProjection s=reductionImage K s := by
  rw [compressedSet,Set.image_image]
  simp only [representation_compress,reductionImage]

variable (s : Set (E →L[ℂ] E))
variable (hps : K.starProjection∈StarSubalgebra.centralizer ℂ s)
variable (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : K.starProjection*v=v) (hvr : v*(1-K.starProjection)=v) (hvi : star v*v=1-K.starProjection)

def restrictionIso : bicomm s ≃⋆ₐ[ℂ] bicomm (reductionImage K s) :=
  (iso K.starProjection isStarProjection_starProjection s hps v hvs hpv hvr hvi).trans
    (transport (cornerRepresentation K) _ _ (representation_compressedSet K s))

theorem restrictionIso_apply (T : bicomm s) :
    (restrictionIso K s hps v hvs hpv hvr hvi T : K →L[ℂ] K)=reduce K (T:E →L[ℂ] E) :=
  representation_compress K T

@[instance_reducible] def operatorTopology {F : Type u_4} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (t : Set (F →L[ℂ] F)) : TopologicalSpace (bicomm t) :=
  TopologicalSpace.induced (fun T : bicomm t => (T:F →L[ℂ] F)) (HilbertUltraweak.topology F)

theorem restrictionIso_normal :
    @Continuous _ _ (operatorTopology s) (operatorTopology (reductionImage K s))
      (restrictionIso K s hps v hvs hpv hvr hvi) := by
  let : TopologicalSpace (E →L[ℂ] E) := HilbertUltraweak.topology E
  let : TopologicalSpace (bicomm s) := operatorTopology s
  let : TopologicalSpace (K →L[ℂ] K) := HilbertUltraweak.topology K
  apply continuous_induced_rng.mpr
  have he : (fun T : bicomm s => (restrictionIso K s hps v hvs hpv hvr hvi T : K →L[ℂ] K))=
      (fun T : bicomm s => reduce K (T:E →L[ℂ] E)) := funext (restrictionIso_apply K s hps v hvs hpv hvr hvi)
  change @Continuous _ _ (operatorTopology s) (HilbertUltraweak.topology K)
    (fun T : bicomm s => (restrictionIso K s hps v hvs hpv hvr hvi T : K →L[ℂ] K))
  rw [he]
  exact (HilbertUltraweak.sandwich_continuous K.orthogonalProjectionOnto K.subtypeL).comp continuous_subtype_val
end FreeGroupFactorMain.FullReducingCorner

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace FullReducingCorner
variable {A : Type u_5} {E : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

theorem normalHull_projection_mem (σ : I → I) :
    X.normalHull.starProjection∈StarSubalgebra.centralizer ℂ (X.generators σ) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro U hU
  rcases hU with ⟨a,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨(X.normalHull_projection_coeff a).eq.symm,
      (by simpa only [map_star] using (X.normalHull_projection_coeff (star a)).eq.symm)⟩
  · refine ⟨(X.normalHull_projection_generator σ i).eq.symm,?_⟩
    change star (X.create i+star (X.create (σ i)))*_= _*star (X.create i+star (X.create (σ i)))
    rw [star_add (R := Operator E),star_star]
    exact ((X.normalHull_projection_annihilate i).add_right (X.normalHull_projection_create (σ i))).eq.symm

theorem reduced_generators (σ : I → I) :
    reductionImage X.normalHull (X.generators σ)=X.reducedSystem.generators σ := by
  have hgen (i : I) : reduce X.normalHull (X.generator σ i)=X.reducedSystem.generator σ i := by
    change reduce X.normalHull (X.create i+star (X.create (σ i)))=
      reduce X.normalHull (X.create i)+star (reduce X.normalHull (X.create (σ i)))
    rw [reduce_add,reduce_star]
  change reduce X.normalHull '' (Set.range X.coeff ∪ Set.range (X.generator σ))=
    Set.range X.reducedSystem.coeff ∪ Set.range (X.reducedSystem.generator σ)
  rw [Set.image_union,← Set.range_comp,← Set.range_comp]
  have hg : reduce X.normalHull ∘ X.generator σ=X.reducedSystem.generator σ := funext hgen
  rw [hg]
  rfl

variable (σ : I → I) (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ (X.generators σ))
variable (hpv : X.normalHull.starProjection*v=v) (hvr : v*(1-X.normalHull.starProjection)=v)
variable (hvi : star v*v=1-X.normalHull.starProjection)

def fullReductionIso : X.generated σ ≃⋆ₐ[ℂ] X.reducedSystem.generated σ := by
  have he := X.reduced_generators σ
  exact (restrictionIso X.normalHull (X.generators σ) (X.normalHull_projection_mem σ) v hvs hpv hvr hvi).trans
    (transport (StarAlgEquiv.refl ℂ _) _ _ (by simpa only [StarAlgEquiv.coe_refl,Set.image_id] using he))

theorem fullReductionIso_apply (T : X.generated σ) :
    (X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull)=reduce X.normalHull (T:Operator E) :=
  restrictionIso_apply X.normalHull _ _ v hvs hpv hvr hvi T

theorem fullReductionIso_normal :
    @Continuous _ _ (X.generatedTopology σ) (X.reducedSystem.generatedTopology σ)
      (X.fullReductionIso σ v hvs hpv hvr hvi) := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (X.generated σ) := X.generatedTopology σ
  let : TopologicalSpace (X.normalHull →L[ℂ] X.normalHull) := ultraweak X.normalHull
  apply continuous_induced_rng.mpr
  have he : (fun T : X.generated σ => (X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull))=
      (fun T : X.generated σ => reduce X.normalHull (T:Operator E)) := funext (X.fullReductionIso_apply σ v hvs hpv hvr hvi)
  change @Continuous _ _ (X.generatedTopology σ) (ultraweak X.normalHull)
    (fun T : X.generated σ => (X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull))
  rw [he]
  exact (HilbertUltraweak.sandwich_continuous X.normalHull.orthogonalProjectionOnto X.normalHull.subtypeL).comp
    continuous_subtype_val

theorem fullReductionIso_trace (T : X.generated σ) :
    inner ℂ X.reducedSystem.root ((X.fullReductionIso σ v hvs hpv hvr hvi T : X.normalHull →L[ℂ] X.normalHull)
      X.reducedSystem.root)=inner ℂ X.root ((T:Operator E) X.root) := by
  rw [fullReductionIso_apply]
  exact inner_reduce X.normalHull _ _ _
end FreeGroupFactorMain.GaussianRecognition.System

end

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition ReducingSubspace
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem weightedFull_left :
    (weightedSystem u v hv hvu).normalHull.starProjection*pRightEdge u v=pRightEdge u v := by
  rw [weightedHull_projection]
  exact pRightEdge_left u v

theorem weightedFull_right :
    pRightEdge u v*(1-(weightedSystem u v hv hvu).normalHull.starProjection)=pRightEdge u v := by
  rw [weightedHull_projection]
  exact pRightEdge_right u v

theorem weightedFull_initial :
    star (pRightEdge u v)*pRightEdge u v=1-(weightedSystem u v hv hvu).normalHull.starProjection := by
  rw [weightedHull_projection]
  exact pRightEdge_initial u v hv hvu

def fullGaussianIso : (weightedSystem u v hv hvu).generated scalarFlip ≃⋆ₐ[ℂ]
    scalarSystem.generated scalarFlip :=
  ((weightedSystem u v hv hvu).fullReductionIso scalarFlip (pRightEdge u v)
    (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
    (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu)).trans
      (reducedGaussianIso u v hv hvu)

theorem fullGaussianIso_normal :
    @Continuous _ _ ((weightedSystem u v hv hvu).generatedTopology scalarFlip)
      (scalarSystem.generatedTopology scalarFlip) (fullGaussianIso u v hv hvu) := by
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace ((weightedSystem u v hv hvu).reducedSystem.generated scalarFlip) :=
    (weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (reducedGaussianIso_normal u v hv hvu).comp
    ((weightedSystem u v hv hvu).fullReductionIso_normal scalarFlip (pRightEdge u v)
      (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
      (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu))

theorem fullGaussianIso_trace (T : (weightedSystem u v hv hvu).generated scalarFlip) :
    inner ℂ scalarSystem.root ((fullGaussianIso u v hv hvu T : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      inner ℂ pRoot ((T:PRange ℕ →L[ℂ] PRange ℕ) pRoot) := by
  rw [fullGaussianIso,StarAlgEquiv.trans_apply,reducedGaussianIso_trace]
  exact (weightedSystem u v hv hvu).fullReductionIso_trace scalarFlip (pRightEdge u v)
    (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
    (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu) T
end FreeGroupFactorMain.WeightedFock

end

end OAI
