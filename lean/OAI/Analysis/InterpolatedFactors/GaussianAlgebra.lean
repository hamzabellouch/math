import OAI.Analysis.InterpolatedFactors.ScalarSystem

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.GaussianRecognition
section Algebraic
variable {A : Type u_1} {B : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

theorem centralizer_transport (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) (T : A) :
    Φ T ∈ StarSubalgebra.centralizer ℂ (Φ '' s) ↔ T ∈ StarSubalgebra.centralizer ℂ s := by
  rw [StarSubalgebra.mem_centralizer_iff,StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h g hg
    have hh := h (Φ g) ⟨g,hg,rfl⟩
    constructor
    · apply Φ.injective
      change Φ (g*T)=Φ (T*g)
      simpa only [map_mul] using hh.1
    · apply Φ.injective
      change Φ (star g*T)=Φ (T*star g)
      simpa only [map_mul,map_star] using hh.2
  · rintro h _ ⟨g,hg,rfl⟩
    exact ⟨by simpa only [map_mul] using congrArg Φ (h g hg).1,
      by simpa only [map_mul,map_star] using congrArg Φ (h g hg).2⟩

theorem centralizer_image (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) :
    (StarSubalgebra.centralizer ℂ (Φ '' s) : Set B)=
      Φ '' (StarSubalgebra.centralizer ℂ s : Set A) := by
  ext T
  constructor
  · intro h
    refine ⟨Φ.symm T,?_,Φ.apply_symm_apply T⟩
    apply (centralizer_transport Φ s (Φ.symm T)).mp
    rw [Φ.apply_symm_apply]
    exact h
  · rintro ⟨T,h,rfl⟩
    exact (centralizer_transport Φ s T).mpr h

theorem bicommutant_transport (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) (T : A) :
    Φ T ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Φ '' s) : Set B) ↔
    T ∈ StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A) := by
  rw [centralizer_image,centralizer_transport]
end Algebraic

variable {E : Type u_3} {F : Type u_4}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

@[instance_reducible] def ultraweak (E : Type u_5) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : TopologicalSpace (Operator E) :=
  ⨅ (ξ : lp (fun _ : ℕ => E) 2) (η : lp (fun _ : ℕ => E) 2),
    TopologicalSpace.induced (fun T : Operator E => ∑' k : ℕ, inner ℂ (η k) (T (ξ k))) inferInstance

def sequenceMap (W : E ≃ₗᵢ[ℂ] F) (ξ : lp (fun _ : ℕ => E) 2) : lp (fun _ : ℕ => F) 2 :=
  ⟨fun n => W (ξ n),Memℓp.of_norm (by simpa only [W.norm_map] using (lp.memℓp ξ).norm)⟩

theorem spatial_normal (W : E ≃ₗᵢ[ℂ] F) :
    @Continuous _ _ (ultraweak E) (ultraweak F) W.conjStarAlgEquiv := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have heq :
      (fun T : Operator E => ∑' k : ℕ,inner ℂ (η k) (W.conjStarAlgEquiv T (ξ k)))=
      (fun T : Operator E => ∑' k : ℕ,
        inner ℂ (sequenceMap W.symm η k) (T (sequenceMap W.symm ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    change inner ℂ (η k) (W (T (W.symm (ξ k)))) =
      inner ℂ (W.symm (η k)) (T (W.symm (ξ k)))
    rw [← W.inner_map_map]
    simp
  change @Continuous _ _ (ultraweak E) _
    (fun T : Operator E => ∑' k : ℕ,inner ℂ (η k) (W.conjStarAlgEquiv T (ξ k)))
  rw [heq]
  exact continuous_iInf_dom (i := sequenceMap W.symm ξ)
    (continuous_iInf_dom (i := sequenceMap W.symm η) continuous_induced_dom)

namespace System
variable {A : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable {covariance : I → I → A → A}
variable (X : System A E I covariance) (Y : System A F I covariance)
variable
  (hstate : ∀ a,inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

def generators (σ : I → I) : Set (Operator E) := Set.range X.coeff ∪ Set.range (X.generator σ)
def generated (σ : I → I) : StarSubalgebra ℂ (Operator E) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (X.generators σ) : Set (Operator E))

@[instance_reducible] def generatedTopology (σ : I → I) : TopologicalSpace (X.generated σ) :=
  TopologicalSpace.induced (fun T : X.generated σ => (T : Operator E)) (ultraweak E)

theorem spatial_generators (σ : I → I) :
    (X.spatial Y hstate hX hY).conjStarAlgEquiv '' X.generators σ=Y.generators σ := by
  rw [generators, generators, Set.image_union]
  congr 1
  · ext T
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨a,(spatial_coeff X Y hstate hX hY a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨X.coeff a,⟨a,rfl⟩,spatial_coeff X Y hstate hX hY a⟩
  · ext T
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(spatial_generator X Y hstate hX hY σ i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨X.generator σ i,⟨i,rfl⟩,spatial_generator X Y hstate hX hY σ i⟩

theorem spatial_generated (σ : I → I) (T : Operator E) :
    (X.spatial Y hstate hX hY).conjStarAlgEquiv T ∈ Y.generated σ ↔ T ∈ X.generated σ := by
  have hh := bicommutant_transport (X.spatial Y hstate hX hY).conjStarAlgEquiv
    (X.generators σ) T
  rw [spatial_generators X Y hstate hX hY σ] at hh
  exact hh

def generatedIso (σ : I → I) : X.generated σ ≃⋆ₐ[ℂ] Y.generated σ where
  toFun T := ⟨(X.spatial Y hstate hX hY).conjStarAlgEquiv T,
    (spatial_generated X Y hstate hX hY σ T).mpr T.property⟩
  invFun T := ⟨(X.spatial Y hstate hX hY).conjStarAlgEquiv.symm T,
    (spatial_generated X Y hstate hX hY σ _).mp (by
      rw [StarAlgEquiv.apply_symm_apply]; exact T.property)⟩
  left_inv T := Subtype.ext (StarAlgEquiv.symm_apply_apply
    (X.spatial Y hstate hX hY).conjStarAlgEquiv (T : Operator E))
  right_inv T := Subtype.ext (StarAlgEquiv.apply_symm_apply
    (X.spatial Y hstate hX hY).conjStarAlgEquiv (T : Operator F))
  map_mul' T U := Subtype.ext (map_mul _ (T : Operator E) (U : Operator E))
  map_add' T U := Subtype.ext (map_add _ (T : Operator E) (U : Operator E))
  map_smul' c T := Subtype.ext (map_smul _ c (T : Operator E))
  map_star' T := Subtype.ext (map_star _ (T : Operator E))

theorem generatedIso_normal (σ : I → I) :
    @Continuous _ _ (X.generatedTopology σ) (Y.generatedTopology σ)
      (X.generatedIso Y hstate hX hY σ) := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (Operator F) := ultraweak F
  let : TopologicalSpace (X.generated σ) := X.generatedTopology σ
  let : TopologicalSpace (Y.generated σ) := Y.generatedTopology σ
  apply continuous_induced_rng.mpr
  have hi : Continuous (fun T : X.generated σ => (T : Operator E)) := continuous_induced_dom
  exact (spatial_normal (X.spatial Y hstate hX hY)).comp hi

theorem generatedIso_trace (σ : I → I) (T : X.generated σ) :
    inner ℂ Y.root ((X.generatedIso Y hstate hX hY σ T : Operator F) Y.root)=
      inner ℂ X.root ((T : Operator E) X.root) :=
  X.spatial_trace Y hstate hX hY (T : Operator E)

end System
end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_8} {E : Type u_9} {I : Type u_10} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

def normalSpan : Submodule ℂ E := Submodule.span ℂ (Set.range X.family)
def normalHull : Submodule ℂ E := X.normalSpan.topologicalClosure

instance normalHull_complete : CompleteSpace X.normalHull := by
  unfold normalHull
  infer_instance

theorem normal_mem (a : A) (w : List (I×A)) : X.normal a w∈X.normalSpan :=
  Submodule.subset_span ⟨(a,w),rfl⟩

theorem normalSpan_coeff (a : A) {ξ : E} (hξ : ξ∈X.normalSpan) : X.coeff a ξ∈X.normalSpan := by
  induction hξ using Submodule.span_induction with
  | mem ξ hξ => obtain ⟨⟨b,w⟩,rfl⟩ := hξ; exact (X.coeff_normal a b w) ▸ X.normal_mem (a*b) w
  | zero => simpa only [map_zero] using X.normalSpan.zero_mem
  | add ξ η _ _ hξ hη => simpa only [map_add] using X.normalSpan.add_mem hξ hη
  | smul c ξ _ hξ => simpa only [map_smul] using X.normalSpan.smul_mem c hξ

theorem normalSpan_create (i : I) {ξ : E} (hξ : ξ∈X.normalSpan) : X.create i ξ∈X.normalSpan := by
  induction hξ using Submodule.span_induction with
  | mem ξ hξ => obtain ⟨⟨a,w⟩,rfl⟩ := hξ; exact (X.create_normal i a w) ▸ X.normal_mem 1 ((i,a)::w)
  | zero => simpa only [map_zero] using X.normalSpan.zero_mem
  | add ξ η _ _ hξ hη => simpa only [map_add] using X.normalSpan.add_mem hξ hη
  | smul c ξ _ hξ => simpa only [map_smul] using X.normalSpan.smul_mem c hξ

theorem normalSpan_annihilate (i : I) {ξ : E} (hξ : ξ∈X.normalSpan) : star (X.create i) ξ∈X.normalSpan := by
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨⟨a,w⟩,rfl⟩ := hξ
    change star (X.create i) (X.normal a w)∈X.normalSpan
    cases w with
    | nil => rw [X.annihilate_normal_nil]; exact X.normalSpan.zero_mem
    | cons q w => rcases q with ⟨j,b⟩; rw [X.annihilate_normal_cons]; exact X.normal_mem _ _
  | zero => simpa only [map_zero] using X.normalSpan.zero_mem
  | add ξ η _ _ hξ hη => simpa only [map_add] using X.normalSpan.add_mem hξ hη
  | smul c ξ _ hξ => simpa only [map_smul] using X.normalSpan.smul_mem c hξ

theorem normalHull_preserve (T : Operator E) (hT : ∀ ξ∈X.normalSpan,T ξ∈X.normalSpan)
    {ξ : E} (hξ : ξ∈X.normalHull) : T ξ∈X.normalHull :=
  closure_minimal (t := {ξ:E | T ξ∈X.normalHull})
    (fun ξ hξ => X.normalSpan.le_topologicalClosure (hT ξ hξ))
    (X.normalSpan.isClosed_topologicalClosure.preimage T.continuous) hξ

theorem normalHull_root : X.root∈X.normalHull := by
  have hh := X.normalSpan.le_topologicalClosure (X.normal_mem 1 [])
  simpa only [normal,map_one,one_apply_eq_self,normalHull] using hh

theorem normalHull_coeff (a : A) {ξ : E} (hξ : ξ∈X.normalHull) : X.coeff a ξ∈X.normalHull :=
  X.normalHull_preserve _ (fun _ h => X.normalSpan_coeff a h) hξ

theorem normalHull_create (i : I) {ξ : E} (hξ : ξ∈X.normalHull) : X.create i ξ∈X.normalHull :=
  X.normalHull_preserve _ (fun _ h => X.normalSpan_create i h) hξ

theorem normalHull_annihilate (i : I) {ξ : E} (hξ : ξ∈X.normalHull) : star (X.create i) ξ∈X.normalHull :=
  X.normalHull_preserve _ (fun _ h => X.normalSpan_annihilate i h) hξ

theorem normalHull_projection_coeff (a : A) : Commute X.normalHull.starProjection (X.coeff a) := by
  apply projection_commutes_of_invariant X.normalHull
  · exact fun _ h => X.normalHull_coeff a h
  · simpa only [← map_star] using (fun ξ h => X.normalHull_coeff (star a) (ξ := ξ) h)

theorem normalHull_projection_create (i : I) : Commute X.normalHull.starProjection (X.create i) :=
  projection_commutes_of_invariant X.normalHull _
    (fun _ h => X.normalHull_create i h) (fun _ h => X.normalHull_annihilate i h)

theorem normalHull_projection_annihilate (i : I) : Commute X.normalHull.starProjection (star (X.create i)) :=
  projection_commutes_of_invariant X.normalHull _
    (fun _ h => X.normalHull_annihilate i h) (by simpa only [star_star] using (fun ξ h => X.normalHull_create i (ξ := ξ) h))

theorem normalHull_projection_generator (σ : I → I) (i : I) :
    Commute X.normalHull.starProjection (X.generator σ i) :=
  (X.normalHull_projection_create i).add_right (X.normalHull_projection_annihilate (σ i))

theorem normalHull_bicommutant (σ : I → I) (T : Operator E) (hT : T∈X.generated σ) : T X.root∈X.normalHull := by
  have hP : X.normalHull.starProjection∈StarSubalgebra.centralizer ℂ (X.generators σ) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro U hU
    rcases hU with ⟨a,rfl⟩ | ⟨i,rfl⟩
    · exact ⟨(X.normalHull_projection_coeff a).eq.symm,
        (by simpa only [map_star] using (X.normalHull_projection_coeff (star a)).eq.symm)⟩
    · refine ⟨(X.normalHull_projection_generator σ i).eq.symm,?_⟩
      change star (X.create i+star (X.create (σ i)))*_= _*star (X.create i+star (X.create (σ i)))
      rw [star_add (R := Operator E),star_star]
      exact ((X.normalHull_projection_annihilate i).add_right (X.normalHull_projection_create (σ i))).eq.symm
  have hh := DFunLike.congr_fun ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hP).1 X.root
  change X.normalHull.starProjection (T X.root)=T (X.normalHull.starProjection X.root) at hh
  rw [X.normalHull.starProjection_eq_self_iff.mpr X.normalHull_root] at hh
  exact X.normalHull.starProjection_eq_self_iff.mp hh
end FreeGroupFactorMain.GaussianRecognition.System

end

end OAI
