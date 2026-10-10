import OAI.Analysis.InterpolatedFactors.Matrices

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
namespace FreeGroupFactorMain.HilbertUltraweak
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {X : Type u_2} [TopologicalSpace X]

theorem finset_sum_continuous {ι : Type u_3} (s : Finset ι) (f : ι → X → (E →L[ℂ] E))
    (hf : ∀ i∈s,@Continuous _ _ _ (topology E) (f i)) :
    @Continuous _ _ _ (topology E) (fun x => ∑ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (@continuous_const X _ _ (topology E) (0 : E →L[ℂ] E))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact add_continuous (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
end FreeGroupFactorMain.HilbertUltraweak

namespace FreeGroupFactorMain.Amplification
variable {G : Type u_4} {H : Type u_5}

 theorem matrixEntry_normal (i j : ℕ) :
    @Continuous _ _ (ultraweakOperatorTopology (ℕ × G)) (ultraweakOperatorTopology G)
      (fun T : GroupOperator (ℕ × G) => matrixEntry T i j) := by
  have hc := HilbertUltraweak.sandwich_continuous (productCoordinate ℕ G i) (productSingle ℕ G j)
  convert hc using 1
  rfl

 theorem matrixBlock_normal (i j : ℕ) :
    @Continuous _ _ (ultraweakOperatorTopology G) (ultraweakOperatorTopology (ℕ × G))
      (matrixBlock (G := G) i j) :=
  HilbertUltraweak.sandwich_continuous (productSingle ℕ G i) (productCoordinate ℕ G j)

variable [Group G] [Group H]

 theorem finiteCornerEntry_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) (i j : Fin n) :
    @Continuous _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (cornerTopology (groupUltraweakTopology G) p hp) (fun x => finiteCornerEntry n p hp x i j) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (FiniteCorner n p hp) := cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp)
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  exact (((matrixEntry_normal i.val j.val).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

 theorem finiteCornerOfMatrix_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    {X : Type u_6} [TopologicalSpace X] (f : X → Fin n → Fin n → Corner p hp)
    (hf : ∀ i j,@Continuous _ _ _ (cornerTopology (groupUltraweakTopology G) p hp) (fun x => f x i j)) :
    @Continuous _ _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (fun x => finiteCornerOfMatrix n p hp (f x)) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  have hc : Continuous (fun x => finiteMatrix n (fun i j => ((f x i j).val : GroupOperator G))) := by
    apply HilbertUltraweak.finset_sum_continuous
    intro i _
    apply HilbertUltraweak.finset_sum_continuous
    intro j _
    exact (matrixBlock_normal i.val j.val).comp (continuous_subtype_val.comp (continuous_subtype_val.comp (hf i j)))
  exact (hc.subtype_mk _).subtype_mk _

 theorem finiteCornerIso_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq)
    (he : @Continuous _ _ (cornerTopology (groupUltraweakTopology G) p hp)
      (cornerTopology (groupUltraweakTopology H) q hq) e) :
    @Continuous _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (cornerTopology (stabilizationTopology H) (finiteProjection n q) (finiteProjection_projection n q hq))
      (finiteCornerIso n p hp q hq e) := by
  let : TopologicalSpace (FiniteCorner n p hp) := cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp)
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  let : TopologicalSpace (Corner q hq) := cornerTopology (groupUltraweakTopology H) q hq
  exact finiteCornerOfMatrix_normal n q hq _ (fun i j => he.comp (finiteCornerEntry_normal n p hp i j))

end FreeGroupFactorMain.Amplification

end

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_7}

 theorem productSingle_norm (i : ℕ) (ξ : GroupHilbert G) : ‖productSingle ℕ G i ξ‖=‖ξ‖ := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
  simp only [productSingle,ContinuousLinearMap.comp_apply,lp.singleContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [LinearIsometryEquiv.norm_map,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2)]

 theorem matrixBlock_productSingle (i j k : ℕ) (T : GroupOperator G) (ξ : GroupHilbert G) :
    matrixBlock i j T (productSingle ℕ G k ξ)=if j=k then productSingle ℕ G i (T ξ) else 0 := by
  simp only [matrixBlock,ContinuousLinearMap.comp_apply,productCoordinate_productSingle]
  split_ifs <;> simp

 theorem finiteDiagonal_productSingle (n : ℕ) (T : GroupOperator G) (k : ℕ) (ξ : GroupHilbert G) :
    finiteDiagonal n T (productSingle ℕ G k ξ)=if k<n then productSingle ℕ G k (T ξ) else 0 := by
  classical
  rw [finiteDiagonal_sum]
  simp only [sum_apply,matrixBlock_productSingle]
  by_cases hk : k<n
  · rw [ite_eq_left hk]
    let j : Fin n := ⟨k,hk⟩
    have he : ∀ i : Fin n,i.val=k ↔ i=j := fun i => (Fin.ext_iff (a := i) (b := j)).symm
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rfl
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    intro hi
    exact hk (hi ▸ i.isLt)

variable [Group G]

 theorem finiteProjection_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (a : ℝ) (_ha : 0≤a) (hpa : canonicalTrace p=(a:ℂ)) :
    stabilizedProjectionTrace (finiteProjection n p)=ENNReal.ofReal (n*a) := by
  classical
  have hv : ‖(p : GroupOperator G) (lp.single 2 (1:G) (1:ℂ))‖^2=a := by
    apply Complex.ofReal_injective
    have hh := canonicalTrace_star_mul p
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,hpa] at hh
    simpa only [Complex.ofReal_pow] using hh.symm
  change (∑' k : ℕ,ENNReal.ofReal (‖finiteDiagonal n (p : GroupOperator G) (lp.single 2 (k,1) (1:ℂ))‖^2))=_
  have he (k : ℕ) : ENNReal.ofReal (‖finiteDiagonal n (p : GroupOperator G) (lp.single 2 (k,1) (1:ℂ))‖^2)=
      if k<n then ENNReal.ofReal a else 0 := by
    rw [←productSingle_single,finiteDiagonal_productSingle]
    split_ifs
    · rw [productSingle_norm,hv]
    · simp
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range n)]
  · have hh : (∑ k∈Finset.range n,if k<n then ENNReal.ofReal a else 0)=∑ _k∈Finset.range n,ENNReal.ofReal a :=
      Finset.sum_congr rfl (fun k hk => ite_eq_left (Finset.mem_range.mp hk))
    rw [hh]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
  · intro k hk
    rw [ite_eq_right (fun h => hk (Finset.mem_range.mpr h))]

 theorem stabilizedTrace_matrix (T : stabilization G) :
    stabilizedTrace T=∑' k : ℕ,canonicalTrace
      (⟨matrixEntry (T : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp T.property k k⟩ : groupVonNeumann G) := by
  classical
  apply tsum_congr
  intro k
  rw [←productSingle_single,productSingle_inner_left,canonicalTrace_eq_inner]
  rfl

 theorem finiteCorner_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) (x : FiniteCorner n p hp) :
    stabilizedTrace x.val=∑ i : Fin n,canonicalTrace (finiteCornerEntry n p hp x i i).val := by
  classical
  rw [stabilizedTrace_matrix]
  have he (k : ℕ) : canonicalTrace
      (⟨matrixEntry (x.val : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp x.val.property k k⟩ : groupVonNeumann G)=
      if hk : k<n then canonicalTrace (finiteCornerEntry n p hp x ⟨k,hk⟩ ⟨k,hk⟩).val else 0 := by
    split_ifs with hk
    · rfl
    · have hz : matrixEntry (x.val : GroupOperator (ℕ × G)) k k=0 := by
        rw [←finiteCorner_reconstruct n p hp x]
        exact matrixEntry_finiteMatrix_out n _ k k (Or.inl (le_of_not_gt hk))
      have hs : (⟨matrixEntry (x.val : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp x.val.property k k⟩ : groupVonNeumann G)=0 := Subtype.ext hz
      rw [hs]
      exact map_zero (canonicalTraceLinear (G := G))
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range n)]
  · rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [dite_eq_left k.isLt]
  · intro k hk
    simp only [dite_eq_right (fun h => hk (Finset.mem_range.mpr h))]

variable {H : Type u_8} [Group H]
 theorem finiteCornerIso_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq)
    (c : ℂ) (hc : ∀ x,canonicalTrace (e x : groupVonNeumann H)=c*canonicalTrace (x : groupVonNeumann G))
    (x : FiniteCorner n p hp) :
    stabilizedTrace (finiteCornerIso n p hp q hq e x).val=c*stabilizedTrace x.val := by
  rw [finiteCorner_trace,finiteCorner_trace,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change canonicalTrace (finiteCornerEntry n q hq (finiteCornerOfMatrix n q hq _) i i).val=_
  rw [finiteCornerEntry_ofMatrix,hc]

end FreeGroupFactorMain.Amplification

end

end OAI
