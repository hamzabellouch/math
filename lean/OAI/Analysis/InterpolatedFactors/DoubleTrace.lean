import OAI.Analysis.InterpolatedFactors.MatrixNormal

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1} [Group G]

section Singles
variable [DecidableEq G]

omit [Group G] in
theorem flattenHilbert_single (i j : ℕ) (g : G) :
    stabilizationFlatten G (lp.single 2 (i,j,g) (1:ℂ))=lp.single 2 (Nat.pair i j,g) 1 := by
  classical
  ext x
  simp only [stabilizationFlatten,hilbertReindex_apply,lp.single_apply,Pi.single_apply]
  congr 1
  exact propext (pairedIndex G).symm_apply_eq

theorem flatten_projectionTrace (T : doubleStabilization G) :
    stabilizedProjectionTrace (flattenStabilizationIso T)=
      ∑' i : ℕ,∑' j : ℕ,ENNReal.ofReal (‖(T : GroupOperator (ℕ × (ℕ × G)))
        (lp.single 2 (i,j,1) (1:ℂ))‖^2) := by
  classical
  unfold stabilizedProjectionTrace
  rw [← Nat.pairEquiv.tsum_eq]
  rw [←ENNReal.tsum_prod]
  apply tsum_congr
  rintro ⟨i,j⟩
  change ENNReal.ofReal (‖(stabilizationFlatten G)
    ((T : GroupOperator (ℕ × (ℕ × G))) ((stabilizationFlatten G).symm _))‖^2)=_
  rw [(stabilizationFlatten G).norm_map]
  congr 1
  congr 1
  congr 1
  apply congrArg (fun ξ => (T : GroupOperator (ℕ × (ℕ × G))) ξ)
  apply (stabilizationFlatten G).injective
  rw [(stabilizationFlatten G).apply_symm_apply,flattenHilbert_single]
  ext x
  simp only [lp.single_apply,Pi.single_apply,Nat.pairEquiv_apply,Function.uncurry_apply_pair]
  by_cases h : x=(Nat.pair i j,(1:G)) <;> simp [h]

end Singles

def doubleFiniteDiagonal (n : ℕ) (T : stabilization G) : doubleStabilization G :=
  ⟨finiteDiagonal n (T : GroupOperator (ℕ × G)),by
    classical
    rw [mem_doubleStabilization_iff_right]
    intro g
    apply matrixEntry_ext
    intro i j
    rw [doubleRight,matrixEntry_diagonal_mul,matrixEntry_mul_diagonal]
    rw [finiteDiagonal_sum]
    simp only [matrixEntry_sum,matrixEntry_matrixBlock]
    by_cases hij : i=j
    · subst j
      by_cases hi : i<n
      · have hs : (∑ k : Fin n,if i=k.val ∧ i=k.val then (T : GroupOperator (ℕ × G)) else 0)=(T : GroupOperator (ℕ × G)) := by
          let k : Fin n := ⟨i,hi⟩
          have he (l : Fin n) : i=l.val ∧ i=l.val ↔ l=k := by simp [k,Fin.ext_iff,eq_comm]
          simp_rw [he]
          simp
        rw [hs]
        exact (mem_stabilization_iff_right _).mp T.property g
      · have hs : (∑ k : Fin n,if i=k.val ∧ i=k.val then (T : GroupOperator (ℕ × G)) else 0)=0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [ite_eq_right]
          rintro ⟨hik,_⟩
          exact hi (hik ▸ k.isLt)
        rw [hs,mul_zero,zero_mul]
    · have hs : (∑ k : Fin n,if i=k.val ∧ j=k.val then (T : GroupOperator (ℕ × G)) else 0)=0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [ite_eq_right]
        rintro ⟨hik,hjk⟩
        exact hij (hik.trans hjk.symm)
      rw [hs,mul_zero,zero_mul]⟩

def finiteFlatten (n : ℕ) (p : stabilization G) : stabilization G :=
  flattenStabilizationIso (doubleFiniteDiagonal n p)

theorem doubleFiniteDiagonal_projection (n : ℕ) (p : stabilization G) (hp : IsStarProjection p) :
    IsStarProjection (doubleFiniteDiagonal n p) := by
  have hm : (p : GroupOperator (ℕ × G))*(p : GroupOperator (ℕ × G))=p := congrArg Subtype.val hp.isIdempotentElem.eq
  have hs : star (p : GroupOperator (ℕ × G))=p := congrArg Subtype.val hp.isSelfAdjoint.star_eq
  constructor
  · apply Subtype.ext
    change finiteDiagonal n (p : GroupOperator (ℕ × G))*finiteDiagonal n (p : GroupOperator (ℕ × G))=_
    rw [finiteDiagonal_mul,hm]
    rfl
  · apply Subtype.ext
    change star (finiteDiagonal n (p : GroupOperator (ℕ × G)))=_
    rw [finiteDiagonal_star,hs]
    rfl

theorem finiteFlatten_projection (n : ℕ) (p : stabilization G) (hp : IsStarProjection p) :
    IsStarProjection (finiteFlatten n p) :=
  (doubleFiniteDiagonal_projection n p hp).map
    (flattenStabilizationIso (G := G)).toStarAlgHom

theorem finiteFlatten_trace (n : ℕ) (p : stabilization G) :
    stabilizedProjectionTrace (finiteFlatten n p)=(n:ℝ≥0∞)*stabilizedProjectionTrace p := by
  classical
  rw [finiteFlatten,flatten_projectionTrace]
  have he (i j : ℕ) : ENNReal.ofReal (‖(doubleFiniteDiagonal n p : GroupOperator (ℕ × (ℕ × G)))
      (lp.single 2 (i,j,1) (1:ℂ))‖^2)=
      if i<n then ENNReal.ofReal (‖(p : GroupOperator (ℕ × G)) (lp.single 2 (j,1) (1:ℂ))‖^2) else 0 := by
    change ENNReal.ofReal (‖finiteDiagonal n (p : GroupOperator (ℕ × G)) _‖^2)=_
    rw [←productSingle_single,finiteDiagonal_productSingle]
    split_ifs
    · rw [productSingle_norm]
    · simp
  simp_rw [he]
  have he' (i : ℕ) : (∑' j : ℕ,if i<n then ENNReal.ofReal (‖(p : GroupOperator (ℕ × G))
      (lp.single 2 (j,1) (1:ℂ))‖^2) else 0)=if i<n then stabilizedProjectionTrace p else 0 := by
    split_ifs <;> simp [stabilizedProjectionTrace]
  simp_rw [he']
  rw [tsum_eq_sum (s := Finset.range n)]
  · simp only [Finset.sum_ite_of_true (fun i hi => Finset.mem_range.mp hi),Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  · intro i hi
    rw [ite_eq_right (fun h => hi (Finset.mem_range.mpr h))]
end

section
variable {G : Type u_2} [Group G]

def finiteCornerSingletonIso (p : groupVonNeumann G) (hp : IsStarProjection p) :
    FiniteCorner 1 p hp ≃⋆ₐ[ℂ] Corner p hp where
  toFun x := finiteCornerEntry 1 p hp x 0 0
  invFun x := finiteCornerOfMatrix 1 p hp (fun _ _ => x)
  left_inv x := by
    apply finiteCorner_ext 1 p hp
    intro i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j
    exact finiteCornerEntry_ofMatrix 1 p hp _ 0 0
  right_inv x := finiteCornerEntry_ofMatrix 1 p hp _ 0 0
  map_mul' x y := by
    rw [finiteCornerEntry_mul]
    simp
  map_add' x y := finiteCornerEntry_add 1 p hp x y 0 0
  map_smul' c x := finiteCornerEntry_smul 1 p hp x c 0 0
  map_star' x := finiteCornerEntry_star 1 p hp x 0 0

theorem finiteCornerSingletonIso_normal (p : groupVonNeumann G) (hp : IsStarProjection p) :
    @Continuous _ _
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 p) (finiteProjection_projection 1 p hp))
      (cornerTopology (groupUltraweakTopology G) p hp) (finiteCornerSingletonIso p hp) :=
  finiteCornerEntry_normal 1 p hp 0 0

theorem finiteCornerSingletonIso_trace (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner 1 p hp) :
    canonicalTrace (finiteCornerSingletonIso p hp x).val=stabilizedTrace x.val := by
  rw [finiteCorner_trace]
  simp only [Fin.sum_univ_one]
  rfl

end

variable {G : Type u_3} {H : Type u_4} [Group G] [Group H]

theorem finiteCornerIso_symm (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq) :
    (finiteCornerIso n p hp q hq e).symm=finiteCornerIso n q hq p hp e.symm := by
  ext x
  rfl

theorem finiteCornerSingletonIso_symm_normal (p : groupVonNeumann G) (hp : IsStarProjection p) :
    @Continuous _ _ (cornerTopology (groupUltraweakTopology G) p hp)
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 p) (finiteProjection_projection 1 p hp))
      (finiteCornerSingletonIso p hp).symm := by
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  exact finiteCornerOfMatrix_normal 1 p hp _ (fun _ _ => continuous_id)

theorem finite_corner_choice_both
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (t : ℝ) (p q : stabilization G) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace q)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) :
    ∃ Φ : Corner p hp ≃⋆ₐ[ℂ] Corner q hq,
      (∀ x, normalizedCornerTrace stabilizedTrace t q hq (Φ x)=
        normalizedCornerTrace stabilizedTrace t p hp x) ∧
      @Continuous _ _ (cornerTopology (stabilizationTopology G) p hp)
        (cornerTopology (stabilizationTopology G) q hq) Φ ∧
      @Continuous _ _ (cornerTopology (stabilizationTopology G) q hq)
        (cornerTopology (stabilizationTopology G) p hp) Φ.symm := by
  have hv : ∃ u : stabilization G, star u*u=p ∧ u*star u=q :=
    equal_finite_trace_equivalence (G := G) hbase p q hp hq htrace hfinite
  rcases hv with ⟨u,hu,hu'⟩
  refine ⟨equivalentCorner p q hp hq u hu hu',?_,?_,?_⟩
  · exact equivalentCorner_normalized_finite_trace p q hp hq hfinite (htrace ▸ hfinite) u hu hu' t
  · exact equivalentCorner_normal p q hp hq u hu hu' (stabilizationTopology G)
      (stabilizationUltraweak_mul_conjugate u)
  · have h1 : star (star u)*star u=q := by rwa [star_star]
    have h2 : star u*star (star u)=p := by rwa [star_star]
    have he : (equivalentCorner p q hp hq u hu hu').symm=equivalentCorner q p hq hp (star u) h1 h2 := by
      apply StarAlgEquiv.ext
      intro x
      apply Subtype.ext
      change star u*(x : stabilization G)*u=star u*(x : stabilization G)*star (star u)
      rw [star_star]
    rw [he]
    exact equivalentCorner_normal q p hq hp (star u) h1 h2 (stabilizationTopology G)
      (stabilizationUltraweak_mul_conjugate (star u))
end FreeGroupFactorMain.Amplification

end

end OAI
