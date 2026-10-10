import OAI.Analysis.InterpolatedFactors.Positive

namespace OAI

noncomputable section

universe u_1 u_2

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1} [Group G]

 theorem cornerStabilization_weight_iff (a : ℝ) (ha : 0<a) (p : stabilization G) (hp : IsStarProjection p)
    (t : ℝ) (_ht : 0≤t) (q : CornerStabilization p hp) :
    cornerStabilizationProjectionTrace a p hp q=ENNReal.ofReal t ↔
    stabilizedProjectionTrace q.val=ENNReal.ofReal (a*t) := by
  have ha0 : ENNReal.ofReal a≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  have hat : ENNReal.ofReal a≠⊤ := ENNReal.ofReal_ne_top
  unfold cornerStabilizationProjectionTrace
  rw [ENNReal.ofReal_mul ha.le]
  constructor
  · intro h
    have hh := congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal a*z) h
    simpa only [←mul_assoc,ENNReal.mul_inv_cancel ha0 hat,one_mul] using hh
  · intro h
    rw [h,←mul_assoc,ENNReal.inv_mul_cancel ha0 hat,one_mul]

 theorem doubleDiagonal_matrix (T : stabilization G) (i j : ℕ) :
    matrixEntry (doubleDiagonal T : GroupOperator (ℕ × (ℕ × G))) i j=
      if i=j then (T : GroupOperator (ℕ × G)) else 0 := by
  change matrixEntry (productAmplification ℕ (ℕ × G) T) i j=_
  ext ξ x
  rw [matrixEntry_apply,productAmplification_productSingle,productSingle_apply]
  by_cases h : i=j <;> simp [h]

 theorem doubleFiniteDiagonal_supported (n : ℕ) (p : stabilization G) (hp : IsStarProjection p)
    (q : Corner p hp) :
    doubleDiagonal p * doubleFiniteDiagonal n q.val=doubleFiniteDiagonal n q.val ∧
    doubleFiniteDiagonal n q.val * doubleDiagonal p=doubleFiniteDiagonal n q.val := by
  constructor
  · apply Subtype.ext
    apply matrixEntry_ext
    intro i j
    change matrixEntry (productAmplification ℕ (ℕ × G) (p : GroupOperator (ℕ × G))*finiteDiagonal n (q.val : GroupOperator (ℕ × G))) i j=matrixEntry (finiteDiagonal n (q.val : GroupOperator (ℕ × G))) i j
    rw [matrixEntry_diagonal_mul,finiteDiagonal_sum]
    simp only [matrixEntry_sum,matrixEntry_matrixBlock,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · exact congrArg Subtype.val q.property.1
    · exact mul_zero _
  · apply Subtype.ext
    apply matrixEntry_ext
    intro i j
    change matrixEntry (finiteDiagonal n (q.val : GroupOperator (ℕ × G))*productAmplification ℕ (ℕ × G) (p : GroupOperator (ℕ × G))) i j=matrixEntry (finiteDiagonal n (q.val : GroupOperator (ℕ × G))) i j
    rw [matrixEntry_mul_diagonal,finiteDiagonal_sum]
    simp only [matrixEntry_sum,matrixEntry_matrixBlock,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · exact congrArg Subtype.val q.property.2
    · exact zero_mul _

theorem finiteFlatten_supported (n : ℕ) (p : stabilization G) (hp : IsStarProjection p)
    (q : Corner p hp) : repeatFlatten p * finiteFlatten n q.val=finiteFlatten n q.val ∧
      finiteFlatten n q.val * repeatFlatten p=finiteFlatten n q.val := by
  obtain ⟨hl,hr⟩ := doubleFiniteDiagonal_supported n p hp q
  constructor
  · have h := congrArg (flattenStabilizationIso (G := G)) hl
    simpa only [map_mul,repeatFlatten,finiteFlatten] using h
  · have h := congrArg (flattenStabilizationIso (G := G)) hr
    simpa only [map_mul,repeatFlatten,finiteFlatten] using h

def cornerFiniteProjection (n : ℕ) (p : stabilization G) (hp : IsStarProjection p)
    (q : Corner p hp) : CornerStabilization p hp :=
  ⟨finiteFlatten n q.val,finiteFlatten_supported n p hp q⟩

theorem cornerFiniteProjection_projection (n : ℕ) (p : stabilization G) (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) : IsStarProjection (cornerFiniteProjection n p hp q) := by
  have hh := finiteFlatten_projection n q.val (nested_projection p hp q hq)
  constructor
  · exact Subtype.ext hh.isIdempotentElem.eq
  · exact Subtype.ext hh.isSelfAdjoint.star_eq
end

open scoped ENNReal
variable {G : Type u_2} [Group G]

theorem projection_weight_of_trace (p : stabilization G) (hp : IsStarProjection p)
    (hfin : stabilizedProjectionTrace p≠⊤) (a : ℝ) (hτ : stabilizedTrace p=(a:ℂ)) :
    stabilizedProjectionTrace p=ENNReal.ofReal a := by
  have h := stabilizedTrace_star_mul p hfin
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,hτ] at h
  have he : (stabilizedProjectionTrace p).toReal=a := Complex.ofReal_injective h.symm
  rw [←he,ENNReal.ofReal_toReal hfin]

theorem corner_projection_weight (a : ℝ) (ha : 0<a) (p : stabilization G) (hp : IsStarProjection p)
    (hpτ : stabilizedProjectionTrace p=ENNReal.ofReal a) (s : ℝ)
    (q : Corner p hp) (hq : IsStarProjection q)
    (hqτ : normalizedCornerTrace stabilizedTrace a p hp q=(s:ℂ)) :
    stabilizedProjectionTrace q.val=ENNReal.ofReal (a*s) := by
  apply projection_weight_of_trace q.val (nested_projection p hp q hq)
    (finite_weight_corner p hp (hpτ ▸ ENNReal.ofReal_ne_top) q) (a*s)
  have ha0 : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have h := congrArg (fun z : ℂ => (a:ℂ)*z) hqτ
  change (a:ℂ)*((a:ℂ)⁻¹*stabilizedTrace q.val)=(a:ℂ)*(s:ℂ) at h
  rw [←mul_assoc,mul_inv_cancel₀ ha0,one_mul] at h
  simpa only [Complex.ofReal_mul] using h

theorem cornerStabilization_projection_exists
    (hpos : ∀(t : ℝ),0<t → ∀(p : stabilization G)(hp : IsStarProjection p),
      stabilizedProjectionTrace p=ENNReal.ofReal t → Nonempty (GroupCornerNormalIso t p hp))
    (hsmall : ∀t : ℝ,0<t → t≤1 → HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t)
    (a : ℝ) (ha : 0<a) (p : stabilization G) (hp : IsStarProjection p)
    (hpτ : stabilizedProjectionTrace p=ENNReal.ofReal a) (t : ℝ) (ht : 0<t) :
    ∃q : CornerStabilization p hp,IsStarProjection q ∧
      cornerStabilizationProjectionTrace a p hp q=ENNReal.ofReal t := by
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have hn0 : 0<(n:ℝ) := ht.trans hn
  have hs : 0<t/(n:ℝ) := div_pos ht hn0
  have hs1 : t/(n:ℝ)≤1 := (div_le_one hn0).mpr hn.le
  obtain ⟨E⟩ := hpos a ha p hp hpτ
  have hx := HasCornerScaling.transport (canonicalTrace (G := G))
    (normalizedCornerTrace stabilizedTrace a p hp) (groupUltraweakTopology G)
    (cornerTopology (stabilizationTopology G) p hp) E.equiv.symm E.inverse_normal E.normal
    E.symm.trace_eq (hsmall _ hs hs1)
  obtain ⟨q,hq,_,hqτ,_,_,_⟩ := hx
  refine ⟨cornerFiniteProjection n p hp q,cornerFiniteProjection_projection n p hp q hq,?_⟩
  apply (cornerStabilization_weight_iff a ha p hp t ht.le _).mpr
  change stabilizedProjectionTrace (finiteFlatten n q.val)=_
  rw [finiteFlatten_trace,corner_projection_weight a ha p hp hpτ (t/(n:ℝ)) q hq hqτ]
  rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  congr 1
  field_simp

def nestedNormalizedIso (a t : ℝ) (p : stabilization G) (hp : IsStarProjection p)
    (q : CornerStabilization p hp) (hq : IsStarProjection q) :
    NormalTracialEquiv
      (normalizedCornerTrace (cornerStabilizationTrace a p hp) t q hq)
      (normalizedCornerTrace stabilizedTrace (a*t) q.val
        (nested_projection (repeatFlatten p) (repeatFlatten_projection p hp) q hq))
      (cornerTopology (cornerStabilizationTopology p hp) q hq)
      (cornerTopology (stabilizationTopology G) q.val
        (nested_projection (repeatFlatten p) (repeatFlatten_projection p hp) q hq)) where
  equiv := nestedCornerEquiv (repeatFlatten p) (repeatFlatten_projection p hp) q hq
  trace_eq x := by
    change ((a*t:ℝ):ℂ)⁻¹ * stabilizedTrace x.val.val=(t:ℂ)⁻¹*((a:ℂ)⁻¹*stabilizedTrace x.val.val)
    rw [Complex.ofReal_mul,mul_inv_rev, mul_assoc]
  normal := nestedCornerEquiv_normal _ _ _ _ _
  inverse_normal := nestedCornerEquiv_symm_normal _ _ _ _ _

theorem cornerStabilization_allPositive
    (hpos : ∀(t : ℝ),0<t → ∀(p : stabilization G)(hp : IsStarProjection p),
      stabilizedProjectionTrace p=ENNReal.ofReal t → Nonempty (GroupCornerNormalIso t p hp))
    (a : ℝ) (ha : 0<a) (p : stabilization G) (hp : IsStarProjection p)
    (hpτ : stabilizedProjectionTrace p=ENNReal.ofReal a) (t : ℝ) (ht : 0<t)
    (q : CornerStabilization p hp) (hq : IsStarProjection q)
    (hqτ : cornerStabilizationProjectionTrace a p hp q=ENNReal.ofReal t) :
    Nonempty (NormalTracialEquiv
      (normalizedCornerTrace (cornerStabilizationTrace a p hp) t q hq)
      (normalizedCornerTrace stabilizedTrace a p hp)
      (cornerTopology (cornerStabilizationTopology p hp) q hq)
      (cornerTopology (stabilizationTopology G) p hp)) := by
  have hqa := (cornerStabilization_weight_iff a ha p hp t ht.le q).mp hqτ
  obtain ⟨E⟩ := hpos (a*t) (mul_pos ha ht) q.val
    (nested_projection (repeatFlatten p) (repeatFlatten_projection p hp) q hq) hqa
  obtain ⟨F⟩ := hpos a ha p hp hpτ
  exact ⟨((nestedNormalizedIso a t p hp q hq).trans E).trans F.symm⟩
end FreeGroupFactorMain.Amplification

end

end OAI
