import OAI.Geometry.QuadricBundles.Model

namespace OAI

namespace QuadricCounterexample
open Set Filter Topology Metric OnePoint
noncomputable section
open scoped Matrix.Norms.Elementwise ComplexOrder

@[simp] lemma reciprocalP1_infty : reciprocalP1 ∞ = (0 : ℂ) := rfl
@[simp] lemma reciprocalP1_zero : reciprocalP1 (0 : ℂ) = ∞ := by simp [reciprocalP1]
lemma reciprocalP1_coe {z : ℂ} (hz : z ≠ 0) : reciprocalP1 z = (z⁻¹ : ℂ) := by
  simp [reciprocalP1,hz]

@[simp] lemma reciprocalP1_involutive (x : ProjectiveLine) :
    reciprocalP1 (reciprocalP1 x) = x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst z; simp
    · rw [reciprocalP1_coe hz, reciprocalP1_coe (inv_ne_zero hz), inv_inv]

lemma reciprocalP1_coe_continuousAt_zero :
    ContinuousAt (fun z : ℂ ↦ reciprocalP1 z) 0 := by
  rw [continuousAt_iff_punctured_nhds, reciprocalP1_zero]
  have he : (fun z : ℂ ↦ reciprocalP1 z) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ ↦ ((z⁻¹ : ℂ) : ProjectiveLine)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact reciprocalP1_coe hz
  apply Tendsto.congr' he.symm
  have ht : Tendsto Inv.inv (𝓝[≠] (0 : ℂ)) (coclosedCompact ℂ) := by
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_nhdsNE_zero (α := ℂ))
  exact (show Tendsto ((↑) : ℂ → ProjectiveLine) (coclosedCompact ℂ) (𝓝 ∞) from
    (by rw [← OnePoint.comap_coe_nhds_infty]; exact tendsto_comap)).comp ht

lemma continuous_reciprocalP1 : Continuous reciprocalP1 := by
  rw [OnePoint.continuous_iff]
  constructor
  · have he : (fun z : ℂ ↦ reciprocalP1 z) =ᶠ[coclosedCompact ℂ]
        (fun z : ℂ ↦ ((z⁻¹ : ℂ) : ProjectiveLine)) := by
      have hn : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
        rw [coclosedCompact_eq_cocompact]
        exact isCompact_singleton.compl_mem_cocompact
      filter_upwards [hn] with z hz
      exact reciprocalP1_coe hz
    apply Tendsto.congr' he.symm
    apply OnePoint.continuous_coe.continuousAt.tendsto.comp
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded (α := ℂ))
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z; exact reciprocalP1_coe_continuousAt_zero
    · have he : (fun w : ℂ ↦ reciprocalP1 w) =ᶠ[𝓝 z]
          (fun w : ℂ ↦ ((w⁻¹ : ℂ) : ProjectiveLine)) := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        exact reciprocalP1_coe hw
      exact (OnePoint.continuous_coe.continuousAt.comp
        (continuousAt_id.inv₀ hz)).congr_of_eventuallyEq he

def reciprocalP1Homeomorph : ProjectiveLine ≃ₜ ProjectiveLine where
  toFun := reciprocalP1
  invFun := reciprocalP1
  left_inv := reciprocalP1_involutive
  right_inv := reciprocalP1_involutive
  continuous_toFun := continuous_reciprocalP1
  continuous_invFun := continuous_reciprocalP1

lemma affineP1_continuous (i : Fin 2) : Continuous (affineP1 i) := by
  fin_cases i
  · exact continuous_reciprocalP1.comp OnePoint.continuous_coe
  · exact OnePoint.continuous_coe

lemma affineP1_isOpenEmbedding (i : Fin 2) : IsOpenEmbedding (affineP1 i) := by
  fin_cases i
  · exact reciprocalP1Homeomorph.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  · exact OnePoint.isOpenEmbedding_coe

lemma affineP1_cover (x : ProjectiveLine) : ∃ i : Fin 2, ∃ z : ℂ, affineP1 i z = x := by
  induction x using OnePoint.rec with
  | infty => exact ⟨0,0,by simp [affineP1]⟩
  | coe z => exact ⟨1,z,rfl⟩

lemma affineQuadric_isOpenEmbedding (i : Fin 2 × Fin 2) :
    IsOpenEmbedding (affineQuadric i) :=
  (affineP1_isOpenEmbedding i.1).prodMap (affineP1_isOpenEmbedding i.2)

lemma affineQuadric_cover (x : QuadricSurface) :
    ∃ i : Fin 2 × Fin 2, ∃ z : ℂ × ℂ, affineQuadric i z = x := by
  obtain ⟨i,z,hz⟩ := affineP1_cover x.1
  obtain ⟨j,w,hw⟩ := affineP1_cover x.2
  exact ⟨(i,j),(z,w),Prod.ext hz hw⟩

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set OnePoint MvPolynomial
noncomputable section

@[simp] lemma coordP1_affine (i : Fin 2) (z : ℂ) : coordP1 i (affineP1 i z) = z := by
  fin_cases i <;> simp [coordP1, affineP1]

@[simp] lemma coordQuadric_affine (i : Fin 2 × Fin 2) (z : BaseCoordinates) :
    coordQuadric i (affineQuadric i z) = z := by
  ext <;> simp [coordQuadric, affineQuadric]

lemma affineP1_coord {i : Fin 2} {x : ProjectiveLine} (hx : x ∈ range (affineP1 i)) :
    affineP1 i (coordP1 i x) = x := by
  obtain ⟨z,rfl⟩ := hx
  rw [coordP1_affine]

lemma affineQuadric_coord {i : Fin 2 × Fin 2} {x : QuadricSurface}
    (hx : x ∈ range (affineQuadric i)) : affineQuadric i (coordQuadric i x) = x := by
  obtain ⟨z,rfl⟩ := hx
  rw [coordQuadric_affine]

lemma mem_range_affineP1 (i : Fin 2) (x : ProjectiveLine) :
    x ∈ range (affineP1 i) ↔ if i = 0 then x ≠ (0 : ℂ) else x ≠ ∞ := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    constructor
    · rintro ⟨z,rfl⟩ h
      have hh := congrArg reciprocalP1 h
      simp [affineP1] at hh
    · intro hx
      refine ⟨coordP1 0 x, ?_⟩
      induction x using OnePoint.rec with
      | infty => simp [coordP1,affineP1]
      | coe z =>
        have hz : z ≠ 0 := by simpa using hx
        simp [coordP1,affineP1,reciprocalP1_coe hz, reciprocalP1_coe (inv_ne_zero hz)]
  · constructor
    · rintro ⟨z,rfl⟩; simp [affineP1]
    · intro hx
      induction x using OnePoint.rec with
      | infty => exact False.elim (hx rfl)
      | coe z => exact ⟨z,rfl⟩

lemma powerP1_affine {m : ℕ} (hm : 0 < m) (i : Fin 2) (z : ℂ) :
    powerP1 m (affineP1 i z) = affineP1 i (z^m) := by
  fin_cases i
  · by_cases hz : z = 0
    · subst z; simp [affineP1,powerP1,hm.ne']
    · simp [affineP1,reciprocalP1_coe hz, reciprocalP1_coe (pow_ne_zero m hz),
        powerP1,inv_pow]
  · rfl

lemma powerQuadric_affine {m : ℕ} (hm : 0 < m) (i : Fin 2 × Fin 2) (z : BaseCoordinates) :
    powerQuadric m (affineQuadric i z) = affineQuadric i (z.1^m,z.2^m) := by
  simp [powerQuadric,affineQuadric,powerP1_affine hm]

lemma powerP1_mem_range_iff {m : ℕ} (hm : 0 < m) (i : Fin 2) (x : ProjectiveLine) :
    powerP1 m x ∈ range (affineP1 i) ↔ x ∈ range (affineP1 i) := by
  rw [mem_range_affineP1,mem_range_affineP1]
  induction x using OnePoint.rec with
  | infty => simp [powerP1]
  | coe z =>
    by_cases hi : i = 0
    · simp [powerP1,hi,pow_eq_zero_iff hm.ne']
    · simp [powerP1,hi]

lemma mem_range_affineQuadric (i : Fin 2 × Fin 2) (x : QuadricSurface) :
    x ∈ range (affineQuadric i) ↔ x.1 ∈ range (affineP1 i.1) ∧ x.2 ∈ range (affineP1 i.2) := by
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨⟨z.1,rfl⟩,⟨z.2,rfl⟩⟩
  · rintro ⟨⟨z,hz⟩,⟨w,hw⟩⟩; exact ⟨(z,w),Prod.ext hz hw⟩

lemma powerQuadric_mem_range_iff {m : ℕ} (hm : 0 < m) (i : Fin 2 × Fin 2) (x : QuadricSurface) :
    powerQuadric m x ∈ range (affineQuadric i) ↔ x ∈ range (affineQuadric i) := by
  rw [mem_range_affineQuadric,mem_range_affineQuadric]
  exact and_congr (powerP1_mem_range_iff hm i.1 x.1) (powerP1_mem_range_iff hm i.2 x.2)

def pullbackPolynomial (m : ℕ) (p : BasePolynomial) : BasePolynomial :=
  (MvPolynomial.bind₁ fun j ↦ MvPolynomial.X j ^ m) p

lemma baseEval_pullback (m : ℕ) (p : BasePolynomial) (z : BaseCoordinates) :
    baseEval (pullbackPolynomial m p) z = baseEval p (z.1^m,z.2^m) := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ ((MvPolynomial.bind₁ _) p) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval _ p = MvPolynomial.eval _ p
  apply congrArg (fun f : Fin 2 → ℂ ↦ MvPolynomial.eval f p)
  funext j; fin_cases j <;> simp

lemma power_principalChart {m : ℕ} (hm : 0 < m) (i : Fin 2 × Fin 2)
    (p : BasePolynomial) (x : QuadricSurface) :
    x ∈ principalChart i (pullbackPolynomial m p) ↔ powerQuadric m x ∈ principalChart i p := by
  constructor
  · rintro ⟨hx,hp⟩
    obtain ⟨z,rfl⟩ := hx
    rw [powerQuadric_affine hm]
    constructor
    · exact ⟨_,rfl⟩
    · simpa only [coordQuadric_affine,baseEval_pullback] using hp
  · rintro ⟨hx,hp⟩
    have hx' := (powerQuadric_mem_range_iff hm i x).mp hx
    obtain ⟨z,rfl⟩ := hx'
    constructor
    · exact ⟨_,rfl⟩
    · simpa only [powerQuadric_affine hm,coordQuadric_affine,baseEval_pullback] using hp

lemma coordP1_overlap {i j : Fin 2} {x : ProjectiveLine}
    (hi : x ∈ range (affineP1 i)) (hj : x ∈ range (affineP1 j)) (hij : i ≠ j) :
    coordP1 i x * coordP1 j x = 1 := by
  obtain ⟨z,rfl⟩ := hi
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq,not_true_eq_false]
  · have hz : z ≠ 0 := by
      intro h; subst z
      simp [affineP1] at hj
    rw [coordP1_affine]
    simp [coordP1,affineP1,reciprocalP1_coe hz, mul_inv_cancel₀ hz]
  · have hz : z ≠ 0 := by
      rw [mem_range_affineP1] at hj
      simpa [affineP1] using hj
    simp [coordP1,affineP1,reciprocalP1_coe hz,mul_inv_cancel₀ hz]

lemma hyperplaneTransition_mul (i j k : Fin 2) (x : ProjectiveLine)
    (hi : x ∈ range (affineP1 i)) (hj : x ∈ range (affineP1 j))
    (hk : x ∈ range (affineP1 k)) :
    hyperplaneTransition i j x * hyperplaneTransition j k x = hyperplaneTransition i k x := by
  by_cases hij : i = j
  · subst j; simp [hyperplaneTransition]
  by_cases hjk : j = k
  · subst k; simp [hyperplaneTransition]
  have hik : i = k := by omega
  subst k
  simp only [hyperplaneTransition,hij,hjk,↓reduceIte]
  exact coordP1_overlap hi hj hij

lemma polarizationTransition_mul (i j k : Fin 2 × Fin 2) (x : QuadricSurface)
    (hi : x ∈ range (affineQuadric i)) (hj : x ∈ range (affineQuadric j))
    (hk : x ∈ range (affineQuadric k)) :
    polarizationTransition i j x * polarizationTransition j k x = polarizationTransition i k x := by
  rw [mem_range_affineQuadric] at hi hj hk
  unfold polarizationTransition
  calc
    _ = (hyperplaneTransition i.1 j.1 x.1 * hyperplaneTransition j.1 k.1 x.1) *
        (hyperplaneTransition i.2 j.2 x.2 * hyperplaneTransition j.2 k.2 x.2) := by ring
    _ = _ := by rw [hyperplaneTransition_mul _ _ _ _ hi.1 hj.1 hk.1,
      hyperplaneTransition_mul _ _ _ _ hi.2 hj.2 hk.2]

@[simp] lemma baseEval_one (z : BaseCoordinates) : baseEval 1 z = 1 := by simp [baseEval]
@[simp] lemma baseEval_zero (z : BaseCoordinates) : baseEval 0 z = 0 := by simp [baseEval]
@[simp] lemma baseEval_mul (p q : BasePolynomial) (z : BaseCoordinates) :
    baseEval (p*q) z = baseEval p z * baseEval q z := by simp [baseEval]

lemma algebraicallyRegular_polynomial (U : Set BaseCoordinates) (p : BasePolynomial) :
    AlgebraicallyRegularOn U (baseEval p) := by
  intro z _
  exact ⟨p,1,by simp,fun w _ _ ↦ by simp⟩

lemma AlgebraicallyRegularOn.mono {U W : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hU : W ⊆ U) : AlgebraicallyRegularOn W f := by
  intro z hz
  obtain ⟨p,q,hq,he⟩ := hf z (hU hz)
  exact ⟨p,q,hq,fun w hw hqw ↦ he w (hU hw) hqw⟩

lemma AlgebraicallyRegularOn.congr {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (he : ∀ z ∈ U, f z = g z) : AlgebraicallyRegularOn U g := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  exact ⟨p,q,hq,fun w hw hqw ↦ (he w hw).symm.trans (h w hw hqw)⟩

lemma AlgebraicallyRegularOn.mul {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hg : AlgebraicallyRegularOn U g) :
    AlgebraicallyRegularOn U (fun z ↦ f z * g z) := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  obtain ⟨r,s,hs,k⟩ := hg z hz
  refine ⟨p*r,q*s,by simpa using mul_ne_zero hq hs,?_⟩
  intro w hw hqw
  have hh : baseEval q w ≠ 0 ∧ baseEval s w ≠ 0 := by simpa using hqw
  dsimp only
  rw [h w hw hh.1,k w hw hh.2,baseEval_mul,baseEval_mul,div_mul_div_comm]

lemma AlgebraicallyRegularOn.comp_power {U W : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (m : ℕ)
    (hU : ∀ z ∈ W, (z.1^m,z.2^m) ∈ U) :
    AlgebraicallyRegularOn W (fun z ↦ f (z.1^m,z.2^m)) := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf (z.1^m,z.2^m) (hU z hz)
  refine ⟨pullbackPolynomial m p,pullbackPolynomial m q,by simpa [baseEval_pullback] using hq,?_⟩
  intro w hw hqw
  simp only [baseEval_pullback] at hqw ⊢
  exact h _ (hU w hw) hqw

lemma polarizationTransition_polynomial (i j : Fin 2 × Fin 2) (z : BaseCoordinates) :
    polarizationTransition i j (affineQuadric i z) =
      baseEval ((if i.1=j.1 then 1 else MvPolynomial.X 0) *
        (if i.2=j.2 then 1 else MvPolynomial.X 1)) z := by
  simp only [polarizationTransition,hyperplaneTransition,affineQuadric,coordP1_affine]
  split_ifs <;> simp [baseEval]

lemma polarizationTransition_regular (i j : Fin 2 × Fin 2) (U : Set BaseCoordinates) :
    AlgebraicallyRegularOn U (fun z ↦ polarizationTransition i j (affineQuadric i z)) := by
  exact (algebraicallyRegular_polynomial U _).congr (fun z _ ↦ (polarizationTransition_polynomial i j z).symm)

def powerPullbackTwist (G : AlgebraicRankTwoBundle) (m : ℕ) (hm : 0 < m) :
    AlgebraicRankTwoBundle where
  numberOfCharts := G.numberOfCharts
  chart := G.chart
  equation i := pullbackPolynomial m (G.equation i)
  finiteCover i hi := by
    unfold pullbackPolynomial
    rw [G.finiteCover i hi]
    exact map_zero _
  covers x := by
    obtain ⟨i,hi⟩ := G.covers (powerQuadric m x)
    exact ⟨i,(power_principalChart hm _ _ _).mpr hi⟩
  transition i j x := polarizationTransition (G.chart i) (G.chart j) x •
    G.transition i j (powerQuadric m x)
  transition_self i x hx := by
    rw [G.transition_self i _ ((power_principalChart hm _ _ _).mp hx)]
    simp [polarizationTransition,hyperplaneTransition]
  transition_mul i j k x hi hj hk := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [polarizationTransition_mul _ _ _ _ hi.1 hj.1 hk.1]
    rw [G.transition_mul i j k _ ((power_principalChart hm _ _ _).mp hi)
      ((power_principalChart hm _ _ _).mp hj) ((power_principalChart hm _ _ _).mp hk)]
  transition_regular i j a b := by
    have hreg := (G.transition_regular i j a b).comp_power m
      (W := {z | baseEval (pullbackPolynomial m (G.equation i)) z ≠ 0 ∧
        affineQuadric (G.chart i) z ∈ principalChart (G.chart j) (pullbackPolynomial m (G.equation j))})
      (fun z hz ↦ show baseEval (G.equation i) (z.1^m,z.2^m) ≠ 0 ∧
          affineQuadric (G.chart i) (z.1^m,z.2^m) ∈ principalChart (G.chart j) (G.equation j) from
        ⟨by simpa only [baseEval_pullback] using hz.1,
         by rw [← powerQuadric_affine hm]; exact (power_principalChart hm _ _ _).mp hz.2⟩)
    apply ((polarizationTransition_regular (G.chart i) (G.chart j) _).mul hreg).congr
    intro z _
    simp only [powerQuadric_affine hm,Matrix.smul_apply,smul_eq_mul]

lemma powerPullbackTwist_spec (G : AlgebraicRankTwoBundle) (m : ℕ) (hm : 0 < m) :
    IsPowerPullbackTwist G m (powerPullbackTwist G m hm) :=
  ⟨rfl,rfl,fun _ ↦ rfl,fun _ _ _ _ _ ↦ rfl⟩

lemma exists_powerPullbackTwist (G : AlgebraicRankTwoBundle) :
    ∃ E : ℕ → AlgebraicRankTwoBundle, ∀ m, 0 < m → IsPowerPullbackTwist G m (E m) := by
  refine ⟨fun m ↦ if hm : 0 < m then powerPullbackTwist G m hm else G, ?_⟩
  intro m hm
  simp only [dite_eq_left hm]
  exact powerPullbackTwist_spec G m hm

end
end QuadricCounterexample

end OAI
