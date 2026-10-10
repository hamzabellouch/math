import OAI.Analysis.InterpolatedFactors.Stabilization

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25

namespace FreeGroupFactorMain.Amplification
namespace OperatorSum
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Operator (E : Type u_6) [NormedAddCommGroup E] [InnerProductSpace ℂ E] := E →L[ℂ] E

def IsPartial (U : Operator E) : Prop := U*star U*U=U

 theorem initial_projection {U : Operator E} (h : IsPartial U) : IsStarProjection (star U*U) := by
  constructor
  · change (star U*U)*(star U*U)=star U*U
    calc
      _ = star U*(U*star U*U) := by noncomm_ring
      _ = _ := by rw [h]
  · simp only [IsSelfAdjoint,star_mul,star_star]

 theorem partial_star {U : Operator E} (h : IsPartial U) : IsPartial (star U) := by
  have hs := congrArg star h
  simpa only [IsPartial,star_mul,star_star,mul_assoc] using hs

 theorem partial_norm_le {U : Operator E} (h : IsPartial U) : ‖U‖ ≤ 1 := by
  have hn := (initial_projection h).norm_le (star U*U)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg U]

structure OrthogonalPartials {ι : Type u_7} (U : ι → Operator E) : Prop where
  isPartial : ∀ i, IsPartial (U i)
  initial : Pairwise (fun i j => star (U i)*U j=0)
  final : Pairwise (fun i j => U i*star (U j)=0)

 theorem OrthogonalPartials.adjoint {ι : Type u_8} {U : ι → Operator E} (h : OrthogonalPartials U) :
    OrthogonalPartials (fun i => star (U i)) where
  isPartial i := partial_star (h.isPartial i)
  initial i j hij := by simpa only [star_star] using h.final hij
  final i j hij := by simpa only [star_star] using h.initial hij

 theorem OrthogonalPartials.finite_offdiag {ι : Type u_9} {U : ι → Operator E}
    (h : OrthogonalPartials U) (s : Finset ι) :
    star (∑ i ∈ s, U i)*(∑ i ∈ s, U i) = ∑ i ∈ s, star (U i)*U i := by
  classical
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_eq_single_of_mem i hi (fun j _ hji => h.initial hji)

 theorem OrthogonalPartials.finite_partial {ι : Type u_10} {U : ι → Operator E}
    (h : OrthogonalPartials U) (s : Finset ι) : IsPartial (∑ i ∈ s, U i) := by
  classical
  change (∑i ∈ s,U i)*star (∑i ∈ s,U i)*(∑i ∈ s,U i) = _
  have hs : (∑i ∈ s,U i)*star (∑i ∈ s,U i) = ∑i ∈ s,U i*star (U i) := by
    simpa only [star_sum,star_star] using h.adjoint.finite_offdiag s
  rw [hs,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single_of_mem i hi]
  · exact h.isPartial i
  · intro j _ hji
    rw [mul_assoc,h.initial (Ne.symm hji),mul_zero]

 theorem OrthogonalPartials.ranges {ι : Type u_11} {U : ι → Operator E}
    (h : OrthogonalPartials U) :
    OrthogonalFamily ℂ (fun i => U i |>.toLinearMap.range)
      (fun i => (U i).toLinearMap.range.subtypeₗᵢ) := by
  rintro i j hij ⟨_,x,rfl⟩ ⟨_,y,rfl⟩
  change inner ℂ (U i x) (U j y) = 0
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ x ((star (U i)*U j) y) = 0
  rw [h.initial hij,zero_apply,inner_zero_right]

 theorem OrthogonalPartials.apply_summable {ι : Type u_12} {U : ι → Operator E}
    (h : OrthogonalPartials U) (x : E) : Summable (fun i => U i x) := by
  let f : ∀ i, (U i).toLinearMap.range := fun i => ⟨U i x,LinearMap.mem_range_self _ x⟩
  apply (h.ranges.summable_iff_norm_sq_summable f).mpr
  apply summable_of_sum_le (fun i => sq_nonneg ‖f i‖) (c := ‖x‖^2)
  intro s
  rw [← h.ranges.norm_sum f s]
  have hn : ‖∑i ∈ s, U i x‖ ≤ ‖x‖ := by
    have hb := (∑i ∈ s, U i).le_opNorm x
    have ho := partial_norm_le (h.finite_partial s)
    calc
      _ = ‖(∑i ∈ s,U i) x‖ := by simp only [sum_apply]
      _ ≤ ‖∑i ∈ s,U i‖*‖x‖ := hb
      _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right ho (norm_nonneg _)
      _ = _ := one_mul _
  change ‖∑i ∈ s,U i x‖^2 ≤ ‖x‖^2
  simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hn

 theorem OrthogonalPartials.tsum_bound {ι : Type u_13} {U : ι → Operator E}
    (h : OrthogonalPartials U) (x : E) : ‖∑'i, U i x‖ ≤ ‖x‖ := by
  apply le_of_tendsto ((h.apply_summable x).hasSum.norm)
  apply Filter.Eventually.of_forall
  intro s
  calc
    _ = ‖(∑i ∈ s,U i) x‖ := by simp only [sum_apply]
    _ ≤ ‖∑i ∈ s,U i‖*‖x‖ := (∑i ∈ s,U i).le_opNorm x
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right (partial_norm_le (h.finite_partial s)) (norm_nonneg _)
    _ = _ := one_mul _

 def OrthogonalPartials.sum {ι : Type u_14} {U : ι → Operator E} (h : OrthogonalPartials U) : Operator E :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑'i,U i x
      map_add' := fun x y => by
        simp only [map_add]
        exact (h.apply_summable x).tsum_add (h.apply_summable y)
      map_smul' := fun c x => by
        simp only [map_smul,RingHom.id_apply]
        exact (h.apply_summable x).tsum_const_smul c }
    1 (fun x => by
      change ‖∑' i, U i x‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact h.tsum_bound x)

 theorem OrthogonalPartials.sum_apply {ι : Type u_15} {U : ι → Operator E}
    (h : OrthogonalPartials U) (x : E) : h.sum x = ∑'i,U i x := rfl

end OperatorSum
end FreeGroupFactorMain.Amplification
namespace FreeGroupFactorMain.Amplification.OperatorSum

section
variable {E : Type u_16} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type u_17} {U : ι → Operator E}

 theorem OrthogonalPartials.sum_star (h : OrthogonalPartials U) :
    h.adjoint.sum = star h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rw [h.adjoint.sum_apply,h.sum_apply]
  change (innerSL ℂ y) (∑' i, star (U i) x) = ((innerSL ℂ).flip x) (∑' i, U i y)
  rw [(innerSL ℂ y).map_tsum (h.adjoint.apply_summable x)]
  have hr := ((innerSL ℂ).flip x).map_tsum (h.apply_summable y)
  rw [hr]
  apply tsum_congr
  intro i
  exact ContinuousLinearMap.adjoint_inner_right (U i) y x

 theorem OrthogonalPartials.star_single_mul_sum (h : OrthogonalPartials U) (i : ι) :
    star (U i)*h.sum = star (U i)*U i := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,h.sum_apply,(star (U i)).map_tsum (h.apply_summable x)]
  rw [tsum_eq_single i]
  · rfl
  · intro j hji
    change (star (U i)*U j) x = 0
    rw [h.initial hji.symm,zero_apply]

 theorem OrthogonalPartials.star_sum_mul_single (h : OrthogonalPartials U) (i : ι) :
    star h.sum*U i = star (U i)*U i := by
  have he := congrArg star (h.star_single_mul_sum i)
  simpa only [star_mul,star_star] using he

 theorem OrthogonalPartials.sum_mul_star_single (h : OrthogonalPartials U) (i : ι) :
    h.sum*star (U i) = U i*star (U i) := by
  have he := h.adjoint.star_sum_mul_single i
  simpa only [h.sum_star,star_star] using he

 theorem OrthogonalPartials.sum_partial (h : OrthogonalPartials U) : IsPartial h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  change (h.sum*star h.sum) (h.sum x) = h.sum x
  rw [h.sum_apply,(h.sum*star h.sum).map_tsum (h.apply_summable x)]
  apply tsum_congr
  intro i
  change (h.sum*star h.sum*U i) x = U i x
  rw [mul_assoc,h.star_sum_mul_single,← mul_assoc,h.sum_mul_star_single,h.isPartial]

 theorem OrthogonalPartials.sum_mem_centralizer (h : OrthogonalPartials U)
    (s : Set (Operator E)) (hU : ∀ i, U i ∈ StarSubalgebra.centralizer ℂ s) :
    h.sum ∈ StarSubalgebra.centralizer ℂ s := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have hc (i) := (StarSubalgebra.mem_centralizer_iff ℂ).mp (hU i) S hS
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change S (h.sum x) = h.sum (S x)
    rw [h.sum_apply,h.sum_apply,S.map_tsum (h.apply_summable x)]
    apply tsum_congr
    intro i
    exact DFunLike.congr_fun (hc i).1 x
  · apply ContinuousLinearMap.ext
    intro x
    change star S (h.sum x) = h.sum (star S x)
    rw [h.sum_apply,h.sum_apply,(star S).map_tsum (h.apply_summable x)]
    apply tsum_congr
    intro i
    exact DFunLike.congr_fun (hc i).2 x

 theorem OrthogonalPartials.sum_left_support (h : OrthogonalPartials U)
    (q : Operator E) (hq : ∀ i, q*U i=U i) : q*h.sum=h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,h.sum_apply,q.map_tsum (h.apply_summable x)]
  apply tsum_congr
  intro i
  exact DFunLike.congr_fun (hq i) x

 theorem OrthogonalPartials.sum_right_support (h : OrthogonalPartials U)
    (p : Operator E) (hp : ∀ i, U i*p=U i) : h.sum*p=h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,h.sum_apply,h.sum_apply]
  apply tsum_congr
  intro i
  exact DFunLike.congr_fun (hp i) x

end
variable {E : Type u_18} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem residual_projection {p e : Operator E} (hp : IsStarProjection p)
    (he : IsStarProjection e) (hep : e*p=e) : IsStarProjection (p-e) := by
  have hpe : p*e=e := by
    have h := congrArg star hep
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,he.isSelfAdjoint.star_eq] using h
  exact ⟨he.isIdempotentElem.sub hp.isIdempotentElem hep hpe,hp.isSelfAdjoint.sub he.isSelfAdjoint⟩

 theorem OrthogonalPartials.sum_final_mul_single {ι : Type u_19} {U : ι → Operator E}
    (h : OrthogonalPartials U) (i : ι) : h.sum*star h.sum*U i=U i := by
  rw [mul_assoc,h.star_sum_mul_single,← mul_assoc,h.sum_mul_star_single,h.isPartial]

 theorem OrthogonalPartials.single_mul_sum_initial {ι : Type u_20} {U : ι → Operator E}
    (h : OrthogonalPartials U) (i : ι) : U i*star h.sum*h.sum=U i := by
  have he := congrArg star (h.adjoint.sum_final_mul_single i)
  simpa only [h.sum_star,star_mul,star_star,mul_assoc] using he

 theorem IsPartial.initial_zero {U : Operator E} (h : star U*U=0) : U=0 := by
  have hn := congrArg norm h
  rw [CStarRing.norm_star_mul_self,norm_zero] at hn
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg U])

def PartialFamily (s : Set (Operator E)) (p q : Operator E) (F : Set (Operator E)) : Prop :=
  (∀ U ∈ F, U ≠ 0 ∧ U ∈ StarSubalgebra.centralizer ℂ s ∧ IsPartial U ∧ q*U=U ∧ U*p=U) ∧
    F.Pairwise (fun U V => star U*V=0 ∧ U*star V=0)

 theorem maximal_partial_family (s : Set (Operator E)) (p q : Operator E) :
    ∃ F, Maximal (PartialFamily s p q) F := by
  apply zorn_subset {F | PartialFamily s p q F}
  intro c hc hchain
  refine ⟨⋃₀ c,⟨?_,?_⟩,fun S hS => Set.subset_sUnion_of_mem hS⟩
  · intro U hU
    obtain ⟨F,hF,hUF⟩ := Set.mem_sUnion.mp hU
    exact (hc hF).1 U hUF
  · intro U hU V hV hne
    obtain ⟨F,hF,hUF⟩ := Set.mem_sUnion.mp hU
    obtain ⟨G,hG,hVG⟩ := Set.mem_sUnion.mp hV
    rcases hchain.total hF hG with hFG|hGF
    · exact (hc hG).2 (hFG hUF) hVG hne
    · exact (hc hF).2 hUF (hGF hVG) hne

 theorem PartialFamily.orthogonal {s : Set (Operator E)} {p q : Operator E}
    {F : Set (Operator E)} (h : PartialFamily s p q F) :
    OrthogonalPartials (fun U : F => (U : Operator E)) where
  isPartial U := (h.1 U U.property).2.2.1
  initial := by
    intro U V hne
    exact (h.2 U.property V.property (fun he => hne (Subtype.ext he))).1
  final := by
    intro U V hne
    exact (h.2 U.property V.property (fun he => hne (Subtype.ext he))).2

 theorem commutant_maximal_partial (s : Set (Operator E)) (p q : Operator E)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpm : p ∈ StarSubalgebra.centralizer ℂ s) (hqm : q ∈ StarSubalgebra.centralizer ℂ s) :
    ∃ V ∈ StarSubalgebra.centralizer ℂ s, IsPartial V ∧ q*V=V ∧ V*p=V ∧
      ∀ T ∈ StarSubalgebra.centralizer ℂ s, (q-V*star V)*T*(p-star V*V)=0 := by
  classical
  obtain ⟨F,hF⟩ := maximal_partial_family s p q
  let h := hF.1.orthogonal
  let V := h.sum
  have hV : V ∈ StarSubalgebra.centralizer ℂ s :=
    h.sum_mem_centralizer s (fun U => (hF.1.1 U U.property).2.1)
  have hVp : V*p=V := h.sum_right_support p (fun U => (hF.1.1 U U.property).2.2.2.2)
  have hqV : q*V=V := h.sum_left_support q (fun U => (hF.1.1 U U.property).2.2.2.1)
  refine ⟨V,hV,h.sum_partial,hqV,hVp,?_⟩
  intro T hT
  let pr := p-star V*V
  let qr := q-V*star V
  have hpr : IsStarProjection pr := residual_projection hp (initial_projection h.sum_partial) (by rw [mul_assoc,hVp])
  have hqr : IsStarProjection qr := residual_projection hq (by simpa only [star_star] using initial_projection (partial_star h.sum_partial)) (by
    have he := congrArg star hqV
    simp only [star_mul,hq.isSelfAdjoint.star_eq] at he
    rw [mul_assoc,he])
  have hprm : pr ∈ StarSubalgebra.centralizer ℂ s := sub_mem hpm (mul_mem (star_mem hV) hV)
  have hqrm : qr ∈ StarSubalgebra.centralizer ℂ s := sub_mem hqm (mul_mem hV (star_mem hV))
  have hq_qr : q*qr=qr := by
    dsimp [qr]
    rw [mul_sub,hq.isIdempotentElem,← mul_assoc,hqV]
  have hpr_p : pr*p=pr := by
    dsimp [pr]
    rw [sub_mul,hp.isIdempotentElem,mul_assoc,hVp]
  by_contra hne
  let W := Polar.partialIsometry (qr*T*pr)
  have hWne : W ≠ 0 := Polar.partialIsometry_nonzero hne
  have hWm : W ∈ StarSubalgebra.centralizer ℂ s :=
    Polar.partialIsometry_mem_centralizer s (mul_mem (mul_mem hqrm hT) hprm)
  have hWp : W*pr=W := Polar.partialIsometry_right_support hpr.isSelfAdjoint (by rw [mul_assoc,hpr.isIdempotentElem])
  have hqW : qr*W=W := Polar.partialIsometry_left_support (by rw [← mul_assoc,← mul_assoc,hqr.isIdempotentElem])
  have hWpartial : IsPartial W := Polar.partialIsometry_partial _
  have hWp' : W*p=W := by rw [← hWp,mul_assoc,hpr_p]
  have hqW' : q*W=W := by rw [← hqW,← mul_assoc,hq_qr]
  have hqrU (U : F) : qr*U=0 := by
    change (q-V*star V)*(U : Operator E)=0
    rw [sub_mul,(hF.1.1 U U.property).2.2.2.1,h.sum_final_mul_single]
    exact sub_self _
  have hUpr (U : F) : (U : Operator E)*pr=0 := by
    change (U : Operator E)*(p-star V*V)=0
    rw [mul_sub,(hF.1.1 U U.property).2.2.2.2,← mul_assoc,h.single_mul_sum_initial]
    exact sub_self _
  have hUW (U : F) : star (U : Operator E)*W=0 ∧ (U : Operator E)*star W=0 := by
    have he := congrArg star (hqrU U)
    simp only [star_mul,hqr.isSelfAdjoint.star_eq,star_zero (Operator E)] at he
    have hw := congrArg star hWp
    simp only [star_mul,hpr.isSelfAdjoint.star_eq] at hw
    constructor
    · rw [← hqW,← mul_assoc,he,zero_mul]
    · rw [← hw,← mul_assoc,hUpr,zero_mul]
  have hWU (U : F) : star W*(U : Operator E)=0 ∧ W*star (U : Operator E)=0 := by
    constructor
    · simpa only [star_mul,star_star,star_zero (Operator E)] using congrArg star (hUW U).1
    · simpa only [star_mul,star_star,star_zero (Operator E)] using congrArg star (hUW U).2
  have hinsert : PartialFamily s p q (insert W F) := by
    constructor
    · intro U hU
      rcases Set.mem_insert_iff.mp hU with rfl|hU
      · exact ⟨hWne,hWm,hWpartial,hqW',hWp'⟩
      · exact hF.1.1 U hU
    · apply hF.1.2.insert
      intro U hU _
      exact ⟨hWU ⟨U,hU⟩,hUW ⟨U,hU⟩⟩
  have hWF : W ∈ F := hF.2 hinsert (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact hWne (IsPartial.initial_zero (hUW ⟨W,hWF⟩).1)

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_21} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def centralSupportSpace (A : StarSubalgebra ℂ (Operator E)) (p : Operator E) : Submodule ℂ E :=
  (Submodule.span ℂ {x | ∃ T ∈ A, ∃ y, x=T (p y)}).topologicalClosure

instance centralSupportSpace_complete (A : StarSubalgebra ℂ (Operator E)) (p : Operator E) :
    CompleteSpace (centralSupportSpace A p) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

 theorem centralSupportSpace_invariant (A : StarSubalgebra ℂ (Operator E)) (p S : Operator E)
    (h : ∀ T ∈ A, ∀ y, ∃ U ∈ A, ∃ z, S (T (p y))=U (p z)) :
    ∀ x ∈ centralSupportSpace A p, S x ∈ centralSupportSpace A p := by
  let K := Submodule.span ℂ {x | ∃ T ∈ A, ∃ y, x=T (p y)}
  have hi : K ∈ Module.End.invtSubmodule S := by
    rw [Module.End.mem_invtSubmodule_iff_map_le,Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro x ⟨T,hT,y,rfl⟩
    change S (T (p y)) ∈ K
    obtain ⟨U,hU,z,he⟩ := h T hT y
    exact Submodule.subset_span ⟨U,hU,z,he⟩
  exact Submodule.topologicalClosure_mem_invtSubmodule hi

 theorem centralSupport_commutes (A : StarSubalgebra ℂ (Operator E)) (p S : Operator E)
    (hS : S ∈ A) : Commute (centralSupportSpace A p).starProjection S := by
  apply starProjection_commute
  · apply centralSupportSpace_invariant
    intro T hT y
    exact ⟨S*T,mul_mem hS hT,y,rfl⟩
  · apply centralSupportSpace_invariant
    intro T hT y
    exact ⟨star S*T,mul_mem (star_mem hS) hT,y,rfl⟩

 theorem centralSupport_mem_centralizer (s : Set (Operator E)) (p : Operator E)
    (hp : p ∈ StarSubalgebra.centralizer ℂ s) :
    (centralSupportSpace (StarSubalgebra.centralizer ℂ s) p).starProjection ∈
      StarSubalgebra.centralizer ℂ s := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have hinv (S' : Operator E) (he : ∀ T ∈ StarSubalgebra.centralizer ℂ s, S'*T=T*S') :
      ∀ x ∈ centralSupportSpace (StarSubalgebra.centralizer ℂ s) p,
        S' x ∈ centralSupportSpace (StarSubalgebra.centralizer ℂ s) p := by
    apply centralSupportSpace_invariant
    intro T hT y
    refine ⟨T,hT,S' y,?_⟩
    change (S'*T*p) y=(T*p*S') y
    rw [he T hT,mul_assoc,he p hp,← mul_assoc]
  have h₁ : ∀ T ∈ StarSubalgebra.centralizer ℂ s, S*T=T*S :=
    fun T hT => ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT S hS).1
  have h₂ : ∀ T ∈ StarSubalgebra.centralizer ℂ s, star S*T=T*star S :=
    fun T hT => ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT S hS).2
  have hc := starProjection_commute _ S (hinv S h₁) (hinv (star S) h₂)
  have hcs := starProjection_commute _ (star S) (hinv (star S) h₂) (by simpa only [star_star] using hinv S h₁)
  exact ⟨hc.eq.symm,hcs.eq.symm⟩

 theorem centralSupport_fixes (A : StarSubalgebra ℂ (Operator E)) (p : Operator E) :
    (centralSupportSpace A p).starProjection*p=p := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨1,one_mem A,x,by simp⟩

 theorem centralSupport_annihilated (A : StarSubalgebra ℂ (Operator E)) (p q : Operator E)
    (h : ∀ T ∈ A, q*T*p=0) : q*(centralSupportSpace A p).starProjection=0 := by
  have hK : centralSupportSpace A p ≤ q.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro x ⟨T,hT,y,rfl⟩
      change (q*T*p) y=0
      rw [h T hT,zero_apply]
    · exact q.isClosed_ker
  apply ContinuousLinearMap.ext
  intro x
  exact hK (Submodule.starProjection_apply_mem _ x)

 theorem cross_corner_nonzero (s : Set (Operator E))
    (hfactor : ∀ P ∈ StarSubalgebra.centralizer ℂ s, IsStarProjection P →
      (∀ S ∈ StarSubalgebra.centralizer ℂ s, Commute P S) → P=0 ∨ P=1)
    (p q : Operator E) (hp : p ∈ StarSubalgebra.centralizer ℂ s) (hpne : p ≠ 0) (hqne : q ≠ 0) :
    ∃ T ∈ StarSubalgebra.centralizer ℂ s, q*T*p ≠ 0 := by
  by_contra! h
  let A := StarSubalgebra.centralizer ℂ s
  let P := (centralSupportSpace A p).starProjection
  have hm : P ∈ A := centralSupport_mem_centralizer s p hp
  have hf : P*p=p := centralSupport_fixes A p
  rcases hfactor P hm isStarProjection_starProjection (fun S hS => centralSupport_commutes A p S hS) with hP|hP
  · apply hpne
    rw [hP,zero_mul] at hf
    exact hf.symm
  · apply hqne
    have hh := centralSupport_annihilated A p q h
    change q*P=0 at hh
    simpa only [hP,mul_one] using hh

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.Amplification.OperatorSum
variable {E : Type u_22} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem factor_partial_comparison (s : Set (Operator E))
    (hfactor : ∀ P ∈ StarSubalgebra.centralizer ℂ s, IsStarProjection P →
      (∀ S ∈ StarSubalgebra.centralizer ℂ s, Commute P S) → P=0 ∨ P=1)
    (p q : Operator E) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpm : p ∈ StarSubalgebra.centralizer ℂ s) (hqm : q ∈ StarSubalgebra.centralizer ℂ s) :
    ∃ V ∈ StarSubalgebra.centralizer ℂ s, IsPartial V ∧ q*V=V ∧ V*p=V ∧
      (star V*V=p ∨ V*star V=q) := by
  obtain ⟨V,hV,hpart,hqV,hVp,hcross⟩ := commutant_maximal_partial s p q hp hq hpm hqm
  refine ⟨V,hV,hpart,hqV,hVp,?_⟩
  by_cases h : p-star V*V=0
  · exact Or.inl (sub_eq_zero.mp h).symm
  · by_cases h' : q-V*star V=0
    · exact Or.inr (sub_eq_zero.mp h').symm
    · obtain ⟨T,hT,hne⟩ := Polar.cross_corner_nonzero s hfactor (p-star V*V) (q-V*star V)
        (sub_mem hpm (mul_mem (star_mem hV) hV)) h h'
      exact (hne (hcross T hT)).elim

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
open OperatorSum
variable {E : Type u_23} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem projection_inner (p : E →L[ℂ] E) (hp : IsStarProjection p) (x : E) :
    inner ℂ x (p x)=(‖p x‖^2 : ℂ) := by
  have he := ContinuousLinearMap.adjoint_inner_right p x (p x)
  rw [← ContinuousLinearMap.star_eq_adjoint,hp.isSelfAdjoint.star_eq] at he
  have hh : p (p x)=p x := congrArg (fun T : E →L[ℂ] E => T x) hp.isIdempotentElem.eq
  rw [hh] at he
  exact he.trans (inner_self_eq_norm_sq_to_K (p x))

 theorem partial_initial_norm_sq (V : E →L[ℂ] E) (hV : IsPartial V) (x : E) :
    ‖(star V*V) x‖^2=‖V x‖^2 := by
  have he : (‖(star V*V) x‖ : ℂ)^2=(‖V x‖ : ℂ)^2 := by
    rw [← projection_inner _ (initial_projection hV)]
    exact (ContinuousLinearMap.adjoint_inner_right V x (V x)).trans (inner_self_eq_norm_sq_to_K (V x))
  exact_mod_cast he

 theorem orthogonal_projection_norm_sq (p q : E →L[ℂ] E)
    (hp : IsSelfAdjoint p) (hpq : p*q=0) (x : E) :
    ‖(p+q) x‖^2=‖p x‖^2+‖q x‖^2 := by
  change ‖p x+q x‖^2=_
  rw [sq,sq,sq]
  apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
  have he := ContinuousLinearMap.adjoint_inner_right p x (q x)
  rw [← ContinuousLinearMap.star_eq_adjoint,hp.star_eq] at he
  have hz : p (q x)=0 := congrArg (fun T : E →L[ℂ] E => T x) hpq
  rw [hz,inner_zero_right] at he
  exact he.symm

 variable {G : Type u_24} [Group G]

 theorem stabilizedProjectionTrace_faithful (T : stabilization G)
    (h : stabilizedProjectionTrace T=0) : T=0 := by
  classical
  have hdelta (j : ℕ) : (T : GroupOperator (ℕ × G)) (lp.single 2 (j,1) (1 : ℂ))=0 := by
    have hh := (ENNReal.tsum_eq_zero.mp h) j
    have hzero : ‖(T : GroupOperator (ℕ × G)) (lp.single 2 (j,1) (1 : ℂ))‖^2=0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hh) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  apply Subtype.ext
  apply matrixEntry_ext
  intro i j
  have hm := (mem_stabilization_iff_matrix _).mp T.property i j
  have hz : matrixEntry (T : GroupOperator (ℕ × G)) i j (lp.single 2 (1 : G) (1 : ℂ))=0 := by
    ext g
    rw [matrixEntry_apply,productSingle_single,hdelta]
    rfl
  have he := groupVN_separating ⟨_,hm⟩ hz
  calc
    matrixEntry (T : GroupOperator (ℕ × G)) i j=0 := congrArg (fun A : groupVonNeumann G => (A : GroupOperator G)) he
    _ = matrixEntry (0 : GroupOperator (ℕ × G)) i j := by
      apply ContinuousLinearMap.ext
      intro ξ
      ext g
      rw [matrixEntry_apply]
      rfl

 theorem stabilizedProjectionTrace_initial (V : stabilization G)
    (hV : IsPartial (V : GroupOperator (ℕ × G))) :
    stabilizedProjectionTrace (star V*V)=stabilizedProjectionTrace V := by
  classical
  apply tsum_congr
  intro j
  congr 1
  exact partial_initial_norm_sq (V : GroupOperator (ℕ × G)) hV _

 theorem stabilizedProjectionTrace_initial_final (V : stabilization G)
    (hV : IsPartial (V : GroupOperator (ℕ × G))) :
    stabilizedProjectionTrace (star V*V)=stabilizedProjectionTrace (V*star V) := by
  classical
  rw [stabilizedProjectionTrace_initial V hV]
  have he := stabilizedProjectionTrace_initial (star V) (partial_star hV)
  rw [star_star,stabilizedProjectionTrace_star] at he
  exact he.symm

 theorem stabilizedProjectionTrace_orthogonal_add (p q : stabilization G)
    (hp : IsSelfAdjoint p) (hpq : p*q=0) :
    stabilizedProjectionTrace (p+q)=stabilizedProjectionTrace p+stabilizedProjectionTrace q := by
  classical
  rw [stabilizedProjectionTrace,stabilizedProjectionTrace,stabilizedProjectionTrace,← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  change ENNReal.ofReal (‖((p : GroupOperator (ℕ × G))+(q : GroupOperator (ℕ × G))) (lp.single 2 (j,1) (1 : ℂ))‖^2)=_
  rw [orthogonal_projection_norm_sq (p : GroupOperator (ℕ × G)) q
    (show IsSelfAdjoint (p : GroupOperator (ℕ × G)) from congrArg Subtype.val hp)
    (congrArg Subtype.val hpq),ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]

 theorem finite_trace_equal_projection_of_le (p e : stabilization G)
    (_hp : IsStarProjection p) (he : IsStarProjection e) (hep : e*p=e)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace e)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) : p=e := by
  have he' : e*(p-e)=0 := by rw [mul_sub,hep,he.isIdempotentElem,sub_self]
  have hs := stabilizedProjectionTrace_orthogonal_add e (p-e) he.isSelfAdjoint he'
  rw [add_sub_cancel,htrace] at hs
  have hzero : stabilizedProjectionTrace (p-e)=0 := by
    have hf : stabilizedProjectionTrace e ≠ ⊤ := htrace ▸ hfinite
    exact (ENNReal.add_right_inj hf).mp (by simpa only [add_zero] using hs.symm)
  exact sub_eq_zero.mp (stabilizedProjectionTrace_faithful (p-e) hzero)

end
open scoped ENNReal
open OperatorSum

 theorem equal_finite_trace_equivalence {G : Type u_25} [Group G]
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (p q : stabilization G) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace q)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) :
    ∃ V : stabilization G, star V*V=p ∧ V*star V=q := by
  have hfac := stabilization_center_projection hbase
  have hp' : IsStarProjection (p : GroupOperator (ℕ × G)) := hp.map (stabilization G).subtype
  have hq' : IsStarProjection (q : GroupOperator (ℕ × G)) := hq.map (stabilization G).subtype
  obtain ⟨V,hV,hpart,hqV,hVp,hside⟩ := factor_partial_comparison (stabilizedRightTranslations G)
    hfac p q hp' hq' p.property q.property
  let U : stabilization G := ⟨V,hV⟩
  have hpart' : IsPartial (U : GroupOperator (ℕ × G)) := hpart
  have hi : IsStarProjection (star U*U) := by
    constructor
    · apply Subtype.ext
      exact (initial_projection hpart).isIdempotentElem
    · apply Subtype.ext
      exact (initial_projection hpart).isSelfAdjoint
  have hf : IsStarProjection (U*star U) := by
    constructor
    · apply Subtype.ext
      change (V*star V)*(V*star V)=V*star V
      simpa only [star_star] using (initial_projection (partial_star hpart)).isIdempotentElem.eq
    · apply Subtype.ext
      change star (V*star V)=V*star V
      simpa only [star_star] using (initial_projection (partial_star hpart)).isSelfAdjoint.star_eq
  have hitrace := stabilizedProjectionTrace_initial_final U hpart'
  refine ⟨U,?_⟩
  rcases hside with he|he
  · have hu : star U*U=p := Subtype.ext he
    have hle : (U*star U)*q=U*star U := by
      apply Subtype.ext
      have he' := congrArg star hqV
      simp only [star_mul,hq'.isSelfAdjoint.star_eq] at he'
      change (V*star V)*(q : GroupOperator (ℕ × G))=V*star V
      rw [mul_assoc,he']
    rw [hu] at hitrace
    have ht : stabilizedProjectionTrace q=stabilizedProjectionTrace (U*star U) := htrace.symm.trans hitrace
    exact ⟨hu,(finite_trace_equal_projection_of_le q (U*star U) hq hf hle ht (htrace ▸ hfinite)).symm⟩
  · have hu : U*star U=q := Subtype.ext he
    have hle : (star U*U)*p=star U*U := by
      apply Subtype.ext
      change (star V*V)*(p : GroupOperator (ℕ × G))=star V*V
      rw [mul_assoc,hVp]
    rw [hu] at hitrace
    have ht : stabilizedProjectionTrace p=stabilizedProjectionTrace (star U*U) := htrace.trans hitrace.symm
    exact ⟨(finite_trace_equal_projection_of_le p (star U*U) hp hi hle ht hfinite).symm,hu⟩

 theorem infinite_equal_finite_trace_equivalence
    (p q : stabilization (FreeGroup ℕ)) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace q)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) :
    ∃ V : stabilization (FreeGroup ℕ), star V*V=p ∧ V*star V=q :=
  equal_finite_trace_equivalence
    (fun T hT => ⟨canonicalTrace T,infinite_free_group_center_scalar T hT⟩) p q hp hq htrace hfinite

end FreeGroupFactorMain.Amplification

end

end OAI
