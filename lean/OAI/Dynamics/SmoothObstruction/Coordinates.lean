import Mathlib

namespace OAI

section

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev E := EuclideanSpace ℝ (Fin d)

noncomputable def coord (S : Diffeomorph I I M M ∞) (a b : M) (x : M) : E (d:=d) →L[ℝ] E (d:=d) :=
  ContinuousLinearMap.inCoordinates (E (d:=d)) (TangentSpace I)
    (E (d:=d)) (TangentSpace I) a x b (S x) (mfderiv I I S x)

def domain (S : Diffeomorph I I M M ∞) (a b : M) : Set M :=
  (chartAt H a).source ∩ S ⁻¹' (chartAt H b).source

/-- The genuine derivative in any independently fixed pair of regular
charts, including half-space charts. -/
theorem continuousOn_coord (S : Diffeomorph I I M M ∞) (a b : M) :
    ContinuousOn (coord I S a b) (domain I S a b) := by
  apply continuousOn_clm_apply.mpr
  intro v
  let e := trivializationAt (E (d:=d)) (TangentSpace I) a
  let e' := trivializationAt (E (d:=d)) (TangentSpace I) b
  have hin : ContinuousOn (fun x => TotalSpace.mk' (E (d:=d)) x (e.symm x v)) e.baseSet := by
    exact e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hx,mem_univ _⟩)
  have htan := S.contMDiff.continuous_tangentMap (show (1 : ℕ∞ω)≤∞ by simp)
  have hmid := htan.comp_continuousOn hin
  have hout : ContinuousOn (fun x => (e' (tangentMap I I S
      (TotalSpace.mk' (E (d:=d)) x (e.symm x v)))).2) (domain I S a b) := by
    apply (e'.continuousOn.comp (hmid.mono (fun x hx => ?_)) (fun x hx => ?_)).snd
    · simpa only [e,TangentBundle.trivializationAt_baseSet] using hx.1
    · apply e'.mem_source.mpr
      change S x∈(chartAt H b).source
      exact hx.2
  apply hout.congr
  intro x hx
  have h₁ : x∈e.baseSet := by simpa only [e,TangentBundle.trivializationAt_baseSet] using hx.1
  have h₂ : S x∈e'.baseSet := by exact hx.2
  change e'.continuousLinearMapAt ℝ (S x)
    ((mfderiv I I S x) ((e.symmL ℝ x) v))=_
  rw [e.symmL_apply h₁,Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e' h₂]
  rfl


noncomputable def coordEquiv (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : E (d:=d) ≃L[ℝ] E (d:=d) :=
  (((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx.1).symm.trans
    (S.mfderivToContinuousLinearEquiv (by simp) x)).trans
    ((trivializationAt (E (d:=d)) (TangentSpace I) b).continuousLinearEquivAt ℝ (S x) hx.2)

@[simp] theorem coordEquiv_coe (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : (coordEquiv I S a b x hx).toContinuousLinearMap=coord I S a b x := by
  rw [coord,ContinuousLinearMap.inCoordinates_eq hx.1 hx.2]
  rfl

/-- The represented derivative is invertible at every point of its actual
coordinate domain. This is not postulated as a cocycle input. -/
theorem bijective_coord (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : Function.Bijective (coord I S a b x) := by
  rw [←coordEquiv_coe I S a b x hx]
  exact (coordEquiv I S a b x hx).bijective

/-- Uniform two-sided derivative bounds on any compact chart-pair patch. -/
theorem bound_on_compact (S : Diffeomorph I I M M ∞) (a b : M)
    {K : Set M} (hK : IsCompact K) (hsub : K⊆domain I S a b) :
    ∃ C : ℝ, 0<C ∧ ∀ x∈K, ‖coord I S a b x‖≤C ∧
      ∀ v, ‖v‖≤C*‖coord I S a b x v‖ := by
  have hc := (continuousOn_coord I S a b).mono hsub
  have hi : ContinuousOn (fun x => Ring.inverse (coord I S a b x)) K := by
    intro x hx
    let : CompleteSpace (E (d:=d) →L[ℝ] E (d:=d)) :=
      ContinuousLinearMap.instCompleteSpace
    have h := NormedRing.inverse_continuousAt (coordEquiv I S a b x (hsub hx)).toUnit
    rw [show ((coordEquiv I S a b x (hsub hx)).toUnit : E (d:=d) →L[ℝ] E (d:=d)) =
      coord I S a b x from coordEquiv_coe I S a b x (hsub hx)] at h
    exact h.comp_continuousWithinAt (hc x hx)
  obtain ⟨C₁,hC₁⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨C₂,hC₂⟩ := hK.exists_bound_of_continuousOn hi
  refine ⟨max C₁ (max C₂ 1), lt_of_lt_of_le zero_lt_one (le_max_right C₂ 1 |>.trans (le_max_right _ _)),?_⟩
  intro x hx
  refine ⟨(hC₁ x hx).trans (le_max_left _ _),?_⟩
  intro v
  let e := coordEquiv I S a b x (hsub hx)
  have he : (e.toContinuousLinearMap)=coord I S a b x := coordEquiv_coe I S a b x (hsub hx)
  have hi' : Ring.inverse (coord I S a b x)=e.symm.toContinuousLinearMap := by
    rw [←he]
    exact Ring.inverse_unit e.toUnit
  have hnv := e.symm.toContinuousLinearMap.le_opNorm (e v)
  simp only [ContinuousLinearEquiv.coe_coe,e.symm_apply_apply] at hnv
  rw [←hi'] at hnv
  calc
    ‖v‖≤‖Ring.inverse (coord I S a b x)‖*‖e v‖ := hnv
    _ ≤ max C₁ (max C₂ 1)*‖e v‖ := mul_le_mul_of_nonneg_right
      ((hC₂ x hx).trans ((le_max_left C₂ 1).trans (le_max_right _ _))) (norm_nonneg _)
    _ = max C₁ (max C₂ 1)*‖coord I S a b x v‖ := by rw [←he]; rfl

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteAtlas
open Set Filter Topology MeasureTheory
universe u
variable {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M]

/-- Compact inner patches covering the whole compact space. This applies to
half-space and nonorientable atlas charts without a global frame. -/
theorem compact_inner_cover (U : M → Set M) (hU : ∀ x,IsOpen (U x))
    (hxU : ∀ x,x∈U x) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (K : ι → Set M),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆U (a i)) ∧ ∀ x,∃ i,x∈K i := by
  choose K hK hKi hKU using fun x => exists_compact_subset (hU x) (hxU x)
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (K x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x,hKi x⟩)
  refine ⟨{x // x∈s},inferInstance,Subtype.val,fun i => K i,fun i => hK i,
    fun i => hKU i,?_⟩
  intro x
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact ⟨⟨i,hi⟩,interior_subset hxi⟩

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace ι]
    

/-- Deterministic measurable choice of the first containing compact patch.
No measurable selection theorem is postulated. -/
theorem measurable_selector (K : ι → Set Ω) (hK : ∀ i,MeasurableSet (K i))
    (hcover : ∀ x,∃ i,x∈K i) :
    ∃ a : Ω → ι,Measurable a ∧ ∀ x,x∈K (a x) := by
  classical
  by_cases hΩ : IsEmpty Ω
  · let := hΩ
    exact ⟨isEmptyElim,measurable_of_empty _,fun x => isEmptyElim x⟩
  have : Nonempty Ω := not_isEmpty_iff.mp hΩ
  have : Nonempty ι := let ⟨i,_⟩ := hcover (Classical.choice inferInstance); ⟨i⟩
  let N := Fintype.card ι
  let e := Fintype.equivFin ι
  let p : Ω → ℕ → Prop := fun x n => ∃ h:n<N,x∈K (e.symm ⟨n,h⟩)
  have hp (x : Ω) : ∃ n,p x n := by
    obtain ⟨i,hi⟩ := hcover x
    exact ⟨(e i).val,⟨(e i).isLt,by simpa using hi⟩⟩
  let k : Ω → ℕ := fun x => Nat.find (hp x)
  have hk : Measurable k := measurable_find hp (fun n => by
    by_cases hn : n<N
    · have he : {x | p x n}=K (e.symm ⟨n,hn⟩) := by
        ext x
        simp only [mem_ofPred_eq,p]
        exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨hn,h⟩⟩
      rw [he]; exact hK _
    · have he : {x | p x n}=∅ := by ext x; simp [p,hn]
      rw [he]; exact MeasurableSet.empty)
  have hkN (x : Ω) : k x<N := (Nat.find_spec (hp x)).choose
  let f : Ω → Fin N := fun x => ⟨k x,hkN x⟩
  have hf : Measurable f := by
    apply measurable_to_countable'
    intro i
    have he : f ⁻¹' {i}={x | k x=i.val} := by
      ext x
      simp [f,Fin.ext_iff]
    rw [he]
    exact measurableSet_eq_fun hk measurable_const
  refine ⟨e.symm ∘ f, (measurable_of_finite e.symm).comp hf,?_⟩
  intro x
  exact (Nat.find_spec (hp x)).choose_spec
end SmoothObstruction.FiniteAtlas

namespace SmoothObstruction.CompactMatrix
open Set Metric

/-- Compact alphabet of uniformly bounded, uniformly invertible derivative
matrices. The coercion remembers the actual matrix, not an extra axiom. -/
abbrev Alphabet (d : ℕ) (K : ℝ) :=
  {A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) //
    ‖A‖≤K ∧ ∀ v,‖v‖≤K*‖A v‖}

instance {d : ℕ} {K : ℝ} : CompactSpace (Alphabet d K) := by
  let T := EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)
  have hc : IsClosed (⋂ (v : EuclideanSpace ℝ (Fin d)), {A : T | ‖v‖≤K*‖A v‖}) := by
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (continuous_const.mul
      ((continuous_id : Continuous (fun A : T => A)).clm_apply
        (continuous_const : Continuous (fun _ : T => v))).norm)
  have he : {A : T | ∀ v, ‖v‖≤K*‖A v‖} =
      ⋂ (v : EuclideanSpace ℝ (Fin d)), {A : T | ‖v‖≤K*‖A v‖} := by
    ext A; simp
  have hf : IsClosed {A : T | ∀ v, ‖v‖≤K*‖A v‖} := he.symm ▸ hc
  have hg : IsClosed {A : T | ‖A‖≤K} := isClosed_le continuous_norm continuous_const
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : T) K).of_isClosed_subset
  · exact hg.inter hf
  · intro A hA
    simpa only [mem_closedBall,dist_zero_right] using hA.1

lemma injective {d : ℕ} {K : ℝ} (A : Alphabet d K) : Function.Injective A.val := by
  intro x y he
  have hh := A.property.2 (x-y)
  rw [map_sub,he,sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

noncomputable def equiv {d : ℕ} {K : ℝ} (A : Alphabet d K) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (LinearEquiv.ofBijective A.val.toLinearMap
    ⟨injective A,(LinearMap.injective_iff_surjective).mp (injective A)⟩).toContinuousLinearEquiv

@[simp] lemma equiv_coe {d : ℕ} {K : ℝ} (A : Alphabet d K) :
    (equiv A).toContinuousLinearMap=A.val := rfl

lemma continuous_equiv {d : ℕ} {K : ℝ} :
    Continuous (fun A : Alphabet d K => (equiv A).toContinuousLinearMap) := continuous_subtype_val

end SmoothObstruction.CompactMatrix

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- A bounded measurable cocycle of the genuine derivative, in a finite
system of measurable chart regions with compact inner patches. -/
theorem actual_coordinate_cocycle_discrete (S : Diffeomorph I I M M ∞) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K : ι → Set M) (c : M → ι) (C : ℝ)
      (A : M → CompactMatrix.Alphabet d C),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable c ∧ (∀ x,x∈K (c x)) ∧ 0<C ∧ Measurable A ∧
      ∀ x,(A x).val=coord I S (a (c x)) (a (c (S x))) x := by
  classical
  obtain ⟨ι,hfin,a,K,hK,hKU,hcover⟩ := FiniteAtlas.compact_inner_cover
    (fun x : M => (chartAt H x).source) (fun x => (chartAt H x).open_source)
    (fun x => mem_chart_source H x)
  let : Fintype ι := hfin
  let : MeasurableSpace ι := ⊤
  obtain ⟨c,hc,hcK⟩ := FiniteAtlas.measurable_selector K
    (fun i => (hK i).isClosed.measurableSet) hcover
  let L : ι × ι → Set M := fun ij => K ij.1 ∩ S ⁻¹' K ij.2
  have hL (ij : ι × ι) : IsCompact (L ij) :=
    (hK ij.1).inter_right ((hK ij.2).isClosed.preimage S.continuous)
  have hLd (ij : ι × ι) : L ij⊆domain I S (a ij.1) (a ij.2) :=
    fun _ hx => ⟨hKU _ hx.1,hKU _ hx.2⟩
  choose D hDp hD using fun ij => bound_on_compact I S (a ij.1) (a ij.2) (hL ij) (hLd ij)
  let C : ℝ := 1+∑ ij,D ij
  have hDC (ij : ι × ι) : D ij≤C := by
    have hh : D ij≤∑ p,D p := Finset.single_le_sum (fun p _ => (hDp p).le) (Finset.mem_univ ij)
    dsimp only [C]; linarith
  have hCp : 0<C := by
    have hh : 0≤∑ ij,D ij := Finset.sum_nonneg (fun p _ => (hDp p).le)
    dsimp only [C]; linarith
  let f : ι × ι → M → (E (d:=d) →L[ℝ] E (d:=d)) := fun ij =>
    (L ij).piecewise (coord I S (a ij.1) (a ij.2)) 0
  have hf (ij : ι × ι) : Measurable (f ij) :=
    ((continuousOn_coord I S (a ij.1) (a ij.2)).mono (hLd ij)).measurable_piecewise
      continuous_const.continuousOn (hL ij).isClosed.measurableSet
  have hf' : Measurable (fun p : M × (ι × ι) => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  have heval : Measurable (fun x => f (c x,c (S x)) x) :=
    hf'.comp (measurable_id.prodMk (hc.prodMk (hc.comp S.continuous.measurable)))
  have hxe (x : M) : x∈L (c x,c (S x)) := ⟨hcK x,hcK (S x)⟩
  have heq (x : M) : f (c x,c (S x)) x=coord I S (a (c x)) (a (c (S x))) x := by
    exact Set.piecewise_eq_of_mem _ _ _ (hxe x)
  have hb (x : M) : ‖f (c x,c (S x)) x‖≤C ∧ ∀ v,‖v‖≤C*‖f (c x,c (S x)) x v‖ := by
    rw [heq]
    exact ⟨((hD _ x (hxe x)).1).trans (hDC _),fun v =>
      ((hD _ x (hxe x)).2 v).trans (mul_le_mul_of_nonneg_right (hDC _) (norm_nonneg _))⟩
  let A : M → CompactMatrix.Alphabet d C := fun x => ⟨f (c x,c (S x)) x,hb x⟩
  exact ⟨ι,hfin,⊤,inferInstance,a,K,c,C,A,hK,hKU,hc,hcK,hCp,heval.subtype_mk,heq⟩

end SmoothObstruction.ManifoldCoordinates

end

end OAI
