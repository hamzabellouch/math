import OAI.Dynamics.SmoothObstruction.TubeProjection

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ProductBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def blockMap (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) :
    EuclideanSpace ℝ (ι ⊕ κ) ≃L[ℝ] E :=
  EuclideanSpace.sumEquivProd.trans
    ((bU.repr.symm.toContinuousLinearEquiv.prodCongr bV.repr.symm.toContinuousLinearEquiv).trans
      (U.prodEquivOfIsCompl V h).toContinuousLinearEquiv)

lemma blockMap_apply (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V)
    (v : EuclideanSpace ℝ (ι ⊕ κ)) :
    blockMap U V h bU bV v=
      (bU.repr.symm (EuclideanSpace.sumEquivProd v).1:E)+
      (bV.repr.symm (EuclideanSpace.sumEquivProd v).2:E) := rfl

lemma sum_norm_sq (v : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖(EuclideanSpace.sumEquivProd v).1‖^2+‖(EuclideanSpace.sumEquivProd v).2‖^2=‖v‖^2 := by
  have hh := WithLp.prod_norm_sq_eq_of_L2 ((PiLp.sumPiLpEquivProdLpPiLp (𝕜:=ℝ) 2 (fun _ : ι ⊕ κ => ℝ)) v)
  rw [LinearIsometryEquiv.norm_map] at hh
  exact hh.symm

/-- The source's basis consists of orthonormal columns within each summand.
Its forward norm is uniformly bounded even when the angle is small. -/
lemma norm_blockMap (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) :
    ‖(blockMap U V h bU bV).toContinuousLinearMap‖≤Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  rw [ContinuousLinearEquiv.coe_coe,blockMap_apply]
  apply (norm_add_le _ _).trans
  change ‖bU.repr.symm (EuclideanSpace.sumEquivProd v).1‖+
    ‖bV.repr.symm (EuclideanSpace.sumEquivProd v).2‖≤_
  rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num)]
  nlinarith [sum_norm_sq v,sq_nonneg (‖(EuclideanSpace.sumEquivProd v).1‖-‖(EuclideanSpace.sumEquivProd v).2‖)]

lemma blockMap_symm_components (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) (x : E) :
    EuclideanSpace.sumEquivProd ((blockMap U V h bU bV).symm x)=
      (bU.repr (U.projectionOnto V h x),bV.repr (V.projectionOnto U h.symm x)) := by
  change EuclideanSpace.sumEquivProd (EuclideanSpace.sumEquivProd.symm
    ((bU.repr.toContinuousLinearEquiv.prodCongr bV.repr.toContinuousLinearEquiv)
      ((U.prodEquivOfIsCompl V h).symm x)))=_
  rw [ContinuousLinearEquiv.apply_symm_apply,Submodule.prodEquivOfIsCompl_symm_apply]
  rfl

/-- Only the inverse pays the complementary-projection condition number. -/
lemma norm_blockMap_symm (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V)
    {H : ℝ} (hH : 0≤H)
    (hU : ∀ x,‖U.projectionOnto V h x‖≤H*‖x‖)
    (hV : ∀ x,‖V.projectionOnto U h.symm x‖≤H*‖x‖) :
    ‖(blockMap U V h bU bV).symm.toContinuousLinearMap‖≤Real.sqrt 2*H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(blockMap U V h bU bV).symm x‖^2≤_
  rw [←sum_norm_sq,blockMap_symm_components]
  simp only [LinearIsometryEquiv.norm_map]
  have hu := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hU x)
  have hv := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hV x)
  rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num)]
  nlinarith
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.ProductBasis
open Set
open scoped EuclideanGeometry
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A fixed ambient coordinate alphabet for the orthonormal-within-group
product basis. The rank may vary from bin to bin without being charged as an
orbit code. Even rank-zero groups retain the exact mixing property. -/
theorem exists_coordinates (U V : Submodule ℝ E) (h : IsCompl U V)
    {H : ℝ} (hH : 0≤H)
    (hU : ∀ x,‖U.projectionOnto V h x‖≤H*‖x‖)
    (hV : ∀ x,‖V.projectionOnto U h.symm x‖≤H*‖x‖) :
    ∃ A : E ≃L[ℝ] E,
      ‖A.toContinuousLinearMap‖≤Real.sqrt 2 ∧
      ‖A.symm.toContinuousLinearMap‖≤Real.sqrt 2*H ∧
      ∀ x y : E,∀ i : Fin d,
        (A.symm (x+(U.projectionOnto V h (y-x):E))) i=(A.symm x) i ∨
        (A.symm (x+(U.projectionOnto V h (y-x):E))) i=(A.symm y) i := by
  classical
  let bU := stdOrthonormalBasis ℝ U
  let bV := stdOrthonormalBasis ℝ V
  have hcard : Fintype.card (Fin (Module.finrank ℝ U) ⊕ Fin (Module.finrank ℝ V))=
      Fintype.card (Fin d) := by
    simpa using (Submodule.finrank_add_eq_of_isCompl h)
  let e : (Fin (Module.finrank ℝ U) ⊕ Fin (Module.finrank ℝ V)) ≃ Fin d :=
    Fintype.equivOfCardEq hcard
  let J := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let A : E ≃L[ℝ] E := J.symm.toContinuousLinearEquiv.trans (blockMap U V h bU bV)
  have hnormJ (x : E) : ‖J.symm x‖=‖x‖ := J.symm.norm_map x
  have hnormA (x : E) : ‖A x‖≤Real.sqrt 2*‖x‖ := by
    exact ((blockMap U V h bU bV).toContinuousLinearMap.le_opNorm (J.symm x)).trans
      (by rw [hnormJ]; exact mul_le_mul_of_nonneg_right (norm_blockMap U V h bU bV) (norm_nonneg _))
  have hnormAi (x : E) : ‖A.symm x‖≤(Real.sqrt 2*H)*‖x‖ := by
    change ‖J ((blockMap U V h bU bV).symm x)‖≤_
    rw [J.norm_map]
    exact ((blockMap U V h bU bV).symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (norm_blockMap_symm U V h bU bV hH hU hV) (norm_nonneg _))
  refine ⟨A,ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hnormA,
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hnormAi,?_⟩
  intro x y i
  have hmix : EuclideanSpace.sumEquivProd ((blockMap U V h bU bV).symm
      (x+(U.projectionOnto V h (y-x):E)))=
      (bU.repr (U.projectionOnto V h y),bV.repr (V.projectionOnto U h.symm x)) := by
    rw [blockMap_symm_components]
    apply Prod.ext
    · change bU.repr (U.projectionOnto V h (x+(U.projectionOnto V h (y-x):E))) = _
      congr 1
      rw [map_add,Submodule.projectionOnto_apply_left,map_sub]
      abel
    · change bV.repr (V.projectionOnto U h.symm (x+(U.projectionOnto V h (y-x):E))) = _
      congr 1
      rw [map_add,Submodule.projectionOnto_apply_right,add_zero]
  have hval (z : E) (j : Fin (Module.finrank ℝ U) ⊕ Fin (Module.finrank ℝ V)) :
      (A.symm z) (e j)=((blockMap U V h bU bV).symm z) j := by
    change (J ((blockMap U V h bU bV).symm z)) (e j)=_
    simp [J,LinearIsometryEquiv.piLpCongrLeft_apply]
  obtain ⟨j,rfl⟩ := e.surjective i
  rw [hval,hval,hval]
  rcases j with j | j
  · right
    have hm := congrArg (fun p => (p.1 : EuclideanSpace ℝ (Fin (Module.finrank ℝ U))) j) hmix
    have hx := congrArg (fun p => (p.1 : EuclideanSpace ℝ (Fin (Module.finrank ℝ U))) j)
      (blockMap_symm_components U V h bU bV y)
    exact hm.trans hx.symm
  · left
    have hm := congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) j) hmix
    have hx := congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) j)
      (blockMap_symm_components U V h bU bV x)
    exact hm.trans hx.symm
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.FiniteGreen.Splitting
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : Evolution E} (B : Splitting T)

lemma ranges_isCompl (t : ℕ) : IsCompl (B.slow t).range (B.fast t).range := by
  refine ⟨Submodule.disjoint_def.mpr ?_,codisjoint_iff.mpr ?_⟩
  · intro x hx hy
    obtain ⟨u,hu⟩ := hx
    obtain ⟨v,hv⟩ := hy
    have hs : B.slow t x=x := by
      rw [←hu]
      change B.slow t (B.slow t u)=B.slow t u
      exact B.slow_self t u
    have hf : B.slow t x=0 := by
      rw [←hv]
      change B.slow t (B.fast t v)=0
      exact B.slow_fast t v
    exact hs.symm.trans hf
  · apply top_unique
    intro x _
    exact Submodule.mem_sup.mpr ⟨B.slow t x,⟨x,rfl⟩,B.fast t x,⟨x,rfl⟩,B.add_apply t x⟩

lemma range_projection_slow (t : ℕ) (x : E) :
    ((B.slow t).range.projectionOnto (B.fast t).range (B.ranges_isCompl t) x:E)=B.slow t x := by
  have h := B.add_apply t x
  conv_lhs => rw [←h]
  rw [map_add]
  have hs := Submodule.projectionOnto_apply_left (B.ranges_isCompl t)
    (⟨B.slow t x,⟨x,rfl⟩⟩ : (B.slow t).range)
  have hf := Submodule.projectionOnto_apply_right (B.ranges_isCompl t)
    (⟨B.fast t x,⟨x,rfl⟩⟩ : (B.fast t).range)
  rw [hs,hf,add_zero]

lemma range_projection_fast (t : ℕ) (x : E) :
    ((B.fast t).range.projectionOnto (B.slow t).range (B.ranges_isCompl t).symm x:E)=B.fast t x := by
  have h := B.add_apply t x
  conv_lhs => rw [←h]
  rw [map_add]
  have hs := Submodule.projectionOnto_apply_right (B.ranges_isCompl t).symm
    (⟨B.slow t x,⟨x,rfl⟩⟩ : (B.slow t).range)
  have hf := Submodule.projectionOnto_apply_left (B.ranges_isCompl t).symm
    (⟨B.fast t x,⟨x,rfl⟩⟩ : (B.fast t).range)
  rw [hs,hf,zero_add]
end SmoothObstruction.FiniteGreen.Splitting

namespace SmoothObstruction.ProductBasis
open SmoothObstruction.FiniteGreen
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The authentic complementary splitting produces its own uniform product
coordinate map, with the exact slow/fast ideal mix and no rank assumptions. -/
theorem splitting_coordinates {T : Evolution E} (B : Splitting T) (t : ℕ)
    {H : ℝ} (hH : 0≤H) (hs : ‖B.slow t‖≤H) (hf : ‖B.fast t‖≤H) :
    ∃ A : E ≃L[ℝ] E,
      ‖A.toContinuousLinearMap‖≤Real.sqrt 2 ∧
      ‖A.symm.toContinuousLinearMap‖≤Real.sqrt 2*H ∧
      ∀ x y : E,∀ i : Fin d,
        (A.symm (x+B.slow t (y-x))) i=(A.symm x) i ∨
        (A.symm (x+B.slow t (y-x))) i=(A.symm y) i := by
  obtain ⟨A,hA,hAi,hm⟩ := exists_coordinates (B.slow t).range (B.fast t).range
    (B.ranges_isCompl t) hH
    (fun x => by
      change ‖((B.slow t).range.projectionOnto (B.fast t).range (B.ranges_isCompl t) x:E)‖≤_
      rw [B.range_projection_slow]
      exact ((B.slow t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
    (fun x => by
      change ‖((B.fast t).range.projectionOnto (B.slow t).range (B.ranges_isCompl t).symm x:E)‖≤_
      rw [B.range_projection_fast]
      exact ((B.fast t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg x)))
  exact ⟨A,hA,hAi,fun x y i => by simpa only [B.range_projection_slow] using hm x y i⟩
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator
variable {d n : ℕ} {K : ℝ}

/-- Authentic gauges give product coordinates for the original coarse bin.
The coordinate groups are allowed to have either rank zero or full rank. -/
theorem Gauge.product_coordinates (A : Gauge d n K) (S : Finset (Fin d)) :
    ∃ L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖L.toContinuousLinearMap‖≤Real.sqrt 2 ∧
      ‖L.symm.toContinuousLinearMap‖≤Real.sqrt 2*Real.exp (2*K) ∧
      ∀ x y : EuclideanSpace ℝ (Fin d),∀ i : Fin d,
        (L.symm (x+(A.splitting S).slow 0 (y-x))) i=(L.symm x) i ∨
        (L.symm (x+(A.splitting S).slow 0 (y-x))) i=(L.symm y) i := by
  apply ProductBasis.splitting_coordinates (A.splitting S) 0 (Real.exp_pos _).le
  · exact EuclideanSplitting.splitting_slow_norm _ _ _ _ _ _ 0
      (A.normU _ (Nat.zero_le n)) (A.normV _ (Nat.zero_le n))
  · exact EuclideanSplitting.splitting_fast_norm _ _ _ _ _ _ 0
      (A.normU _ (Nat.zero_le n)) (A.normV _ (Nat.zero_le n))
end SmoothObstruction.ShortBin

namespace SmoothObstruction.FiniteBins
open Set
variable {X C : Type*} {d n : ℕ} {K : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Extend the genuinely selected bin coordinates to unused bins. The arbitrary
identity coordinates are never used by a retained input. -/
theorem product_coordinates (P : X → C) (G : Set X) (hK : 0≤K)
    (A : Active P G → ShortBin.Gauge d n K) (S : Active P G → Finset (Fin d)) :
    ∃ L : C → E ≃L[ℝ] E,
      (∀ c,‖(L c).toContinuousLinearMap‖≤Real.sqrt 2) ∧
      (∀ c,‖(L c).symm.toContinuousLinearMap‖≤Real.sqrt 2*Real.exp (2*K)) ∧
      ∀ c : Active P G,∀ x y : E,∀ i : Fin d,
        ((L c.val).symm (x+((A c).splitting (S c)).slow 0 (y-x))) i=
          ((L c.val).symm x) i ∨
        ((L c.val).symm (x+((A c).splitting (S c)).slow 0 (y-x))) i=
          ((L c.val).symm y) i := by
  classical
  choose L hL hLi hm using fun c => (A c).product_coordinates (S c)
  let F (c : C) : E ≃L[ℝ] E := if h : ∃ x∈G,P x=c then L ⟨c,h⟩ else ContinuousLinearEquiv.refl ℝ E
  have hroot : 1≤Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hexp : 1≤Real.exp (2*K) := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨F,?_,?_,?_⟩
  · intro c
    dsimp only [F]
    split_ifs with hc
    · exact hL _
    · exact (show ‖(ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap‖≤1 from ContinuousLinearMap.norm_id_le).trans hroot
  · intro c
    dsimp only [F]
    split_ifs with hc
    · exact hLi _
    · exact (show ‖(ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap‖≤1 from ContinuousLinearMap.norm_id_le).trans
        (le_trans hroot (by nlinarith [Real.sqrt_nonneg (2:ℝ)]))
  · intro c x y i
    rcases c with ⟨c,hc⟩
    simpa only [F,dite_eq_left hc] using hm ⟨c,hc⟩ x y i
end SmoothObstruction.FiniteBins

namespace SmoothObstruction.AtlasCores
open Set MeasureTheory Metric
open scoped ENNReal NNReal
variable {M ι : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype ι]

/-- Compact cores of a finite measurable cover cost arbitrarily little of the
original measure. No relative distribution inside a selector fiber is used. -/
theorem finite_cores (μ : Measure M) [IsFiniteMeasure μ]
    [Measure.InnerRegularCompactLTTop μ] (A : ι → Set M)
    (hA : ∀ i,MeasurableSet (A i)) (hcover : ∀ x,∃ i,x∈A i)
    (ε : ℝ≥0) (hε : 0<ε) :
    ∃ K : ι → Set M,(∀ i,K i⊆A i) ∧ (∀ i,IsCompact (K i)) ∧
      μ (⋃ i,K i)ᶜ≤ε := by
  classical
  let δ : ℝ≥0 := ε/(Fintype.card ι+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  choose K hKA hK hμK using fun i =>
    (hA i).exists_isCompact_sdiff_lt (measure_ne_top μ (A i))
      (show (δ : ℝ≥0∞)≠0 by exact_mod_cast ne_of_gt hδ)
  refine ⟨K,hKA,hK,?_⟩
  have hsub : (⋃ i,K i)ᶜ⊆⋃ i,A i\K i := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i,hi,fun hk => hx (mem_iUnion.mpr ⟨i,hk⟩)⟩
  calc
    μ (⋃ i,K i)ᶜ≤μ (⋃ i,A i\K i) := measure_mono hsub
    _ ≤ ∑ i,μ (A i\K i) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι,(δ : ℝ≥0∞) := Finset.sum_le_sum (fun i _ => (hμK i).le)
    _ = ((Fintype.card ι : ℝ≥0)*δ : ℝ≥0) := by simp
    _ ≤ (ε : ℝ≥0∞) := by
      exact_mod_cast (show (Fintype.card ι : ℝ≥0)*δ≤ε from by
        dsimp [δ]
        rw [←mul_div_assoc,div_le_iff₀ (show (0 : ℝ≥0)<Fintype.card ι+1 by positivity)]
        nlinarith)

/-- Positive finitely many scales have a positive common lower bound, including
an empty index type. This avoids a nonempty-atlas convention. -/
lemma finite_positive_min (a : ι → ℝ) (ha : ∀ i,0<a i) :
    ∃ r : ℝ,0<r ∧ ∀ i,r≤a i := by
  classical
  have h : ∀ s : Finset ι,∃ r : ℝ,0<r ∧ ∀ i∈s,r≤a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r,hr,hra⟩ := ih
      refine ⟨min r (a i),lt_min hr (ha i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hra j hj)
  obtain ⟨r,hr,hra⟩ := h Finset.univ
  exact ⟨r,hr,fun i => hra i (Finset.mem_univ i)⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- Disjoint compact chart cores admit one radius whose closed thickenings
remain pairwise disjoint and inside the designated open charts. -/
theorem separated_neighborhoods (K U : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hKU : ∀ i,K i⊆U i) (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ r : ℝ,0<r ∧ (∀ i,cthickening r (K i)⊆U i) ∧
      Pairwise (fun i j => Disjoint (cthickening r (K i)) (cthickening r (K j))) := by
  classical
  choose a ha hsub using fun i => (hK i).exists_cthickening_subset_open (hU i) (hKU i)
  obtain ⟨r,hr,hra⟩ := finite_positive_min a ha
  have hp (ij : ι×ι) : ∃ δ : ℝ,0<δ ∧
      (ij.1≠ij.2 → Disjoint (cthickening δ (K ij.1)) (cthickening δ (K ij.2))) := by
    by_cases h : ij.1=ij.2
    · exact ⟨1,by norm_num,fun hn => (hn h).elim⟩
    · obtain ⟨δ,hδ,hd⟩ := (hdisj h).exists_cthickenings (hK ij.1) (hK ij.2).isClosed
      exact ⟨δ,hδ,fun _ => hd⟩
  choose b hb hbd using hp
  obtain ⟨s,hs,hsb⟩ := finite_positive_min b hb
  refine ⟨min r s,lt_min hr hs,?_,?_⟩
  · intro i
    exact (cthickening_mono (le_trans (min_le_left _ _) (hra i)) _).trans (hsub i)
  · intro i j hij
    apply (hbd (i,j) hij).mono
    · exact cthickening_mono (le_trans (min_le_right _ _) (hsb (i,j))) _
    · exact cthickening_mono (le_trans (min_le_right _ _) (hsb (i,j))) _
/-- The finite atlas selector now yields coherent disjoint retained chart cores
and a single positive safety radius, with error measured in the ORIGINAL law. -/
theorem selector_cores [CompactSpace M] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure M) [IsFiniteMeasure μ]
    (c : M → ι) (hc : Measurable c) (U : ι → Set M)
    (hU : ∀ i,IsOpen (U i)) (hcU : ∀ x,x∈U (c x))
    (ε : ℝ≥0) (hε : 0<ε) :
    ∃ (K : ι → Set M) (r : ℝ),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆c ⁻¹' {i}) ∧
      μ (⋃ i,K i)ᶜ≤ε ∧ 0<r ∧
      (∀ i,cthickening r (K i)⊆U i) ∧
      Pairwise (fun i j => Disjoint (cthickening r (K i)) (cthickening r (K j))) := by
  obtain ⟨K,hKA,hK,hμK⟩ := finite_cores μ (fun i => c ⁻¹' {i})
    (fun i => hc (measurableSet_singleton i)) (fun x => ⟨c x,rfl⟩) ε hε
  have hKU : ∀ i,K i⊆U i := by
    intro i x hx
    have he : c x=i := hKA i hx
    simpa only [he] using hcU x
  have hd : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij ((hKA i hx).symm.trans (hKA j hy))
  obtain ⟨r,hr,hsub,hsep⟩ := separated_neighborhoods K U hK hU hKU hd
  exact ⟨K,r,hK,hKA,hμK,hr,hsub,hsep⟩
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.AtlasCores
open Set MeasureTheory Metric
open scoped ENNReal NNReal
variable {M ι : Type*} [MeasurableSpace M]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Modify a chart selector only in disjoint protected neighborhoods. On the
retained compact cores the new selector is genuinely locally constant, so
nearby switched endpoints recover the same chart label. -/
theorem protected_selector (c : M → ι) (hc : Measurable c)
    (U V : ι → Set M) (hV : ∀ i,MeasurableSet (V i))
    (hVU : ∀ i,V i⊆U i) (hcU : ∀ x,x∈U (c x))
    (hd : Pairwise (fun i j => Disjoint (V i) (V j))) :
    ∃ q : M → ι,Measurable q ∧ (∀ x,x∈U (q x)) ∧
      (∀ i,∀ x∈V i,q x=i) ∧
      ∀ x,x∉⋃ i,V i → q x=c x := by
  let W : ι → Set M := fun i => V i ∪ ((⋃ j,V j)ᶜ ∩ c ⁻¹' {i})
  have hW : ∀ i,MeasurableSet (W i) := fun i => (hV i).union
    ((MeasurableSet.iUnion hV).compl.inter (hc (measurableSet_singleton i)))
  have hcover : ∀ x,∃ i,x∈W i := by
    intro x
    by_cases hx : x∈⋃ i,V i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact ⟨i,Or.inl hi⟩
    · exact ⟨c x,Or.inr ⟨hx,rfl⟩⟩
  obtain ⟨q,hq,hqW⟩ := FiniteAtlas.measurable_selector W hW hcover
  have hqV : ∀ i,∀ x∈V i,q x=i := by
    intro i x hx
    rcases hqW x with h|h
    · by_contra hi
      exact Set.disjoint_left.mp (hd hi) h hx
    · exact (h.1 (mem_iUnion.mpr ⟨i,hx⟩)).elim
  refine ⟨q,hq,?_,hqV,?_⟩
  · intro x
    rcases hqW x with h|h
    · exact hVU _ h
    · have he : c x=q x := h.2
      rw [←he]
      exact hcU x
  · intro x hx
    rcases hqW x with h|h
    · exact (hx (mem_iUnion.mpr ⟨q x,h⟩)).elim
    · exact (show c x=q x from h.2).symm

variable [MetricSpace M] [BorelSpace M]

/-- A coherent finite chart selector with an original-measure compact core
and a uniform endpoint recoverability radius. Nothing is conditioned on a
good Oseledets/frame set, and no intermediate chart codes refine the cells. -/
theorem stable_selector [CompactSpace M] (μ : Measure M) [IsFiniteMeasure μ]
    (c : M → ι) (hc : Measurable c) (U : ι → Set M)
    (hU : ∀ i,IsOpen (U i)) (hcU : ∀ x,x∈U (c x))
    (ε : ℝ≥0) (hε : 0<ε) :
    ∃ (q : M → ι) (K : ι → Set M) (r : ℝ),
      Measurable q ∧ (∀ x,x∈U (q x)) ∧
      (∀ i,IsCompact (K i)) ∧ μ (⋃ i,K i)ᶜ≤ε ∧ 0<r ∧
      (∀ i,∀ x∈K i,q x=i) ∧
      ∀ x∈⋃ i,K i,∀ y,dist y x≤r → q y=q x := by
  obtain ⟨K,r,hK,_,hm,hr,hKU,hd⟩ := selector_cores μ c hc U hU hcU ε hε
  obtain ⟨q,hq,hqU,hqK,_⟩ := protected_selector c hc U (fun i => cthickening r (K i))
    (fun i => isClosed_cthickening.measurableSet) hKU hcU hd
  have hKq : ∀ i,∀ x∈K i,q x=i := by
    intro i x hx
    exact hqK i x (self_subset_cthickening _ hx)
  refine ⟨q,K,r,hq,hqU,hK,hm,hr,hKq,?_⟩
  intro x hx y hy
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  rw [hKq i x hi]
  apply hqK i y
  exact mem_cthickening_of_dist_le y x r (K i) hi hy
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.AtlasCores
open Set MeasureTheory Metric
open scoped ENNReal NNReal
variable {M ι : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A stable selector can be chosen in any prescribed positive enlargement
of the original compact patches. This preserves uniform chart bounds while
charging only one fixed compact-core error in the original measure. -/
theorem compact_stable_selector (μ : Measure M) [IsFiniteMeasure μ]
    (c : M → ι) (hc : Measurable c) (K : ι → Set M)
    (hcK : ∀ x,x∈K (c x))
    {r : ℝ} (hr : 0<r) (ε : ℝ≥0) (hε : 0<ε) :
    ∃ (q : M → ι) (L : ι → Set M) (s : ℝ),
      Measurable q ∧ (∀ x,x∈cthickening r (K (q x))) ∧
      (∀ i,IsCompact (L i)) ∧ μ (⋃ i,L i)ᶜ≤ε ∧ 0<s ∧
      (∀ i,L i⊆K i) ∧ (∀ i,∀ x∈L i,q x=i) ∧
      ∀ x∈⋃ i,L i,∀ y,dist y x ≤ s → q y=q x := by
  obtain ⟨L,s,hL,hLc,hm,hs,hLU,hd⟩ := selector_cores μ c hc
    (fun i => thickening r (K i)) (fun _ => isOpen_thickening)
    (fun x => self_subset_thickening hr _ (hcK x)) ε hε
  have hLK (i : ι) : L i⊆K i := by
    intro x hx
    have he : c x=i := hLc i hx
    simpa only [he] using hcK x
  obtain ⟨q,hq,hqU,hqL,_⟩ := protected_selector c hc
    (fun i => thickening r (K i)) (fun i => cthickening s (L i))
    (fun _ => isClosed_cthickening.measurableSet) hLU
    (fun x => self_subset_thickening hr _ (hcK x)) hd
  have hLq (i : ι) (x : M) (hx : x∈L i) : q x=i :=
    hqL i x (self_subset_cthickening _ hx)
  refine ⟨q,L,s,hq,fun x => thickening_subset_cthickening r _ (hqU x),hL,hm,hs,hLK,hLq,?_⟩
  intro x hx y hy
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  rw [hLq i x hi]
  exact hqL i y (mem_cthickening_of_dist_le y x s (L i) hi hy)
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator NNReal ENNReal
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [CompactSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- Stable endpoint chart labels and actual good gauges are compatible.
The chart-core error is fixed before the dyadic sequence is constructed;
no orbit code or endpoint label is added to the future cell partition. -/
theorem good_stable_gauges (S : Diffeomorph I I M M ∞)
    (μ : ProbabilityMeasure M) (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M))
    {η : ℝ} (hη : 0<η) (ε : ℝ≥0) (hε : 0<ε) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K L : ι → Set M) (q : M → ι) (s : ℝ),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable q ∧ (∀ x,x∈K (q x)) ∧
      (∀ i,IsCompact (L i)) ∧ (μ : Measure M) (⋃ i,L i)ᶜ≤ε ∧ 0<s ∧
      (∀ i,L i⊆K i) ∧ (∀ i,∀ x∈L i,q x=i) ∧
      (∀ x∈⋃ i,L i,∀ y,dist y x ≤ s → q y=q x) ∧
      ∃ (b : ℕ → ℝ) (R C : ℝ) (G : ℕ → Set M),
        0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
        Summable (fun k => (b k)^2) ∧
        (∀ k,IsCompact (G k) ∧ 1-η/100≤(μ : Measure M).real (G k)) ∧
        ∀ᶠ k in atTop,∀ x∈G k,
          Nonempty (BilateralGauge I S a q (2^k) (C*(b k*2^k)) R x) := by
  obtain ⟨ι,hfin,hmeas,hsc,a,K,c,hK,hKU,hc,hcK,b,R,C,G,hR,hC,hbp,hbf,hbs,hG,hg⟩ :=
    good_bilateral_gauges I S μ hS hη
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  let : MeasurableSingletonClass ι := hsc
  obtain ⟨r,D,hr,hD,hcarry⟩ := uniform_carried_bilateral_explicit I a K hK hKU
  choose r₀ hr₀ hr₀U using fun i =>
    (hK i).exists_cthickening_subset_open (chartAt H (a i)).open_source (hKU i)
  obtain ⟨t,ht,htr⟩ := CarriedCharts.finite_positive_lower r₀ hr₀
  let v := min r t
  have hv : 0<v := lt_min hr ht
  let K' (i : ι) := cthickening v (K i)
  have hK' (i : ι) : IsCompact (K' i) := (hK i).cthickening
  have hK'U (i : ι) : K' i⊆(chartAt H (a i)).source :=
    (cthickening_mono ((min_le_right r t).trans (htr i)) _).trans (hr₀U i)
  obtain ⟨q,L,s,hq,hqK,hL,hm,hs,hLK,hLq,hstable⟩ :=
    AtlasCores.compact_stable_selector (μ : Measure M) c hc K hcK hv ε hε
  let C' := C+Real.log D
  have hlog : 0≤Real.log D := Real.log_nonneg hD
  have hC' : 0≤C' := add_nonneg hC hlog
  refine ⟨ι,hfin,hmeas,hsc,a,K',L,q,s,hK',hK'U,hq,hqK,hL,hm,hs,
    fun i => (hLK i).trans (self_subset_cthickening _),hLq,hstable,
    b,R,C',G,hR,hC',hbp,hbf,hbs,hG,?_⟩
  filter_upwards [hg] with k hk
  intro x hx
  obtain ⟨A⟩ := hk x hx
  have hqK' y : y∈cthickening r (K (q y)) :=
    cthickening_mono (min_le_left r t) _ (hqK y)
  obtain ⟨F,Z,hFl,hZl,hU,hV,hFs,hZs,_⟩ := hcarry S c x (2^k) (C*(b k*2^k)) R A
    (fun t => q (S^[t] x)) (fun t => q (S.symm^[t] x)) hcK rfl
    (fun t _ => hqK' _) (fun t _ => hqK' _)
  have hbound : C*(b k*2^k)+Real.log D≤C'*(b k*2^k) := by
    have hn := GoodStationary.burden_ge_one b hbf k
    dsimp only [C']
    nlinarith
  have hexp := Real.exp_le_exp.mpr hbound
  refine ⟨{
    lam := A.lam
    rate_bound := A.rate_bound
    UF := F.U
    VF := F.V
    UB := Z.U
    VB := Z.V
    invF := fun t => ⟨F.UV t,F.VU t⟩
    invB := fun t => ⟨Z.UV t,Z.VU t⟩
    centerU := hU
    centerV := hV
    normF := fun t ht => ⟨(F.normU t ht).trans hexp,(F.normV t ht).trans hexp⟩
    normB := fun t ht => ⟨(Z.normU t ht).trans hexp,(Z.normV t ht).trans hexp⟩
    stepF := ?_
    stepB := ?_
  }⟩
  · intro t ht
    have hl : F.lam=A.lam := funext hFl
    simpa only [hl] using hFs t ht
  · intro t ht
    have hl : Z.lam=(fun i => -A.lam i) := funext hZl
    simpa only [hl] using hZs t ht
end SmoothObstruction.ManifoldCoordinates

end

end OAI
