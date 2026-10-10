import OAI.Analysis.BackwardIntertwiners.PolarDiagonals

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def polarAlgebra : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) := strongGenerated (Set.range polarDiagonal)
lemma polarDiagonal_mem (n : ℤ) : polarDiagonal n ∈ polarAlgebra := subset_strongGenerated _ ⟨n,rfl⟩
lemma polarAlgebra_closed : StronglyClosed polarAlgebra := strongGenerated_closed _
lemma polarAlgebra_le_full : polarAlgebra ≤ fullMultiplierAlgebra := by
  apply strongGenerated_le fullMultiplier_stronglyClosed
  rintro _ ⟨n,rfl⟩
  exact ⟨betaSymbol n,rfl⟩
lemma polarAlgebra_commutative {A B : GlobalHilbert →L[ℂ] GlobalHilbert}
    (hA : A ∈ polarAlgebra) (hB : B ∈ polarAlgebra) : A*B=B*A :=
  fullMultiplier_commute (polarAlgebra_le_full hA) (polarAlgebra_le_full hB)

lemma halfExponent_eq_ten_iff (t : ℕ → ℕ) (k : ℕ) : halfExponent t k=10 ↔ k=0 := by
  constructor
  · intro h
    have hl := halfExponent_lower t k
    rw [h] at hl
    have hk : (k:ℝ)=0 := by have := Nat.cast_nonneg (α:=ℝ) k; nlinarith
    exact_mod_cast hk
  · rintro rfl
    simp [halfExponent,residueCorrection]
lemma explicitBeta_central (x : Base) (j : ℤ) : explicitBeta x j=Real.exp (-10) ↔ j=-1 ∨ j=0 := by
  have hh (t : ℕ → ℕ) (k : ℕ) : Real.exp (-halfExponent t k)=Real.exp (-10) ↔ k=0 := by
    rw [Real.exp_eq_exp,neg_inj,halfExponent_eq_ten_iff]
  cases j with
  | ofNat k =>
    change Real.exp (-halfExponent (plusResidue x) k)=Real.exp (-10) ↔ _
    rw [hh]
    change k=0 ↔ (k:ℤ) = -1 ∨ (k:ℤ) = 0
    omega
  | negSucc k =>
    change Real.exp (-halfExponent (minusResidue x) k)=Real.exp (-10) ↔ _
    rw [hh]
    omega
lemma sliceProjection_central (r : ℤ) : sliceProjection r=
    levelProjection (-r-1) (Real.exp (-10)) * levelProjection (-r) (Real.exp (-10)) := by
  rw [sliceProjection_diagonal,levelProjection,levelProjection,diagonalProjection_mul]
  apply diagonalProjection_ext
  intro j
  apply EventuallyEq.of_eq
  ext x
  change (x ∈ if j=r then Set.univ else ∅) ↔
    (explicitBeta x (j+(-r-1))=Real.exp (-10) ∧ explicitBeta x (j+-r)=Real.exp (-10))
  simp only [explicitBeta_central]
  by_cases hj : j=r <;> simp [hj] <;> omega
lemma sliceProjection_mem_polar (r : ℤ) : sliceProjection r ∈ polarAlgebra := by
  rw [sliceProjection_central]
  exact polarAlgebra.mul_mem
    (levelProjection_mem_all polarAlgebra_closed _ _ (polarDiagonal_mem _))
    (levelProjection_mem_all polarAlgebra_closed _ _ (polarDiagonal_mem _))


def rectangleProjection (r : ℤ) (E : Set Base) (hE : MeasurableSet E) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (fun j => if j=r then E else ∅) (fun j => by split_ifs; exact hE; exact MeasurableSet.empty)
lemma rectangleProjection_univ (r : ℤ) : rectangleProjection r Set.univ MeasurableSet.univ=sliceProjection r :=
  (sliceProjection_diagonal r).symm
lemma rectangleProjection_empty (r : ℤ) : rectangleProjection r ∅ MeasurableSet.empty=0 := by
  unfold rectangleProjection
  convert diagonalProjection_empty using 2
  ext j x
  simp
lemma rectangleProjection_ext {r : ℤ} {E F : Set Base} {hE : MeasurableSet E} {hF : MeasurableSet F}
    (he : E=ᵐ[baseMeasure] F) : rectangleProjection r E hE=rectangleProjection r F hF := by
  apply diagonalProjection_ext
  intro j
  by_cases hj : j=r <;> simp only [hj,↓reduceIte]
  · exact he
  · exact Filter.EventuallyEq.rfl
lemma rectangleProjection_mul (r : ℤ) (E F : Set Base) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    rectangleProjection r E hE * rectangleProjection r F hF=rectangleProjection r (E∩F) (hE.inter hF) := by
  rw [rectangleProjection,rectangleProjection,diagonalProjection_mul]
  apply diagonalProjection_ext
  intro j
  apply EventuallyEq.of_eq
  by_cases hj : j=r <;> simp only [hj,↓reduceIte,Set.inter_empty]
lemma rectangleProjection_compl (r : ℤ) (E : Set Base) (hE : MeasurableSet E) :
    rectangleProjection r Eᶜ hE.compl = sliceProjection r - rectangleProjection r E hE := by
  rw [sliceProjection_diagonal]
  change diagonalRepresentation _ = diagonalRepresentation _ - diagonalRepresentation _
  rw [←map_sub]
  congr 1
  apply Subtype.ext
  funext x j
  change projectionSymbol _ _ x j = projectionSymbol _ _ x j - projectionSymbol _ _ x j
  by_cases hj : j=r <;> by_cases he : x∈E <;> simp [hj,he]
lemma rectangleProjection_union (r : ℤ) (E F : Set Base) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    rectangleProjection r (E∪F) (hE.union hF) = rectangleProjection r E hE+rectangleProjection r F hF-
      rectangleProjection r E hE * rectangleProjection r F hF := by
  change diagonalRepresentation _ = diagonalRepresentation _+diagonalRepresentation _-diagonalRepresentation _*diagonalRepresentation _
  rw [←map_mul,←map_add,←map_sub]
  congr 1
  apply Subtype.ext
  funext x j
  change projectionSymbol _ _ x j = projectionSymbol _ _ x j + projectionSymbol _ _ x j - projectionSymbol _ _ x j * projectionSymbol _ _ x j
  by_cases hj : j=r <;> by_cases he : x∈E <;> by_cases hf : x∈F <;> simp [hj,he,hf]

def blockAnchor (m : ℕ) : ℕ := 8^(m-1)
lemma blockAnchor_ne_zero (m : ℕ) : blockAnchor m ≠ 0 := pow_ne_zero _ (by norm_num)
lemma blockAnchor_block {m : ℕ} (hm : 1 ≤ m) : weightBlock (blockAnchor m)=m := by
  rw [weightBlock,blockAnchor,Nat.log_pow (by norm_num : 1<8)]
  omega
def residueEigenvalue (m t : ℕ) : ℝ :=
  Real.exp (-(10*((blockAnchor m:ℝ)+1)+100*((2^m:ℝ)-2+(t:ℝ))))
lemma beta_anchor_residue {m : ℕ} (hm : 1 ≤ m) (t : ℕ) (x : Base) :
    explicitBeta x (blockAnchor m) = residueEigenvalue m t ↔ residue m x=t := by
  change Real.exp (-halfExponent (plusResidue x) (blockAnchor m))=residueEigenvalue m t ↔ _
  rw [residueEigenvalue,Real.exp_eq_exp,neg_inj]
  simp only [halfExponent,residueCorrection,blockAnchor_ne_zero,↓reduceIte,
    residueScale,blockAnchor_block hm,plusResidue]
  push_cast
  constructor
  · intro h
    have he : (residue m x:ℝ)=(t:ℝ) := by linarith
    exact_mod_cast he
  · intro h
    rw [h]
lemma residue_rectangle_spectral {m : ℕ} (hm : 1 ≤ m) (t : ℕ) (r : ℤ) :
    rectangleProjection r (residueClass m t) (measurableSet_residueClass m t) =
      sliceProjection r * levelProjection ((blockAnchor m:ℤ)-r) (residueEigenvalue m t) := by
  rw [sliceProjection_diagonal,levelProjection,diagonalProjection_mul]
  apply diagonalProjection_ext
  intro j
  apply EventuallyEq.of_eq
  ext x
  by_cases hj : j=r
  · subst j


    simp only [↓reduceIte,Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_ofPred_eq]
    change residue m x=t ↔ explicitBeta x (r+((blockAnchor m:ℤ)-r))=residueEigenvalue m t
    rw [show r+((blockAnchor m:ℤ)-r)=(blockAnchor m:ℤ) by omega]
    exact (beta_anchor_residue hm t x).symm
  · simp [hj]
lemma residue_rectangle_mem (m t : ℕ) (r : ℤ) :
    rectangleProjection r (residueClass m t) (measurableSet_residueClass m t) ∈ polarAlgebra := by
  by_cases hm : m=0
  · subst m
    have hz (x : Base) : residue 0 x=0 := by have := residue_lt 0 x; norm_num at this; omega
    by_cases ht : t=0
    · have he : residueClass 0 t=Set.univ := by ext x; simp [residueClass,hz,ht]
      have hr : rectangleProjection r (residueClass 0 t) (measurableSet_residueClass 0 t)=sliceProjection r := by
        exact (rectangleProjection_ext (EventuallyEq.of_eq he)).trans (rectangleProjection_univ r)
      rw [hr]
      exact sliceProjection_mem_polar _
    · have he : residueClass 0 t=∅ := by ext x; simp [residueClass,hz,Ne.symm ht]
      have hr : rectangleProjection r (residueClass 0 t) (measurableSet_residueClass 0 t)=0 := by
        exact (rectangleProjection_ext (EventuallyEq.of_eq he)).trans (rectangleProjection_empty r)
      rw [hr]
      exact polarAlgebra.zero_mem
  · rw [residue_rectangle_spectral (by omega : 1 ≤ m)]
    exact polarAlgebra.mul_mem (sliceProjection_mem_polar _)
      (levelProjection_mem_all polarAlgebra_closed _ _ (polarDiagonal_mem _))

lemma borel_le_of_residue_measurable (m : MeasurableSpace (PadicInt 2))
    (hm : ∀ n t : ℕ, @MeasurableSet (PadicInt 2) m {x | twoResidue n x=t}) :
    padicBorel ≤ m := by
  let : MeasurableSpace (PadicInt 2) := padicBorel
  let R : PadicInt 2 → ℕ → ℕ := fun x n => twoResidue n x
  have hc : Continuous R := continuous_pi fun n =>
    continuous_of_discreteTopology.comp (continuous_twoResidue n)
  have hi : Function.Injective R := by
    intro x y h
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    apply ZMod.val_injective
    exact congrFun h n
  have he : MeasurableEmbedding R := (hc.isClosedEmbedding hi).measurableEmbedding
  have hr : @Measurable _ _ m inferInstance R := by
    let : MeasurableSpace (PadicInt 2) := m
    apply Measurable.of_eval
    intro n
    exact measurable_to_countable' (hm n)
  exact he.comap_eq.symm.le.trans hr.comap_le

lemma rectangleProjection_finiteUnion_mem (r : ℤ) (E : ℕ → Set Base)
    (hE : ∀ i, MeasurableSet (E i)) (hmem : ∀ i, rectangleProjection r (E i) (hE i) ∈ polarAlgebra)
    (s : Finset ℕ) : rectangleProjection r (⋃ i ∈ s, E i) (by measurability) ∈ polarAlgebra := by
  induction s using Finset.induction_on with
  | empty =>
    have he : (⋃ i ∈ (∅:Finset ℕ), E i)=∅ := by simp
    have hp : rectangleProjection r (⋃ i ∈ (∅ : Finset ℕ), E i) (by measurability) =
        rectangleProjection r ∅ MeasurableSet.empty := rectangleProjection_ext (EventuallyEq.of_eq he)
    rw [hp, rectangleProjection_empty]
    exact polarAlgebra.zero_mem
  | @insert i s hi hs =>
    have he : (⋃ k ∈ insert i s, E k)=E i ∪ ⋃ k ∈ s,E k := by simp
    have hp : rectangleProjection r (⋃ k ∈ insert i s, E k) (by measurability) =
        rectangleProjection r (E i ∪ ⋃ k ∈ s, E k) ((hE i).union (by measurability)) :=
      rectangleProjection_ext (EventuallyEq.of_eq he)
    rw [hp,
      rectangleProjection_union r (E i) (⋃ k∈s,E k) (hE i) (by measurability)]
    exact polarAlgebra.sub_mem (polarAlgebra.add_mem (hmem i) hs) (polarAlgebra.mul_mem (hmem i) hs)

lemma rectangleProjection_iUnion_mem (r : ℤ) (E : ℕ → Set Base)
    (hE : ∀ i, MeasurableSet (E i)) (hmem : ∀ i, rectangleProjection r (E i) (hE i) ∈ polarAlgebra) :
    rectangleProjection r (⋃ i, E i) (MeasurableSet.iUnion hE) ∈ polarAlgebra := by
  let a (s : Finset ℕ) : DiagonalSymbol := projectionSymbol
    (fun j => if j=r then ⋃i∈s,E i else ∅) (fun j => by split_ifs <;> measurability)
  let b : DiagonalSymbol := projectionSymbol
    (fun j => if j=r then ⋃i,E i else ∅) (fun j => by split_ifs <;> measurability)
  apply polarAlgebra_closed.mem_of_tendsto (l:=atTop) (T:=fun s => diagonalOperator (a s))
  · exact Eventually.of_forall (rectangleProjection_finiteUnion_mem r E hE hmem)
  · intro f
    apply diagonalOperator_tendsto (b:=b) a zero_le_one
      (fun s => projectionSymbol_norm_le _ _) (projectionSymbol_norm_le _ _)
    apply Eventually.of_forall
    intro x j
    apply tendsto_const_nhds.congr'
    by_cases hj : j=r
    · by_cases hx : x ∈ ⋃i,E i
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        filter_upwards [eventually_ge_atTop ({i}:Finset ℕ)] with s hs
        have his : i∈s := Finset.singleton_subset_iff.mp hs
        have hxs : x∈⋃i∈s,E i := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨his,hi⟩⟩
        simp [a,b,hj,hx,hxs]
      · exact Eventually.of_forall (fun s => by
          have hxs : x ∉ ⋃i∈s,E i := fun h => hx (by
            obtain ⟨i,hi,hiE⟩ := Set.mem_iUnion.mp h |>.imp (fun i hi => Set.mem_iUnion.mp hi)
            exact Set.mem_iUnion.mpr ⟨i,hiE⟩)
          simp [a,b,hj,hx,hxs])
    · exact Eventually.of_forall (fun s=>by simp [a,b,hj])


@[instance_reducible]
def polarProjectionMeasurableSpace (r : ℤ) : MeasurableSpace Base where
  MeasurableSet' E := ∃ hE : MeasurableSet E, rectangleProjection r E hE ∈ polarAlgebra
  measurableSet_empty := ⟨MeasurableSet.empty,by rw [rectangleProjection_empty]; exact polarAlgebra.zero_mem⟩
  measurableSet_compl E h := by
    obtain ⟨hE,hm⟩ := h
    refine ⟨hE.compl,?_⟩
    rw [rectangleProjection_compl r E hE]
    exact polarAlgebra.sub_mem (sliceProjection_mem_polar r) hm
  measurableSet_iUnion E h := by
    choose hE hm using h
    exact ⟨MeasurableSet.iUnion hE,rectangleProjection_iUnion_mem r E hE hm⟩

lemma rectangleProjection_borel_mem (r : ℤ) {E : Set (PadicInt 2)} (hE : MeasurableSet E) :
    rectangleProjection r E (hE.nullMeasurableSet (μ:=baseHaar)) ∈ polarAlgebra := by
  have hm : padicBorel ≤ polarProjectionMeasurableSpace r :=
    borel_le_of_residue_measurable _ (fun m t =>
      ⟨measurableSet_residueClass m t,residue_rectangle_mem m t r⟩)
  exact (hm E hE).choose_spec

lemma rectangleProjection_mem (r : ℤ) (E : Set Base) (hE : MeasurableSet E) :
    rectangleProjection r E hE ∈ polarAlgebra := by
  obtain ⟨F,hsub,hF,he⟩ := (show NullMeasurableSet (show Set (PadicInt 2) from E) baseHaar from hE).exists_measurable_superset_ae_eq
  have he' : (show Set Base from F)=ᵐ[baseMeasure] E := he
  rw [←rectangleProjection_ext (hE:=hF.nullMeasurableSet (μ:=baseHaar)) he']
  exact rectangleProjection_borel_mem r hF
lemma DiagonalSymbol.sum_apply {ι : Type*} (s : Finset ι) (a : ι → DiagonalSymbol) (x : Base) (j : ℤ) :
    (∑ i ∈ s, a i) x j = ∑ i ∈ s, a i x j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [Finset.sum_insert,hi,hs]


def simpleSliceSymbol (r : ℤ) (f : SimpleFunc Base ℂ) : DiagonalSymbol :=
  ∑ t ∈ f.range, t • projectionSymbol
    (fun j => if j=r then f ⁻¹' {t} else ∅)
    (fun j=>by split_ifs; exact f.measurableSet_fiber t; exact MeasurableSet.empty)
lemma simpleSliceSymbol_apply (r : ℤ) (f : SimpleFunc Base ℂ) (x : Base) (j : ℤ) :
    simpleSliceSymbol r f x j=if j=r then f x else 0 := by
  simp only [simpleSliceSymbol,DiagonalSymbol.sum_apply,DiagonalSymbol.smul_apply,projectionSymbol_apply]
  by_cases hj : j=r
  · simp only [hj,↓reduceIte,Set.mem_preimage,Set.mem_singleton_iff,mul_ite,mul_one,mul_zero]
    rw [Finset.sum_eq_single (f x)]
    · simp
    · intro b hb hbx
      simp [Ne.symm hbx]
    · exact fun hn => (hn (f.mem_range_self x)).elim
  · simp [hj]
lemma simpleSliceSymbol_mem (r : ℤ) (f : SimpleFunc Base ℂ) : diagonalOperator (simpleSliceSymbol r f) ∈ polarAlgebra := by
  change diagonalRepresentation (∑ t ∈ f.range, _) ∈ polarAlgebra
  rw [map_sum]
  apply polarAlgebra.sum_mem
  intro t ht
  rw [map_smul]
  exact polarAlgebra.smul_mem (rectangleProjection_mem r (f ⁻¹' {t}) (f.measurableSet_fiber t)) t

def sliceSymbol (r : ℤ) (a : DiagonalSymbol) : DiagonalSymbol :=
  a * projectionSymbol (fun j=>if j=r then Set.univ else ∅) (fun j=>by split_ifs <;> measurability)
lemma sliceSymbol_apply (r : ℤ) (a : DiagonalSymbol) (x : Base) (j : ℤ) :
    sliceSymbol r a x j=if j=r then a x r else 0 := by
  by_cases hj : j=r <;> simp [sliceSymbol,hj]
lemma sliceSymbol_norm_le (r : ℤ) (a : DiagonalSymbol) (x : Base) (j : ℤ) :
    ‖sliceSymbol r a x j‖ ≤ a.bound := by
  rw [sliceSymbol_apply]
  split_ifs
  · exact a.norm_le_bound x r
  · simpa using a.bound_nonneg
lemma sliceSymbol_mem (r : ℤ) (a : DiagonalSymbol) : diagonalOperator (sliceSymbol r a) ∈ polarAlgebra := by
  let f (n : ℕ) : SimpleFunc Base ℂ := SimpleFunc.approxOn (fun x=>a x r) (a.measurable r) Set.univ 0 (Set.mem_univ _) n
  apply polarAlgebra_closed.mem_of_tendsto (l:=atTop) (T:=fun n=>diagonalOperator (simpleSliceSymbol r (f n)))
  · exact Eventually.of_forall (fun n=>simpleSliceSymbol_mem r (f n))
  · intro v
    apply diagonalOperator_tendsto (C:=2*a.bound) _ _ (mul_nonneg (by norm_num) a.bound_nonneg)
    · intro n x j
      rw [simpleSliceSymbol_apply]
      split_ifs
      · exact (SimpleFunc.norm_approxOn_zero_le (a.measurable r) (Set.mem_univ (0:ℂ)) x n).trans
          (by linarith [a.norm_le_bound x r])
      · simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) a.bound_nonneg
    · intro x j
      exact (sliceSymbol_norm_le r a x j).trans (by linarith [a.bound_nonneg])
    · apply Eventually.of_forall
      intro x j
      simp only [simpleSliceSymbol_apply,sliceSymbol_apply]
      by_cases hj : j=r
      · simp only [hj,↓reduceIte]
        exact SimpleFunc.tendsto_approxOn (a.measurable r) (Set.mem_univ (0:ℂ)) (by simp)
      · simp only [hj,↓reduceIte]
        exact tendsto_const_nhds

lemma finiteSliceSymbol_apply (s : Finset ℤ) (a : DiagonalSymbol) (x : Base) (j : ℤ) :
    (∑ r ∈ s,sliceSymbol r a) x j=if j∈s then a x j else 0 := by
  rw [DiagonalSymbol.sum_apply]
  simp_rw [sliceSymbol_apply]
  simp
lemma diagonalOperator_mem_polar (a : DiagonalSymbol) : diagonalOperator a ∈ polarAlgebra := by
  let T (s : Finset ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert := diagonalOperator (∑ r ∈ s,sliceSymbol r a)
  apply polarAlgebra_closed.mem_of_tendsto (l:=atTop) (T:=T)
  · apply Eventually.of_forall
    intro s
    change diagonalRepresentation (∑ r ∈ s,sliceSymbol r a) ∈ polarAlgebra
    rw [map_sum]
    exact polarAlgebra.sum_mem (fun r _=>sliceSymbol_mem r a)
  · intro v
    apply diagonalOperator_tendsto (C:=a.bound) _ _ a.bound_nonneg
    · intro s x j
      rw [finiteSliceSymbol_apply]
      split_ifs
      · exact a.norm_le_bound x j
      · simpa using a.bound_nonneg
    · exact a.norm_le_bound
    · apply Eventually.of_forall
      intro x j
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ({j}:Finset ℤ)] with s hs
      rw [finiteSliceSymbol_apply,ite_eq_left (Finset.singleton_subset_iff.mp hs)]



theorem polarAlgebra_eq_fullMultiplier : polarAlgebra=fullMultiplierAlgebra := by
  apply le_antisymm polarAlgebra_le_full
  rintro T ⟨a,rfl⟩
  exact diagonalOperator_mem_polar a


end
end BackwardIntertwiners

end OAI
