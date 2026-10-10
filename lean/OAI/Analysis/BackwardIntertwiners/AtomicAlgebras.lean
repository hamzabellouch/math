import OAI.Analysis.BackwardIntertwiners.PolarFactors

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

attribute [local instance] realOperatorTower realOperatorCommute complexNormalCalculus complexClosedCalculus realSelfAdjointCalculus

open InnerProductSpace ContinuousLinearMap

def MinimalProjection (A : StarSubalgebra ℂ (H →L[ℂ] H)) (P : H →L[ℂ] H) : Prop :=
  IsStarProjection P ∧ P ≠ 0 ∧ P ∈ A ∧ ∀ Q : H →L[ℂ] H,
    IsStarProjection Q → Q ∈ A → Q*P=Q → Q=0 ∨ Q=P

def AtomicAlgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (P : ι → H →L[ℂ] H),
    (∀ i, MinimalProjection A (P i)) ∧
    (∀ i j, i ≠ j → P i * P j = 0) ∧
    ∀ v : H, HasSum (fun i => P i v) v

def DiffuseAlgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ¬∃ P, MinimalProjection A P

lemma selfAdjoint_commutes_rankOne {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {u v : H} {t : ℝ} (hu : T u = (t:ℂ) • u) (hv : T v = (t:ℂ) • v) :
    T * rankOne ℂ u v = rankOne ℂ u v * T := by
  ext z
  change T (inner ℂ v z • u) = inner ℂ v (T z) • u
  have hi : inner ℂ (T v) z = inner ℂ v (T z) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) v z
  rw [map_smul,hu,←hi,hv,
    inner_smul_left,Complex.conj_ofReal,smul_smul,mul_comm]

lemma projection_reverse_mul {P Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : Q*P=Q) : P*Q=Q := by
  have hh := congrArg star h
  simpa only [star_mul,hP.isSelfAdjoint.star_eq,hQ.isSelfAdjoint.star_eq] using hh


lemma eigenspace_projection_minimal {s : Set (H →L[ℂ] H)}
    (hs : ∀ T ∈ s, IsSelfAdjoint T) {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (hP₀ : P ≠ 0) (hPA : P ∈ strongGenerated s)
    (hscalar : ∀ T ∈ s, ∃ t : ℝ, ∀ v : H, P v = v → T v = (t:ℂ) • v) :
    MinimalProjection (strongGenerated s) P := by
  refine ⟨hP,hP₀,hPA,?_⟩
  intro Q hQ hQA hQP
  by_cases hQ₀ : Q=0
  · exact Or.inl hQ₀
  right
  obtain ⟨z,hz⟩ : ∃ z : H, Q z ≠ 0 := by
    by_contra! hz
    apply hQ₀
    ext z
    exact hz z
  let v := Q z
  have hv₀ : v ≠ 0 := hz
  have hQv : Q v = v := DFunLike.congr_fun hQ.isIdempotentElem z
  have hPv : P v = v := DFunLike.congr_fun (projection_reverse_mul hP hQ hQP) z
  have hcomm (u : H) (hPu : P u=u) : Q * rankOne ℂ u v = rankOne ℂ u v * Q := by
    have hle : strongGenerated s ≤ StarSubalgebra.centralizer ℂ {rankOne ℂ u v} := by
      apply strongGenerated_le (strong_centralizer_closed _)
      intro T hT
      apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      intro R hR
      obtain rfl : R = rankOne ℂ u v := hR
      obtain ⟨t,ht⟩ := hscalar T hT
      refine ⟨(selfAdjoint_commutes_rankOne (hs T hT) (ht u hPu) (ht v hPv)).symm, ?_⟩
      change (rankOne ℂ u v).adjoint * T = T * (rankOne ℂ u v).adjoint
      rw [InnerProductSpace.adjoint_rankOne]
      exact (selfAdjoint_commutes_rankOne (hs T hT) (ht v hPv) (ht u hPu)).symm
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hQA) _ (Set.mem_singleton _)).1.symm
  have hfix (u : H) (hPu : P u=u) : Q u=u := by
    have hh := DFunLike.congr_fun (hcomm u hPu) v
    change Q (inner ℂ v v • u) = inner ℂ v (Q v) • u at hh
    rw [hQv,map_smul] at hh
    exact (smul_right_injective H (inner_self_ne_zero.mpr hv₀)) hh
  have he : Q*P=P := by
    ext z
    exact hfix (P z) (DFunLike.congr_fun hP.isIdempotentElem z)
  exact hQP.symm.trans he



def halfExponentIndex (t : ℕ → ℕ) (k : ℕ) : ℤ :=
  10*((k:ℤ)+1) + if k=0 then 0 else 100*((residueScale k:ℤ)-2+(t (weightBlock k):ℤ))
lemma halfExponentIndex_cast (t : ℕ → ℕ) (k : ℕ) :
    (halfExponentIndex t k : ℝ) = halfExponent t k := by
  simp only [halfExponentIndex,halfExponent,residueCorrection]
  split_ifs <;> push_cast <;> rfl

def exponentIndex (x : Base) : ℤ → ℤ
  | .ofNat k => halfExponentIndex (plusResidue x) k
  | .negSucc k => halfExponentIndex (minusResidue x) k
lemma exponentIndex_cast (x : Base) (j : ℤ) : (exponentIndex x j : ℝ)=explicitExponent x j := by
  cases j <;> exact halfExponentIndex_cast _ _
lemma explicitBeta_exponentIndex (x : Base) (j : ℤ) :
    explicitBeta x j=Real.exp (-(exponentIndex x j : ℝ)) := by
  rw [exponentIndex_cast]
  rfl
lemma exp_neg_int_injective : Function.Injective (fun z : ℤ => Real.exp (-(z:ℝ))) := by
  intro a b h
  have hh := neg_injective (Real.exp_injective h)
  exact_mod_cast hh


def jointLevel (F : Finset ℤ) (t : ↥F → ℤ) (j : ℤ) : Set Base :=
  {x | ∀ n : ↥F, explicitBeta x (j+n)=Real.exp (-(t n:ℝ))}
lemma jointLevel_eq_iInter (F : Finset ℤ) (t : ↥F → ℤ) (j : ℤ) :
    jointLevel F t j=⋂ n : ↥F, {x : Base | explicitBeta x (j+(n:ℤ))=Real.exp (-(t n:ℝ))} := by
  ext x
  simp [jointLevel]
lemma jointLevel_measurable (F : Finset ℤ) (t : ↥F → ℤ) (j : ℤ) : MeasurableSet (jointLevel F t j) := by
  rw [jointLevel_eq_iInter]
  exact MeasurableSet.iInter fun n : ↥F => measurableSet_eq_fun (measurable_explicitBeta (j+(n:ℤ))) measurable_const
lemma jointLevel_partition (F : Finset ℤ) (x : Base) (j : ℤ) : ∃! t : ↥F → ℤ, x ∈ jointLevel F t j := by
  refine ⟨fun n => exponentIndex x (j+n),fun n => explicitBeta_exponentIndex _ _,?_⟩
  intro t ht
  funext n
  exact exp_neg_int_injective ((ht n).symm.trans (explicitBeta_exponentIndex x (j+n)))

def jointProjection (F : Finset ℤ) (t : ↥F → ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (jointLevel F t) (jointLevel_measurable F t)
def finitePolarAlgebra (F : Finset ℤ) : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) :=
  strongGenerated (polarDiagonal '' (F : Set ℤ))
lemma finitePolarAlgebra_mem (F : Finset ℤ) {n : ℤ} (hn : n ∈ F) : polarDiagonal n ∈ finitePolarAlgebra F :=
  subset_strongGenerated _ ⟨n,hn,rfl⟩
lemma DiagonalSymbol.prod_apply {ι : Type*} (s : Finset ι) (a : ι → DiagonalSymbol) (x : Base) (j : ℤ) :
    (∏ i ∈ s, a i) x j = ∏ i ∈ s, a i x j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [Finset.prod_insert,hi,hs]
lemma diagonalRepresentation_prod_mem {ι : Type*} (s : Finset ι) (a : ι → DiagonalSymbol)
    (A : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert))
    (ha : ∀ i ∈ s, diagonalRepresentation (a i) ∈ A) : diagonalRepresentation (∏ i ∈ s, a i) ∈ A := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    rw [Finset.prod_insert hi,map_mul]
    exact A.mul_mem (ha i (Finset.mem_insert_self _ _)) (hs fun k hk => ha k (Finset.mem_insert_of_mem hk))
lemma projectionSymbol_prod {ι : Type*} [Fintype ι] (E : ι → ℤ → Set Base)
    (hE : ∀ i j, MeasurableSet (E i j)) :
    (∏ i, projectionSymbol (E i) (hE i)) =
      projectionSymbol (fun j => ⋂ i, E i j) (fun j => MeasurableSet.iInter fun i => hE i j) := by
  apply Subtype.ext
  funext x j
  rw [DiagonalSymbol.prod_apply]
  simp only [projectionSymbol_apply,Finset.prod_boole,Finset.mem_univ,true_implies,Set.mem_iInter]
lemma jointProjection_mem (F : Finset ℤ) (t : ↥F → ℤ) : jointProjection F t ∈ finitePolarAlgebra F := by
  have he : jointProjection F t = diagonalRepresentation (∏ n : ↥F,
      projectionSymbol (fun j => {x | explicitBeta x (j+n)=Real.exp (-(t n:ℝ))})
        (fun j => measurableSet_eq_fun (measurable_explicitBeta (j+n)) measurable_const)) := by
    rw [projectionSymbol_prod]
    apply diagonalProjection_ext
    intro j
    exact EventuallyEq.of_eq (jointLevel_eq_iInter F t j)
  rw [he]
  apply diagonalRepresentation_prod_mem
  intro n _
  exact levelProjection_mem_all (strongGenerated_closed _) n _ (finitePolarAlgebra_mem F n.property)
lemma jointProjection_isStarProjection (F : Finset ℤ) (t : ↥F → ℤ) : IsStarProjection (jointProjection F t) :=
  diagonalProjection_isStarProjection _ _
lemma jointProjection_eigen (F : Finset ℤ) (t : ↥F → ℤ) (n : ↥F) :
    polarDiagonal n * jointProjection F t = (Real.exp (-(t n:ℝ)):ℂ) • jointProjection F t := by
  change diagonalRepresentation (betaSymbol n) * diagonalRepresentation (projectionSymbol _ _) =
    (Real.exp (-(t n:ℝ)):ℂ) • diagonalRepresentation (projectionSymbol _ _)
  rw [←map_mul,←map_smul]
  congr 1
  apply Subtype.ext
  funext x j
  change (explicitBeta x (j+n):ℂ) * projectionSymbol _ _ x j =
    (Real.exp (-(t n:ℝ)):ℂ) * projectionSymbol _ _ x j
  by_cases hx : x ∈ jointLevel F t j
  · rw [hx n]
  · simp [hx]
lemma jointProjection_orthogonal (F : Finset ℤ) {s t : ↥F → ℤ} (hst : s ≠ t) :
    jointProjection F s * jointProjection F t = 0 := by
  rw [jointProjection,jointProjection,diagonalProjection_mul,←diagonalProjection_empty]
  apply diagonalProjection_ext
  intro j
  apply EventuallyEq.of_eq
  ext x
  change (x ∈ jointLevel F s j ∧ x ∈ jointLevel F t j) ↔ False
  exact ⟨fun ⟨hs,ht⟩ => hst ((jointLevel_partition F x j).unique hs ht),False.elim⟩

lemma jointProjection_minimal (F : Finset ℤ) {t : ↥F → ℤ} (ht : jointProjection F t ≠ 0) :
    MinimalProjection (finitePolarAlgebra F) (jointProjection F t) := by
  apply eigenspace_projection_minimal
    (fun _ h => by obtain ⟨n,hn,rfl⟩ := h; exact polarDiagonal_selfAdjoint n)
    (jointProjection_isStarProjection F t) ht (jointProjection_mem F t)
  rintro T ⟨n,hn,rfl⟩
  refine ⟨Real.exp (-(t ⟨n,hn⟩:ℝ)),?_⟩
  intro v hv
  have hh := DFunLike.congr_fun (jointProjection_eigen F t ⟨n,hn⟩) v
  change polarDiagonal n (jointProjection F t v)= (Real.exp (-(t ⟨n,hn⟩:ℝ)):ℂ) • jointProjection F t v at hh
  simpa only [hv] using hh


lemma partitionProjection_hasSum {ι : Type*} [Countable ι]
    (E : ι → ℤ → Set Base) (hE : ∀ i j, MeasurableSet (E i j))
    (hpart : ∀ x j, ∃! i, x ∈ E i j) (f : GlobalHilbert) :
    HasSum (fun i => diagonalProjection (E i) (hE i) f) f := by
  let a (s : Finset ι) : DiagonalSymbol := ∑ i ∈ s, projectionSymbol (E i) (hE i)
  have hsum (s : Finset ι) (x : Base) (j : ℤ) :
      a s x j = if (hpart x j).choose ∈ s then 1 else 0 := by
    have he (i : ι) : projectionSymbol (E i) (hE i) x j =
        if i=(hpart x j).choose then (1:ℂ) else 0 := by
      simp only [projectionSymbol_apply]
      congr 1
      exact propext ⟨fun hi => (hpart x j).choose_spec.2 i hi,
        fun hi => hi ▸ (hpart x j).choose_spec.1⟩
    change (∑ i ∈ s, projectionSymbol (E i) (hE i)) x j = _
    rw [DiagonalSymbol.sum_apply]
    simp_rw [he]
    simp
  have hlim := diagonalOperator_tendsto (l:=atTop) a 1 zero_le_one
    (fun s x j => by rw [hsum]; split_ifs <;> norm_num)
    (by simp) (Eventually.of_forall fun x j => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ({(hpart x j).choose}:Finset ι)] with s hs
      rw [hsum]
      simp only [Finset.singleton_subset_iff] at hs
      simp [hs]) f
  have he (s : Finset ι) : diagonalOperator (a s) f = ∑ i ∈ s, diagonalProjection (E i) (hE i) f := by
    change diagonalRepresentation (∑ i ∈ s, projectionSymbol (E i) (hE i)) f = _
    rw [map_sum]
    simp only [sum_apply]
    rfl
  change Tendsto (fun s : Finset ι => ∑ i ∈ s, diagonalProjection (E i) (hE i) f) atTop (𝓝 f)
  simpa only [he,diagonalOperator_one,one_apply_eq_self] using hlim
lemma jointProjection_hasSum (F : Finset ℤ) (f : GlobalHilbert) :
    HasSum (fun t : ↥F → ℤ => jointProjection F t f) f :=
  partitionProjection_hasSum _ (jointLevel_measurable F) (jointLevel_partition F) f

theorem finitePolarAlgebra_atomic (F : Finset ℤ) : AtomicAlgebra (finitePolarAlgebra F) := by
  refine ⟨{t : ↥F → ℤ // jointProjection F t ≠ 0},inferInstance,
    fun t => jointProjection F t,fun t => jointProjection_minimal F t.property,?_,?_⟩
  · intro s t hst
    exact jointProjection_orthogonal F (fun he => hst (Subtype.ext he))
  · intro v
    apply (hasSum_subtype_iff_of_support_subset ?_).mpr (jointProjection_hasSum F v)
    intro t ht
    change jointProjection F t ≠ 0
    intro he
    apply ht
    change jointProjection F t v = 0
    rw [he]; rfl

lemma minimal_projection_dichotomy {P : GlobalHilbert →L[ℂ] GlobalHilbert}
    (hP : MinimalProjection polarAlgebra P) {Q : GlobalHilbert →L[ℂ] GlobalHilbert}
    (hQ : IsStarProjection Q) (hQm : Q ∈ polarAlgebra) {v : GlobalHilbert} (hv : P v=v) :
    Q v=0 ∨ Q v=v := by
  have hcom : Commute Q P := polarAlgebra_commutative hQm hP.2.2.1
  have hsub : (Q*P)*P=Q*P := by rw [mul_assoc,hP.1.isIdempotentElem.eq]
  rcases hP.2.2.2 (Q*P) (hQ.mul hP.1 hcom) (polarAlgebra.mul_mem hQm hP.2.2.1) hsub with h0|h1
  · left
    have he := DFunLike.congr_fun h0 v
    simpa only [mul_apply_eq_comp,hv,zero_apply] using he
  · right
    have he := DFunLike.congr_fun h1 v
    simpa only [mul_apply_eq_comp,hv] using he

lemma rectangleProjection_coord (r : ℤ) (E : Set Base) (hE : MeasurableSet E) (v : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ j,
      rectangleProjection r E hE v x j = if j=r ∧ x∈E then v x j else 0 := by
  filter_upwards [diagonalOperator_coord
    (projectionSymbol (fun j=>if j=r then E else ∅) (by intro j; split_ifs; exact hE; exact MeasurableSet.empty)) v]
    with x hx j
  rw [show rectangleProjection r E hE v x j = _ from hx j]
  by_cases hj : j=r <;> by_cases he : x∈E <;> simp [hj,he]



theorem polarAlgebra_diffuse : DiffuseAlgebra polarAlgebra := by
  rintro ⟨P,hP⟩
  obtain ⟨z,hz⟩ : ∃ z : GlobalHilbert, P z ≠ 0 := by
    by_contra h
    apply hP.2.1
    apply ContinuousLinearMap.ext
    intro z
    change P z=0
    exact not_not.mp (fun hn => h ⟨z,hn⟩)
  let v := P z
  have hv : v ≠ 0 := hz
  have hPv : P v=v := DFunLike.congr_fun hP.1.isIdempotentElem.eq z
  let Q (r : ℤ) (m t : ℕ) := rectangleProjection r (residueClass m t) (measurableSet_residueClass m t)
  have hQ (r : ℤ) (m t : ℕ) : Q r m t v=0 ∨ Q r m t v=v :=
    minimal_projection_dichotomy hP (diagonalProjection_isStarProjection _ _) (residue_rectangle_mem m t r) hPv
  let B : Set Base := {x | ∀ (r : ℤ) (m t : ℕ) (j : ℤ),
    (Q r m t v=0 → (if j=r ∧ residue m x=t then v x j else 0)=0) ∧
    (Q r m t v=v → (if j=r ∧ residue m x=t then v x j else 0)=v x j)}
  have hB : ∀ᵐ x ∂baseMeasure, x∈B := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro t
    filter_upwards [rectangleProjection_coord r (residueClass m t) (measurableSet_residueClass m t) v,
      Lp.coeFn_zero (E:=Fiber) (p:=2) (μ:=baseMeasure)] with x hx hzero j
    have hx : ∀ j, Q r m t v x j = if j=r ∧ residue m x=t then v x j else 0 := by
      intro j
      by_cases coordinate : j = r <;> by_cases residueValue : residue m x = t <;>
        simpa [Q, residueClass, coordinate, residueValue] using hx j
    constructor
    · intro hh
      have he := hx j
      rw [hh,hzero] at he
      exact he.symm
    · intro hh
      have he := hx j
      rw [hh] at he
      exact he.symm
  obtain ⟨x₀,hx₀,hnz⟩ : ∃ x : Base, x∈B ∧ v x ≠ 0 := by
    by_contra h
    apply hv
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hB] with x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  obtain ⟨r,hr⟩ : ∃ r : ℤ, v x₀ r ≠ 0 := by
    by_contra h
    apply hnz
    apply lp.ext
    funext j
    exact not_not.mp (fun hn => h ⟨j,hn⟩)
  have hfixed (m : ℕ) : Q r m (residue m x₀) v=v := by
    rcases hQ r m (residue m x₀) with h0|h1
    · have hh := (hx₀ r m (residue m x₀) r).1 h0
      simp only [true_and,↓reduceIte] at hh
      exact (hr hh).elim
    · exact h1
  apply hv
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hxne : ∀ᵐ x ∂baseMeasure, x ≠ x₀ := by
    have he : ∀ᵐ x ∂baseMeasure, x ∉ ({x₀}:Set Base) := ae_iff.mpr (by simp)
    simpa using he
  filter_upwards [hB,hxne] with x hx hne
  apply lp.ext
  funext j
  by_contra hnonzero
  have hc (m : ℕ) : j=r ∧ residue m x=residue m x₀ := by
    have hh := (hx r m (residue m x₀) j).2 (hfixed m)
    by_contra hn
    rw [ite_eq_right hn] at hh
    exact hnonzero hh.symm
  exact hne (residue_separates (fun m => (hc m).2))



def PurePointResolution (T : H →L[ℂ] H) : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (P : ι → H →L[ℂ] H) (eigenvalue : ι → ℝ),
    (∀ i, IsStarProjection (P i) ∧ P i ≠ 0 ∧ T * P i = (eigenvalue i:ℂ) • P i) ∧
    (∀ i j, i ≠ j → P i * P j = 0) ∧ ∀ v : H, HasSum (fun i => P i v) v

lemma polarDiagonal_purePoint : PurePointResolution (polarDiagonal 0) := by
  let F : Finset ℤ := {0}
  let I := {t : ↥F → ℤ // jointProjection F t ≠ 0}
  refine ⟨I,inferInstance,fun t=>jointProjection F t,
    fun t=>Real.exp (-((t.val ⟨0,by simp [F]⟩):ℝ)),?_,?_,?_⟩
  · intro t
    refine ⟨jointProjection_isStarProjection _ _,t.property,?_⟩
    exact jointProjection_eigen F t ⟨0,by simp [F]⟩
  · intro s t hst
    exact jointProjection_orthogonal F (fun he => hst (Subtype.ext he))
  · intro v
    apply (hasSum_subtype_iff_of_support_subset ?_).mpr (jointProjection_hasSum F v)
    intro t ht
    change jointProjection F t ≠ 0
    intro he
    apply ht
    change jointProjection F t v = 0
    rw [he]; rfl

lemma polarDiagonal_constantBasis_zero :
    polarDiagonal 0 (constantBasis 0)=(Real.exp (-10):ℂ) • constantBasis 0 := by
  apply Lp.ext
  filter_upwards [polarDiagonal_ae 0 (constantBasis 0),constantBasis_ae 0,
    Lp.coeFn_smul (Real.exp (-10):ℂ) (constantBasis 0)] with x hx hb hs
  rw [hs,Pi.smul_apply]
  ext j
  rw [hx,hb,lp.coeFn_smul,Pi.smul_apply]
  by_cases hj : j=0
  · simp [hj]
  · simp only [lp.single_apply_ne _ _ _ hj, smul_eq_mul, mul_zero]
lemma polarDiagonal_not_commute :
    polarDiagonal 0 * forwardOperator ≠ forwardOperator * polarDiagonal 0 := by
  intro h
  have hC : (Real.exp (-10):ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero (-10)
  have he := DFunLike.congr_fun h (constantBasis 0)
  change polarDiagonal 0 (forwardOperator (constantBasis 0))=
    forwardOperator (polarDiagonal 0 (constantBasis 0)) at he
  rw [forwardOperator_constantBasis_zero,polarDiagonal_constantBasis_zero,map_smul,map_smul,
    forwardOperator_constantBasis_zero] at he
  have he' : polarDiagonal 0 (constantBasis 1)=(Real.exp (-10):ℂ) • constantBasis 1 :=
    (smul_right_injective GlobalHilbert hC) he
  have hb : ∀ᵐ x ∂baseMeasure, explicitBeta x 1=Real.exp (-10) := by
    filter_upwards [polarDiagonal_ae 0 (constantBasis 1),constantBasis_ae 1,
      Lp.coeFn_smul (Real.exp (-10):ℂ) (constantBasis 1)] with x hx h1 hs
    have hf := congrArg (fun v:GlobalHilbert=>v x 1) he'
    rw [hx,hs,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,h1,lp.single_apply_self,smul_eq_mul,mul_one,mul_one] at hf
    have hf' := Complex.ofReal_injective hf
    simpa only [add_zero] using hf'
  obtain ⟨x,hx⟩ := hb.exists
  have hlt : explicitBeta x 1 < Real.exp (-10) := by
    change Real.exp (-halfExponent (plusResidue x) 1)<Real.exp (-10)
    apply Real.exp_lt_exp.mpr
    have hh := halfExponent_lower (plusResidue x) 1
    norm_num at hh
    linarith
  exact (ne_of_lt hlt) hx


end
end BackwardIntertwiners

end OAI
