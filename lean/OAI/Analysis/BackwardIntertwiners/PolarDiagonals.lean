import OAI.Analysis.BackwardIntertwiners.StrongClosure

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


def betaSymbol (n : ℤ) : DiagonalSymbol :=
  ⟨fun x j => (explicitBeta x (j+n):ℂ),
    ⟨fun j => Complex.continuous_ofReal.measurable.comp (measurable_explicitBeta (j+n)),
      Real.exp (-10), (Real.exp_pos _).le, fun x j => by
        simpa only [Complex.norm_real,Real.norm_of_nonneg (explicitBeta_pos _ _).le] using explicitBeta_le x (j+n)⟩⟩
@[simp] lemma betaSymbol_apply (n : ℤ) (x : Base) (j : ℤ) :
    betaSymbol n x j = (explicitBeta x (j+n):ℂ) := rfl
lemma betaSymbol_star (n : ℤ) : star (betaSymbol n) = betaSymbol n := by
  apply Subtype.ext
  funext x j
  simp

def polarDiagonal (n : ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert := diagonalOperator (betaSymbol n)
lemma polarDiagonal_ae (n : ℤ) (f : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ j, polarDiagonal n f x j = (explicitBeta x (j+n):ℂ)*f x j :=
  diagonalOperator_coord _ _
lemma polarDiagonal_selfAdjoint (n : ℤ) : IsSelfAdjoint (polarDiagonal n) := by
  change star (diagonalOperator (betaSymbol n)) = diagonalOperator (betaSymbol n)
  rw [←diagonalOperator_star,betaSymbol_star]
lemma polarDiagonal_commute (m n : ℤ) : polarDiagonal m * polarDiagonal n = polarDiagonal n * polarDiagonal m := by
  change diagonalRepresentation (betaSymbol m) * diagonalRepresentation (betaSymbol n) = diagonalRepresentation (betaSymbol n) * diagonalRepresentation (betaSymbol m)
  rw [←map_mul,mul_comm,map_mul]



def projectionSymbol (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) : DiagonalSymbol :=
  ⟨fun x j => (E j).indicator (fun _ => (1:ℂ)) x,
    ⟨fun j => measurable_const.indicator (hE j), 1, zero_le_one, fun x j => by
      by_cases hx : x ∈ E j <;> simp [hx]⟩⟩
@[simp] lemma projectionSymbol_apply (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j))
    (x : Base) (j : ℤ) : projectionSymbol E hE x j = if x ∈ E j then 1 else 0 := rfl
lemma projectionSymbol_norm_le (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j))
    (x : Base) (j : ℤ) : ‖projectionSymbol E hE x j‖ ≤ 1 := by
  by_cases hx : x ∈ E j <;> simp [hx]
lemma projectionSymbol_star (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) :
    star (projectionSymbol E hE) = projectionSymbol E hE := by
  apply Subtype.ext
  funext x j
  change star (projectionSymbol E hE x j) = projectionSymbol E hE x j
  by_cases hx : x ∈ E j <;> simp [hx]
lemma projectionSymbol_idempotent (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) :
    projectionSymbol E hE * projectionSymbol E hE = projectionSymbol E hE := by
  apply Subtype.ext
  funext x j
  change projectionSymbol E hE x j * projectionSymbol E hE x j = projectionSymbol E hE x j
  by_cases hx : x ∈ E j <;> simp [hx]

def diagonalProjection (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalOperator (projectionSymbol E hE)
lemma diagonalProjection_ae (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) (f : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ j, diagonalProjection E hE f x j = if x ∈ E j then f x j else 0 := by
  filter_upwards [diagonalOperator_coord (projectionSymbol E hE) f] with x hx j
  change diagonalOperator (projectionSymbol E hE) f x j = _
  rw [hx,projectionSymbol_apply]
  split_ifs <;> simp
lemma diagonalProjection_isStarProjection (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) :
    IsStarProjection (diagonalProjection E hE) := by
  constructor
  · change diagonalOperator (projectionSymbol E hE) * diagonalOperator (projectionSymbol E hE) = _
    rw [←diagonalOperator_mul,projectionSymbol_idempotent]
    rfl
  · change star (diagonalOperator (projectionSymbol E hE)) = diagonalOperator (projectionSymbol E hE)
    rw [←diagonalOperator_star,projectionSymbol_star]
lemma diagonalProjection_mul (E F : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j))
    (hF : ∀ j, MeasurableSet (F j)) :
    diagonalProjection E hE * diagonalProjection F hF =
      diagonalProjection (fun j => E j ∩ F j) (fun j => (hE j).inter (hF j)) := by
  change diagonalOperator _ * diagonalOperator _ = diagonalOperator _
  rw [←diagonalOperator_mul]
  congr 1
  apply Subtype.ext
  funext x j
  change projectionSymbol E hE x j * projectionSymbol F hF x j = projectionSymbol _ _ x j
  by_cases hx : x ∈ E j <;> by_cases hy : x ∈ F j <;> simp [hx,hy]
lemma diagonalProjection_compl (E : ℤ → Set Base) (hE : ∀ j, MeasurableSet (E j)) :
    diagonalProjection (fun j => (E j)ᶜ) (fun j => (hE j).compl) = 1-diagonalProjection E hE := by
  change diagonalRepresentation _ = 1-diagonalRepresentation _
  rw [←map_one diagonalRepresentation,←map_sub]
  congr 1
  apply Subtype.ext
  funext x j
  change projectionSymbol _ _ x j = 1-projectionSymbol E hE x j
  by_cases hx : x ∈ E j <;> simp [hx]
lemma diagonalProjection_empty : diagonalProjection (fun _ => ∅) (fun _ => MeasurableSet.empty) = 0 := by
  have h : projectionSymbol (fun _ => ∅) (fun _ => MeasurableSet.empty) = 0 := by
    apply Subtype.ext; funext x j; simp
  exact congrArg diagonalOperator h |>.trans diagonalOperator_zero
lemma diagonalProjection_univ : diagonalProjection (fun _ => Set.univ) (fun _ => MeasurableSet.univ) = 1 := by
  have h : projectionSymbol (fun _ => Set.univ) (fun _ => MeasurableSet.univ) = 1 := by
    apply Subtype.ext; funext x j; simp
  exact congrArg diagonalOperator h |>.trans diagonalOperator_one
lemma diagonalProjection_ext {E F : ℤ → Set Base} {hE : ∀ j, MeasurableSet (E j)}
    {hF : ∀ j, MeasurableSet (F j)} (h : ∀ j, E j =ᵐ[baseMeasure] F j) :
    diagonalProjection E hE = diagonalProjection F hF := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalProjection_ae E hE f,diagonalProjection_ae F hF f,
    ae_all_iff.mpr h] with x hx hy he
  ext j
  rw [hx,hy]
  have hh : (x ∈ E j) = (x ∈ F j) := he j
  simp only [hh]
lemma diagonalProjection_nonzero {E : ℤ → Set Base} {hE : ∀ j, MeasurableSet (E j)}
    (j : ℤ) (hj : baseMeasure (E j) ≠ 0) : diagonalProjection E hE ≠ 0 := by
  intro he
  apply hj
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [diagonalProjection_ae E hE (constantBasis j),constantBasis_ae j,
    Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hb hz
  intro hxE
  have h := hx j
  rw [he] at h
  change (0 : GlobalHilbert) x j = _ at h
  rw [hz,hb] at h
  simp [hxE] at h


lemma explicitBeta_le_one (x : Base) (j : ℤ) : explicitBeta x j ≤ 1 :=
  (explicitBeta_le x j).trans (Real.exp_le_one_iff.mpr (by norm_num))

def levelProjection (n : ℤ) (t : ℝ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (fun j => {x | explicitBeta x (j+n) = t})
    (fun j => measurableSet_eq_fun (measurable_explicitBeta (j+n)) measurable_const)

lemma peak_nonneg {b t : ℝ} (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ 1-(b-t)^2 := by
  have h₁ : 0 ≤ (1-(b-t))*(1+(b-t)) := mul_nonneg (by linarith) (by linarith)
  nlinarith
lemma peak_le_one (b t : ℝ) : 1-(b-t)^2 ≤ 1 := by nlinarith [sq_nonneg (b-t)]
lemma peak_lt_one {b t : ℝ} (h : b ≠ t) : 1-(b-t)^2 < 1 := by
  have h' : 0 < (b-t)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
  linarith

def peakSymbol (n : ℤ) (t : ℝ) : DiagonalSymbol := 1-(betaSymbol n - (t:ℂ) • 1)^2
@[simp] lemma peakSymbol_apply (n : ℤ) (t : ℝ) (x : Base) (j : ℤ) :
    peakSymbol n t x j = ((1-(explicitBeta x (j+n)-t)^2:ℝ):ℂ) := by
  simp [peakSymbol,Complex.ofReal_sub,Complex.ofReal_pow]
lemma peakSymbol_bound (n : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (x : Base) (j : ℤ) :
    ‖peakSymbol n t x j‖ ≤ 1 := by
  rw [peakSymbol_apply,Complex.norm_real,Real.norm_of_nonneg
    (peak_nonneg (explicitBeta_pos _ _).le (explicitBeta_le_one _ _) ht₀ ht₁)]
  exact peak_le_one _ _
lemma peakSymbol_powers_tendsto (n : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (x : Base) (j : ℤ) :
    Tendsto (fun k : ℕ => (peakSymbol n t ^k) x j) atTop
      (𝓝 (if explicitBeta x (j+n)=t then (1:ℂ) else 0)) := by
  simp only [DiagonalSymbol.pow_apply,peakSymbol_apply]
  by_cases he : explicitBeta x (j+n)=t
  · simp [he]
  · simp only [he,↓reduceIte]
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [Complex.norm_real,Real.norm_of_nonneg
      (peak_nonneg (explicitBeta_pos _ _).le (explicitBeta_le_one _ _) ht₀ ht₁)]
    exact peak_lt_one he
lemma levelProjection_mem {A : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert)}
    (hA : StronglyClosed A) (n : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hn : polarDiagonal n ∈ A) : levelProjection n t ∈ A := by
  have hq : diagonalOperator (peakSymbol n t) ∈ A := by
    change diagonalRepresentation (1-(betaSymbol n - (t:ℂ) • 1)^2) ∈ A
    rw [map_sub,map_one,map_pow,map_sub,map_smul,map_one]
    exact A.sub_mem A.one_mem (A.pow_mem (A.sub_mem hn (A.smul_mem A.one_mem _)) _)
  apply hA.mem_of_tendsto (l:=atTop) (T:=fun k : ℕ => diagonalOperator (peakSymbol n t ^k))
  · exact Eventually.of_forall fun k => by
      change diagonalRepresentation (peakSymbol n t ^k) ∈ A
      rw [map_pow]
      exact A.pow_mem hq _
  · intro f
    apply diagonalOperator_tendsto (C:=1) _ _ zero_le_one
    · intro k x j
      rw [DiagonalSymbol.pow_apply,norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (peakSymbol_bound n ht₀ ht₁ x j)
    · exact projectionSymbol_norm_le _ _
    · exact Eventually.of_forall fun x j => by
        simpa using peakSymbol_powers_tendsto n ht₀ ht₁ x j



def baseProjection (E : Set Base) (hE : MeasurableSet E) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (fun _ => E) (fun _ => hE)
lemma baseProjection_ae (E : Set Base) (hE : MeasurableSet E) (f : GlobalHilbert) :
    baseProjection E hE f =ᵐ[baseMeasure] E.indicator f := by
  filter_upwards [diagonalProjection_ae (fun _ => E) (fun _ => hE) f] with x hx
  ext j
  by_cases he : x ∈ E <;> simpa [baseProjection,he] using hx j
lemma baseProjection_mem_full (E : Set Base) (hE : MeasurableSet E) :
    baseProjection E hE ∈ fullMultiplierAlgebra := ⟨projectionSymbol _ _,rfl⟩
lemma diagonal_commute (a b : DiagonalSymbol) :
    diagonalOperator a * diagonalOperator b = diagonalOperator b * diagonalOperator a := by
  rw [←diagonalOperator_mul,←diagonalOperator_mul,mul_comm]
lemma fullMultiplier_commute {A B : GlobalHilbert →L[ℂ] GlobalHilbert}
    (hA : A ∈ fullMultiplierAlgebra) (hB : B ∈ fullMultiplierAlgebra) : A*B=B*A := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact diagonal_commute a b
lemma baseProjection_constant (E : Set Base) (hE : MeasurableSet E) (v : Fiber) :
    baseProjection E hE (Lp.const 2 baseMeasure v) =
      indicatorConstLp 2 hE (measure_ne_top baseMeasure E) v := by
  apply Lp.ext
  filter_upwards [baseProjection_ae E hE (Lp.const 2 baseMeasure v),Lp.coeFn_const 2 baseMeasure v,
    (indicatorConstLp_coeFn (p:=2) (hs:=hE) (hμs:=measure_ne_top baseMeasure E) (c:=v))] with x hx hv hi
  rw [hx,hi]
  by_cases he : x ∈ E <;> simp [he]
lemma L2_norm_sq (f : GlobalHilbert) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂baseMeasure := by
  rw [L2_norm_eq_sqrt,Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
lemma baseProjection_norm_sq (E : Set Base) (hE : MeasurableSet E) (f : GlobalHilbert) :
    ‖baseProjection E hE f‖^2 = ∫ x in E, ‖f x‖^2 ∂baseMeasure := by
  rw [L2_norm_sq,←integral_indicator hE]
  apply integral_congr_ae
  filter_upwards [baseProjection_ae E hE f] with x hx
  rw [hx]
  by_cases he : x ∈ E <;> simp [he]
lemma local_operator_energy_bound (T : GlobalHilbert →L[ℂ] GlobalHilbert)
    (hT : ∀ E (hE : MeasurableSet E), baseProjection E hE * T = T * baseProjection E hE)
    (f : GlobalHilbert) : ∀ᵐ x ∂baseMeasure, ‖T f x‖^2 ≤ ‖T‖^2 * ‖f x‖^2 := by
  have hI (g : GlobalHilbert) : Integrable (fun x : Base => ‖g x‖^2) baseMeasure :=
    (Lp.memLp g).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  apply ae_le_of_forall_setIntegral_le (μ:=baseMeasure) (hI (T f)) ((hI f).const_mul (‖T‖^2))
  intro E hE _
  rw [←baseProjection_norm_sq E hE,integral_const_mul,←baseProjection_norm_sq E hE]
  have he : baseProjection E hE (T f) = T (baseProjection E hE f) := DFunLike.congr_fun (hT E hE) f
  rw [he]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (baseProjection E hE f)) 2

lemma sliceProjection_diagonal (j : ℤ) : sliceProjection j =
    diagonalProjection (fun k => if k=j then Set.univ else ∅)
      (fun k => by split_ifs <;> measurability) := by
  ext1 f
  apply Lp.ext
  filter_upwards [sliceProjection_ae j f,diagonalProjection_ae (fun k => if k=j then Set.univ else ∅)
      (fun k => by split_ifs <;> measurability) f] with x hx hy
  ext k
  rw [hx,hy]
  by_cases he : k=j <;> simp [he,lp.single_apply]
lemma sliceProjection_mem_full (j : ℤ) : sliceProjection j ∈ fullMultiplierAlgebra := by
  rw [sliceProjection_diagonal]
  exact ⟨projectionSymbol _ _,rfl⟩


def columnSymbol (T : GlobalHilbert →L[ℂ] GlobalHilbert) : DiagonalSymbol :=
  ⟨fun x j => if ‖T (constantBasis j) x j‖ ≤ ‖T‖ then T (constantBasis j) x j else 0,
    ⟨fun j => by
      have hm : Measurable (fun x => T (constantBasis j) x j) :=
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).continuous.comp_stronglyMeasurable
          (Lp.stronglyMeasurable (T (constantBasis j)))).measurable
      exact hm.ite (measurableSet_le hm.norm measurable_const) measurable_const,
      ‖T‖,norm_nonneg T,fun x j => by dsimp only; split_ifs with h <;> simp_all⟩⟩
lemma columnSymbol_ae (T : GlobalHilbert →L[ℂ] GlobalHilbert)
    (hT : ∀ E (hE : MeasurableSet E), baseProjection E hE * T = T * baseProjection E hE)
    (j : ℤ) : ∀ᵐ x ∂baseMeasure, columnSymbol T x j = T (constantBasis j) x j := by
  filter_upwards [local_operator_energy_bound T hT (constantBasis j),constantBasis_ae j] with x hx hj
  have hh : ‖T (constantBasis j) x‖ ≤ ‖T‖ := by
    have h₁ : ‖constantBasis j x‖=1 := by rw [hj]; simp
    rw [h₁] at hx
    nlinarith [norm_nonneg (T (constantBasis j) x),norm_nonneg T]
  have hc : ‖T (constantBasis j) x j‖ ≤ ‖T‖ := (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) _ j).trans hh
  exact ite_eq_left hc

lemma columnSymbol_basis (T : GlobalHilbert →L[ℂ] GlobalHilbert)
    (hT : ∀ E (hE : MeasurableSet E), baseProjection E hE * T = T * baseProjection E hE)
    (hS : ∀ j, sliceProjection j * T = T * sliceProjection j) (j : ℤ) :
    diagonalOperator (columnSymbol T) (constantBasis j) = T (constantBasis j) := by
  have he : sliceProjection j (T (constantBasis j)) = T (constantBasis j) := by
    rw [show sliceProjection j (T (constantBasis j)) = T (sliceProjection j (constantBasis j)) from DFunLike.congr_fun (hS j) _]
    simp [sliceProjection_constantBasis]
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (columnSymbol T) (constantBasis j),constantBasis_ae j,
    columnSymbol_ae T hT j,sliceProjection_ae j (T (constantBasis j))] with x hx hj hc hs
  rw [he] at hs
  ext k
  rw [hx,hj,hs]
  by_cases hk : k=j
  · subst k; simp [hc]
  · simp [lp.single_apply,hk]

lemma operators_equal_of_constantBasis {T D : GlobalHilbert →L[ℂ] GlobalHilbert}
    (hc : ∀ j, T (constantBasis j)=D (constantBasis j))
    (hT : ∀ E (hE : MeasurableSet E), baseProjection E hE*T=T*baseProjection E hE)
    (hD : ∀ E (hE : MeasurableSet E), baseProjection E hE*D=D*baseProjection E hE) : T=D := by
  have hconst (v : Fiber) : T (Lp.const 2 baseMeasure v)=D (Lp.const 2 baseMeasure v) := by
    let L := (Lp.constL 2 baseMeasure ℂ : Fiber →L[ℂ] GlobalHilbert)
    have h₁ := (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ∞) v).map (T.comp L).toAddMonoidHom (T.comp L).continuous
    have h₂ := (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ∞) v).map (D.comp L).toAddMonoidHom (D.comp L).continuous
    have hh (j : ℤ) : (T.comp L) (lp.single 2 j (v j)) = (D.comp L) (lp.single 2 j (v j)) := by
      have he : (lp.single 2 j (v j) : Fiber) = (v j) • lp.single 2 j (1:ℂ) := by
        rw [←lp.single_smul]; simp
      rw [he,map_smul,map_smul]
      exact congrArg (fun w : GlobalHilbert => v j • w) (hc j)
    exact h₁.unique (h₂.congr_fun hh)
  ext1 f
  apply Lp.induction (by norm_num : (2:ENNReal) ≠ ∞) (fun f : GlobalHilbert => T f=D f) (f:=f)
  · intro v E hE hfin
    rw [Lp.simpleFunc.coe_indicatorConst,←baseProjection_constant E hE v]
    have heT := DFunLike.congr_fun (hT E hE) (Lp.const 2 baseMeasure v)
    have heD := DFunLike.congr_fun (hD E hE) (Lp.const 2 baseMeasure v)
    change baseProjection E hE (T _) = T (baseProjection E hE _) at heT
    change baseProjection E hE (D _) = D (baseProjection E hE _) at heD
    rw [←heT,←heD,hconst]
  · intro f g hf hg _ h₁ h₂
    simp only [map_add,h₁,h₂]
  · exact isClosed_eq T.continuous D.continuous

lemma fullMultiplier_centralizer_eq : StarSubalgebra.centralizer ℂ (fullMultiplierAlgebra : Set _) =
    fullMultiplierAlgebra := by
  apply le_antisymm
  · intro T hT
    have hcomm {P : GlobalHilbert →L[ℂ] GlobalHilbert} (hP : P ∈ fullMultiplierAlgebra) : P*T=T*P :=
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT P hP).1
    have hbase : ∀ E (hE : MeasurableSet E), baseProjection E hE*T=T*baseProjection E hE :=
      fun E hE => hcomm (baseProjection_mem_full E hE)
    refine ⟨columnSymbol T, ?_⟩
    apply operators_equal_of_constantBasis (columnSymbol_basis T hbase (fun j => hcomm (sliceProjection_mem_full j)))
    · intro E hE
      exact diagonal_commute _ _
    · exact hbase
  · intro T hT
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro P hP
    exact ⟨fullMultiplier_commute hP hT,fullMultiplier_commute (fullMultiplierAlgebra.star_mem' hP) hT⟩
lemma fullMultiplier_stronglyClosed : StronglyClosed fullMultiplierAlgebra := by
  rw [←fullMultiplier_centralizer_eq]
  exact strong_centralizer_closed _

lemma levelProjection_mem_all {A : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert)}
    (hA : StronglyClosed A) (n : ℤ) (t : ℝ) (hn : polarDiagonal n ∈ A) : levelProjection n t ∈ A := by
  by_cases ht : 0 ≤ t ∧ t ≤ 1
  · exact levelProjection_mem hA n ht.1 ht.2 hn
  have he : levelProjection n t = 0 := by
    unfold levelProjection
    rw [←diagonalProjection_empty]
    apply diagonalProjection_ext
    intro j
    apply EventuallyEq.of_eq
    ext x
    change (explicitBeta x (j+n)=t) ↔ False
    constructor
    · intro hx
      apply ht
      rw [←hx]
      exact ⟨(explicitBeta_pos _ _).le,explicitBeta_le_one _ _⟩
    · exact False.elim
  rw [he]
  exact A.zero_mem




end
end BackwardIntertwiners

end OAI
