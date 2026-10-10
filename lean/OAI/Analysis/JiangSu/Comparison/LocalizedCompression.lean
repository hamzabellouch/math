import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.CornerDivision

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma cornerCFC_mem {u : D} (hu : IsStarProjection u) (x : D) (f : ℝ → ℝ) :
    u*cornerCFC hu x f = cornerCFC hu x f ∧ cornerCFC hu x f*u = cornerCFC hu x f :=
  (cfc f (ProjectionCorner.compress hu x) : ProjectionCorner hu).property

lemma cornerCFC_nonneg {u : D} (hu : IsStarProjection u) {x : D}
    (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1) {f : ℝ → ℝ} (hfc : Continuous f)
    (hf : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ f t) : 0 ≤ cornerCFC hu x f := by
  let a := ProjectionCorner.compress hu x
  let g : ℝ → ℝ := fun t => Real.sqrt (f t)
  let b : ProjectionCorner hu := cfc g a
  have hg : Continuous g := Real.continuous_sqrt.comp hfc
  have hb : IsSelfAdjoint b := cfc_predicate g a
  have he : b*b = cfc f a := by
    dsimp [b]
    rw [←cfc_mul g g a hg.continuousOn hg.continuousOn]
    apply cfc_congr
    intro t ht
    exact Real.mul_self_sqrt (hf t (spectrum_subset_unit_interval
      (compress_selfAdjoint hu hx) ((compress_norm_le hu x).trans hxn) ht))
  have he' : cornerCFC hu x f = star (b:D)*(b:D) := by
    rw [(ProjectionCorner.isSelfAdjoint_coe hu hb).star_eq]
    exact congrArg Subtype.val he.symm
  rw [he']
  exact star_mul_self_nonneg _

omit [PartialOrder D] [StarOrderedRing D] in
lemma cornerCFC_norm_le_one {u : D} (hu : IsStarProjection u) {x : D}
    (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ∈ Set.Icc 0 1) :
    ‖cornerCFC hu x f‖ ≤ 1 := by
  change ‖(cfc f (ProjectionCorner.compress hu x) : ProjectionCorner hu)‖ ≤ 1
  apply norm_cfc_le zero_le_one
  intro t ht
  have h := hf t (spectrum_subset_unit_interval (compress_selfAdjoint hu hx)
    ((compress_norm_le hu x).trans hxn) ht)
  simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2

omit [PartialOrder D] [StarOrderedRing D] in
lemma localized_cutoff_mem {u : D} (hu : IsStarProjection u) (x : D)
    (f : ℝ → ℝ) (α : ℝ) :
    u*directCutoff α (cornerCFC hu x f)=directCutoff α (cornerCFC hu x f) ∧
    directCutoff α (cornerCFC hu x f)*u=directCutoff α (cornerCFC hu x f) := by
  let a := ProjectionCorner.compress hu x
  let y : ProjectionCorner hu := cfc f a
  have hy : IsSelfAdjoint y := cfc_predicate f a
  have he := ProjectionCorner.coe_cfc hu hy (fun t : ℝ => min (t/α) 1)
    (by fun_prop) (by simp)
  change ((cfc _ y : ProjectionCorner hu) : D) = directCutoff α (cornerCFC hu x f) at he
  rw [←he]
  exact (cfc _ y : ProjectionCorner hu).property

omit [PartialOrder D] [StarOrderedRing D] in
lemma localized_cutoff_compression {u p : D} (hu : IsStarProjection u)
    (hp : IsStarProjection p) {x : D} (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf01 : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ∈ Set.Icc 0 1)
    {α ε μ : ℝ} (hα : 0 < α) (hε : 0 ≤ ε)
    (hsupp : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ≠ 0 → |t-μ| ≤ ε)
    (hkp : directCutoff α (cornerCFC hu x f)*p=p)
    (hpk : p*directCutoff α (cornerCFC hu x f)=p) :
    u*p=p ∧ p*u=p ∧ ‖p*x*p-μ • p‖ ≤ ε := by
  let a := ProjectionCorner.compress hu x
  let y : ProjectionCorner hu := cfc f a
  let g : ℝ → ℝ := fun t => min (f t/α) 1
  let k : ProjectionCorner hu := cfc g a
  have ha : IsSelfAdjoint a := compress_selfAdjoint hu hx
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hy : IsSelfAdjoint y := cfc_predicate f a
  have hk : (k : D) = directCutoff α (cornerCFC hu x f) := by
    have he := ProjectionCorner.coe_cfc hu hy (fun t : ℝ => min (t/α) 1)
      (by fun_prop) (by simp)
    dsimp [k,g]
    dsimp [y] at he
    rw [←cfc_comp (fun t : ℝ => min (t/α) 1) f a ha (by fun_prop) hf.continuousOn] at he
    exact he
  have hup : u*p=p := by rw [←hkp,←hk,←mul_assoc,k.property.1,hk,hkp]
  have hpu : p*u=p := by rw [←hpk,←hk,mul_assoc,k.property.2,hk,hpk]
  refine ⟨hup,hpu,?_⟩
  let z : ProjectionCorner hu := k*(a-μ • 1)*k
  have hz : z = cfc (fun t : ℝ => g t*(t-μ)*g t) a := by
    dsimp [z,k]
    rw [cfc_mul _ _ a (by fun_prop) hg.continuousOn,
      cfc_mul _ _ a hg.continuousOn (by fun_prop),
      cfc_sub (fun t : ℝ => t) (fun _ : ℝ => μ) a continuous_id.continuousOn continuous_const.continuousOn,
      cfc_id' ℝ a ha,cfc_const μ a ha,Algebra.algebraMap_eq_smul_one]
  have hzn : ‖z‖ ≤ ε := by
    rw [hz]
    apply norm_cfc_le hε
    intro t ht
    have ht' := spectrum_subset_unit_interval ha ((compress_norm_le hu x).trans hxn) ht
    have hg0 : 0 ≤ g t := le_min (div_nonneg (hf01 t ht').1 hα.le) zero_le_one
    have hg1 : g t ≤ 1 := min_le_right _ _
    by_cases hft : f t=0
    · simp [g,hft,hε]
    · rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg hg0]
      exact (mul_le_mul (mul_le_mul hg1 (hsupp t ht' hft) (abs_nonneg _) zero_le_one)
        hg1 hg0 (by positivity)).trans_eq (by ring)
  have he : p*x*p-μ • p = p*(z:D)*p := by
    change p*x*p-μ • p = p*((k:D)*(u*x*u-μ • u)*(k:D))*p
    symm
    calc
      _ = (p*(k:D))*(u*x*u-μ • u)*((k:D)*p) := by simp only [mul_assoc]
      _ = p*(u*x*u-μ • u)*p := by rw [hk,hpk,hkp]
      _ = _ := by
        simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,
          ←mul_assoc,hpu,hp.isIdempotentElem.eq]
        rw [mul_assoc (p*x) u p,hup]

  rw [he]
  exact (compress_norm_le hp (z:D)).trans hzn

lemma positiveCut_trace_lower (τ : TracialState D) {y : D} (hy : 0 ≤ y)
    {α : ℝ} (hα : 0 ≤ α) :
    (τ.functional y).re-α ≤ (τ.functional (directPositiveCut α y)).re := by
  have hn : ‖y-directPositiveCut α y‖ ≤ α := by
    rw [directPositiveCut]
    nth_rw 1 [←cfc_id' ℝ y hy.isSelfAdjoint]
    rw [←cfc_sub (fun t : ℝ => t) (fun t : ℝ => max (t-α) 0) y
      continuous_id.continuousOn (by fun_prop)]
    apply norm_cfc_le hα
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg hy ht
    change |t-max (t-α) 0| ≤ α
    rw [abs_of_nonneg (sub_nonneg.mpr (max_le (sub_le_self _ hα) ht0))]
    exact sub_le_comm.mpr (le_max_left (t-α) 0)
  have ht := (Complex.re_le_norm (τ.functional (y-directPositiveCut α y))).trans
    ((trace_norm_le_norm _ _).trans hn)
  rw [map_sub,Complex.sub_re] at ht
  exact sub_le_comm.mp ht

end DirectComparison

namespace DirectComparison
open Pureness CurrentMain
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

structure ProjectionPacking (q : D) where
  Index : Type
  [indexFintype : Fintype Index]
  piece : Index → D
  projection : ∀ i, IsStarProjection (piece i)
  orthogonal : Pairwise (fun i j => piece i*piece j=0)
  sum_le : (∑ i, piece i) ≤ q

attribute [instance] ProjectionPacking.indexFintype
namespace ProjectionPacking
variable {q : D} (P : ProjectionPacking q)

def total : D := ∑ i, P.piece i
def residual : D := q-P.total
omit [StarOrderedRing D] in
lemma total_projection : IsStarProjection P.total :=
  orthogonal_projection_sum Finset.univ P.piece (fun i _ => P.projection i)
    (fun _ _ _ _ hij => P.orthogonal hij)
omit [StarOrderedRing D] in
lemma total_le : P.total ≤ q := P.sum_le
lemma piece_le_total (i : P.Index) : P.piece i ≤ P.total :=
  Finset.single_le_sum (fun j _ => (P.projection j).nonneg) (Finset.mem_univ i)
lemma piece_le (i : P.Index) : P.piece i ≤ q := (P.piece_le_total i).trans P.sum_le
lemma residual_projection (hq : IsStarProjection q) : IsStarProjection P.residual :=
  P.total_projection.sub_of_mul_eq_left hq ((P.total_projection.le_iff_mul_eq_left hq).mp P.total_le)
lemma residual_le : P.residual ≤ q := sub_le_self _ P.total_projection.nonneg
omit [StarOrderedRing D] in
lemma total_add_residual : P.total+P.residual=q := by dsimp [residual]; abel
lemma piece_mul_residual (hq : IsStarProjection q) (i : P.Index) :
    P.piece i*P.residual=0 := by
  rw [residual,mul_sub,(P.projection i).le_iff_mul_eq_left hq |>.mp (P.piece_le i),
    (P.projection i).le_iff_mul_eq_left P.total_projection |>.mp (P.piece_le_total i),sub_self]
lemma residual_mul_piece (hq : IsStarProjection q) (i : P.Index) :
    P.residual*P.piece i=0 := by
  have h := congrArg star (P.piece_mul_residual hq i)
  simpa only [star_mul,(P.residual_projection hq).isSelfAdjoint.star_eq,
    (P.projection i).isSelfAdjoint.star_eq,star_zero] using h

def empty (hq : IsStarProjection q) : ProjectionPacking q where
  Index := Empty
  piece := Empty.elim
  projection := by intro i;cases i
  orthogonal := by intro i;cases i
  sum_le := by simpa using hq.nonneg

@[simp] lemma empty_total (hq : IsStarProjection q) : (empty hq).total=0 := by
  change (∑ i : Empty, (Empty.elim i : D)) = 0
  simp
@[simp] lemma empty_residual (hq : IsStarProjection q) : (empty hq).residual=q := by
  simp [residual]

def singleton {p : D} (hp : IsStarProjection p) (hpq : p ≤ q) : ProjectionPacking q where
  Index := Unit
  piece := fun _ => p
  projection := fun _ => hp
  orthogonal := by intro i j hij; exact (hij (Subsingleton.elim i j)).elim
  sum_le := by simpa using hpq
omit [StarOrderedRing D] in
@[simp] lemma singleton_total {p : D} (hp : IsStarProjection p) (hpq : p ≤ q) :
    (singleton hp hpq).total=p := by
  change (∑ _ : Unit, p) = p
  simp

def append (hq : IsStarProjection q) (Q : ProjectionPacking P.residual) : ProjectionPacking q where
  Index := Sum P.Index Q.Index
  piece := Sum.elim P.piece Q.piece
  projection := by intro i;cases i with
    | inl i => exact P.projection i
    | inr i => exact Q.projection i
  orthogonal := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact P.orthogonal (fun h => hij (congrArg Sum.inl h))
      | inr j =>
        have hQ := ((Q.projection j).le_iff_mul_eq_right (P.residual_projection hq)).mp (Q.piece_le j)
        change P.piece i*Q.piece j=0
        rw [←hQ,←mul_assoc,P.piece_mul_residual hq,zero_mul]
    | inr i =>
      cases j with
      | inl j =>
        have hQ := ((Q.projection i).le_iff_mul_eq_left (P.residual_projection hq)).mp (Q.piece_le i)
        change Q.piece i*P.piece j=0
        rw [←hQ,mul_assoc,P.residual_mul_piece hq,mul_zero]
      | inr j => exact Q.orthogonal (fun h => hij (congrArg Sum.inr h))
  sum_le := by
    rw [Fintype.sum_sum_type]
    change P.total+Q.total ≤ q
    exact (add_le_add le_rfl Q.total_le).trans_eq P.total_add_residual

@[simp] lemma append_total (hq : IsStarProjection q) (Q : ProjectionPacking P.residual) :
    (P.append hq Q).total=P.total+Q.total := by
  exact Fintype.sum_sum_type _
lemma append_residual (hq : IsStarProjection q) (Q : ProjectionPacking P.residual) :
    (P.append hq Q).residual=Q.residual := by
  change q-(P.append hq Q).total = (q-P.total)-Q.total
  rw [append_total]; abel
lemma residual_append_le (hq : IsStarProjection q) (Q : ProjectionPacking P.residual) :
    (P.append hq Q).residual ≤ P.residual := by
  rw [append_residual]; exact Q.residual_le
lemma total_le_append (hq : IsStarProjection q) (Q : ProjectionPacking P.residual) :
    P.total ≤ (P.append hq Q).total := by
  rw [append_total]; exact le_add_of_nonneg_right Q.total_projection.nonneg

def refine (Q : ∀ i : P.Index, ProjectionPacking (P.piece i)) : ProjectionPacking q where
  Index := Σ i : P.Index, (Q i).Index
  piece := fun i => (Q i.1).piece i.2
  projection := fun i => (Q i.1).projection i.2
  orthogonal := by
    rintro ⟨i,s⟩ ⟨j,t⟩ hst
    by_cases hij : i=j
    · subst j
      exact (Q i).orthogonal (fun he => hst (congrArg (Sigma.mk i) he))
    · exact mul_eq_zero_of_supports
        (((Q i).projection s).le_iff_mul_eq_left (P.projection i) |>.mp ((Q i).piece_le s))
        (((Q j).projection t).le_iff_mul_eq_right (P.projection j) |>.mp ((Q j).piece_le t))
        (P.orthogonal hij)
  sum_le := by
    rw [Fintype.sum_sigma]
    exact (Finset.sum_le_sum (fun i _ => (Q i).sum_le)).trans P.sum_le
lemma refine_total (Q : ∀ i : P.Index, ProjectionPacking (P.piece i)) :
    (P.refine Q).total = ∑ i, (Q i).total := Fintype.sum_sigma _
lemma refine_residual (Q : ∀ i : P.Index, ProjectionPacking (P.piece i)) :
    (P.refine Q).residual = P.residual+∑ i, (Q i).residual := by
  rw [residual,refine_total,residual]
  simp only [residual,Finset.sum_sub_distrib]
  change q-∑ i, (Q i).total = (q-∑ i,P.piece i)+((∑ i,P.piece i)-(∑ i,(Q i).total))
  abel

end ProjectionPacking
end DirectComparison
end

end OAI
