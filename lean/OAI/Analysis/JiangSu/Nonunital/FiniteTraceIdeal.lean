import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.MatrixComparison

namespace OAI

noncomputable section
namespace NonunitalGamma

section
open TraceCone Filter Topology
open scoped ENNReal NNReal ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma star_square_add_le (x y : A) :
    star (x+y)*(x+y) ≤ (2:ℝ) • (star x*x+star y*y) := by
  have h : 0 ≤ star (x-y)*(x-y) := star_mul_self_nonneg _
  have he : star (x-y)*(x-y)=(2:ℝ) • (star x*x+star y*y)-star (x+y)*(x+y) := by
    simp only [star_sub,star_add,two_smul]
    noncomm_ring
  rw [he] at h
  exact sub_nonneg.mp h

lemma finite_star_square_add (τ : ExtendedTrace A) {x y : A}
    (hx : τ (Positive.starMul x) < ∞) (hy : τ (Positive.starMul y) < ∞) :
    τ (Positive.starMul (x+y)) < ∞ := by
  have h := τ.monotone (show Positive.starMul (x+y) ≤
    Positive.smul 2 (Positive.add (Positive.starMul x) (Positive.starMul y)) from
    star_square_add_le x y)
  apply lt_of_le_of_lt h
  change τ (Positive.smul 2 (Positive.add (Positive.starMul x) (Positive.starMul y))) < ∞
  rw [τ.map_smul,τ.map_add]
  exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hx,hy⟩)

lemma finite_star_square_mul_left (τ : ExtendedTrace A) (x : A) {y : A}
    (hy : τ (Positive.starMul y) < ∞) : τ (Positive.starMul (x*y)) < ∞ := by
  have h : Positive.starMul (x*y) ≤ Positive.smul ‖star x*x‖₊ (Positive.starMul y) := by
    change star (x*y)*(x*y) ≤ ‖star x*x‖ • (star y*y)
    simpa only [star_mul,mul_assoc] using
      CStarAlgebra.star_left_conjugate_le_norm_smul (a := y) (b := star x*x)
  apply lt_of_le_of_lt (τ.monotone h)
  change τ (Positive.smul ‖star x*x‖₊ (Positive.starMul y)) < ∞
  rw [τ.map_smul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hy

lemma finite_star_square_mul_right (τ : ExtendedTrace A) {x : A} (y : A)
    (hx : τ (Positive.starMul x) < ∞) : τ (Positive.starMul (x*y)) < ∞ := by
  have hx' : τ (Positive.starMul (star x)) < ∞ := by
    simpa only [Positive.starMul,star_star] using (τ.tracial x ▸ hx)
  have h := finite_star_square_mul_left τ (star y) hx'
  have he : Positive.starMul (star y*star x) = Positive.mulStar (x*y) := by
    apply Subtype.ext
    simp only [Positive.starMul,Positive.mulStar,star_mul,star_star,mul_assoc]
  rw [he,←τ.tracial] at h
  exact h

def finiteTraceIdeal (τ : ExtendedTrace A) : TwoSidedIdeal A := .mk'
  {x | τ (Positive.starMul x) < ∞}
  (by
    change τ (Positive.starMul 0) < ∞
    simpa only [Positive.starMul,Positive.zero,star_zero,zero_mul] using
      (show τ Positive.zero < ∞ by rw [τ.map_zero];exact ENNReal.zero_lt_top))
  (fun hx hy => finite_star_square_add τ hx hy)
  (by intro x hx;simpa only [Set.mem_ofPred_eq,Positive.starMul,star_neg,neg_mul_neg] using hx)
  (fun {x y} hy => finite_star_square_mul_left τ x hy)
  (fun {x y} hx => finite_star_square_mul_right τ y hx)

@[simp] lemma mem_finiteTraceIdeal (τ : ExtendedTrace A) (x : A) :
    x ∈ finiteTraceIdeal τ ↔ τ (Positive.starMul x) < ∞ := by
  simp only [finiteTraceIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq]

lemma finiteTraceIdeal_dense (hsimple : TopologicallySimple A) (τ : ExtendedTrace A)
    {b : A} (hb : 0 ≤ b) (hb0 : b ≠ 0) (hτ : τ ⟨b,hb⟩ < ∞) :
    Dense (finiteTraceIdeal τ : Set A) := by
  have hs : CFC.sqrt b ∈ finiteTraceIdeal τ := by
    rw [mem_finiteTraceIdeal]
    have he : Positive.starMul (CFC.sqrt b)=(⟨b,hb⟩ : Positive A) := by
      apply Subtype.ext
      exact (congrArg (fun t => t*CFC.sqrt b) (CFC.sqrt_nonneg b).star_eq).trans
        (CFC.sqrt_mul_sqrt_self b hb)
    rwa [he]
  have hs0 : CFC.sqrt b ≠ 0 := (CFC.sqrt_eq_zero_iff b hb).not.mpr hb0
  let I := closedTwoSidedIdeal (finiteTraceIdeal τ)
  have hI : IsClosed (I : Set A) := by
    dsimp only [I]
    rw [coe_closedTwoSidedIdeal]
    exact isClosed_closure
  rcases hsimple I hI with hbot|htop
  · have hm : CFC.sqrt b ∈ I := by
      change CFC.sqrt b ∈ closedTwoSidedIdeal (finiteTraceIdeal τ)
      rw [←SetLike.mem_coe,coe_closedTwoSidedIdeal]
      exact subset_closure hs
    rw [hbot,TwoSidedIdeal.mem_bot] at hm
    exact (hs0 hm).elim
  · rw [dense_iff_closure_eq]
    simpa only [I,coe_closedTwoSidedIdeal,TwoSidedIdeal.coe_top] using
      congrArg (fun J : TwoSidedIdeal A => (J : Set A)) htop

theorem denselyFinite_of_finite_nonzero (hsimple : TopologicallySimple A) (τ : ExtendedTrace A)
    {b : A} (hb : 0 ≤ b) (hb0 : b ≠ 0) (hτ : τ ⟨b,hb⟩ < ∞) :
    WeightDenselyFinite τ := by
  have hd := finiteTraceIdeal_dense hsimple τ hb hb0 hτ
  intro a
  obtain ⟨x,hx,hlim⟩ := mem_closure_iff_seq_limit.mp (hd (CFC.sqrt a.1))
  have ht : Tendsto (fun n => Positive.starMul (x n)) atTop (𝓝 a) := by
    apply tendsto_subtype_rng.mpr
    simpa only [Positive.starMul,(CFC.sqrt_nonneg a.1).star_eq,CFC.sqrt_mul_sqrt_self a.1 a.2]
      using hlim.star.mul hlim
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun n =>
    (mem_finiteTraceIdeal τ (x n)).mp (hx n))

end

open TraceCone Filter Topology CurrentMain Pureness
open scoped ENNReal NNReal ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma bounded_ray_of_finite_test [Nonempty (NormalizedTrace A)]
    (hsimple : TopologicallySimple A) (hcone : AllDenselyFiniteTracesBounded A)
    (τ : ExtendedTrace A) (b : Positive A) (hb : b.1≠0)
    (m C : ℝ≥0) (hm : 0 < m)
    (hmin : ∀ σ : NormalizedTrace A, (m:ℝ) ≤ (σ.functional b.1).re)
    (hC : τ b ≤ (C:ℝ≥0∞)) :
    ∃ r : ℝ≥0, ∃ σ : NormalizedTrace A, r ≤ C/m ∧
      ∀ a : Positive A, τ a=(r:ℝ≥0∞)*ENNReal.ofReal (σ.functional a.1).re := by
  classical
  by_cases hz : τ=0
  · subst τ
    exact ⟨0,Classical.choice inferInstance,by positivity,fun a => by simp⟩
  have hfinite : τ b < ∞ := hC.trans_lt ENNReal.coe_lt_top
  have ht := hcone τ (denselyFinite_of_finite_nonzero hsimple τ b.2 hb hfinite)
  let r : ℝ≥0 := ‖positiveFunctionalCLM (boundedWeightFunctional τ ht)‖₊
  let σ := normalizedWeight τ ht hz
  refine ⟨r,σ,?_,fun a => normalizedWeight_ray τ ht hz a⟩
  have ht' : (r:ℝ≥0∞)*ENNReal.ofReal (σ.functional b.1).re ≤ (C:ℝ≥0∞) := by
    rw [←normalizedWeight_ray τ ht hz b]
    exact hC
  have hrm : (r:ℝ≥0∞)*(m:ℝ≥0∞) ≤ (C:ℝ≥0∞) := by
    apply le_trans (mul_le_mul_of_nonneg_left ?_ (zero_le (α := ℝ≥0∞))) ht'
    rw [←ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hmin σ)
  have hrm' : r*m ≤ C := by exact_mod_cast hrm
  exact (le_div_iff₀ hm).mpr hrm'

def generalizedLimitValue (U : Ultrafilter ℕ) (ν : ℕ → ExtendedTrace A)
    (z : ℕ → Positive A) : ℝ≥0∞ :=
  ⨆ ε : ℝ≥0, ⨆ (_ : 0 < ε), limUnder (U : Filter ℕ) (fun n => ν n (Positive.cut ε (z n)))

lemma ennreal_ultrafilter_tendsto (U : Ultrafilter ℕ) (f : ℕ → ℝ≥0∞) :
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨x,_,hx⟩ := isCompact_univ.ultrafilter_le_nhds (U.map f) (by simp)
  exact ⟨x,hx⟩

lemma cut_nonzero_exists (a : Positive A) (ha : a.1≠0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ (Positive.cut ε a).1≠0 := by
  let ε : ℝ≥0 := ‖a.1‖₊/2
  have hn : 0 < ‖a.1‖ := norm_pos_iff.mpr ha
  have he : 0 < ε := by
    apply div_pos (show 0 < ‖a.1‖₊ by exact_mod_cast hn) (by norm_num)
  refine ⟨ε,he,?_⟩
  intro hz
  have h := Positive.norm_sub_cut_le ε a
  rw [hz,sub_zero] at h
  change ‖a.1‖ ≤ ‖a.1‖/2 at h
  linarith

lemma eventually_finite_test {U : Ultrafilter ℕ} {ν : ℕ → ExtendedTrace A}
    {a : Positive A} {ε : ℝ≥0} (hε : 0 < ε)
    (ha : generalizedLimitValue U ν (fun _ => a)<∞) :
    ∃ C : ℝ≥0, ∀ᶠ n in (U : Filter ℕ), ν n (Positive.cut ε a) ≤ (C:ℝ≥0∞) := by
  have hle : limUnder (U : Filter ℕ) (fun n => ν n (Positive.cut ε a)) ≤
      generalizedLimitValue U ν (fun _ => a) := le_iSup_of_le ε (le_iSup_of_le hε le_rfl)
  let L := limUnder (U : Filter ℕ) (fun n => ν n (Positive.cut ε a))
  have hL : L<∞ := hle.trans_lt ha
  obtain ⟨C,hC,_⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hL
  refine ⟨C,?_⟩
  exact ((ennreal_ultrafilter_tendsto U _).eventually (gt_mem_nhds hC)).mono fun _ h => h.le

theorem generalized_eventually_bounded_rays [Nonempty (NormalizedTrace A)]
    [CompactSpace (NormalizedTrace A)] (U : Ultrafilter ℕ)
    (hsimple : TopologicallySimple A) (hcone : AllDenselyFiniteTracesBounded A)
    (ν : ℕ → ExtendedTrace A) (a : Positive A) (ha0 : a.1≠0)
    (ha : generalizedLimitValue U ν (fun _ => a)<∞) :
    ∃ K : ℝ≥0, ∃ r : ℕ → ℝ≥0, ∃ σ : ℕ → NormalizedTrace A,
      (∀ n, r n ≤ K) ∧ ∀ᶠ n in (U : Filter ℕ),
        ∀ b : Positive A, ν n b=(r n:ℝ≥0∞)*ENNReal.ofReal ((σ n).functional b.1).re := by
  classical
  obtain ⟨ε,hε,hε0⟩ := cut_nonzero_exists a ha0
  obtain ⟨C,hC⟩ := eventually_finite_test hε ha
  obtain ⟨m,hm,hmin⟩ := uniform_positive_trace hsimple (Positive.cut ε a).1 (Positive.cut ε a).2 hε0
  let m' : ℝ≥0 := ⟨m,hm.le⟩
  have hm' : 0 < m' := hm
  let K := C/m'
  have hex (n : ℕ) (hn : ν n (Positive.cut ε a) ≤ (C:ℝ≥0∞)) :
      ∃ r : ℝ≥0, ∃ σ : NormalizedTrace A, r ≤ K ∧
        ∀ b : Positive A, ν n b=(r:ℝ≥0∞)*ENNReal.ofReal (σ.functional b.1).re :=
    bounded_ray_of_finite_test hsimple hcone (ν n) (Positive.cut ε a) hε0 m' C hm' hmin hn
  let r := fun n => if hn : ν n (Positive.cut ε a) ≤ (C:ℝ≥0∞) then (hex n hn).choose else 0
  let σ := fun n => if hn : ν n (Positive.cut ε a) ≤ (C:ℝ≥0∞) then
      (hex n hn).choose_spec.choose else Classical.choice inferInstance
  refine ⟨K,r,σ,?_,?_⟩
  · intro n
    dsimp [r]
    split_ifs with hn
    · exact (hex n hn).choose_spec.choose_spec.1
    · exact bot_le
  · filter_upwards [hC] with n hn
    simpa only [r,σ,dite_eq_left hn] using (hex n hn).choose_spec.choose_spec.2

end NonunitalGamma
end

end OAI
