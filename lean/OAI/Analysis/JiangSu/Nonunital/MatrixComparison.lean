import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzOrder
import OAI.Analysis.JiangSu.Nonunital.MatrixDiagonal
import OAI.Analysis.JiangSu.Nonunital.Stabilization
import OAI.Analysis.JiangSu.Comparison.FamilyRanks

namespace OAI


noncomputable section
namespace NonunitalGamma
open Filter Topology TraceCone Pureness DirectComparison
open scoped ComplexOrder ENNReal NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem sqrt_conjugate {B : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (b : B) (hb : 0 ≤ b) (x : B) :
    star (CFC.sqrt b*x)*(CFC.sqrt b*x)=star x*b*x := by
  simp only [star_mul,(CFC.sqrt_nonneg b).star_eq,mul_assoc]
  rw [←mul_assoc (CFC.sqrt b),CFC.sqrt_mul_sqrt_self b hb]

lemma NormalizedTrace.continuous_unitized_eval (a : Unitization ℂ A) :
    Continuous (fun τ : NormalizedTrace A => τ.unitized.functional a) := by
  change Continuous (fun τ : NormalizedTrace A => a.fst+τ.functional a.snd)
  exact continuous_const.add (NormalizedTrace.continuous_eval a.snd)

lemma NormalizedTrace.continuous_matrix_eval (n : ℕ) [NeZero n]
    (a : MatrixStage (Unitization ℂ A) n) :
    Continuous (fun τ : NormalizedTrace A => (matrixTracialState τ.unitized).functional a) := by
  change Continuous (fun τ : NormalizedTrace A => (Fintype.card (Fin n) : ℂ)⁻¹ *
    ∑ i : Fin n,τ.unitized.functional (a i i))
  exact continuous_const.mul (continuous_finsetSum _ (fun index _ => NormalizedTrace.continuous_unitized_eval (a index index)))

def scalarOne : A →⋆ₙₐ[ℂ] FinMatrix A 1 where
  toFun a := fun _ _ => a
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' a b := by
    ext i j
    change a*b = ∑ _k : Fin 1, a*b
    simp
  map_star' a := rfl

def scalarCorner (n : ℕ) (h : 1 ≤ n) : A →⋆ₙₐ[ℂ] FinMatrix A n :=
  (matrixInclusion h).comp scalarOne

lemma inr_scalarCorner (n : ℕ) (h : 1 ≤ n) (a : A) :
    finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) n (scalarCorner n h a)=
      DirectComparison.scalarCorner h (Unitization.inr a) := by
  change finiteMatrixMap _ n (matrixInclusion h (scalarOne a))=_
  rw [finiteMatrixMap_inclusion,shared_matrixInclusion_eq_corner]
  change corner h _ = corner h (Pureness.scalarFinOneEquiv (Unitization.inr a))
  congr 1
  apply CStarMatrix.ext
  intro i j
  have hij : i=j := Subsingleton.elim _ _
  simp only [scalarOne, Pureness.scalarFinOneEquiv_apply, Pureness.scalarMatrixHom]
  change (Unitization.inr a : Unitization ℂ A) =
    if i = j then Unitization.inr a else 0
  simp [hij]


lemma scalarCorner_injective (n : ℕ) (h : 1 ≤ n) : Function.Injective (scalarCorner (A := A) n h) := by
  intro a b hab
  apply Unitization.inr_injective (R := ℂ)
  apply DirectComparison.scalarCorner_injective h
  simpa only [inr_scalarCorner] using congrArg (finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) n) hab

lemma NormalizedTrace.matrix_rank_inr (τ : NormalizedTrace A) (n : ℕ) [NeZero n]
    (a : Positive (FinMatrix A n)) :
    (τ.weight.matrixTrace (Fin n)).rank a =
      matrixRank τ.unitized (finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) n a.1) := by
  change ((functionalWeight τ.functional τ.tracial).matrixTrace (Fin n)).rank a = _
  rw [←τ.stabilized_rank_stage n a,NormalizedTrace.stabilized,ExtendedTrace.rank_pullback,
    sharedExtendedTrace_rank]
  change completedRootRank τ.unitized (sharedMatrixEquiv
    (stabilizationInr (matrixLimitStage n a.1)))=_
  rw [stabilizationInr,stabilizationMap_stage,sharedMatrixEquiv_stage]
  exact completedRootRank_include τ.unitized n _ (map_nonneg _ a.2)

lemma trace_lt_rank (hsimple : TopologicallySimple A) (τ : NormalizedTrace A)
    (b : A) (hb : 0 ≤ b) (hb0 : b ≠ 0) (hbn : ‖b‖ < 1) :
    (τ.functional b).re < (τ.rank b).toReal := by
  have hn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hτ0 : τ.functional b ≠ 0 := fun h => hb0 (τ.faithful hsimple b hb h)
  have ht : 0 < (τ.functional b).re :=
    (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hb) hτ0.symm)).1
  have hbi : 0 ≤ (Unitization.inr b : Unitization ℂ A) := Unitization.inr_nonneg_iff.mpr hb
  have hlo := ENNReal.toReal_mono (DirectComparison.directRank_ne_top τ.unitized _ hbi)
    (normalized_trace_le_rank τ.unitized _ hbi)
  rw [ENNReal.toReal_ofReal (τ.unitized.functional.map_nonneg (normalizePositive_nonneg _ hbi)).1] at hlo
  have he : (τ.unitized.functional (normalizePositive (Unitization.inr b))).re = ‖b‖⁻¹ * (τ.functional b).re := by
    rw [normalizePositive,τ.unitized.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul,
      Unitization.norm_inr,NormalizedTrace.unitized_inr]
  rw [he] at hlo
  have hi : 1 < ‖b‖⁻¹ := (one_lt_inv₀ hn).mpr hbn
  change (τ.functional b).re < (normalizedRootRank τ.unitized (Unitization.inr b)).toReal
  exact (lt_mul_of_one_lt_left ht hi).trans_le hlo

lemma matrix_comparison_inr (hsimple : TopologicallySimple A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : StrictComparison hcone)
    (n : ℕ) [NeZero n] (hn : 1 ≤ n) (b : A) (hb : 0 ≤ b) (hb0 : b≠0) (hbn : ‖b‖<1)
    (v : Positive (FinMatrix A n))
    (hup : ∀ τ : NormalizedTrace A, ((τ.weight.matrixTrace (Fin n)).rank v).toReal ≤ (τ.functional b).re) :
    CuntzSubequiv (finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) n v.1)
      (DirectComparison.scalarCorner hn (Unitization.inr b)) := by
  let bM : Positive (FinMatrix A n) := ⟨scalarCorner n hn b,map_nonneg _ hb⟩
  have hbM : (matrixLimitStage n bM.1) ≠ 0 := by
    intro h
    apply hb0
    apply scalarCorner_injective n hn
    apply (matrixLimitStage_isometry n).injective
    simpa only [map_zero] using h
  have hc := comparison_of_normalized_rank_lt hcone hcmp
    (Positive.map (matrixLimitStage n) v) (Positive.map (matrixLimitStage n) bM) hbM (fun τ => by
      rw [τ.stabilized_rank_stage,τ.stabilized_rank_stage]
      change (τ.weight.matrixTrace (Fin n)).rank v < (τ.weight.matrixTrace (Fin n)).rank bM
      rw [τ.matrix_rank_inr n v,τ.matrix_rank_inr n bM]
      have hb' : 0 ≤ (Unitization.inr b : Unitization ℂ A) := Unitization.inr_nonneg_iff.mpr hb
      change matrixRank τ.unitized (finiteMatrixMap _ n v.1) < matrixRank τ.unitized (finiteMatrixMap _ n (scalarCorner n hn b))
      rw [inr_scalarCorner,DirectComparison.matrixRank_scalarCorner τ.unitized hn _ hb']
      apply (ENNReal.toReal_lt_toReal (matrixRank_ne_top τ.unitized _ (map_nonneg _ v.2))
        (DirectComparison.directRank_ne_top τ.unitized _ hb')).mp
      have hu := hup τ
      rw [τ.matrix_rank_inr n v] at hu
      exact hu.trans_lt (trace_lt_rank hsimple τ b hb hb0 hbn))
  have hm := (hc.map (stabilizationInr (A := A))).map
    (sharedMatrixEquiv (A := Unitization ℂ A)).toNonUnitalStarAlgHom
  have he : ∀ w : Positive (FinMatrix A n),
      sharedMatrixEquiv (stabilizationInr (matrixLimitStage n w.1))=
        completedMatrixInclude (Unitization ℂ A) n (finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) n w.1) := by
    intro w
    rw [stabilizationInr,stabilizationMap_stage,sharedMatrixEquiv_stage]
  have hp := (cuntzSubequiv_iff_shared _ _).mpr hm
  change CuntzSubequiv (sharedMatrixEquiv (stabilizationInr (matrixLimitStage n v.1)))
    (sharedMatrixEquiv (stabilizationInr (matrixLimitStage n bM.1))) at hp
  rw [he v,he bM] at hp
  change CuntzSubequiv _ (completedMatrixInclude (Unitization ℂ A) n (finiteMatrixMap _ n (scalarCorner n hn b))) at hp
  rw [inr_scalarCorner] at hp
  exact (cuntzSubequiv_completedMatrixInclude_iff _ n _ _).mp hp

lemma hereditary_inr_reflect (b : A) (hb : 0 ≤ b) {p : Unitization ℂ A}
    (hp : p ∈ Pureness.hereditaryCarrier (Unitization.inr b)) (hp0 : 0 ≤ p) :
    ∃ q : A, q ∈ hereditaryCarrier b ∧ 0 ≤ q ∧ Unitization.inr q=p ∧ ‖q‖=‖p‖ := by
  have hc : IsClosed {z : Unitization ℂ A | z.fst=0 ∧ z.snd ∈ hereditaryCarrier b} :=
    (isClosed_eq Unitization.continuous_fst continuous_const).inter
      (isClosed_closure.preimage Unitization.continuous_snd)
  have hm : p.fst=0 ∧ p.snd ∈ hereditaryCarrier b := by
    apply closure_minimal ?_ hc hp
    rintro z ⟨w,rfl⟩
    constructor
    · simp only [Unitization.fst_mul,Unitization.fst_inr,zero_mul]
    · change ((Unitization.inr b : Unitization ℂ A)*w*Unitization.inr b).snd ∈ hereditarySubalgebra b hb
      have he : ((Unitization.inr b : Unitization ℂ A)*w*Unitization.inr b).snd =
          w.fst • (b*b) + b*w.snd*b := by
        simp only [Unitization.snd_mul,Unitization.fst_mul,Unitization.fst_inr,
          Unitization.snd_inr,zero_mul,zero_smul,zero_add,add_mul,smul_mul_assoc]
      rw [he]
      exact (hereditarySubalgebra b hb).add_mem
        (hereditary_complex_smul_mem (w.fst : ℂ) ((hereditarySubalgebra b hb).mul_mem
          (self_mem_hereditary b hb) (self_mem_hereditary b hb)))
        (subset_closure ⟨w.snd,rfl⟩)
  have he : (Unitization.inr p.snd : Unitization ℂ A)=p := by
    apply Unitization.ext <;> simp [hm.1]
  refine ⟨p.snd,hm.2,?_,he,?_⟩
  · exact Unitization.inr_nonneg_iff.mp (he ▸ hp0)
  · rw [←Unitization.norm_inr (𝕜 := ℂ),he]

lemma uniform_positive_trace [CompactSpace (NormalizedTrace A)]
    (hsimple : NonunitalGamma.TopologicallySimple A) (b : A) (hb : 0 ≤ b) (hb0 : b≠0) :
    ∃ m : ℝ, 0 < m ∧ ∀ τ : NormalizedTrace A, m ≤ (τ.functional b).re := by
  obtain ⟨m,hm,hb⟩ := isCompact_univ.exists_forall_le'
    (NormalizedTrace.continuous_eval_re b).continuousOn (fun τ _ => by
      have hn : τ.functional b≠0 := fun hz => hb0 (τ.faithful hsimple b hb hz)
      exact (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hb) hn.symm)).1)
  exact ⟨m,hm,fun τ => hb τ (Set.mem_univ _)⟩

lemma rank_approximant_below_trace [Nontrivial A] [CompactSpace (NormalizedTrace A)]
    (hsimple : NonunitalGamma.TopologicallySimple A) (hproj : Projectionless A)
    (hT : Nonempty (NormalizedTrace A)) (b : A) (hb : 0 ≤ b) (hb0 : b≠0) (hbn : ‖b‖<1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ k : Positive (FinMatrix A (N+1)), ‖k.1‖ ≤ 1 ∧
      ∀ τ : NormalizedTrace A,
        (τ.functional b).re-2*δ < ((τ.weight.matrixTrace (Fin (N+1))).rank k).toReal ∧
        ((τ.weight.matrixTrace (Fin (N+1))).rank k).toReal ≤ (τ.functional b).re := by
  obtain ⟨m,hm,hmt⟩ := uniform_positive_trace hsimple b hb hb0
  let α := min (δ/4) (1/2 : ℝ)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hαδ : α ≤ δ/4 := min_le_left _ _
  have hα1 : α ≤ 1/2 := min_le_right _ _
  let ξ := min (δ/4) (α*m/4)
  have hξ : 0 < ξ := lt_min (by positivity) (by positivity)
  have hξδ : ξ ≤ δ/4 := min_le_left _ _
  have hξm : ξ ≤ α*m/4 := min_le_right _ _
  let g : A := (1-α) • b
  have hg : 0 ≤ g := by exact smul_nonneg (by linarith) hb
  obtain ⟨N,k,hkn,hk⟩ := rank_approximation hsimple hproj hT g hg hξ
  refine ⟨N,k,hkn,fun τ => ?_⟩
  obtain ⟨_,_,herr,hdef0,hdef⟩ := hk τ
  have ht : (τ.functional g).re=(1-α)*(τ.functional b).re := by
    dsimp only [g]
    rw [τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul]
  rw [ht] at herr
  have hlow := (abs_lt.mp herr).1
  have hup := (abs_lt.mp herr).2
  have hbt : (τ.functional b).re ≤ 1 := by
    have hn := (positiveFunctionalCLM τ.functional).le_opNorm b
    rw [τ.norm_one,one_mul] at hn
    exact (Complex.re_le_norm _).trans (hn.trans hbn.le)
  have hbm := hmt τ
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hbt hα.le]
  · nlinarith [mul_le_mul_of_nonneg_left hbm hα.le]

theorem almost_projection [Nontrivial A] [CompactSpace (NormalizedTrace A)]
    (hsimple : NonunitalGamma.TopologicallySimple A) (hproj : Projectionless A)
    (hT : Nonempty (NormalizedTrace A)) (hcone : AllDenselyFiniteTracesBounded A)
    (hcmp : NonunitalGamma.StrictComparison hcone)
    (b : A) (hb : 0 ≤ b) (hbn : ‖b‖ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : A, p ∈ NonunitalGamma.hereditaryCarrier b ∧ 0 ≤ p ∧ ‖p‖ ≤ 1 ∧
      ∀ τ : NormalizedTrace A,
        (τ.functional b).re-2*δ < (τ.functional p).re ∧
        (τ.functional p).re ≤ (τ.functional b).re ∧
        0 ≤ (τ.functional (p-p*p)).re ∧ (τ.functional (p-p*p)).re < 2*δ := by
  by_cases hb0 : b=0
  · subst b
    refine ⟨0,subset_closure ⟨0,by simp⟩,le_rfl,by simp,?_⟩
    intro τ
    simp only [map_zero,Complex.zero_re,zero_mul,sub_zero]
    exact ⟨by linarith,le_rfl,le_rfl,by linarith⟩
  obtain ⟨l,v,_,hvapprox⟩ := rank_approximant_below_trace hsimple hproj hT b hb hb0 hbn δ hδ
  let B := MatrixStage (Unitization ℂ A) (l+1)
  let hl : 1 ≤ l+1 := Nat.succ_le_succ (Nat.zero_le _)
  let vM : B := finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) (l+1) v.1
  have hvM : 0 ≤ vM := map_nonneg _ v.2
  let bM : B := DirectComparison.scalarCorner hl (Unitization.inr b)
  have hbM : 0 ≤ bM := DirectComparison.scalarCorner_nonneg hl (Unitization.inr_nonneg_iff.mpr hb)
  have hNr : 0 < ((l+1 : ℕ) : ℝ) := by positivity
  let d : ℝ := δ/(l+1:ℕ)
  have hd : ((l+1 : ℕ):ℝ)*d=δ := by dsimp [d];field_simp
  let θ : NormalizedTrace A → TracialState B := fun τ => matrixTracialState τ.unitized
  have hr (τ : NormalizedTrace A) :
      ((τ.weight.matrixTrace (Fin (l+1))).rank v).toReal =
        ((l+1 : ℕ):ℝ)*(normalizedRootRank (θ τ) vM).toReal := by
    rw [τ.matrix_rank_inr,matrixRank_toReal,Fintype.card_fin]
  have ht (τ : NormalizedTrace A) :
      ((l+1 : ℕ):ℝ)*((θ τ).functional bM).re=(τ.functional b).re := by
    simpa only [NormalizedTrace.unitized_inr] using scalarCorner_trace_scale τ.unitized hl (Unitization.inr b)
  have hup : ∀ τ : NormalizedTrace A, (normalizedRootRank (θ τ) vM).toReal ≤ ((θ τ).functional bM).re := by
    intro τ
    have hu := (hvapprox τ).2
    rw [hr τ,←ht τ] at hu
    nlinarith
  have hgap : ∀ τ : NormalizedTrace A, ((θ τ).functional bM).re-2*d < (normalizedRootRank (θ τ) vM).toReal := by
    intro τ
    have hlo := (hvapprox τ).1
    rw [hr τ,←ht τ] at hlo
    nlinarith
  obtain ⟨η,hη,hηcut⟩ := family_uniform_positive_cut θ
    (NormalizedTrace.continuous_matrix_eval (l+1)) vM hvM
    (fun τ => ((θ τ).functional bM).re-2*d)
    ((Complex.continuous_re.comp (NormalizedTrace.continuous_matrix_eval (l+1) bM)).sub continuous_const) hgap
  let t := η/3
  have ht0 : 0 < t := by dsimp [t];positivity
  have h3 : 3*t=η := by dsimp [t];ring
  have hcmpM := matrix_comparison_inr hsimple hcone hcmp (l+1) hl b hb hb0 hbn v (fun τ => (hvapprox τ).2)
  obtain ⟨x,hx⟩ := (cuntzSubequiv_iff_norm vM bM).mp hcmpM t ht0
  have hs := sqrt_conjugate bM hbM x
  obtain ⟨pM,hpMmem,hpM0,hpMn,hpMτ⟩ := family_scalar_almost_projection_step θ bM vM x hbM hvM t d ht0
    (by rw [hs,norm_sub_rev];exact hx) (by simpa only [h3] using hηcut) hup
  obtain ⟨pU,hpUmem,hpU0,hpUe,hpUn⟩ := hereditary_scalarCorner_reflect hl (Unitization.inr b) hpMmem hpM0
  obtain ⟨p,hpmem,hp0,hpe,hpn⟩ := hereditary_inr_reflect b hb hpUmem hpU0
  refine ⟨p,hpmem,hp0,by rw [hpn];exact hpUn.trans_le hpMn,fun τ => ?_⟩
  obtain ⟨hlo,hhi,hnon,hdef⟩ := hpMτ τ
  have hbt := ht τ
  have hpt : ((l+1 : ℕ):ℝ)*((θ τ).functional pM).re=(τ.functional p).re := by
    rw [←hpUe,←hpe]
    simpa only [NormalizedTrace.unitized_inr] using scalarCorner_trace_scale τ.unitized hl (Unitization.inr p)
  have hpd : ((l+1 : ℕ):ℝ)*((θ τ).functional (pM-pM*pM)).re=(τ.functional (p-p*p)).re := by
    rw [←hpUe,←map_mul (DirectComparison.scalarCorner (A := Unitization ℂ A) hl),
      ←map_sub (DirectComparison.scalarCorner (A := Unitization ℂ A) hl),←hpe,
      ←Unitization.inr_mul,←Unitization.inr_sub]
    simpa only [NormalizedTrace.unitized_inr] using scalarCorner_trace_scale τ.unitized hl (Unitization.inr (p-p*p))
  refine ⟨?_,?_,?_,?_⟩
  · have hm := mul_lt_mul_of_pos_left hlo hNr;nlinarith
  · have hm := mul_le_mul_of_nonneg_left hhi hNr.le;nlinarith
  · nlinarith
  · have hm := mul_lt_mul_of_pos_left hdef hNr;nlinarith

end NonunitalGamma

end

end OAI
