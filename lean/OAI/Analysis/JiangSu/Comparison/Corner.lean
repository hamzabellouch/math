import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traces.TraceRankApproximation
import OAI.Analysis.JiangSu.Comparison.CornerComparison
import OAI.Analysis.JiangSu.MatrixAlgebras.CompletedCornerRange
import OAI.Analysis.JiangSu.MatrixAlgebras.FinOneMatrixTransport
import OAI.Analysis.JiangSu.CStarAlgebras.CompletedRootRank
import OAI.Analysis.JiangSu.Comparison.Ranks

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l : ℕ}

omit [PartialOrder A] [StarOrderedRing A] in
lemma cornerProjection_mul_corner (h : k ≤ l) (a : MatrixStage A k) :
    cornerProjection h * corner h a = corner h a := by
  rw [cornerProjection_eq]
  change cornerHom h 1 * cornerHom h a = cornerHom h a
  rw [←map_mul,one_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_mul_cornerProjection (h : k ≤ l) (a : MatrixStage A k) :
    corner h a * cornerProjection h = corner h a := by
  rw [cornerProjection_eq]
  change cornerHom h a * cornerHom h 1 = cornerHom h a
  rw [←map_mul,mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_compressed_sandwich (h : k ≤ l) (b c : MatrixStage A k)
    (w : MatrixStage A l) :
    corner h (b * compress h w * c) = corner h b * w * corner h c := by
  change cornerHom h (b * compress h w * c) = _
  rw [map_mul,map_mul]
  change corner h b * corner h (compress h w) * corner h c = _
  rw [corner_compress]
  calc
    _ = (corner h b * cornerProjection h) * w *
        (cornerProjection h * corner h c) := by simp only [mul_assoc]
    _ = _ := by rw [corner_mul_cornerProjection,cornerProjection_mul_corner]

omit [PartialOrder A] [StarOrderedRing A] in
lemma compress_corner_sandwich (h : k ≤ l) (b c : MatrixStage A k)
    (w : MatrixStage A l) :
    compress h (corner h b * w * corner h c) = b * compress h w * c := by
  rw [←corner_compressed_sandwich,compress_corner]

theorem hereditary_corner_reflect (h : k ≤ l) (b : MatrixStage A k)
    {p : MatrixStage A l} (hp : p ∈ hereditaryCarrier (corner h b)) :
    corner h (compress h p) = p ∧ compress h p ∈ hereditaryCarrier b := by
  have hclosed : IsClosed {z : MatrixStage A l | corner h (compress h z) = z} :=
    isClosed_eq ((corner_isometry h).continuous.comp (compress_continuous h)) continuous_id
  have hr : corner h (compress h p) = p := by
    apply (closure_minimal ?_ hclosed) hp
    rintro z ⟨w,rfl⟩
    change corner h (compress h (corner h b * w * corner h b)) = _
    rw [compress_corner_sandwich,corner_compressed_sandwich]
  refine ⟨hr,?_⟩
  obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hp
  apply isClosed_closure.mem_of_tendsto ((compress_continuous h).continuousAt.tendsto.comp ht)
  apply Eventually.of_forall
  intro n
  obtain ⟨w,hw⟩ := hu n
  rw [Function.comp_apply,←hw,compress_corner_sandwich]
  exact subset_closure ⟨compress h w,rfl⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma map_mem_hereditary {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →⋆ₙₐ[ℂ] B) (hφ : Continuous φ) {b p : A} (hp : p ∈ hereditaryCarrier b) :
    φ p ∈ hereditaryCarrier (φ b) := by
  obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hp
  apply isClosed_closure.mem_of_tendsto (hφ.continuousAt.tendsto.comp ht)
  apply Eventually.of_forall
  intro n
  obtain ⟨w,hw⟩ := hu n
  rw [Function.comp_apply,←hw]
  exact subset_closure ⟨φ w,by rw [map_mul,map_mul]⟩

def scalarCorner (h : 1 ≤ l) : A →⋆ₙₐ[ℂ] MatrixStage A l :=
  (cornerHom h).comp scalarFinOneEquiv.toStarAlgHom.toNonUnitalStarAlgHom

lemma scalarCorner_apply (h : 1 ≤ l) (b : A) :
    scalarCorner h b = corner h (scalarFinOneEquiv b) := rfl

lemma scalarCorner_injective (h : 1 ≤ l) : Function.Injective (scalarCorner (A := A) h) :=
  (corner_injective h).comp scalarFinOneEquiv.injective

lemma scalarCorner_isometry (h : 1 ≤ l) : Isometry (scalarCorner (A := A) h) :=
  NonUnitalStarAlgHom.isometry _ (scalarCorner_injective h)

lemma scalarCorner_nonneg (h : 1 ≤ l) {b : A} (hb : 0 ≤ b) : 0 ≤ scalarCorner h b :=
  map_nonneg (scalarCorner h) hb

lemma scalarCorner_norm (h : 1 ≤ l) (b : A) : ‖scalarCorner h b‖ = ‖b‖ :=
  NonUnitalStarAlgHom.norm_map _ (scalarCorner_injective h) b

lemma matrixTrace_scalarCorner (τ : TracialState A) (h : 1 ≤ l) (b : A) :
    matrixTrace τ (scalarCorner h b) = τ.functional b := by
  rw [scalarCorner_apply,matrixTrace_corner]
  simp only [matrixTrace_apply,Fin.sum_univ_one]
  rfl

lemma scalarCorner_trace [NeZero l] (τ : TracialState A) (h : 1 ≤ l) (b : A) :
    ((matrixTracialState (ι := Fin l) τ).functional (scalarCorner h b)).re =
      (τ.functional b).re / l := by
  change (((Fintype.card (Fin l) : ℂ)⁻¹) * matrixTrace τ (scalarCorner h b)).re = _
  rw [matrixTrace_scalarCorner]
  simp only [Fintype.card_fin,←Complex.ofReal_natCast,←Complex.ofReal_inv,
    Complex.re_ofReal_mul,div_eq_mul_inv,mul_comm]

lemma scalarCorner_trace_scale [NeZero l] (τ : TracialState A) (h : 1 ≤ l) (b : A) :
    (l : ℝ) * ((matrixTracialState (ι := Fin l) τ).functional (scalarCorner h b)).re =
      (τ.functional b).re := by
  simpa only [Fintype.card_fin,matrixTrace_scalarCorner] using
    matrixTracialState_scale τ (scalarCorner h b)

lemma matrixRank_scalarCorner [NeZero l] (τ : TracialState A) (h : 1 ≤ l)
    (b : A) (hb : 0 ≤ b) : matrixRank τ (scalarCorner h b) = normalizedRootRank τ b := by
  have he : (matrixRank τ (scalarCorner h b)).toReal = (normalizedRootRank τ b).toReal := by
    apply tendsto_nhds_unique
      (matrixPower_trace_tendsto_realRank τ _ (scalarCorner_nonneg h hb))
    convert positivePower_trace_tendsto τ b hb using 1
    funext n
    rw [positivePower_nonUnital_map (scalarCorner h) (scalarCorner_isometry h).continuous
      b hb _ (by positivity),matrixTrace_scalarCorner]
  rw [←ENNReal.ofReal_toReal (matrixRank_ne_top τ _ (scalarCorner_nonneg h hb)),
    ←ENNReal.ofReal_toReal (ne_of_lt ((normalizedRootRank_le_one τ b hb).trans_lt ENNReal.one_lt_top)),he]

theorem hereditary_scalarCorner_reflect (h : 1 ≤ l) (b : A)
    {p : MatrixStage A l} (hp : p ∈ hereditaryCarrier (scalarCorner h b)) (hp0 : 0 ≤ p) :
    ∃ q : A, q ∈ hereditaryCarrier b ∧ 0 ≤ q ∧ scalarCorner h q = p ∧ ‖q‖ = ‖p‖ := by
  obtain ⟨he,hm⟩ := hereditary_corner_reflect h (scalarFinOneEquiv b) hp
  let q := (scalarFinOneEquiv (A := A)).symm (compress h p)
  have hq : scalarCorner h q = p := by
    rw [scalarCorner_apply,StarAlgEquiv.apply_symm_apply]
    exact he
  refine ⟨q,?_,?_,hq,?_⟩
  · let φ : MatrixStage A 1 →⋆ₙₐ[ℂ] A :=
      (scalarFinOneEquiv (A := A)).symm.toStarAlgHom.toNonUnitalStarAlgHom
    have hφ : Continuous φ := (StarAlgEquiv.isometry (scalarFinOneEquiv (A := A)).symm).continuous
    have hmem := map_mem_hereditary φ hφ hm
    change scalarFinOneEquiv.symm (compress _ p) ∈
      hereditaryCarrier (scalarFinOneEquiv.symm (scalarFinOneEquiv b)) at hmem
    simpa only [StarAlgEquiv.symm_apply_apply] using hmem
  · have hpos := matrix_entry_nonneg p hp0 (Fin.castLE h 0)
    simpa only [q,scalarFinOneEquiv_symm_apply,compress] using hpos
  · rw [←scalarCorner_norm h q,hq]

end DirectComparison

namespace DirectComparison
open Pureness Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_lt_rank_of_norm_lt_one (hsimple : TopologicallySimple A)
    (τ : TracialState A) (b : A) (hb : 0 ≤ b) (hb0 : b ≠ 0) (hbn : ‖b‖ < 1) :
    (τ.functional b).re < (normalizedRootRank τ b).toReal := by
  have hn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hτ0 : τ.functional b ≠ 0 := fun h => hb0 (τ.faithful hsimple b hb h)
  have ht : 0 < (τ.functional b).re :=
    (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hb) hτ0.symm)).1
  have hlo := ENNReal.toReal_mono (directRank_ne_top τ b hb) (normalized_trace_le_rank τ b hb)
  rw [ENNReal.toReal_ofReal (τ.functional.map_nonneg (normalizePositive_nonneg b hb)).1] at hlo
  have he : (τ.functional (normalizePositive b)).re = ‖b‖⁻¹ * (τ.functional b).re := by
    rw [normalizePositive,τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul]
  rw [he] at hlo
  have hi : 1 < ‖b‖⁻¹ := (one_lt_inv₀ hn).mpr hbn
  nlinarith

lemma matrix_approximant_cuntzBelow (hsimple : TopologicallySimple A)
    (hcmp : StrictComparison A) {l : ℕ} [NeZero l] (hl : 1 ≤ l)
    (b : A) (hb : 0 ≤ b) (hb0 : b ≠ 0) (hbn : ‖b‖ < 1)
    (v : MatrixStage A l) (hv : 0 ≤ v)
    (hvupper : ∀ τ : TracialState A, (matrixRank τ v).toReal ≤ (τ.functional b).re) :
    CuntzSubequiv v (scalarCorner hl b) := by
  apply (cuntzSubequiv_completedMatrixInclude_iff A l v (scalarCorner hl b)).mp
  apply hcmp _ _ (completedMatrixInclude_nonneg A l v hv)
    (completedMatrixInclude_nonneg A l _ (scalarCorner_nonneg hl hb))
  · intro hz
    have he : scalarCorner hl b = 0 := (completedMatrixInclude_isometry A l).injective
      (hz.trans (map_zero _).symm)
    exact hb0 ((scalarCorner_injective hl) (he.trans (map_zero _).symm))
  · intro τ
    rw [completedRootRank_include τ l v hv,
      completedRootRank_include τ l _ (scalarCorner_nonneg hl hb),matrixRank_scalarCorner τ hl b hb]
    apply (ENNReal.toReal_lt_toReal (matrixRank_ne_top τ v hv) (directRank_ne_top τ b hb)).mp
    exact (hvupper τ).trans_lt (trace_lt_rank_of_norm_lt_one hsimple τ b hb hb0 hbn)

theorem almost_projection (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hT : Nonempty (TracialState A)) (hcmp : StrictComparison A)
    (b : A) (hb : 0 ≤ b) (hbn : ‖b‖ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : A, p ∈ hereditaryCarrier b ∧ 0 ≤ p ∧ ‖p‖ ≤ 1 ∧
      ∀ τ : TracialState A,
        (τ.functional b).re-2*δ < (τ.functional p).re ∧
        (τ.functional p).re ≤ (τ.functional b).re ∧
        0 ≤ (τ.functional (p-p*p)).re ∧ (τ.functional (p-p*p)).re < 2*δ := by
  by_cases hb0 : b = 0
  · subst b
    refine ⟨0,subset_closure ⟨0,by simp⟩,le_rfl,by simp,?_⟩
    intro τ
    simp only [map_zero,Complex.zero_re,zero_mul,sub_zero]
    exact ⟨by linarith,le_rfl,le_rfl,by linarith⟩
  obtain ⟨l,v,hv,hvapprox⟩ := trace_rank_approximation hsimple hinf hT b hb (δ/2) (by positivity)
  let B := MatrixStage A (l+1)
  let hl : 1 ≤ l+1 := Nat.succ_le_succ (Nat.zero_le _)
  let : NonUnitalContinuousFunctionalCalculus ℝ B IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ B := CStarAlgebra.instNonnegSpectrumClass
  let bM : B := scalarCorner hl b
  have hbM : 0 ≤ bM := scalarCorner_nonneg hl hb
  have hN : 0 < (l+1 : ℕ) := Nat.succ_pos _
  have hNr : 0 < ((l+1 : ℕ) : ℝ) := by exact_mod_cast hN
  let d : ℝ := δ / (l+1 : ℕ)
  have hd : ((l+1 : ℕ) : ℝ)*d = δ := mul_div_cancel₀ δ hNr.ne'
  have hup : ∀ ρ : TracialState B, (normalizedRootRank ρ v).toReal ≤ (ρ.functional bM).re := by
    intro ρ
    let τ := ρ.comap scalarMatrixHom
    have hρ : matrixTracialState τ = ρ := matrixTracialState_comap ρ
    have hr : (matrixRank τ v).toReal = ((l+1 : ℕ) : ℝ) * (normalizedRootRank ρ v).toReal := by
      rw [matrixRank_toReal,Fintype.card_fin,hρ]
    have ht : ((l+1 : ℕ) : ℝ) * (ρ.functional bM).re = (τ.functional b).re := by
      simpa only [hρ] using scalarCorner_trace_scale τ hl b
    have hu := (hvapprox τ).1
    nlinarith
  have hgap : ∀ ρ : TracialState B, (ρ.functional bM).re - 2*d < (normalizedRootRank ρ v).toReal := by
    intro ρ
    let τ := ρ.comap scalarMatrixHom
    have hρ : matrixTracialState τ = ρ := matrixTracialState_comap ρ
    have hr : (matrixRank τ v).toReal = ((l+1 : ℕ) : ℝ) * (normalizedRootRank ρ v).toReal := by
      rw [matrixRank_toReal,Fintype.card_fin,hρ]
    have ht : ((l+1 : ℕ) : ℝ) * (ρ.functional bM).re = (τ.functional b).re := by
      simpa only [hρ] using scalarCorner_trace_scale τ hl b
    have hl := (hvapprox τ).2
    nlinarith
  obtain ⟨η,hη,hηcut⟩ := uniform_direct_positive_cut v hv
    (fun ρ : TracialState B => (ρ.functional bM).re - 2*d)
    ((Complex.continuous_re.comp (TracialState.continuous_eval bM)).sub continuous_const) hgap
  let t := η/3
  have ht : 0 < t := by dsimp [t]; positivity
  have h3 : 3*t = η := by dsimp [t]; ring
  have hcomp := matrix_approximant_cuntzBelow hsimple hcmp hl b hb hb0 hbn v hv
    (fun τ => by have h := (hvapprox τ).1; linarith)
  obtain ⟨x,hx⟩ := (cuntzSubequiv_iff_norm v bM).mp hcomp t ht
  have hs : star (CFC.sqrt bM*x)*(CFC.sqrt bM*x) = star x*bM*x := by
    simp only [star_mul,(CFC.sqrt_nonneg bM).star_eq,mul_assoc]
    rw [←mul_assoc (CFC.sqrt bM),CFC.sqrt_mul_sqrt_self bM hbM]
  obtain ⟨pM,hpMmem,hpM0,hpMn,hpMτ⟩ := direct_scalar_almost_projection_step bM v x hbM hv
    t d ht (by
      change ‖star (CFC.sqrt bM*x)*(CFC.sqrt bM*x)-v‖ < t
      rw [hs,norm_sub_rev]
      exact hx) (by simpa only [h3] using hηcut) hup
  obtain ⟨p,hpmem,hp0,hpe,hpn⟩ := hereditary_scalarCorner_reflect hl b hpMmem hpM0
  refine ⟨p,hpmem,hp0,hpn.trans_le hpMn,?_⟩
  intro τ
  let ρ := matrixTracialState (ι := Fin (l+1)) τ
  obtain ⟨hlo,hhi,hnon,hdef⟩ := hpMτ ρ
  have hbt : ((l+1 : ℕ) : ℝ) * (ρ.functional bM).re = (τ.functional b).re :=
    scalarCorner_trace_scale τ hl b
  have hpt : ((l+1 : ℕ) : ℝ) * (ρ.functional pM).re = (τ.functional p).re := by
    rw [←hpe]; exact scalarCorner_trace_scale τ hl p
  have hpd : ((l+1 : ℕ) : ℝ) * (ρ.functional (pM-pM*pM)).re =
      (τ.functional (p-p*p)).re := by
    rw [←hpe,←map_mul (scalarCorner (A := A) hl),←map_sub (scalarCorner (A := A) hl)]
    exact scalarCorner_trace_scale τ hl (p-p*p)
  refine ⟨?_,?_,?_,?_⟩
  · have hm := mul_lt_mul_of_pos_left hlo hNr
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hhi hNr.le
    nlinarith
  · nlinarith
  · have hm := mul_lt_mul_of_pos_left hdef hNr
    nlinarith

end DirectComparison
end

end OAI
