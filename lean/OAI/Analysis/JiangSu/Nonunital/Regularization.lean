import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.QuotientSurjective
import OAI.Analysis.JiangSu.Nonunital.FiniteTraceIdeal

namespace OAI


noncomputable section
namespace NonunitalGamma
open TraceCone Filter Topology CurrentMain Pureness
open scoped ENNReal NNReal ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma NormalizedTrace.norm_apply_le (σ : NormalizedTrace A) (a : A) : ‖σ.functional a‖ ≤ ‖a‖ := by
  exact trace_norm_le σ a

lemma NormalizedTrace.cut_error (σ : NormalizedTrace A) (z : Positive A) (ε : ℝ≥0) :
    0 ≤ (σ.functional z.1).re-(σ.functional (Positive.cut ε z).1).re ∧
      (σ.functional z.1).re-(σ.functional (Positive.cut ε z).1).re ≤ (ε:ℝ) := by
  have hl := σ.functional.monotone (Positive.cut_le ε z)
  constructor
  · exact sub_nonneg.mpr hl.1
  · calc
      (σ.functional z.1).re-(σ.functional (Positive.cut ε z).1).re =
          (σ.functional (z.1-(Positive.cut ε z).1)).re := by rw [map_sub,Complex.sub_re]
      _ ≤ ‖σ.functional (z.1-(Positive.cut ε z).1)‖ := Complex.re_le_norm _
      _ ≤ ‖z.1-(Positive.cut ε z).1‖ := σ.norm_apply_le _
      _ ≤ (ε:ℝ) := Positive.norm_sub_cut_le ε z

lemma bounded_ray_remove_regularization (U : Ultrafilter ℕ) (ν : ℕ → ExtendedTrace A)
    (r : ℕ → ℝ≥0) (σ : ℕ → NormalizedTrace A) (K : ℝ≥0) (hrK : ∀ n, r n ≤ K)
    (heq : ∀ᶠ n in (U : Filter ℕ), ∀ b : Positive A,
      ν n b=(r n:ℝ≥0∞)*ENNReal.ofReal ((σ n).functional b.1).re)
    (R : ℝ) (hr : Tendsto (fun n => (r n:ℝ)) (U : Filter ℕ) (𝓝 R))
    (z : ℕ → Positive A) (M : ℝ) (hz : ∀ n, ‖(z n).1‖ ≤ M)
    (L : ℝ) (hL : Tendsto (fun n => ((σ n).functional (z n).1).re) (U : Filter ℕ) (𝓝 L)) :
    generalizedLimitValue U ν z=ENNReal.ofReal R*ENNReal.ofReal L := by
  have hR : 0 ≤ R := ge_of_tendsto' hr (fun n => (r n).2)
  have hM : 0 ≤ M := (norm_nonneg (z 0).1).trans (hz 0)
  let f := fun n => (r n:ℝ)*((σ n).functional (z n).1).re
  have hf : Tendsto f (U : Filter ℕ) (𝓝 (R*L)) := hr.mul hL
  let g := fun (ε : ℝ≥0) n => (r n:ℝ)*((σ n).functional (Positive.cut ε (z n)).1).re
  have hgpos (ε : ℝ≥0) (n : ℕ) : 0 ≤ g ε n :=
    mul_nonneg (r n).2 (((σ n).functional.map_nonneg (Positive.cut ε (z n)).2).1)
  have hgbound (ε : ℝ≥0) (n : ℕ) : ‖g ε n‖ ≤ (K:ℝ)*M := by
    rw [Real.norm_of_nonneg (hgpos ε n)]
    apply mul_le_mul (by exact_mod_cast hrK n) ?_ (((σ n).functional.map_nonneg (Positive.cut ε (z n)).2).1) K.2
    calc
      ((σ n).functional (Positive.cut ε (z n)).1).re ≤
          ‖(σ n).functional (Positive.cut ε (z n)).1‖ := Complex.re_le_norm _
      _ ≤ ‖(Positive.cut ε (z n)).1‖ := (σ n).norm_apply_le _
      _ ≤ ‖(z n).1‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
        (Positive.cut_le ε (z n)) (Positive.cut ε (z n)).2
      _ ≤ M := hz n
  let l := fun ε => limUnder (U : Filter ℕ) (g ε)
  have hgl (ε : ℝ≥0) : Tendsto (g ε) (U : Filter ℕ) (𝓝 (l ε)) :=
    bounded_ultrafilter_tendsto U _ ((K:ℝ)*M) (hgbound ε)
  have hcut (ε : ℝ≥0) : limUnder (U : Filter ℕ) (fun n => ν n (Positive.cut ε (z n)))=
      ENNReal.ofReal (l ε) := by
    apply tendsto_nhds_unique (ennreal_ultrafilter_tendsto U _)
    apply (ENNReal.tendsto_ofReal (hgl ε)).congr'
    filter_upwards [heq] with n hn
    change ENNReal.ofReal ((r n:ℝ)*((σ n).functional (Positive.cut ε (z n)).1).re)=ν n (Positive.cut ε (z n))
    rw [hn]
    exact (ENNReal.ofReal_mul (r n).coe_nonneg).trans
      (congrArg (fun t : ℝ≥0∞ => t*ENNReal.ofReal ((σ n).functional (Positive.cut ε (z n)).1).re)
        (ENNReal.ofReal_coe_nnreal (p := r n)))
  have hle (ε : ℝ≥0) : l ε ≤ R*L := by
    apply le_of_tendsto_of_tendsto (hgl ε) hf
    exact Eventually.of_forall fun n => mul_le_mul_of_nonneg_left
      (sub_nonneg.mp ((σ n).cut_error (z n) ε).1) (r n).2
  have herr (ε : ℝ≥0) : R*L ≤ l ε+(K:ℝ)*(ε:ℝ) := by
    apply le_of_tendsto_of_tendsto hf ((hgl ε).add_const _)
    apply Eventually.of_forall
    intro n
    have hd := ((σ n).cut_error (z n) ε).2
    have hm := mul_le_mul_of_nonneg_left hd (r n).2
    have hk := mul_le_mul_of_nonneg_right (show (r n:ℝ) ≤ K by exact_mod_cast hrK n) ε.2
    dsimp only [f,g]
    rw [mul_sub] at hm
    simp only [NNReal.toReal] at hm hk ⊢
    linarith
  have hvle : generalizedLimitValue U ν z ≤ ENNReal.ofReal (R*L) := by
    apply iSup_le fun ε => iSup_le fun _ => ?_
    rw [hcut]
    exact ENNReal.ofReal_le_ofReal (hle ε)
  have hvfinite : generalizedLimitValue U ν z ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvle
  rw [←ENNReal.ofReal_mul hR]
  refine le_antisymm hvle ?_
  apply (ENNReal.ofReal_le_iff_le_toReal hvfinite).mpr
  apply le_of_forall_pos_le_add
  intro η hη
  let ε : ℝ≥0 := ⟨η/((K:ℝ)+1),by positivity⟩
  have hε : 0 < ε := by change 0 < η/((K:ℝ)+1);positivity
  have hcut_le : ENNReal.ofReal (l ε) ≤ generalizedLimitValue U ν z := by
    rw [←hcut]
    exact le_iSup_of_le ε (le_iSup_of_le hε le_rfl)
  have hlv : l ε ≤ (generalizedLimitValue U ν z).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hvfinite).mp hcut_le
  have hεK : (K:ℝ)*(ε:ℝ) ≤ η := by
    change (K:ℝ)*(η/((K:ℝ)+1)) ≤ η
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith [herr ε]

theorem generalized_limit_finite_multiple [Nonempty (NormalizedTrace A)]
    [CompactSpace (NormalizedTrace A)] (U : Ultrafilter ℕ)
    (hsimple : TopologicallySimple A) (hcone : AllDenselyFiniteTracesBounded A)
    (ν : ℕ → ExtendedTrace A) (a : Positive A) (ha0 : a.1≠0)
    (ha : generalizedLimitValue U ν (fun _ => a)<∞) :
    ∃ R : ℝ≥0, ∃ σ : ℕ → NormalizedTrace A,
      ∀ (z : lp (fun _ : ℕ => A) ∞) (hz : ∀ n, 0 ≤ z n),
        generalizedLimitValue U ν (fun n => ⟨z n,hz n⟩)=(R:ℝ≥0∞)*
          ENNReal.ofReal ((familyLimitTrace (fun t : NormalizedTrace A => t.unitized) U σ).functional
            (sequenceQuotientMap (A := A) U z)).re := by
  obtain ⟨K,r,σ,hrK,heq⟩ := generalized_eventually_bounded_rays U hsimple hcone ν a ha0 ha
  let R := limUnder (U : Filter ℕ) (fun n => (r n:ℝ))
  have hr : Tendsto (fun n => (r n:ℝ)) (U : Filter ℕ) (𝓝 R) :=
    bounded_ultrafilter_tendsto U (fun n => (r n:ℝ)) (K:ℝ) (fun n => by
      rw [Real.norm_of_nonneg (r n).coe_nonneg]
      exact_mod_cast hrK n)
  have hR : 0 ≤ R := ge_of_tendsto' hr (fun n => (r n).2)
  refine ⟨⟨R,hR⟩,σ,?_⟩
  intro z hz
  have hL := Complex.continuous_re.continuousAt.tendsto.comp (familyLimitTrace_tendsto (fun t : NormalizedTrace A => t.unitized) U σ (boundedInr (A := A) z))
  simp only [boundedInr_apply,NormalizedTrace.unitized_inr] at hL
  have h := bounded_ray_remove_regularization U ν r σ K hrK heq R hr
    (fun n => ⟨z n,hz n⟩) ‖z‖ (fun n => lp.norm_apply_le_norm ENNReal.top_ne_zero z n) _ hL
  have hc := ENNReal.ofReal_eq_coe_nnreal hR
  rw [hc] at h
  exact h

end NonunitalGamma

end

end OAI
