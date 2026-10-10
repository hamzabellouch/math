import OAI.Analysis.TracialSplitting.FullProjections

namespace OAI

universe uA uD


section

noncomputable section

noncomputable section

noncomputable section

open Filter Topology

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section SmallFullProjection

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma full_of_complement_bound (hsimple : TopologicallySimple A)
    (ι : A →⋆ₐ[ℂ] D) {b : A} (hb : 0 ≤ b) (hbn : ‖b‖ = 1)
    {g : D} (hg : IsStarProjection g) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (hc : (1-g) * ι b * (1-g) ≤ α • (1-g)) : IsFull g := by
  by_contra hn
  let J := ClosedSelfAdjointSpan.ideal hg.isSelfAdjoint
  let : Nontrivial J.Quotient := ClosedSelfAdjointSpan.nontrivial_quotient hg.isSelfAdjoint hn
  let π := J.quotientStarHom
  have hπg : π g = 0 := ClosedSelfAdjointSpan.quotientMap_g hg.isSelfAdjoint
  have hπr : π (1-g) = 1 := by rw [map_sub,map_one,hπg,sub_zero]
  have hπc := map_rel π hc
  have hπsmul : π (α • (1-g)) = algebraMap ℂ J.Quotient (α : ℂ) * π (1-g) := by
    rw [Algebra.smul_def,map_mul]
    congr 1
  simp only [map_mul,hπsmul,hπr,one_mul,mul_one] at hπc
  have hπb : 0 ≤ π (ι b) := map_nonneg π (map_nonneg ι hb)
  have hnrm : ‖π (ι b)‖ ≤ α := (CStarAlgebra.norm_le_iff_le_algebraMap _ hα hπb).mpr (by
    exact hπc)
  have hfaith := simple_starAlgHom_injective hsimple (π.comp ι)
  have he := NonUnitalStarAlgHom.norm_map (π.comp ι) hfaith b
  change ‖π (ι b)‖ = ‖b‖ at he
  rw [he,hbn] at hnrm
  exact (not_le_of_gt hα1) hnrm

theorem small_full_projections (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (ι : A →⋆ₐ[ℂ] D)
    (hRR : RealRankZero D) (hT : Nonempty (TracialState D))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ := by
  classical
  let := hT
  have hTA : Nonempty (TracialState A) := ⟨pullbackTrace (Classical.choice hT) ι⟩
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0 < (3/8 : ℝ)*δ by positivity)
  obtain ⟨b,hb,hbn,hbτ⟩ := small_positive hsimple hinf hTA (n+1) (by omega)
  have hbD : 0 ≤ ι b := map_nonneg ι hb
  obtain ⟨g,hg,hl,hu⟩ := exists_spectral_cut hRR (IsSelfAdjoint.of_nonneg hbD)
    (1/2 : ℝ) (show (0 : ℝ) < 1/8 by norm_num)
  norm_num at hl hu
  refine ⟨g,hg,full_of_complement_bound hsimple ι hb hbn hg
    (by norm_num : (0 : ℝ) ≤ 5/8) (by norm_num) hu,?_⟩
  have ht (τ : TracialState D) : (τ.functional g).re ≤ (8/3 : ℝ) * (1/(n+1 : ℝ)) := by
    have h1 := (τ.functional.monotone hl).1
    change (τ.functional ((3/8 : ℝ) • g)).re ≤ (τ.functional (g * ι b * g)).re at h1
    rw [τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul,
      trace_projection_corner τ hg] at h1
    have h2 := trace_mul_mono_left τ hbD hg.le_one
    rw [one_mul] at h2
    have h3 := hbτ (pullbackTrace τ ι)
    change (τ.functional (ι b)).re ≤ 1 / ((n+1 : ℕ) : ℝ) at h3
    simp only [Nat.cast_add,Nat.cast_one] at h3
    linarith
  exact (ciSup_le ht).trans_lt (by linarith)

end SmallFullProjection

end CurrentMain

end

end

end

end

end OAI
