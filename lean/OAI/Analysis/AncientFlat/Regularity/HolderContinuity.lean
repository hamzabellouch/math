import OAI.Analysis.AncientFlat.Regularity.HolderAlgebra

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace ParabolicInterior
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E]
lemma continuous_pdist (q : V × ℝ) : Continuous (fun p => pdist p q) := by
  unfold pdist
  exact (continuous_fst.sub continuous_const).norm.add
    (((continuous_snd.sub continuous_const).abs).rpow_const (by intro p; right; norm_num))
lemma pdist_self (p : V × ℝ) : pdist p p=0 := by simp [pdist]
lemma HolderBound.continuousOn {α K : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E}
    (h : HolderBound α Ω f K) (hα : 0<α) : ContinuousOn f Ω := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have ht : Tendsto (fun q => K*pdist q p^α) (𝓝[Ω] p) (𝓝 0) := by
    have hc : Continuous (fun q => K*pdist q p^α) := continuous_const.mul
      ((continuous_pdist p).rpow_const (by intro q; exact Or.inr hα.le))
    simpa only [pdist_self,Real.zero_rpow hα.ne',mul_zero] using (hc.tendsto p).mono_left (nhdsWithin_le_nhds : 𝓝[Ω] p≤𝓝 p)
  exact squeeze_zero' (Eventually.of_forall (fun q => norm_nonneg _))
    (mem_of_superset self_mem_nhdsWithin (fun q hq => h.2 q hq p hp)) ht
lemma HolderBound.spatial {α K : ℝ} {I : Set ℝ} {f : V × ℝ → E}
    (h : HolderBound α {p | p.2∈I} f K) {t : ℝ} (ht : t∈I) (x y : V) :
    ‖f (x,t)-f (y,t)‖≤K*‖x-y‖^α := by
  simpa [pdist] using h.2 (x,t) ht (y,t) ht
lemma HolderBound.temporal {α K : ℝ} {I : Set ℝ} {f : V × ℝ → E}
    (h : HolderBound α {p | p.2∈I} f K) {s t : ℝ} (hs : s∈I) (ht : t∈I) (x : V) :
    ‖f (x,s)-f (x,t)‖≤K*|s-t|^(α/4) := by
  have hh := h.2 (x,s) hs (x,t) ht
  simpa only [pdist,sub_self,norm_zero,zero_add,←Real.rpow_mul (abs_nonneg _),
    show (1:ℝ)/4*α=α/4 by ring] using hh
lemma continuousOn_bcf_of_holder (α K : ℝ) (hα : 0<α) (hK : 0≤K)
    (I : Set ℝ) (u : ℝ → (V →ᵇ E))
    (h : HolderBound α {p : V × ℝ | p.2∈I} (fun p => u p.2 p.1) K) :
    ContinuousOn u I := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hpow : 0<α/4 := by positivity
  have hb (s : ℝ) (hs : s∈I) : ‖u s-u t‖≤K*|s-t|^(α/4) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    exact h.temporal hs ht x
  have hc : Continuous (fun s : ℝ => K*|s-t|^(α/4)) := continuous_const.mul
    ((continuous_id.sub continuous_const).abs.rpow_const (by intro; exact Or.inr hpow.le))
  have hl : Tendsto (fun s : ℝ => K*|s-t|^(α/4)) (𝓝[I] t) (𝓝 0) := by
    simpa only [sub_self,abs_zero,Real.zero_rpow hpow.ne',mul_zero] using
      (hc.tendsto t).mono_left (nhdsWithin_le_nhds : 𝓝[I] t≤𝓝 t)
  exact squeeze_zero' (Eventually.of_forall (fun s => norm_nonneg _))
    (mem_of_superset self_mem_nhdsWithin hb) hl
lemma continuousOn_c0_of_holder (α K : ℝ) (hα : 0<α) (hK : 0≤K)
    (I : Set ℝ) (u : ℝ → C₀(V,E))
    (h : HolderBound α {p : V × ℝ | p.2∈I} (fun p => u p.2 p.1) K) :
    ContinuousOn u I := by
  exact (ZeroAtInftyContinuousMap.isometry_toBCF (α := V) (β := E)).isEmbedding.continuousOn_iff.mpr
    (continuousOn_bcf_of_holder α K hα hK I (fun t => (u t).toBCF) h)
end ParabolicInterior

end

end OAI
