import OAI.Analysis.AncientFlat.Weighted.WeightedSource
import OAI.Analysis.AncientFlat.Weighted.ExactXNorm
import OAI.Analysis.AncientFlat.Profile.RadialRealCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction ENNReal
namespace FlatWeighted
open ParabolicInterior FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma YBound.congr {α w a M : ℝ} {f g : V × ℝ → ℂ} (h : YBound α w a M f)
    (he : ∀ p : V × ℝ, p.2<0 → f p=g p) : YBound α w a M g := by
  intro p hp
  have he' (q : V × ℝ) (hq : q∈localDomain a p) : pullback (w-4) p f q=pullback (w-4) p g q := by
    unfold pullback
    rw [he _ hq.2.2.2]
  obtain ⟨hs,hh⟩ := h p hp
  exact ⟨fun q hq => by rw [←he' q hq]; exact hs q hq,
    fun q hq r hr => by rw [←he' q hq,←he' r hr]; exact hh q hq r hr⟩
lemma YBound.yNorm {α w a M : ℝ} {f : V × ℝ → ℂ} (h : YBound α w a M f) (hM : 0≤M) :
    yNorm α w a f≤ENNReal.ofReal (2*M) := by
  apply iSup_le
  intro p
  exact holderBound_holderNorm hM (h p.val p.property)
lemma finite_yBound {α w a : ℝ} {f : V × ℝ → ℂ} (hf : yNorm α w a f≠⊤) :
    YBound α w a (yNorm α w a f).toReal f :=
  yNorm_YBound ENNReal.toReal_nonneg (by rw [ENNReal.ofReal_toReal hf])
lemma YBound.add {α w a M N : ℝ} {f g : V × ℝ → ℂ}
    (hf : YBound α w a M f) (hg : YBound α w a N g) : YBound α w a (M+N) (f+g) := by
  intro p hp
  change HolderBound α (localDomain a p) (fun q => sigma p^(-(w-4)) • (f (chart p q)+g (chart p q))) (M+N)
  simpa only [smul_add,pullback] using (hf p hp).add (hg p hp)
lemma YBound.const_smul {α w a M : ℝ} {f : V × ℝ → ℂ}
    (hf : YBound α w a M f) (c : ℝ) : YBound α w a (|c| * M) (c • f) := by
  intro p hp
  have he (q : V × ℝ) : pullback (w-4) p (c • f) q=c • pullback (w-4) p f q := by
    simp only [pullback,Pi.smul_apply]
    exact smul_comm _ _ _
  constructor
  · intro q hq
    rw [he,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hf p hp).1 q hq) (abs_nonneg c)
  · intro q hq r hr
    rw [he,he,←smul_sub,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left ((hf p hp).2 q hq r hr) (abs_nonneg c)).trans_eq (by ring)

def sourceSpace (α w a : ℝ) : Submodule ℝ (V × ℝ → ℂ) where
  carrier := {f | yNorm α w a f≠⊤ ∧ (∀ p : V × ℝ, 0≤p.2 → f p=0) ∧
    (∀ t : ℝ, t<0 → Radial (fun x => f (x,t))) ∧
    (∀ t : ℝ, t<0 → RealValued (fun x => f (x,t)))}
  zero_mem' := by
    refine ⟨?_,by simp,by simp [Radial],by simp [RealValued]⟩
    have h : YBound α w a 0 (0 : V × ℝ → ℂ) := by
      intro p hp
      constructor <;> intros <;> simp [pullback]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.yNorm le_rfl)
  add_mem' := by
    intro f g hf hg
    refine ⟨?_,?_,?_,?_⟩
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (((finite_yBound hf.1).add (finite_yBound hg.1)).yNorm (by positivity))
    · intro p hp
      simp [hf.2.1 p hp,hg.2.1 p hp]
    · intro t ht R x
      simp only [Pi.add_apply,hf.2.2.1 t ht R,hg.2.2.1 t ht R]
    · intro t ht x
      simp only [Pi.add_apply,star_add,hf.2.2.2 t ht x,hg.2.2.2 t ht x]
  smul_mem' := by
    intro c f hf
    refine ⟨?_,?_,?_,?_⟩
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (((finite_yBound hf.1).const_smul c).yNorm (by positivity))
    · intro p hp
      simp [hf.2.1 p hp]
    · intro t ht R x
      simp only [Pi.smul_apply,hf.2.2.1 t ht R]
    · intro t ht x
      simp only [Pi.smul_apply,star_smul,star_trivial,hf.2.2.2 t ht x]
def sourceNorm (α w a : ℝ) (f : sourceSpace (V := V) α w a) : ℝ :=
  (yNorm α w a f.val).toReal
lemma sourceNorm_nonneg (α w a : ℝ) (f : sourceSpace (V := V) α w a) : 0≤ sourceNorm α w a f := ENNReal.toReal_nonneg

variable [FiniteDimensional ℝ V]

def sourceLift (γ α a : ℝ) (hγ1 : γ<1/2) (hα : 0<α) (ha : 0<a)
    (f : sourceSpace (V := V) α (-2+4*γ) a) : ℝ →ᵇ C₀(V,ℂ) :=
  Classical.choose ((finite_yBound f.property.1).exists_source_bcf hγ1 hα ha ENNReal.toReal_nonneg)
lemma sourceLift_apply (γ α a : ℝ) (hγ1 : γ<1/2) (hα : 0<α) (ha : 0<a)
    (f : sourceSpace (V := V) α (-2+4*γ) a) (τ : ℝ) (z : V) :
    sourceLift γ α a hγ1 hα ha f τ z=normalizedSource γ f.val τ z :=
  (Classical.choose_spec ((finite_yBound f.property.1).exists_source_bcf hγ1 hα ha ENNReal.toReal_nonneg)).1 τ z
lemma sourceLift_norm (γ α a : ℝ) (hγ1 : γ<1/2) (hα : 0<α) (ha : 0<a)
    (f : sourceSpace (V := V) α (-2+4*γ) a) :
    ‖sourceLift γ α a hγ1 hα ha f‖≤ sourceNorm α (-2+4*γ) a f :=
  (Classical.choose_spec ((finite_yBound f.property.1).exists_source_bcf hγ1 hα ha ENNReal.toReal_nonneg)).2

def sourceLiftLinear (γ α a : ℝ) (hγ1 : γ<1/2) (hα : 0<α) (ha : 0<a) :
    sourceSpace (V := V) α (-2+4*γ) a →ₗ[ℝ] (ℝ →ᵇ C₀(V,ℂ)) where
  toFun := sourceLift γ α a hγ1 hα ha
  map_add' f g := by
    ext τ z
    simp only [sourceLift_apply,normalizedSource,Submodule.coe_add,Pi.add_apply,smul_add,
      BoundedContinuousFunction.add_apply,ZeroAtInftyContinuousMap.add_apply]
  map_smul' c f := by
    ext τ z
    simp only [sourceLift_apply,normalizedSource,Submodule.coe_smul,Pi.smul_apply,
      BoundedContinuousFunction.smul_apply,ZeroAtInftyContinuousMap.smul_apply]
    exact smul_comm _ _ _
end FlatWeighted

end

end OAI
