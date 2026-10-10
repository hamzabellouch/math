import OAI.Analysis.AncientFlat.Geometry.ExtensionHolder
import OAI.Analysis.AncientFlat.Evolution.FiniteScaling
import OAI.Analysis.AncientFlat.Weighted.ExactXNorm

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma holder_normBox_pullback {α w a M : ℝ} {f : V × ℝ → ℂ} {p : V × ℝ}
    (hs : sigma p=1) (hh : HolderBound α (normBox a p) f M) :
    HolderBound α (localDomain a p) (pullback w p f) M := by
  have he (q : V × ℝ) : pullback w p f q=f (chart p q) := by simp only [pullback,hs,Real.one_rpow,one_smul]
  constructor
  · intro q hq
    rw [he]
    exact hh.1 _ (mem_image_of_mem _ hq)
  · intro q hq r hr
    rw [he,he]
    have h := hh.2 _ (mem_image_of_mem _ hq) _ (mem_image_of_mem _ hr)
    simpa only [chart_pdist,hs,one_mul] using h
lemma extension_YBound {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ)
    {α w a T M K : ℝ} {f : V × ℝ → ℂ} (hf : FiniteYBound α w a T M f)
    (hα : 0≤α) (hw : w≤4) (hT : 0<T) (ha : 0<a) (ha1 : a≤1/16) (hM : 0≤M) (hK : 0≤K)
    (hk : ∀ T : ℝ, 0<T → ∀ p : V × ℝ, p.2<0 → sigma p=1 →
      HolderBound α (normBox a p) (extensionWeight ψ T) K) :
    YBound α w a (2*K*(((1:ℝ)/8)^(w-4)+((1:ℝ)/8)^(w-4)*((1:ℝ)/8)^(-α)+
        2*((1:ℝ)/8)^(w-4)/(a*((1:ℝ)/8))^α)*M) (innerExtension ψ T f) := by
  intro p hp
  obtain ⟨r,hr,q,hq,hs,rfl⟩ := normalize_sigma p hp
  have hTr : 0<T/r^4 := div_pos hT (pow_pos hr _)
  have hh := (hf.scale r hr).extension_normBox hψ hα hw hTr ha ha1 hM hK q hq hs (hk _ hTr q hq hs)
  have ht := holder_normBox_pullback (w := w-4) hs hh
  rw [←innerExtension_scale ψ (w-4) T r hr f] at ht
  simpa only [←localDomain_scale a r hr q, pullback_scale (w-4) r hr q hq] using ht

theorem innerExtension_bound (ψ : ℝ → ℝ) (hψ : ExtensionCutoff ψ)
    (δ α a : ℝ) (hδ : 0<δ) (hδ1 : δ<1) (hα : 0<α) (hα1 : α<1)
    (ha : 0<a) (ha1 : a≤1/16) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 0<T → ∀ f : V × ℝ → ℂ,
      finiteYNorm α (-2+2*δ) a T f≠⊤ →
      yNorm α (-2+2*δ) a (innerExtension ψ T f)≤
        ENNReal.ofReal C*finiteYNorm α (-2+2*δ) a T f := by
  let w := -2+2*δ
  have hw : w ∈ Ioo (-2) 0 := by
    dsimp [w]
    constructor <;> linarith [hδ, hδ1]
  let C0 := ((1:ℝ)/8)^(w-4)+((1:ℝ)/8)^(w-4)*((1:ℝ)/8)^(-α)+2*((1:ℝ)/8)^(w-4)/(a*((1:ℝ)/8))^α
  have hC : 0<C0 := by dsimp [C0]; positivity
  obtain ⟨K,hK,hk⟩ := extensionWeight_normBox (V := V) hψ α hα hα1.le
  refine ⟨4*K*C0,by positivity,?_⟩
  intro T hT f hf
  have hbound := extension_YBound hψ (finiteYNorm_finite_bound hf) hα.le
    (hw.2.le.trans (by norm_num)) hT ha ha1 ENNReal.toReal_nonneg hK.le
    (fun T hT p hp hs => hk T a hT ha ha1 p hp hs)
  have hN : yNorm α w a (innerExtension ψ T f)≤
      ENNReal.ofReal (2*(2*K*C0*(finiteYNorm α w a T f).toReal)) := by
    apply iSup_le
    intro p
    exact holderBound_holderNorm (by positivity) (hbound p.val p.property)
  calc
    _ ≤ ENNReal.ofReal (2*(2*K*C0*(finiteYNorm α w a T f).toReal)) := hN
    _ = ENNReal.ofReal (4*K*C0)*finiteYNorm α w a T f := by
      rw [show 2*(2*K*C0*(finiteYNorm α w a T f).toReal)=(4*K*C0)*(finiteYNorm α w a T f).toReal by ring,
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hf]
end FlatWeighted

end

end OAI
