import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CutAttachedEndH1

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma fullEnd_partition_jet (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b κ : ℝ) {D : Set (Fin 3 → ℝ)}
    {χ η : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    (hpart : ∀ x∈D,(fun y => χ y+η y)=ᶠ[𝓝 x] (fun _ => 1))
    (hpos : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → 0<a*(sourceCollarTime (WithLp.ofLp x)-b))
    (u v z : H1)
    (hue : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u x=χ (WithLp.ofLp x)*(attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient u x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*(attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1))
    (hve : ∀ᵐ x∂ballMeasure,
      weakValue v x=κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))) ∧
      ∀ i,weakGradient v x i=κ*(fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))+
        χ (WithLp.ofLp x)*(if 0<a*(sourceCollarTime (WithLp.ofLp x)-b) then
          fderiv ℝ (fun y => a*(sourceCollarTime y-b)) (WithLp.ofLp x) (Pi.single i 1) else 0)))
    (hze : ∀ᵐ x∂ballMeasure,
      weakValue z x=η (WithLp.ofLp x)*fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient z x i=
        fderiv ℝ η (WithLp.ofLp x) (Pi.single i 1)*fullAttachedEndValue s f a b κ (WithLp.ofLp x)+
        η (WithLp.ofLp x)*fullAttachedEndGradient s f a b κ (WithLp.ofLp x) i) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue (u+v+z) x=fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient (u+v+z) x i=fullAttachedEndGradient s f a b κ (WithLp.ofLp x) i := by
  filter_upwards [hue,hve,hze,hpos,weakValue_add u v,weakValue_add (u+v) z,
    weakGradient_add u v,weakGradient_add (u+v) z] with x hux hvx hzx hnx hv₀ hv₁ hg₀ hg₁ hx
  have ht := hnx hx
  have hpu := (hpart (WithLp.ofLp x) hx).self_of_nhds
  change χ (WithLp.ofLp x)+η (WithLp.ofLp x)=1 at hpu
  have hpd : ∀ i : Fin 3,
      fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)+
      fderiv ℝ η (WithLp.ofLp x) (Pi.single i 1)=0 := by
    have hd : fderiv ℝ (fun y => χ y+η y) (WithLp.ofLp x)=0 := by
      rw [(hpart (WithLp.ofLp x) hx).fderiv_eq]
      exact fderiv_const_apply (1:ℝ)
    change fderiv ℝ (χ+η) (WithLp.ofLp x)=0 at hd
    rw [fderiv_add (hχ.differentiable (by simp) _) (hη.differentiable (by simp) _)] at hd
    intro i
    exact congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hd
  constructor
  · rw [hv₁]
    simp only [Pi.add_apply]
    rw [hv₀]
    simp only [Pi.add_apply]
    rw [(hux hx).1,hvx.1,hzx.1,max_eq_right ht.le]
    dsimp only [fullAttachedEndValue]
    calc
      _=(χ (WithLp.ofLp x)+η (WithLp.ofLp x))*
        ((attachedEndPoissonField s (f) a b 0 (WithLp.ofLp x)).re+
         κ*(a*(sourceCollarTime (WithLp.ofLp x)-b))) := by ring
      _=_ := by rw [hpu,one_mul]
  · intro i
    rw [hg₁]
    simp only [Pi.add_apply]
    rw [hg₀]
    simp only [Pi.add_apply,WithLp.ofLp_add]
    rw [(hux hx).2 i,hvx.2 i,hzx.2 i,max_eq_right ht.le,ite_eq_left ht]
    dsimp only [fullAttachedEndValue,fullAttachedEndGradient]
    calc
      _=(fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)+
          fderiv ℝ η (WithLp.ofLp x) (Pi.single i 1))*
        ((attachedEndPoissonField s (f) a b 0 (WithLp.ofLp x)).re+
          κ*(a*(sourceCollarTime (WithLp.ofLp x)-b)))+
        (χ (WithLp.ofLp x)+η (WithLp.ofLp x))*
        (fderiv ℝ (fun y => (attachedEndPoissonField s (f) a b 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1)+
          κ*fderiv ℝ (fun y => a*(sourceCollarTime y-b))
            (WithLp.ofLp x) (Pi.single i 1)) := by ring
      _=_ := by rw [hpd i,hpu,zero_mul,one_mul,zero_add]

end ScalarConductivity

end

end OAI
