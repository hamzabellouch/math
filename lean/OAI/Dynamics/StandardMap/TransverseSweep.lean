import OAI.Dynamics.StandardMap.WeightedChart

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma transverse_intersections_unique (x y X Y α β : ℝ)
    (_hα : 0 ≤ α) (hβ : 0 ≤ β) (hsmall : α*β < 1)
    (hx : |x-X| ≤ α*|y-Y|) (hy : |y-Y| ≤ β*|x-X|) : x=X ∧ y=Y := by
  have hyy : |y-Y| ≤ (α*β)*|y-Y| := by
    calc
      _ ≤ β*|x-X| := hy
      _ ≤ β*(α*|y-Y|) := mul_le_mul_of_nonneg_left hx hβ
      _ = _ := by ring
  have he : |y-Y|=0 := by nlinarith [abs_nonneg (y-Y)]
  have hx0 : |x-X|=0 := by rw [he,mul_zero] at hx; exact le_antisymm hx (abs_nonneg _)
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp hx0),sub_eq_zero.mp (abs_eq_zero.mp he)⟩

lemma transverse_sweep_injective (F : ℝ × ℝ → ℝ) (X : ℝ → ℝ) (Θ : ℝ × ℝ → ℝ)
    (I D : Set ℝ) (α β : ℝ) (hI : IsPreconnected I)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsmall : α*β < 1)
    (hX : ∀ y ∈ D, X y ∈ I)
    (hbase : ∀ y ∈ D, Θ (X y,y)=y)
    (hcont : ∀ y ∈ D, ContinuousOn (fun u => Θ (u,y)) I)
    (hlevel : ∀ y ∈ D, ∀ u ∈ I, F (u,Θ (u,y))=F (X y,y))
    (hreg : ∀ y ∈ D, ∀ u ∈ I, ∃ a b : ℝ, b ≠ 0 ∧
      HasStrictFDerivAt F (planeDual a b) (u,Θ (u,y)))
    (hforward : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ α*|y-z|)
    (hbackward : ∀ y ∈ D, ∀ u ∈ I, ∀ v ∈ I, |Θ (u,y)-Θ (v,y)| ≤ β*|u-v|) :
    InjOn (fun z : ℝ × ℝ => (z.1,Θ z)) (I ×ˢ D) := by
  intro z hz w hw he
  have hu : z.1=w.1 := by
    have hh := congrArg (fun v : ℝ × ℝ => v.1) he
    exact hh
  have hθ : Θ (z.1,z.2)=Θ (z.1,w.2) := by
    have hh := congrArg (fun v : ℝ × ℝ => v.2) he
    change Θ (z.1,z.2)=Θ (w.1,w.2) at hh
    rwa [← hu] at hh
  have hLv : F (X z.2,z.2)=F (X w.2,w.2) := by
    rw [← hlevel z.2 hz.2 z.1 hz.1,← hlevel w.2 hw.2 z.1 hz.1,hθ]
  have hc := regular_graphs_coincide F (fun u => Θ (u,z.2)) (fun u => Θ (u,w.2)) I hI
    (hcont z.2 hz.2) (hcont w.2 hw.2) (F (X z.2,z.2)) (hlevel z.2 hz.2)
    (fun u hu => (hlevel w.2 hw.2 u hu).trans hLv.symm) (hreg z.2 hz.2) z.1 hz.1 hθ
  have hby : |z.2-w.2| ≤ β*|X z.2-X w.2| := by
    have hh := hbackward z.2 hz.2 (X z.2) (hX z.2 hz.2) (X w.2) (hX w.2 hw.2)
    have hc' : Θ (X w.2,z.2)=Θ (X w.2,w.2) := hc (hX w.2 hw.2)
    rw [hbase z.2 hz.2,hc',hbase w.2 hw.2] at hh
    exact hh
  have hy := (transverse_intersections_unique (X z.2) z.2 (X w.2) w.2 α β hα hβ hsmall
    (hforward z.2 hz.2 w.2 hw.2) hby).2
  exact Prod.ext hu hy
end StandardMapEntropy

end OAI
