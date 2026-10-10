import OAI.Analysis.AncientFlat.Regularity.WithinInterpolation
import OAI.Analysis.AncientFlat.Evolution.InitialCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicShort
open ParabolicInterior ParabolicInitial ParabolicInterpolation
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [CompleteSpace E] in
lemma short_sup (h M : ℝ) (hh : 0<h) (hM : 0≤M) (u ut : ℝ → V → E)
    (hd : ∀ p∈slab 2 h, HasDerivWithinAt (fun t => u t p.1) (ut p.2 p.1) (Icc 0 h) p.2)
    (hu0 : ∀ x : V, ‖x‖<2 → u 0 x=0)
    (hut : ∀ p∈slab 2 h, ‖ut p.2 p.1‖≤M) :
    ∀ p∈slab 2 h, ‖u p.2 p.1‖≤h*M := by
  intro p hp
  have he := (convex_Icc (0:ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => u s p.1)
    (fun s hs => hd (p.1,s) ⟨hp.1,hs⟩) (fun s hs => hut (p.1,s) ⟨hp.1,hs⟩)
    (show (0:ℝ)∈Icc 0 h from ⟨le_rfl,hh.le⟩) hp.2
  simp only [hu0 p.1 hp.1,sub_zero,Real.norm_eq_abs,abs_of_nonneg hp.2.1] at he
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hp.2.2 hM])
lemma short_explicit (j : ℕ) (hj : j≤3) (h q M α : ℝ)
    (hh : 0<h) (hq : 0<q) (hq1 : q≤1) (hg : 1+12*q≤2)
    (hM : 0≤M) (hα : 0≤α) (hα1 : α≤1) (u ut : ℝ → V → E)
    (hs : ∀ t∈Icc 0 h, ContDiff ℝ 4 (u t))
    (hd : ∀ p∈slab 2 h, HasDerivWithinAt (fun t => u t p.1) (ut p.2 p.1) (Icc 0 h) p.2)
    (hu0 : ∀ x : V, ‖x‖<2 → u 0 x=0)
    (hut : ∀ p∈slab 2 h, ‖ut p.2 p.1‖≤M)
    (hD : ∀ p∈slab 2 h, ‖iteratedFDeriv ℝ 4 (u p.2) p.1‖≤M) :
    HolderBound α (slab 1 h) (fun p => iteratedFDeriv ℝ j (u p.2) p.1)
      (110*(h*M/q^j+q^(4-j)*M)/q^α) := by
  let v : ℝ → V → E := fun t x => timeAffineExtension 0 h (fun t => u t x) (fun t => ut t x) t
  have he (t : ℝ) (ht : t∈Icc 0 h) : v t=u t :=
    funext (fun x => timeAffineExtension_eq 0 h (fun t => u t x) (fun t => ut t x) ht)
  have hu := short_sup h M hh hM u ut hd hu0 hut
  have hv := lower_parabolic_bound j hj v ut (Icc 0 h) ordConnected_Icc 1 2 q (h*M) M α
    hq hq1 hg (mul_nonneg hh.le hM) hM hα hα1
    (fun t ht => by rw [he t ht]; exact hs t ht)
    (fun t ht x hx => timeAffineExtension_hasDerivAt 0 h hh (fun t => u t x)
      (fun t => ut t x) (fun s hs => hd (x,s) ⟨hx,hs⟩) t ht)
    (fun t ht x hx => hut (x,t) ⟨hx,ht⟩)
    (fun t ht x hx => by rw [he t ht]; exact hu (x,t) ⟨hx,ht⟩)
    (fun t ht x hx => by rw [he t ht]; exact hD (x,t) ⟨hx,ht⟩)
  exact ⟨fun p hp => by simpa only [he p.2 hp.2] using hv.1 p hp,
    fun p hp q hq => by simpa only [he p.2 hp.2,he q.2 hq.2] using hv.2 p hp q hq⟩
end ParabolicShort

end

end OAI
