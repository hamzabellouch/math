import OAI.Analysis.AncientFlat.Evolution.CutoffCore
import OAI.Analysis.AncientFlat.Regularity.CommutatorHolder
import OAI.Analysis.AncientFlat.Regularity.HolderExtension

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicCommutator
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma cutoff_uniform_holder (α : ℝ) (hα : 0<α) (hα1 : α≤1) :
    ∃ A : ℝ, 0<A ∧
      (∀ n : ℕ, n≤4 → HolderBound α univ
        (fun p : V × ℝ => iteratedFDeriv ℝ n (cutoff p.2) p.1) A) ∧
      HolderBound α univ (fun p : V × ℝ => cutoffTime p.2 p.1) A := by
  obtain ⟨A0,h0,H0⟩ := cutoff_jet_holder (V := V) α hα hα1 0
  obtain ⟨A1,h1,H1⟩ := cutoff_jet_holder (V := V) α hα hα1 1
  obtain ⟨A2,h2,H2⟩ := cutoff_jet_holder (V := V) α hα hα1 2
  obtain ⟨A3,h3,H3⟩ := cutoff_jet_holder (V := V) α hα hα1 3
  obtain ⟨A4,h4,H4⟩ := cutoff_jet_holder (V := V) α hα hα1 4
  obtain ⟨At,ht,Ht⟩ := cutoff_time_holder (V := V) α hα hα1
  refine ⟨A0+A1+A2+A3+A4+At,by positivity,?_,Ht.mono (by linarith)⟩
  intro n hn
  interval_cases n
  · exact H0.mono (by linarith)
  · exact H1.mono (by linarith)
  · exact H2.mono (by linarith)
  · exact H3.mono (by linarith)
  · exact H4.mono (by linarith)
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma slab_mem_cylinder_two (p : V × ℝ) (ht : p.2∈Icc (-2) 0) (hx : ‖p.1‖<2) :
    p∈cylinder 2 := by
  refine ⟨hx,?_,ht.2⟩
  norm_num; linarith [ht.1]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedSpace ℝ E] in
lemma cylinder_two_globalize {α H : ℝ} (hα : 0≤α) (hα1 : α≤1) (hH : 0≤H)
    (g : V × ℝ → E) (hg : HolderBound α (cylinder 2) g H)
    (hz : ∀ p, 7/4≤‖p.1‖ → g p=0) :
    HolderBound α {p : V × ℝ | p.2∈Icc (-2) 0} g (5*H) := by
  convert holder_globalize α H H hα hα1 hH hH (Icc (-2) 0) g
    (fun p _ hx => hz p hx)
    (fun p ht hx => hg.1 p (slab_mem_cylinder_two p ht hx))
    (fun p ht hx q hqt hqx => hg.2 p (slab_mem_cylinder_two p ht hx) q
      (slab_mem_cylinder_two q hqt hqx)) using 1; ring
lemma cutoff_regular_holder (α A M : ℝ) (hα : 0≤α) (hα1 : α≤1) (hA : 0≤A) (hM : 0≤M)
    (ha : ∀ n : ℕ, n≤4 → HolderBound α univ
      (fun p : V × ℝ => iteratedFDeriv ℝ n (cutoff p.2) p.1) A)
    (hat : HolderBound α univ (fun p : V × ℝ => cutoffTime p.2 p.1) A)
    (u ut : ℝ → V → E) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hu : ∀ n : ℕ, n≤4 → HolderBound α (cylinder 2)
      (fun p => iteratedFDeriv ℝ n (u p.2) p.1) M)
    (hut : HolderBound α (cylinder 2) (fun p => ut p.2 p.1) M) :
    HolderBound α {p : V × ℝ | p.2∈Icc (-2) 0} (fun p => cutoffValue u p.2 p.1) (160*A*M) ∧
    HolderBound α {p : V × ℝ | p.2∈Icc (-2) 0} (fun p => cutoffDerivative u ut p.2 p.1) (160*A*M) ∧
    HolderBound α {p : V × ℝ | p.2∈Icc (-2) 0}
      (fun p => iteratedFDeriv ℝ 4 (cutoffValue u p.2) p.1) (160*A*M) := by
  have Hχ := (HolderBound.of_jet_zero cutoff (ha 0 (by omega))).restrict (subset_univ (cylinder 2))
  have Hu := HolderBound.of_jet_zero u (hu 0 (by omega))
  have Hv := Hχ.smul Hu hA hM
  have Ht := (Hχ.smul hut hA hM).add ((hat.restrict (subset_univ (cylinder 2))).smul Hu hA hM)
  have Hj : HolderBound α (cylinder 2)
      (fun p => iteratedFDeriv ℝ 4 (cutoffValue u p.2) p.1) (32*A*M) := by
    have Hc := commutator_holder α (cylinder 2) cutoff u A M hA hM
      (fun p _ => (cutoff_contDiff p.2).of_le (by change ((4:ℕ∞):WithTop ℕ∞)≤((⊤:ℕ∞):WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
      (fun p _ => hs p.2) (fun n _ hn => (ha n hn).restrict (subset_univ _))
      (fun n hn => hu n (by omega))
    have H := (Hχ.smul (hu 4 le_rfl) hA hM).add Hc
    convert H using 1
    · funext p; dsimp [ParabolicCommutator.commutator,cutoffValue]; abel
    · ring
  refine ⟨?_,?_,?_⟩
  · exact (cylinder_two_globalize hα hα1 (by positivity) _ Hv
      (fun p hx => by rw [cutoff_zero_space p.2 (by linarith),zero_smul])).mono (by nlinarith [mul_nonneg hA hM])
  · exact (cylinder_two_globalize hα hα1 (by positivity) _ Ht
      (fun p hx => cutoffDerivative_zero u ut p.2 p.1 (by linarith))).mono (by nlinarith [mul_nonneg hA hM])
  · convert cylinder_two_globalize hα hα1 (by positivity) _ Hj
      (fun p hx => cutoff_product_jet_zero 4 p.2 (u p.2) p.1 hx) using 1; ring
end ParabolicLocalization

end

end OAI
