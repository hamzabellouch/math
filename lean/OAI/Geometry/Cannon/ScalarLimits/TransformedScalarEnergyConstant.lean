import Mathlib
import OAI.Geometry.Cannon.Energy.MeshEnergy
import OAI.Geometry.Cannon.ScalarLimits.OscillationPairwise
import OAI.Geometry.Cannon.Energy.Extend
import OAI.Geometry.Cannon.Flows.OscillationMonoRange

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open Set Filter Topology TopologicalSpace Metric

namespace CannonApprox

open CannonGrid CannonLevel CannonChart CannonPacking CannonScalarEnergy CannonCrossEnergy
open Set Metric Filter Topology

theorem exists_transformed_scalar_energy_constant {X : Type*} [MetricSpace X]
    (Q : ℕ) (CP L J B b : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hL : 1 ≤ L) (hJ : 0 < J) (hB : 0 < B) (hb : 0 < b)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (e : Square → X), IsEmbedding e →
      ∀ (g : X ≃ₜ X), (∀ x y, b*dist x y ≤ dist (g.symm x) (g.symm y)) →
        (∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y) →
      ∀ {α β : Type*} [Fintype α] [Fintype β] (centers : α → X) (q : β → X) (r : ℝ),
        0 < r → max (L*(L*(B*J)+1)+3) (max 1 b)*r ≤ 1 →
        (∀ i j, i ≠ j → r ≤ dist (centers i) (centers j)) →
        (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
        (∀ i, ball (g.symm (centers i)) (L*(L*(B*J)+1)*r) ⊆ range e) →
        ∀ (ρ : β → ℝ), (∀ i, 0 ≤ ρ i) →
          Admissible (fun i => e ⁻¹' ball (q i) (2*r)) ρ →
        ∀ (n : ℕ) (hn : 0 < n),
        (∀ z : Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
          dist (e z) (e (vertex (3*n) (by omega) i)) < r) →
        (∑ i, (oscillation
          ((extend e (scalar (fun j => e ⁻¹' ball (q j) (2*r)) ρ n hn)) ∘ g.symm)
          (closedBall (centers i) (J*r)))^2) ≤ E*(∑ j, (ρ j)^2) := by
  obtain ⟨E,hE,hbound⟩ := exists_scalar_energy_constant Q CP L (B*J) b
    hpack hCP hL (mul_pos hB hJ) hb hpaths
  refine ⟨E,hE,?_⟩
  intro e he g hglower hgupper α β _ _ centers q r hr hscale hc hq hchart ρ hρ hadm n hn hmesh
  let f := scalar (fun j => e ⁻¹' ball (q j) (2*r)) ρ n hn
  have hf : Continuous f := (scalar_properties _ ρ hρ hadm n hn).1
  have hsep (i j : α) (hij : i ≠ j) : b*r ≤ dist (g.symm (centers i)) (g.symm (centers j)) :=
    (mul_le_mul_of_nonneg_left (hc i j hij) hb.le).trans (hglower _ _)
  apply le_trans _ (hbound e he (g.symm ∘ centers) q r hr hscale hsep hq hchart
    ρ hρ hadm n hn hmesh)
  apply Finset.sum_le_sum
  intro i _
  let S := closedBall (centers i) (J*r)
  let T := e ⁻¹' closedBall (g.symm (centers i)) (B*J*r)
  have hT : IsCompact T := (isClosed_closedBall.preimage he.continuous).isCompact
  have hsub : ((extend e f) ∘ g.symm) '' S ⊆ f '' T := by
    rintro v ⟨z,hz,rfl⟩
    have hdist : dist (g.symm z) (g.symm (centers i)) ≤ B*J*r := by
      exact (hgupper z (centers i)).trans (by
        have hh := mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) hB.le
        nlinarith)
    have hinside : g.symm z ∈ range e := by
      apply hchart i
      rw [mem_ball]
      have hLpos : 0 < L := zero_lt_one.trans_le hL
      have hBJ : 0 < B*J := mul_pos hB hJ
      have hstep : B*J ≤ L*(B*J) := by nlinarith
      have hprod : B*J ≤ L*(L*(B*J)) :=
        hstep.trans (mul_le_mul_of_nonneg_left hstep hLpos.le)
      exact hdist.trans_lt (mul_lt_mul_of_pos_right (by nlinarith) hr)
    obtain ⟨w,hw⟩ := hinside
    refine ⟨w,by simpa only [T,mem_preimage,mem_closedBall,hw] using hdist,?_⟩
    rw [Function.comp_apply,← hw,extend_apply e he.injective]
  have hh := oscillation_mono_range (f := (extend e f) ∘ g.symm) (g := f)
    (S := S) (T := T) ⟨centers i,mem_closedBall_self (mul_nonneg hJ.le hr.le)⟩
    (hT.image hf).bddAbove (hT.image hf).bddBelow hsub
  exact pow_le_pow_left₀ hh.1 hh.2 2

end CannonApprox

namespace CannonApprox

open CannonGrid CannonLevel CannonChart CannonPacking CannonScalarEnergy CannonCrossEnergy
open Set Metric Filter Topology

theorem transformed_scalar_energy_tail {X : Type*} [MetricSpace X] [CompactSpace X]
    (Q : ℕ) (CP L J B b : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hL : 1 ≤ L) (hJ : 0 < J) (hB : 0 < B) (hb : 0 < b)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (e : Square → X) (he : IsEmbedding e) (g : X ≃ₜ X)
    (hglower : ∀ x y, b*dist x y ≤ dist (g.symm x) (g.symm y))
    (hgupper : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (ρ : ∀ n, ι n → ℝ) (hρ : ∀ n i, 0 ≤ ρ n i)
    (hadm : ∀ n, Admissible (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n))
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (hmesh : ∀ n z, ∀ i : Index (3*m n), weight (3*m n) z i ≠ 0 →
      dist (e z) (e (vertex (3*m n) (by have := hm n; omega) i)) < r n)
    (M : ℕ → ℝ) (hMlim : Tendsto M atTop atTop) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ n, (∑ i, (ρ n i)^2) ≤ A/M n) (K : Set X)
    (hK : IsCompact K) (hKU : K ⊆ g '' interior (range e)) :
    let F := fun n => (extend e
      (scalar (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n) (m n) (hm n))) ∘ g.symm
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ᶠ n in atTop,
        (∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
          closedBall (p n i) (J*r n) ⊆ g '' interior (range e)) ∧
        meshEnergy (p n) (r n) J (F n) K ≤ D/M n) ∧
      Tendsto (fun n => meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 0) := by
  classical
  let F := fun n => (extend e
    (scalar (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n) (m n) (hm n))) ∘ g.symm
  obtain ⟨E,hE,hbound⟩ := exists_transformed_scalar_energy_constant Q CP L J B b
    hpack hCP hL hJ hB hb hpaths
  let K₀ := g.symm '' K
  have hK₀ : IsCompact K₀ := hK.image g.symm.continuous
  have hK₀U : K₀ ⊆ interior (range e) := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨w,hw,hwz⟩ := hKU hz
    simpa only [← hwz,g.symm_apply_apply] using hw
  obtain ⟨δ,hδ,hδU⟩ := hK₀.exists_thickening_subset_open isOpen_interior hK₀U
  let T := L*(L*(B*J)+1)
  let S := max (T+3) (max 1 b)
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hBJ : 0 < B*J := mul_pos hB hJ
  have hstep : B*J ≤ L*(B*J) := by nlinarith
  have hprod : B*J ≤ L*(L*(B*J)) :=
    hstep.trans (mul_le_mul_of_nonneg_left hstep hLpos.le)
  have hT : B*J < T := by dsimp [T]; nlinarith
  have hsmall₁ : ∀ᶠ n in atTop, S*r n < 1 := by
    have ht : Tendsto (fun n => S*r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
        Tendsto (fun n => S*r n) atTop (𝓝 (S*0)))
    exact ht.eventually_lt_const zero_lt_one
  have hsmall₂ : ∀ᶠ n in atTop, (T+2*B)*r n < δ := by
    have ht : Tendsto (fun n => (T+2*B)*r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
        Tendsto (fun n => (T+2*B)*r n) atTop (𝓝 ((T+2*B)*0)))
    exact ht.eventually_lt_const hδ
  have htail : ∀ᶠ n in atTop,
      (∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
        closedBall (p n i) (J*r n) ⊆ g '' interior (range e)) ∧
      meshEnergy (p n) (r n) J (F n) K ≤ (E*A)/M n := by
    filter_upwards [hsmall₁,hsmall₂] with n hn₁ hn₂
    have hnear (i : ι n) (hi : (ball (p n i) (2*r n) ∩ K).Nonempty) :
        ball (g.symm (p n i)) (T*r n) ⊆ interior (range e) := by
      obtain ⟨z,hzi,hzK⟩ := hi
      intro w hw
      apply hδU
      refine mem_thickening_iff.mpr ⟨g.symm z,⟨z,hzK,rfl⟩,?_⟩
      have hzdist : dist (g.symm (p n i)) (g.symm z) < B*(2*r n) :=
        (hgupper _ _).trans_lt (mul_lt_mul_of_pos_left (by
          simpa only [mem_ball,dist_comm] using hzi) hB)
      exact (dist_triangle w (g.symm (p n i)) (g.symm z)).trans_lt
        ((add_lt_add (mem_ball.mp hw) hzdist).trans_le (by nlinarith))
    refine ⟨?_,?_⟩
    · intro i hi z hz
      have hdz : dist (g.symm z) (g.symm (p n i)) < T*r n := by
        apply (hgupper _ _).trans_lt
        exact (mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) hB.le).trans_lt
          (by have hh := mul_lt_mul_of_pos_right hT (hr n); nlinarith)
      exact ⟨g.symm z,hnear i hi (mem_ball.mpr hdz),g.apply_symm_apply z⟩
    · let α := {i : ι n // (ball (p n i) (2*r n) ∩ K).Nonempty}
      have hcenters (i j : α) (hij : i ≠ j) : r n ≤ dist (p n i.val) (p n j.val) :=
        hpsep n i.val j.val (fun h => hij (Subtype.ext h))
      have hh := hbound e he g hglower hgupper (fun i : α => p n i.val) (p n) (r n)
        (hr n) hn₁.le hcenters (hpsep n) (fun i => (hnear i.val i.property).trans interior_subset)
        (ρ n) (hρ n) (hadm n) (m n) (hm n) (hmesh n)
      exact hh.trans ((mul_le_mul_of_nonneg_left (henergy n) hE).trans_eq (by ring))
  refine ⟨E*A,mul_nonneg hE hA,htail,?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun n => meshEnergy_nonneg _ _ _ _ _))
    (htail.mono (fun _ hn => hn.2))
  simpa only [div_eq_mul_inv,mul_zero] using
    (tendsto_const_nhds.mul hMlim.inv_tendsto_atTop :
      Tendsto (fun n => (E*A)*(M n)⁻¹) atTop (𝓝 ((E*A)*0)))

end CannonApprox

end
end
end
end
end
end
end
end
end

end OAI
