import Mathlib
import OAI.Geometry.Cannon.Modulus.RadialCellEnergy
import OAI.Geometry.Cannon.Flows.Oscillation
import OAI.Geometry.Cannon.Energy.RawFunction

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
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonScalarEnergy

open CannonCrossEnergy CannonPacking

lemma oscillation_le_of_pairwise {Y : Type*} [TopologicalSpace Y]
    {f : Y → ℝ} (hf : Continuous f) {A : Set Y} (hA : IsCompact A)
    {E : ℝ} (hE : 0 ≤ E) (hpair : ∀ x ∈ A, ∀ y ∈ A, |f x-f y| ≤ E) :
    oscillation f A ≤ E := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simpa [CannonCrossEnergy.oscillation] using hE
  obtain ⟨x,hx,heqx⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨y,hy,heqy⟩ := (hA.image hf).sInf_mem (hne.image f)
  have hh := (le_abs_self (f x-f y)).trans (hpair x hx y hy)
  simpa only [CannonCrossEnergy.oscillation,← heqx,← heqy] using hh

lemma oscillation_nonneg_of_compact {Y : Type*} [TopologicalSpace Y]
    {f : Y → ℝ} (hf : Continuous f) {A : Set Y} (hA : IsCompact A) :
    0 ≤ oscillation f A := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [CannonCrossEnergy.oscillation]
  · exact oscillation_nonneg hf hA hne

theorem uniform_local_energy_bound {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    (Q : ℕ) (C A b : ℝ) (hp : PolynomialPacking (X := X) Q C)
    (hC : 0 ≤ C) (hA : 0 < A) (hb : 0 < b) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ {α β : Type*} [Fintype α] [Fintype β]
        (centers : α → X) (q : β → X) (r : ℝ),
        0 < r → max A (max 1 b)*r ≤ 1 →
        (∀ i j, i ≠ j → b*r ≤ dist (centers i) (centers j)) →
        (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
        ∀ (f : Y → ℝ), Continuous f → ∀ (cells : α → Set Y),
        (∀ i, IsCompact (cells i)) → ∀ (ρ : β → ℝ), (∀ j, 0 ≤ ρ j) →
        (∀ i, ∀ x ∈ cells i, ∀ y ∈ cells i, |f x-f y| ≤
          ∑ j ∈ Finset.univ.filter (fun j => dist (q j) (centers i) ≤ A*r), ρ j) →
        (∑ i, (oscillation f (cells i))^2) ≤ E*(∑ j, (ρ j)^2) := by
  classical
  obtain ⟨Bq,hBq⟩ := exists_overlap_bound Q C A 1 hp hC hA zero_lt_one
  obtain ⟨Bp,hBp⟩ := exists_overlap_bound Q C A b hp hC hA hb
  refine ⟨(Bq:ℝ)*Bp,by positivity,?_⟩
  intro α β _ _ centers q r hr hscale hc hq f hf cells hcells ρ hρ hlocal
  let R : α → Finset β := fun i => Finset.univ.filter
    (fun j => dist (q j) (centers i) ≤ A*r)
  have hscaleq : max A 1*r ≤ 1 := (mul_le_mul_of_nonneg_right
    (max_le_max_left A (le_max_left 1 b)) hr.le).trans hscale
  have hscalep : max A b*r ≤ 1 := (mul_le_mul_of_nonneg_right
    (max_le_max_left A (le_max_right 1 b)) hr.le).trans hscale
  have hrow : ∀ i, (R i).card ≤ Bq := by
    intro i
    simpa only [R,dist_comm] using hBq q Finset.univ (centers i) r hr hscaleq
      (fun i _ j _ hij => by simpa using hq i j hij)
  have hcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ Bp := by
    intro j
    simpa only [R,Finset.mem_filter,Finset.mem_univ,true_and] using
      hBp centers Finset.univ (q j) r hr hscalep (fun i _ j _ hij => hc i j hij)
  calc
    (∑ i, (oscillation f (cells i))^2) ≤ ∑ i, (∑ j ∈ R i, ρ j)^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (oscillation_nonneg_of_compact hf (hcells i))
        (oscillation_le_of_pairwise hf (hcells i)
          (Finset.sum_nonneg (fun j _ => hρ j)) (hlocal i)) 2
    _ ≤ (Bq:ℝ)*Bp*(∑ j, (ρ j)^2) :=
      CannonTransfer.overlap_energy R ρ Bq Bp hrow hcol

end CannonScalarEnergy

namespace CannonApprox

open CannonGrid CannonLevel CannonPacking CannonScalarEnergy CannonCrossEnergy CannonCells

theorem exists_scalar_energy_constant {X : Type*} [MetricSpace X]
    (Q : ℕ) (C L J b : ℝ) (hp : PolynomialPacking (X := X) Q C)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hJ : 0 < J) (hb : 0 < b)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (e : CannonGrid.Square → X), Topology.IsEmbedding e →
      ∀ {α β : Type*} [Fintype α] [Fintype β]
        (centers : α → X) (q : β → X) (r : ℝ),
        0 < r → max (L*(L*J+1)+3) (max 1 b)*r ≤ 1 →
        (∀ i j, i ≠ j → b*r ≤ dist (centers i) (centers j)) →
        (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
        (∀ i, Metric.ball (centers i) (L*(L*J+1)*r) ⊆ range e) →
        ∀ (ρ : β → ℝ), (∀ i, 0 ≤ ρ i) →
        Admissible (fun i => e ⁻¹' Metric.ball (q i) (2*r)) ρ →
        ∀ (n : ℕ) (hn : 0 < n),
        (∀ z : CannonGrid.Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
          dist (e z) (e (vertex (3*n) (by omega) i)) < r) →
        (∑ i, (CannonCrossEnergy.oscillation
          (scalar (fun j => e ⁻¹' Metric.ball (q j) (2*r)) ρ n hn)
          (e ⁻¹' Metric.closedBall (centers i) (J*r)))^2) ≤ E*(∑ j, (ρ j)^2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA : 0 < L*(L*J+1)+3 := by positivity
  obtain ⟨E,hE,hbound⟩ := uniform_local_energy_bound (Y := CannonGrid.Square)
    Q C (L*(L*J+1)+3) b hp hC hA hb
  refine ⟨E,hE,?_⟩
  intro e he α β _ _ centers q r hr hscale hcenters hq hchart ρ hρ hadm n hn hmesh
  have hf := (scalar_properties _ ρ hρ hadm n hn).1
  apply hbound centers q r hr hscale hcenters hq _ hf
    (fun i => e ⁻¹' Metric.closedBall (centers i) (J*r))
    (fun i => (isClosed_closedBall.preimage he.continuous).isCompact) ρ hρ
  intro i x hx y hy
  exact scalar_local_oscillation e he L J r hL hJ hr hpaths (centers i) (hchart i)
    q ρ hρ hadm n hn hmesh x y (by simpa [dist_comm] using hx)
      (by simpa [dist_comm] using hy)

theorem exists_scalar_of_crossing_modulus {X : Type*} [MetricSpace X]
    (Q : ℕ) (C L J b : ℝ) (hp : PolynomialPacking (X := X) Q C)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hJ : 0 < J) (hb : 0 < b)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (e : CannonGrid.Square → X), Topology.IsEmbedding e →
      ∀ {β : Type*} [Fintype β] (q : β → X) (r : ℝ),
        0 < r → max (L*(L*J+1)+3) (max 1 b)*r ≤ 1 →
        (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
        (∀ z : CannonGrid.Square, ∃ i, e z ∈ Metric.ball (q i) (2*r)) →
        ∃ f : CannonGrid.Square → ℝ,
          Continuous f ∧ (∀ z, f z ∈ Icc 0 1) ∧
          (∀ z ∈ topBand, f z = 0) ∧ (∀ z ∈ bottomBand, f z = 1) ∧
          (∀ t ∈ Ioo (0:ℝ) 1, ∃ A : Set CannonGrid.Square,
            IsCompact A ∧ IsConnected A ∧ A ⊆ centralRectangle ∧
            (∀ z ∈ A, f z = t) ∧ (∃ z ∈ A, z.1 = 0) ∧ (∃ z ∈ A, z.1 = 1) ∧
            (∀ {x y : CannonGrid.Square} (p : Path x y), f x < t →
              t < f y → ∃ s, p s ∈ A)) ∧
          (∀ {α : Type*} [Fintype α] (centers : α → X),
            (∀ i j, i ≠ j → b*r ≤ dist (centers i) (centers j)) →
            (∀ i, Metric.ball (centers i) (L*(L*J+1)*r) ⊆ range e) →
            (∑ i, (CannonCrossEnergy.oscillation f
                (e ⁻¹' Metric.closedBall (centers i) (J*r)))^2) ≤
              E*(modulus (fun j => e ⁻¹' Metric.ball (q j) (2*r)) CannonRectangle.leftRight)⁻¹) := by
  obtain ⟨E,hE,henergy⟩ := exists_scalar_energy_constant Q C L J b hp hC hL hJ hb hpaths
  refine ⟨E,hE,?_⟩
  intro e he β _ q r hr hscale hq hcover
  obtain ⟨_,ρ,hρ,hadm,hdual⟩ := CannonRectangle.exists_dual_weights
    (fun i => e ⁻¹' Metric.ball (q i) (2*r)) hcover
  obtain ⟨n,hn,hmesh⟩ := exists_mesh e he.continuous hr
  have hf := scalar_properties _ ρ hρ hadm n hn
  refine ⟨scalar _ ρ n hn,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,?_,?_⟩
  · intro t ht
    exact scalar_level _ ρ hρ hadm n hn ht
  · intro α _ centers hsep hchart
    rw [← hdual]
    exact henergy e he centers q r hr hscale hsep hq hchart ρ hρ hadm n hn hmesh

end CannonApprox

open Set Metric Topology

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
