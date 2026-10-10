import Mathlib
import OAI.Geometry.Cannon.Energy.NormalizedModulus

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
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology

namespace CannonRecords

lemma exists_later_record (f : ℕ → ℝ) (hunbounded : ∀ C : ℝ, ∃ n, C < f n)
    (n : ℕ) (C : ℝ) :
    ∃ k, n < k ∧ C < f k ∧ ∀ l ≤ k, f l ≤ f k := by
  obtain ⟨a,ha,hmax⟩ := (Finset.range (n+1)).exists_max_image f (by simp)
  obtain ⟨m,hm⟩ := hunbounded (max C (f a))
  obtain ⟨k,hk,hkmax⟩ := (Finset.range (m+1)).exists_max_image f (by simp)
  have hmk : f m ≤ f k := hkmax m (by simp)
  have hnk : n < k := by
    by_contra hn
    have hk' : k ≤ n := le_of_not_gt hn
    have hak := hmax k (by simpa using hk')
    have hma : f a < f m := (le_max_right C (f a)).trans_lt hm
    linarith
  refine ⟨k,hnk,(le_max_left C (f a)).trans_lt (hm.trans_le hmk),?_⟩
  intro l hl
  apply hkmax l
  exact Finset.mem_range.mpr (lt_of_le_of_lt hl (Finset.mem_range.mp hk))

theorem exists_records (f : ℕ → ℝ) (hunbounded : ∀ C : ℝ, ∃ n, C < f n) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (f ∘ N) atTop atTop ∧
      ∀ j l, l ≤ N j → f l ≤ f (N j) := by
  choose next hnext using exists_later_record f hunbounded
  let N : ℕ → ℕ := fun j => Nat.rec (next 0 0) (fun i n => next n (i+1)) j
  have hzero : N 0 = next 0 0 := rfl
  have hsucc (i : ℕ) : N (i+1) = next (N i) (i+1) := rfl
  have hstrict : StrictMono N := strictMono_nat_of_lt_succ (fun i => by
    rw [hsucc]
    exact (hnext (N i) (i+1)).1)
  refine ⟨N,hstrict,?_,?_⟩
  · apply tendsto_atTop_mono (f := fun j : ℕ => (j:ℝ))
    · intro j
      cases j with
      | zero => simpa only [Function.comp_apply, hzero, Nat.cast_zero] using (hnext 0 0).2.1.le
      | succ j => simpa only [Function.comp_apply, hsucc, Nat.cast_add, Nat.cast_one] using
            (hnext (N j) (j+1)).2.1.le
    · exact tendsto_natCast_atTop_atTop
  · intro j l hl
    cases j with
    | zero => exact (hnext 0 0).2.2 l hl
    | succ j => exact (hnext (N j) (j+1)).2.2 l hl

theorem weighted_records (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n)
    (lam : ℝ) (hlam : 1 ≤ lam) (hunbounded : ∀ C : ℝ, ∃ n, C < M n / lam^n) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (M ∘ N) atTop atTop ∧
      ∀ j l, l ≤ N j → M (N j-l) ≤ (lam^l)⁻¹ * M (N j) := by
  obtain ⟨N,hN,hlim,hrecord⟩ := exists_records (fun n => M n/lam^n) hunbounded
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  refine ⟨N,hN,?_,?_⟩
  · apply tendsto_atTop_mono (g := M ∘ N) (f := (fun n => M n/lam^n) ∘ N) _ hlim
    intro j
    exact div_le_self (hM _) (one_le_pow₀ hlam)
  · intro j l hl
    have hh := hrecord j (N j-l) (Nat.sub_le _ _)
    have hpow : lam^(N j) = lam^(N j-l)*lam^l := by
      rw [← pow_add, Nat.sub_add_cancel hl]
    rw [div_le_div_iff₀ (pow_pos hlampos _) (pow_pos hlampos _)] at hh
    rw [hpow] at hh
    have : M (N j-l)*lam^l ≤ M (N j) := by
      apply (mul_le_mul_iff_left₀ (pow_pos hlampos (N j-l))).mp
      nlinarith [hh]
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ (pow_pos hlampos l)).mpr this

end CannonRecords

namespace CannonApprox

open CannonCharts CannonCells CannonGrid CannonRecords Filter

theorem record_scalar_sequence {X : Type*} [MetricSpace X] [CompactSpace X]
    (φ : X ≃ₜ CannonCharts.SphereTwo) (d : ℝ) (hd : 0 < d)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcover : ∀ n x, ∃ i, x ∈ Metric.ball (p n i) (2*r n))
    (hM : ∀ n, 0 < modulus (fun i => Metric.ball (p n i) (2*r n)) (macroFamily d))
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hunbounded : ∀ A : ℝ, ∃ n,
      A < modulus (fun i => Metric.ball (p n i) (2*r n)) (macroFamily d)/lam^n) :
    let M := fun n => modulus (fun i => Metric.ball (p n i) (2*r n)) (macroFamily d)
    ∃ e : Plane → X, Topology.IsOpenEmbedding e ∧
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (M ∘ N) atTop atTop ∧
        (∀ j l, l ≤ N j → M (N j-l) ≤ (lam^l)⁻¹*M (N j)) ∧
        ∃ ρ : (j : ℕ) → ι (N j) → ℝ, ∃ m : ℕ → ℕ, ∃ hm : ∀ j, 0 < m j,
          ∀ j, (∀ i, 0 ≤ ρ j i) ∧
            Admissible (fun i => (e ∘ squareMap) ⁻¹' Metric.ball (p (N j) i) (2*r (N j))) (ρ j) ∧
            (∑ i, (ρ j i)^2) ≤ A/M (N j) ∧
            (∀ z : Square, ∀ i : Index (3*m j), weight (3*m j) z i ≠ 0 →
              dist ((e ∘ squareMap) z)
                ((e ∘ squareMap) (vertex (3*m j) (by have := hm j; omega) i)) < r (N j)) := by
  let C := fun n i => Metric.ball (p n i) (2*r n)
  let M := fun n => modulus (C n) (macroFamily d)
  obtain ⟨R,hR,hMR,hrec⟩ := weighted_records M (fun n => (hM n).le) lam hlam hunbounded
  obtain ⟨e,he,A,hA,S,hS,ρ,hρ⟩ := localized_chart_reciprocal_weights φ d hd
    (fun n => ι (R n)) (fun n => C (R n)) (fun n => hcover (R n)) (fun n => hM (R n))
  let N := R ∘ S
  have hE : Topology.IsEmbedding (e ∘ squareMap) := he.isEmbedding.comp squareMap_embedding
  have hmesh (j : ℕ) := exists_mesh (e ∘ squareMap) hE.continuous (hr (N j))
  choose m hm hmesh using hmesh
  refine ⟨e,he,A,hA,N,hR.comp hS,hMR.comp hS.tendsto_atTop,?_,ρ,m,hm,?_⟩
  · intro j l hl
    exact hrec (S j) l hl
  · intro j
    exact ⟨(hρ j).1,(hρ j).2.1,(hρ j).2.2,hmesh j⟩

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
