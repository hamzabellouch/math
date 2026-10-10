import OAI.NumberTheory.JointDickman.Amplification.GraphEndpointDensity

namespace OAI

/-! # The periodic majorant of a fixed arithmetic graph representation -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def graphEdgeEnvelope (B a b c : ℕ) (j : ℤ) (n : ℕ) : ℝ :=
  if b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j then graphResidueEnvelope B a b c j n else 0

noncomputable def graphEdgePeriod (B a b c : ℕ) : ℕ :=
  a*b*∏ p ∈ graphGoodPrimes B a b c, p

noncomputable def graphEdgeMean (B a b c : ℕ) : ℝ :=
  (auxiliaryRatio B^(1/2 : ℝ))^3 *
    ((1/((a : ℝ)*b)) * ∏ p ∈ graphGoodPrimes B a b c, (1-3/(2*(p : ℝ))))

theorem zmod_representative_reduce {d q : ℕ} [NeZero q] (hd : d ∣ q) (n : ℕ) :
    (((n : ZMod q).val : ℕ) : ZMod d) = (n : ZMod d) := by
  rw [ZMod.val_natCast]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  exact Nat.mod_mod_of_dvd n hd

theorem graphEdgePeriod_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (B c : ℕ) :
    0 < graphEdgePeriod B a b c := by
  unfold graphEdgePeriod
  exact Nat.mul_pos (Nat.mul_pos ha hb)
    (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (mem_filter.mp hp).1).pos))

theorem graphGoodPrimes_coprime (B a b c : ℕ) :
    (a*b).Coprime (∏ p ∈ graphGoodPrimes B a b c, p) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  have h := (mem_filter.mp hp).2
  have hprime := auxiliaryPrimes_prime B p (mem_filter.mp hp).1
  exact Nat.Coprime.mul_left (hprime.coprime_iff_not_dvd.mpr h.1).symm
    (hprime.coprime_iff_not_dvd.mpr h.2.1).symm

theorem graphEdgeEnvelope_natCast {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (B c : ℕ) (j : ℤ) (n : ℕ) :
    graphEdgeEnvelope B a b c j (n : ZMod (graphEdgePeriod B a b c)).val =
      graphEdgeEnvelope B a b c j n := by
  classical
  let : NeZero (graphEdgePeriod B a b c) :=
    ⟨(graphEdgePeriod_pos (NeZero.pos a) (NeZero.pos b) B c).ne'⟩
  have habd : a*b ∣ graphEdgePeriod B a b c := dvd_mul_right _ _
  have hind := zmod_representative_reduce habd n
  have hiff : (b ∣ (n : ZMod (graphEdgePeriod B a b c)).val ∧
      (a : ℤ) ∣ ((n : ZMod (graphEdgePeriod B a b c)).val : ℤ)+j) ↔
      (b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j) := by
    rw [graph_endpoint_congruence hab, graph_endpoint_congruence hab, hind]
  unfold graphEdgeEnvelope
  rw [if_congr hiff rfl rfl]
  split_ifs
  · unfold graphResidueEnvelope
    congr 1
    apply prod_congr rfl
    intro p hp
    have hpd : p ∣ graphEdgePeriod B a b c :=
      (dvd_prod_of_mem id hp).trans (dvd_mul_left _ _)
    rw [zmod_representative_reduce hpd]
  · rfl

theorem graphEdgeEnvelope_mean {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (B c : ℕ) (j : ℤ)
    (hj : ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0)
    (he : (a : ℤ) = b+j*c) :
    letI : NeZero (graphEdgePeriod B a b c) :=
      ⟨(graphEdgePeriod_pos (NeZero.pos a) (NeZero.pos b) B c).ne'⟩
    (∑ x : ZMod (graphEdgePeriod B a b c), graphEdgeEnvelope B a b c j x.val) /
      (graphEdgePeriod B a b c : ℝ) = graphEdgeMean B a b c := by
  classical
  let G := graphGoodPrimes B a b c
  have hG : ∀ p ∈ G, p.Prime := fun p hp => auxiliaryPrimes_prime B p (mem_filter.mp hp).1
  let : NeZero (∏ p ∈ G, p) := ⟨prod_ne_zero_iff.mpr (fun p hp => (hG p hp).ne_zero)⟩
  let : ∀ p : G, NeZero p.val := fun p => ⟨(hG p p.property).ne_zero⟩
  have hm := graph_endpoint_three_root_mean hab G hG (graphGoodPrimes_coprime B a b c) j
    (fun p hp => (mem_filter.mp hp).2.1)
    (fun p hp => (mem_filter.mp hp).2.2.1)
    (fun p hp => (mem_filter.mp hp).2.2.2) hj he
  have hprod (n : ℕ) :
      (∏ p : G, residueWeight (1/2) (0 : ZMod p.val) (n : ZMod p.val) *
        residueWeight (1/2) (-(j : ZMod p.val)) (n : ZMod p.val) *
        residueWeight (1/2) ((b : ZMod p.val)*(c : ZMod p.val)⁻¹) (n : ZMod p.val)) =
      ∏ p ∈ G, residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
        residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
        residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p) :=
    G.prod_coe_sort (fun p : ℕ => residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
      residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
      residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p))
  simp_rw [hprod] at hm
  unfold graphEdgeEnvelope graphResidueEnvelope graphEdgePeriod graphEdgeMean
  have hid (n : ℕ) :
      (if b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j then
        (auxiliaryRatio B^(1/2 : ℝ))^3 *
          ∏ p ∈ G, residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
            residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
            residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p)
        else 0) =
      (auxiliaryRatio B^(1/2 : ℝ))^3 *
        ((if b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j then (1 : ℝ) else 0) *
          ∏ p ∈ G, residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
            residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
            residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p)) := by
    split_ifs <;> simp
  simp_rw [show graphGoodPrimes B a b c = G from rfl, hid]
  rw [← mul_sum, mul_div_assoc]
  simpa only [Nat.cast_mul, Nat.cast_prod] using congrArg
    (fun t : ℝ => (auxiliaryRatio B^(1/2 : ℝ))^3*t) hm

theorem graphEdgeEnvelope_average_tendsto {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (B c : ℕ) (j : ℤ)
    (hj : ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0)
    (he : (a : ℤ) = b+j*c) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, graphEdgeEnvelope B a b c j n)/(N : ℝ))
      atTop (𝓝 (graphEdgeMean B a b c)) := by
  let : NeZero (graphEdgePeriod B a b c) :=
    ⟨(graphEdgePeriod_pos (NeZero.pos a) (NeZero.pos b) B c).ne'⟩
  have h := real_periodic_moment_tendsto
    (fun x : ZMod (graphEdgePeriod B a b c) => graphEdgeEnvelope B a b c j x.val) 1
  simpa only [pow_one, graphEdgeEnvelope_natCast hab,
    graphEdgeEnvelope_mean hab B c j hj he] using h

end JointDickman

end OAI
